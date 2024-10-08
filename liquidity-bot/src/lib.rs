// Copyright (c) 2023 MobileCoin Inc.

#![feature(assert_matches)]

// TODO:
// - Prometheus metrics
// - Fog support (grep for "FogResolver::default")
// - RTH support (grep for "EmptyMemoBuilder::default")

mod admin_service;
mod config;
mod convert;
mod error;
mod metrics;
pub mod mini_wallet;

pub use admin_service::AdminService;
pub use config::Config;
pub use error::Error;
pub use metrics::{update_periodic_metrics, METRICS_POLL_INTERVAL};

use deqs_api::{
    deqs::{QuoteStatusCode, SubmitQuotesRequest, SubmitQuotesResponse},
    deqs_grpc::DeqsClientApiClient,
    DeqsClientUri,
};
use deqs_quote_book_api::Quote;
use futures::executor::block_on;
use grpcio::{ChannelBuilder, EnvBuilder};
use mc_common::logger::{log, Logger};
use mc_crypto_ring_signature_signer::{LocalRingSigner, OneTimeKeyDeriveData};
use mc_fog_report_resolver::FogResolver;
use mc_ledger_db::{Ledger, LedgerDB};
use mc_transaction_builder::{
    EmptyMemoBuilder, InputCredentials, ReservedSubaddresses, SignedContingentInputBuilder,
};
use mc_transaction_core::{AccountKey, Amount, BlockVersion, RevealedTxOut, TokenId};
use mc_transaction_extra::SignedContingentInput;
use mc_util_grpc::ConnectionUriGrpcioChannel;
use mini_wallet::{MatchedTxOut, WalletEvent};
use rand::Rng;
use rust_decimal::{prelude::ToPrimitive, Decimal};
use serde::{Deserialize, Serialize};
use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};
use tokio::{
    sync::{mpsc, oneshot},
    time::interval,
};

// Minimum time to wait between attempts to submit SCIs to the DEQS.
const RESUBMIT_POLL_INTERVAL: Duration = Duration::from_secs(30);

// Minimum time to wait before re-submitting quotes to the DEQS.
// Note that quotes needing refreshed are checked every RESUBMIT_POLL_INTERVAL.
const QUOTE_REFRESH_INTERVAL: Duration = Duration::from_secs(600);

/// A TxOut we want to submit to the DEQS
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PendingTxOut {
    /// The TxOut we are tracking
    matched_tx_out: MatchedTxOut,

    /// The SCI we generated from the TxOut
    sci: SignedContingentInput,
}

/// A TxOut we listed on the DEQS
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ListedTxOut {
    /// The TxOut we are tracking
    matched_tx_out: MatchedTxOut,

    /// The quote we got from the DEQS.
    quote: Quote,

    /// Last time we tried to submit this TxOut to the DEQS.
    /// This is represented as milliseconds since Epoch to make it compatible
    /// with with Protobufs.
    last_submitted_at: u64,
}

/// Statistics about the liquidity bot's current state.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Stats {
    /// Number of pending TxOuts grouped by the TxOut's token id.
    num_pending_tx_outs_by_token_id: HashMap<TokenId, usize>,

    /// Total value of pending TxOuts grouped by the TxOut's token id.
    total_pending_tx_outs_value_by_token_id: HashMap<TokenId, u64>,

    /// Number of listed TxOuts grouped by the TxOut's token id.
    num_listed_tx_outs_by_token_id: HashMap<TokenId, usize>,

    /// Total value of listed TxOuts grouped by the TxOut's token id.
    total_listed_tx_outs_value_by_token_id: HashMap<TokenId, u64>,
}
impl From<&LiquidityBotTask> for Stats {
    fn from(task: &LiquidityBotTask) -> Self {
        let mut num_pending_tx_outs_by_token_id = HashMap::new();
        let mut total_pending_tx_outs_value_by_token_id = HashMap::new();

        for pending_tx_out in &task.pending_tx_outs {
            let token_id = pending_tx_out.matched_tx_out.amount.token_id;
            *num_pending_tx_outs_by_token_id.entry(token_id).or_default() += 1;
            *total_pending_tx_outs_value_by_token_id
                .entry(token_id)
                .or_default() += pending_tx_out.matched_tx_out.amount.value;
        }

        let mut num_listed_tx_outs_by_token_id = HashMap::new();
        let mut total_listed_tx_outs_value_by_token_id = HashMap::new();
        for listed_tx_out in &task.listed_tx_outs {
            let token_id = listed_tx_out.matched_tx_out.amount.token_id;
            *num_listed_tx_outs_by_token_id.entry(token_id).or_default() += 1;
            *total_listed_tx_outs_value_by_token_id
                .entry(token_id)
                .or_default() += listed_tx_out.matched_tx_out.amount.value;
        }

        // Ensure there's a zero value for each token id we know about but haven't
        // encountered.
        for token_id in task.pairs.keys().copied() {
            num_pending_tx_outs_by_token_id.entry(token_id).or_default();
            total_pending_tx_outs_value_by_token_id
                .entry(token_id)
                .or_default();
            num_listed_tx_outs_by_token_id.entry(token_id).or_default();
            total_listed_tx_outs_value_by_token_id
                .entry(token_id)
                .or_default();
        }

        Self {
            num_pending_tx_outs_by_token_id,
            total_pending_tx_outs_value_by_token_id,
            num_listed_tx_outs_by_token_id,
            total_listed_tx_outs_value_by_token_id,
        }
    }
}

/// Information about a fulfilled SCI.
/// Currently only used for logging/metrics but in the future we might store it
/// in a database or something like that.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FulfilledSci {
    /// The listed TxOut that was fulfilled.
    listed_tx_out: ListedTxOut,

    /// The partial fill output that we asked for as a condition for the SCI
    /// being consumed.
    requested_counter_output: RevealedTxOut,

    /// The partial fill output we received from the counterparty.
    received_counter_output: MatchedTxOut,

    /// Received base token change output
    received_base_change_output: Option<MatchedTxOut>,
}
impl FulfilledSci {
    pub fn fill_percents(&self) -> Result<f64, Error> {
        let requested_value = self.requested_counter_output.reveal_amount()?.0.value;
        let received_value = self.received_counter_output.amount.value;
        Ok((received_value as f64) / (requested_value as f64))
    }
}

/// Commands used for interfacing with the LiquidityBotTask.
#[derive(Debug)]
enum Command {
    /// Incoming wallet event.
    WalletEvent(WalletEvent),

    /// Get stats
    GetStats(oneshot::Sender<Stats>),

    /// Get pending TxOuts
    GetPendingTxOuts(oneshot::Sender<Vec<PendingTxOut>>),

    /// Get listed TxOuts
    GetListedTxOuts(oneshot::Sender<Vec<ListedTxOut>>),
}

struct LiquidityBotTask {
    /// Account key
    account_key: AccountKey,

    /// Ledger DB
    ledger_db: LedgerDB,

    /// Pairs we are interested in listing.
    /// This is a map of the base token to the counter token and the swap rate
    /// we are offering. The rate specifies how many counter tokens are
    /// needed to get one base token.
    pairs: HashMap<TokenId, (TokenId, Decimal)>,

    /// List of TxOuts we would like to submit to the DEQS.
    pending_tx_outs: Vec<PendingTxOut>,

    /// List of TxOuts we successfully submitted to the DEQS.
    listed_tx_outs: Vec<ListedTxOut>,

    /// Logger.
    logger: Logger,

    /// Command receiver.
    command_rx: mpsc::UnboundedReceiver<Command>,

    /// Shutdown receiver, used to signal the event loop to shutdown.
    shutdown_rx: mpsc::UnboundedReceiver<()>,

    /// Shutdown acknowledgement sender, used to signal the caller that the the
    /// event loop terminated (when it goes out of scope).
    shutdown_ack_tx: Option<mpsc::UnboundedSender<()>>,

    /// DEQS client.
    deqs_client: DeqsClientApiClient,
}

impl LiquidityBotTask {
    pub async fn run(mut self) {
        let shutdown_ack_tx = self.shutdown_ack_tx.take();

        let mut resubmit_tx_outs_interval = interval(RESUBMIT_POLL_INTERVAL);
        resubmit_tx_outs_interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);

        loop {
            tokio::select! {
                event = self.command_rx.recv() => {
                    match event {
                        Some(Command::WalletEvent(WalletEvent::BlockProcessed { received_tx_outs, spent_tx_outs, .. })) => {
                            // Look at spent TxOuts and see if they match any SCIs we submitted.
                            let spent_listed_tx_outs = self.unlist_spent_tx_outs(&spent_tx_outs);

                            match self.look_for_fulfilled_scis(&spent_listed_tx_outs, &received_tx_outs) {
                                Ok(fulfilled_scis) => {
                                    for fulfilled_sci in fulfilled_scis {
                                        metrics::PER_TOKEN_METRICS.update_metrics_from_fulfilled_sci(&fulfilled_sci);
                                    }
                                }

                                Err(err) => {
                                    log::error!(
                                        self.logger,
                                        "Error looking at spent TxOuts: {} (spent listed scis pubkeys: {:?})",
                                        err,
                                        spent_listed_tx_outs.iter().map(|ltxo| ltxo.matched_tx_out.tx_out.public_key).collect::<Vec<_>>(),
                                    );
                                }
                            }

                            // Try and add any new TxOuts to the pending list.
                            match self.update_pending_tx_outs_from_received_tx_outs(&received_tx_outs) {
                                Ok(true) => {
                                    // New tx outs were added to the pending queue, so lets try and submit it.
                                    if let Err(err) = self.submit_pending_tx_outs().await {
                                        log::info!(self.logger, "Error submitting pending TxOuts: {}", err);
                                    }
                                }

                                Ok(false) => {
                                    // Nothing new was added.
                                }

                                Err(err) => {
                                    log::error!(self.logger, "Error adding TxOut: {}", err);
                                }
                            }
                        }

                        Some(Command::GetStats(tx)) => {
                            tx.send(Stats::from(&self)).expect("channel should be open");
                        }

                        Some(Command::GetPendingTxOuts(tx)) => {
                            tx.send(self.pending_tx_outs.clone()).expect("channel should be open");
                        }

                        Some(Command::GetListedTxOuts(tx)) => {
                            tx.send(self.listed_tx_outs.clone()).expect("channel should be open");
                        }


                        None => {
                            log::error!(self.logger, "Wallet event receiver closed");
                            break;
                        }
                    }
                }

                _ = resubmit_tx_outs_interval.tick() => {
                    if let Err(err) = self.resubmit_listed_tx_outs(QUOTE_REFRESH_INTERVAL).await {
                        log::info!(self.logger, "Error resubmitting TxOuts: {}", err);
                    }

                    if let Err(err) = self.submit_pending_tx_outs().await {
                        log::info!(self.logger, "Error submitting pending TxOuts: {}", err);
                    }
               }

                _ = self.shutdown_rx.recv() => {
                    log::info!(&self.logger, "shutdown requested");
                    break
                }

            }
        }

        drop(shutdown_ack_tx);
    }

    /// Go over the list of spent TxOuts and see if any of them match any of the
    /// listed ones, returning the removed listed TxOuts.
    fn unlist_spent_tx_outs(&mut self, spent_tx_outs: &[MatchedTxOut]) -> Vec<ListedTxOut> {
        spent_tx_outs
            .iter()
            .filter_map(|mtxo| {
                let listed_txo_idx = self
                    .listed_tx_outs
                    .iter()
                    .position(|ltxo| ltxo.matched_tx_out.key_image == mtxo.key_image);
                listed_txo_idx.map(|idx| self.listed_tx_outs.remove(idx))
            })
            .collect()
    }

    /// Go over a list of spent ListedTxOuts and see if they were fulfilled or
    /// cancelled.
    fn look_for_fulfilled_scis(
        &mut self,
        spent_listed_tx_outs: &[ListedTxOut],
        received_tx_outs: &[MatchedTxOut],
    ) -> Result<Vec<FulfilledSci>, Error> {
        let mut fulfilled_scis = Vec::new();

        for listed_tx_out in spent_listed_tx_outs {
            let partial_fill_outputs = listed_tx_out
                .quote
                .sci()
                .tx_in
                .input_rules
                .as_ref()
                .map(|input_rules| &input_rules.partial_fill_outputs);

            let num_partial_fill_outputs = partial_fill_outputs
                .map(|partial_fill_outputs| partial_fill_outputs.len())
                .unwrap_or(0);
            if num_partial_fill_outputs != 1 {
                // At the moment, `create_pending_tx_out`, which generates the SCI, always
                // creates SCIs with a single partial fill output.
                log::warn!(self.logger, "Somehow ended up with a spent listed TxOut {} without exactly one partial fill output.", listed_tx_out.matched_tx_out.tx_out.public_key);
                continue;
            }

            let partial_fill_output = &partial_fill_outputs.unwrap()[0];

            // See if the partial fill output is included in this block, if it is then it
            // implies the SCI was consumed.
            let received_counter_output = received_tx_outs
                .iter()
                .find(|mtxo| mtxo.tx_out.public_key == partial_fill_output.tx_out.public_key);

            // There might be a change output holding whatever wasn't consumed from the
            // input the SCI was offering. This will happen for partial SCIs.
            let received_base_change_output = listed_tx_out
                .quote
                .sci()
                .tx_in
                .input_rules
                .as_ref()
                .and_then(|input_rules| input_rules.partial_fill_change.as_ref())
                .and_then(|txo| {
                    received_tx_outs
                        .iter()
                        .find(|mtxo| mtxo.tx_out.public_key == txo.tx_out.public_key)
                })
                .cloned();

            if received_base_change_output.is_none() {
                log::warn!(
                    self.logger,
                    "Somehow ended up with a spent listed TxOut {} without a change output.",
                    listed_tx_out.matched_tx_out.tx_out.public_key
                );
            }

            match received_counter_output.cloned() {
                Some(received_counter_output) => {
                    let fulfilled_sci = FulfilledSci {
                        requested_counter_output: partial_fill_output.clone(),
                        listed_tx_out: listed_tx_out.clone(),
                        received_counter_output,
                        received_base_change_output,
                    };

                    log::info!(
                        self.logger,
                        "TxOut {} was spent, and the partial fill output {} was included in block with amount {:?} ({}% filled). {:?} change returned",
                        fulfilled_sci.listed_tx_out.matched_tx_out.tx_out.public_key,
                        fulfilled_sci.received_counter_output.tx_out.public_key,
                        fulfilled_sci.received_counter_output.amount,
                        fulfilled_sci.fill_percents()? * 100.0,
                        fulfilled_sci.received_base_change_output.as_ref().map(|mtxo| mtxo.amount),
                    );

                    fulfilled_scis.push(fulfilled_sci);
                }
                None => {
                    log::info!(self.logger, "TxOut {} was spent, but the partial fill output was not included in block. Maybe SCI got cancelled?", listed_tx_out.matched_tx_out.tx_out.public_key);
                }
            }
        }

        Ok(fulfilled_scis)
    }

    /// Updates our pending TxOuts from the received TxOuts, returning Ok(true)
    /// if we added any new ones.
    fn update_pending_tx_outs_from_received_tx_outs(
        &mut self,
        matched_tx_outs: &[MatchedTxOut],
    ) -> Result<bool, Error> {
        let mut added = false;

        for matched_tx_out in matched_tx_outs.iter().cloned() {
            // Check if this is a TxOut for a token we are capable of calculating a swap
            // rate for.
            if !self.pairs.contains_key(&matched_tx_out.amount.token_id) {
                continue;
            }

            // See if we already have this TxOut in our lists. We want to do this
            // check since its possible we will encounter the same TxOut twice
            // when the bot starts up due to a race between when the ledger
            // scanner starts scanning the blockchain and when we grab the list of currently
            // matched TxOuts in the ledger.
            // We compare by key image since its faster than comparing the whole
            // MatchedTxOut and it uniquely identifies a TxOut.
            if self
                .pending_tx_outs
                .iter()
                .any(|ptxo| ptxo.matched_tx_out.key_image == matched_tx_out.key_image)
            {
                continue;
            }

            if self
                .listed_tx_outs
                .iter()
                .any(|ltxo| ltxo.matched_tx_out.key_image == matched_tx_out.key_image)
            {
                continue;
            }

            let tracked_tx_out = self.create_pending_tx_out(matched_tx_out)?;
            self.pending_tx_outs.push(tracked_tx_out);
            added = true;
        }

        Ok(added)
    }

    async fn submit_pending_tx_outs(&mut self) -> Result<(), Error> {
        if self.pending_tx_outs.is_empty() {
            return Ok(());
        }

        // TODO should batch in case we have too many
        let scis = self
            .pending_tx_outs
            .iter()
            .map(|pending_tx_out| (&pending_tx_out.sci).into())
            .collect();
        let mut req = SubmitQuotesRequest::default();
        req.set_quotes(scis);

        let resp = self.submit_quotes(&req).await?;
        sanity_check_submit_quotes_response(&resp, req.quotes.len())?;

        for (pending_tx_out, status_code, error_msg, quote) in itertools::izip!(
            self.pending_tx_outs.drain(..),
            &resp.status_codes,
            &resp.error_messages,
            &resp.quotes
        ) {
            match status_code {
                QuoteStatusCode::CREATED | QuoteStatusCode::QUOTE_ALREADY_EXISTS => {
                    let quote = Quote::try_from(quote)?;

                    // Check if the SCI is actually the one we submitted, or a different one.
                    if quote.sci() == &pending_tx_out.sci {
                        log::info!(
                            self.logger,
                            "Submitted TxOut {} to DEQS, quote id is {}",
                            hex::encode(pending_tx_out.matched_tx_out.tx_out.public_key),
                            quote.id(),
                        );
                    } else {
                        assert_eq!(status_code, &QuoteStatusCode::QUOTE_ALREADY_EXISTS);
                        log::info!(
                            self.logger,
                            "DEQS returned a different SCI than the one we submitted for TxOut {}",
                            hex::encode(pending_tx_out.matched_tx_out.tx_out.public_key),
                        );
                    }

                    // NOTE: We are taking the SCI that is returned from the DEQS, and not the one
                    // we submitted. We do this because it is possible that the
                    // DEQS will already have an SCI for the TxOut we just tried
                    // using. For example, this could happen when the bot restarts.
                    // The important implication of this is that once we pick up whatever SCI we got
                    // from the DEQS and put it in our `listed_tx_outs` list, we
                    // will keep re-submitting it (trying to keep it listed). In
                    // the future we might want to change this behavior to only do this if the swap
                    // rate is the one we are configured for. Some other options
                    // for followup work are:
                    //
                    // 1. Have the bot persist which SCIs it submitted, so after a restart it does
                    // not get surprised when its  TxOutss are already listed.
                    //
                    // 2. Have the bot cancel SCIs that are not the one it submitted, but this would
                    // only make sense if it persists state since otherwise it will cancel all of
                    // its SCIs every time it restarts.
                    let listed_tx_out = ListedTxOut {
                        matched_tx_out: pending_tx_out.matched_tx_out,
                        quote,
                        last_submitted_at: now_since_epoch(),
                    };
                    self.listed_tx_outs.push(listed_tx_out);
                }

                QuoteStatusCode::QUOTE_IS_STALE => {
                    log::info!(
                        self.logger,
                        "DEQS rejected TxOut {}: quote is stale",
                        hex::encode(pending_tx_out.matched_tx_out.tx_out.public_key)
                    );
                }

                err => {
                    log::error!(
                        self.logger,
                        "DEQS rejected TxOut {} for a reason we did not expect: {:?} ({})",
                        hex::encode(pending_tx_out.matched_tx_out.tx_out.public_key),
                        err,
                        error_msg,
                    );
                }
            }
        }

        Ok(())
    }

    async fn resubmit_listed_tx_outs(&mut self, older_than: Duration) -> Result<(), Error> {
        // Split our listed list into two: those that we want to try and resubmit and
        // those that have been resubmitted recently enough.
        let current_time = now_since_epoch();

        let (to_resubmit, to_keep) =
            self.listed_tx_outs
                .drain(..)
                .partition::<Vec<_>, _>(|listed_tx_out| {
                    current_time
                        .checked_sub(listed_tx_out.last_submitted_at)
                        .unwrap_or_default()
                        > older_than.as_millis() as u64
                });
        self.listed_tx_outs = to_keep;

        if to_resubmit.is_empty() {
            return Ok(());
        }

        log::debug!(
            self.logger,
            "Need to resubmit {} TxOuts and hold on {} TxOuts",
            to_resubmit.len(),
            self.listed_tx_outs.len()
        );

        // TODO should batch in case we have too many to resubmit
        let scis = to_resubmit
            .iter()
            .map(|tracked_tx_out| tracked_tx_out.quote.sci().into())
            .collect();
        let mut req = SubmitQuotesRequest::default();
        req.set_quotes(scis);

        // Try and submit the quotes to the DEQS, if it fails we need to put them back
        // and assume they are still listed. We will try again later.
        let resp = match self.submit_quotes(&req).await {
            Ok(resp) => resp,
            Err(err) => {
                self.listed_tx_outs.extend(to_resubmit);
                return Err(err);
            }
        };
        sanity_check_submit_quotes_response(&resp, req.quotes.len())?;

        for (mut listed_tx_out, status_code, error_msg, quote) in itertools::izip!(
            to_resubmit,
            &resp.status_codes,
            &resp.error_messages,
            &resp.quotes
        ) {
            match status_code {
                QuoteStatusCode::CREATED => {
                    let quote = Quote::try_from(quote)?;

                    // Sanity check that the DEQS is behaving as expected.
                    assert_eq!(quote.sci(), listed_tx_out.quote.sci());

                    log::info!(
                        self.logger,
                        "Re-submitted TxOut {} to DEQS, quote id is {}",
                        hex::encode(listed_tx_out.matched_tx_out.tx_out.public_key),
                        quote.id(),
                    );
                    listed_tx_out.quote = quote.clone();
                    listed_tx_out.last_submitted_at = now_since_epoch();
                    self.listed_tx_outs.push(listed_tx_out);
                }

                QuoteStatusCode::QUOTE_ALREADY_EXISTS => {
                    let quote = Quote::try_from(quote)?;

                    if quote == listed_tx_out.quote {
                        log::debug!(
                            self.logger,
                            "DEQS confirmed quote {} is still listed",
                            quote.id(),
                        );
                    } else {
                        log::info!(
                            self.logger,
                            "DEQS returned a different SCI than the one we submitted for TxOut {}",
                            hex::encode(listed_tx_out.matched_tx_out.tx_out.public_key),
                        );

                        // See long comment in `submit_pending_tx_outs` about why we do this.
                        // The TLDR is that its possible there was a different quote listed for the
                        // SCI we submitted.
                        listed_tx_out.quote = quote;
                    }

                    listed_tx_out.last_submitted_at = now_since_epoch();
                    self.listed_tx_outs.push(listed_tx_out);
                }

                QuoteStatusCode::QUOTE_IS_STALE => {
                    log::info!(self.logger, "Quote {} expired", listed_tx_out.quote.id());
                }

                err => {
                    // NOTE: Right now this implies we stop tracking the listed TxOut.
                    log::error!(
                        self.logger,
                        "DEQS rejected TxOut {} for a reason we did not expect: {:?} ({})",
                        hex::encode(listed_tx_out.matched_tx_out.tx_out.public_key),
                        err,
                        error_msg,
                    );
                }
            }
        }

        Ok(())
    }

    fn create_pending_tx_out(&self, matched_tx_out: MatchedTxOut) -> Result<PendingTxOut, Error> {
        let (counter_token_id, swap_rate) = self
            .pairs
            .get(&matched_tx_out.amount.token_id)
            .ok_or(Error::UnknownTokenId(matched_tx_out.amount.token_id))?;

        let counter_amount: u64 = (Decimal::from(matched_tx_out.amount.value) * swap_rate)
            .ceil() // We round up in case the conversion results in a fractional amount.
            .to_u64()
            .ok_or_else(|| {
                Error::DecimalConversion(format!(
                    "Could not convert {} times {} to u64",
                    matched_tx_out.amount.value, swap_rate
                ))
            })?;

        log::info!(
            self.logger,
            "Creating SCI for TxOut with amount {}: wanting {} counter tokens (token id {})",
            matched_tx_out.amount.value,
            counter_amount,
            counter_token_id,
        );

        // Construct a ring. The first step is to choose tx out indices.
        let mut rng = rand::thread_rng();
        let mut sampled_indices = HashSet::new();

        const RING_SIZE: usize = 11;
        let num_txos = self.ledger_db.num_txos()?;
        while sampled_indices.len() < RING_SIZE {
            let index = rng.gen_range(0..num_txos);
            sampled_indices.insert(index);
        }
        let mut sampled_indices_vec: Vec<u64> = sampled_indices.into_iter().collect();

        // Ensure our TxOut is in the ring. Always using index 0 is safe since
        // InputCredentials::new sorts the ring.
        let our_tx_out_index = self
            .ledger_db
            .get_tx_out_index_by_public_key(&matched_tx_out.tx_out.public_key)?;
        sampled_indices_vec[0] = our_tx_out_index;

        // Get the actual TxOuts
        let tx_outs = sampled_indices_vec
            .iter()
            .map(|idx| self.ledger_db.get_tx_out_by_index(*idx))
            .collect::<Result<Vec<_>, _>>()?;

        // Get proofs for all those indexes.
        let proofs = self
            .ledger_db
            .get_tx_out_proof_of_memberships(&sampled_indices_vec)?;

        // Create our InputCredentials
        let input_credentials = InputCredentials::new(
            tx_outs,
            proofs,
            0,
            OneTimeKeyDeriveData::SubaddressIndex(matched_tx_out.subaddress_index),
            *self.account_key.view_private_key(),
        )?;

        // Build the SCI
        let block_version = BlockVersion::MAX;
        let fog_resolver = FogResolver::default(); // TODO

        let mut builder = SignedContingentInputBuilder::new(
            block_version,
            input_credentials,
            fog_resolver,
            EmptyMemoBuilder, // TODO
        )?;
        builder.add_partial_fill_output(
            Amount::new(counter_amount, *counter_token_id),
            &self.account_key.default_subaddress(),
            &mut rng,
        )?;
        builder.add_partial_fill_change_output(
            matched_tx_out.amount,
            &ReservedSubaddresses::from(&self.account_key),
            &mut rng,
        )?;
        let sci = builder.build(&LocalRingSigner::from(&self.account_key), &mut rng)?;

        Ok(PendingTxOut {
            matched_tx_out,
            sci,
        })
    }

    async fn submit_quotes(
        &self,
        req: &SubmitQuotesRequest,
    ) -> Result<SubmitQuotesResponse, Error> {
        let start = Instant::now();

        let resp = self
            .deqs_client
            .submit_quotes_async(req)
            .map_err(|err| {
                metrics::SUBMIT_QUOTES_GRPC_FAIL.observe(start.elapsed().as_secs_f64());
                err
            })?
            .await
            .map_err(|err| {
                metrics::SUBMIT_QUOTES_GRPC_FAIL.observe(start.elapsed().as_secs_f64());
                err
            })?;

        metrics::SUBMIT_QUOTES_GRPC_SUCCESS.observe(start.elapsed().as_secs_f64());

        Ok(resp)
    }
}

/// Interface for interacting with the liquidity bot
#[derive(Clone)]
pub struct LiquidityBotInterface {
    /// Command tx, used to send commands to the event loop.
    command_tx: mpsc::UnboundedSender<Command>,
}

impl LiquidityBotInterface {
    /// Bridge in a wallet event.
    pub fn notify_wallet_event(&self, event: WalletEvent) {
        self.command_tx
            .send(Command::WalletEvent(event))
            .expect("command tx failed"); // We assume the channel stays
                                          // open for as long as the bot is
                                          // running.
    }

    /// Get statistics.
    pub async fn stats(&self) -> Stats {
        let (tx, rx) = oneshot::channel();
        self.command_tx
            .send(Command::GetStats(tx))
            .expect("command tx failed");
        rx.await.expect("command rx failed")
    }

    /// Get pending tx outs.
    pub async fn pending_tx_outs(&self) -> Vec<PendingTxOut> {
        let (tx, rx) = oneshot::channel();
        self.command_tx
            .send(Command::GetPendingTxOuts(tx))
            .expect("command tx failed");
        rx.await.expect("command rx failed")
    }

    /// Get listed tx outs.
    pub async fn listed_tx_outs(&self) -> Vec<ListedTxOut> {
        let (tx, rx) = oneshot::channel();
        self.command_tx
            .send(Command::GetListedTxOuts(tx))
            .expect("command tx failed");
        rx.await.expect("command rx failed")
    }
}

pub struct LiquidityBot {
    /// Interface for interacting with the liquidity bot.
    interface: LiquidityBotInterface,

    /// Shutdown sender, used to signal the event loop to shutdown.
    shutdown_tx: mpsc::UnboundedSender<()>,

    /// Shutdown acknowledged receiver.
    shutdown_ack_rx: mpsc::UnboundedReceiver<()>,
}
impl LiquidityBot {
    /// Construct a new LiquidityBot instance.
    pub fn new(
        account_key: AccountKey,
        ledger_db: LedgerDB,
        pairs: HashMap<TokenId, (TokenId, Decimal)>,
        deqs_uri: &DeqsClientUri,
        logger: Logger,
    ) -> Self {
        let (command_tx, command_rx) = mpsc::unbounded_channel();
        let (shutdown_tx, shutdown_rx) = mpsc::unbounded_channel();
        let (shutdown_ack_tx, shutdown_ack_rx) = mpsc::unbounded_channel();

        let env = Arc::new(EnvBuilder::new().name_prefix("deqs-client-grpc").build());
        let ch = ChannelBuilder::default_channel_builder(env).connect_to_uri(deqs_uri, &logger);
        let deqs_client = DeqsClientApiClient::new(ch);

        let task = LiquidityBotTask {
            account_key,
            ledger_db,
            pairs,
            pending_tx_outs: Vec::new(),
            listed_tx_outs: Vec::new(),
            command_rx,
            deqs_client,
            shutdown_rx,
            shutdown_ack_tx: Some(shutdown_ack_tx),
            logger,
        };
        tokio::spawn(task.run());
        Self {
            interface: LiquidityBotInterface { command_tx },
            shutdown_tx,
            shutdown_ack_rx,
        }
    }

    pub fn interface(&self) -> &LiquidityBotInterface {
        &self.interface
    }

    /// Request the event loop task to shut down.
    pub async fn shutdown(&mut self) {
        if self.shutdown_tx.send(()).is_err() {
            return;
        }

        // Wait for the event loop to drop the ack sender.
        let _ = self.shutdown_ack_rx.recv().await;
    }
}

impl Drop for LiquidityBot {
    fn drop(&mut self) {
        block_on(self.shutdown());
    }
}

fn sanity_check_submit_quotes_response(
    resp: &SubmitQuotesResponse,
    expected_len: usize,
) -> Result<(), Error> {
    if resp.status_codes.len() != expected_len {
        return Err(Error::InvalidGrpcResponse(format!("Number of status codes in response does not match number of quotes in request. Expected {}, got {}.", expected_len, resp.status_codes.len())));
    }

    if resp.error_messages.len() != expected_len {
        return Err(Error::InvalidGrpcResponse(format!("Number of error messages in response does not match number of quotes in request. Expected {}, got {}.", expected_len, resp.error_messages.len())));
    }

    if resp.quotes.len() != expected_len {
        return Err(Error::InvalidGrpcResponse(format!("Number of quotes in response does not match number of quotes in request. Expected {}, got {}.", expected_len, resp.quotes.len())));
    }

    Ok(())
}

fn now_since_epoch() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("System time is before UNIX_EPOCH")
        .as_millis() as u64
}

#[cfg(test)]
mod tests {
    use std::assert_matches::assert_matches;

    use crate::mini_wallet::AccountLedgerScanner;

    use super::*;
    use deqs_api::deqs as grpc_api;
    use deqs_quote_book_api::Quote;
    use deqs_test_server::DeqsTestServer;
    use mc_common::logger::{async_test_with_logger, Logger};
    use mc_crypto_ring_signature_signer::NoKeysRingSigner;
    use mc_ledger_db::test_utils::{
        add_txos_and_key_images_to_ledger, create_ledger, initialize_ledger,
    };
    use mc_transaction_builder::{test_utils::get_input_credentials, TransactionBuilder};
    use mc_transaction_core::{constants::MILLIMOB_TO_PICOMOB, Token};
    use mc_transaction_core_test_utils::{get_outputs, KeyImage, Mob, MockFogResolver};
    use rand::{rngs::StdRng, RngCore, SeedableRng};
    use rust_decimal_macros::dec;

    struct TestContext {
        deqs_server: DeqsTestServer,
        task: LiquidityBotTask,
        ledger_db: LedgerDB,
        account_key: AccountKey,
        rng: StdRng,
    }
    impl TestContext {
        pub fn new(pairs: &[(TokenId, TokenId, Decimal)], logger: &Logger) -> Self {
            let mut rng: StdRng = SeedableRng::from_seed([1u8; 32]);
            let account_key = AccountKey::random(&mut rng);

            let mut ledger_db = create_ledger();
            let n_blocks = 3;
            initialize_ledger(
                BlockVersion::MAX,
                &mut ledger_db,
                n_blocks,
                &account_key,
                &mut rng,
            );

            let deqs_server = DeqsTestServer::start(logger.clone());
            let deqs_client = deqs_server.client();

            let (_command_tx, command_rx) = mpsc::unbounded_channel();
            let (_shutdown_tx, shutdown_rx) = mpsc::unbounded_channel();
            let (shutdown_ack_tx, _shutdown_ack_rx) = mpsc::unbounded_channel();

            let pairs = pairs
                .iter()
                .map(|(base_token, counter_token, rate)| (*base_token, (*counter_token, *rate)))
                .collect();

            let task = LiquidityBotTask {
                account_key: account_key.clone(),
                ledger_db: ledger_db.clone(),
                pairs,
                pending_tx_outs: Vec::new(),
                listed_tx_outs: Vec::new(),
                command_rx,
                deqs_client,
                shutdown_rx,
                shutdown_ack_tx: Some(shutdown_ack_tx),
                logger: logger.clone(),
            };

            Self {
                deqs_server,
                task,
                ledger_db,
                account_key,
                rng,
            }
        }

        pub fn create_matched_tx_out(&mut self, amount: Amount) -> MatchedTxOut {
            let recipient = self.account_key.default_subaddress();
            let recipient_and_amount = vec![(recipient, amount)];
            let outputs = get_outputs(BlockVersion::MAX, &recipient_and_amount, &mut self.rng);

            let block_data = add_txos_and_key_images_to_ledger(
                &mut self.ledger_db,
                BlockVersion::MAX,
                outputs,
                vec![KeyImage::from(self.rng.next_u64())],
                &mut self.rng,
            )
            .unwrap();

            MatchedTxOut {
                block_index: block_data.block().index,
                tx_out: block_data.contents().outputs[0].clone(),
                amount,
                subaddress_index: 0,
                key_image: KeyImage::from(self.rng.next_u64()),
            }
        }
    }

    fn default_pairs() -> Vec<(TokenId, TokenId, Decimal)> {
        vec![
            // MOB for eUSD at a rate of 0.5eUSD per MOB
            (TokenId::MOB, TokenId::from(1), dec!(0.5)),
            // eUSD for MOB at a rate of 3.0MOB per eUSD
            (TokenId::from(1), TokenId::MOB, dec!(3.0)),
        ]
    }

    #[async_test_with_logger]
    async fn update_pending_tx_outs_from_received_tx_outs_behaves_correctly(logger: Logger) {
        let mut test_ctx = TestContext::new(&default_pairs(), &logger);
        assert_eq!(test_ctx.task.pending_tx_outs.len(), 0);

        // Create four MatchedTxOuts, two for each pair the bot is offering and two
        // unrelated ones.
        let matched_tx_outs = vec![
            test_ctx.create_matched_tx_out(Amount::new(100, TokenId::MOB)),
            test_ctx.create_matched_tx_out(Amount::new(100, TokenId::from(1))),
            test_ctx.create_matched_tx_out(Amount::new(100, TokenId::from(2))),
            test_ctx.create_matched_tx_out(Amount::new(100, TokenId::from(3))),
        ];

        assert!(test_ctx
            .task
            .update_pending_tx_outs_from_received_tx_outs(&matched_tx_outs)
            .unwrap());

        // We should see two pending tx outs, one for each pair the bot is offering.
        assert_eq!(test_ctx.task.pending_tx_outs.len(), 2);

        for (idx, (expected_token_id, expected_partial_amount)) in
            [(TokenId::from(1), dec!(50)), (TokenId::from(0), dec!(300))]
                .iter()
                .enumerate()
        {
            assert_eq!(
                test_ctx.task.pending_tx_outs[idx].matched_tx_out,
                matched_tx_outs[idx]
            );
            let sci = &test_ctx.task.pending_tx_outs[idx].sci;

            assert!(sci.tx_in.ring.contains(&matched_tx_outs[idx].tx_out));

            let input_rules = sci.tx_in.input_rules.as_ref().unwrap();
            assert_eq!(input_rules.partial_fill_outputs.len(), 1);
            let (partial_fill_amount, _) =
                input_rules.partial_fill_outputs[0].reveal_amount().unwrap();
            assert_eq!(partial_fill_amount.token_id, *expected_token_id);
            assert_eq!(
                Decimal::from(partial_fill_amount.value),
                *expected_partial_amount
            );
        }

        // Calling update_pending_tx_outs_from_received_tx_outs with just TxOuts for
        // tokens the bot is not configured for should result in nothing getting
        // added..
        let orig_pending_tx_outs = test_ctx.task.pending_tx_outs.clone();

        assert!(!test_ctx
            .task
            .update_pending_tx_outs_from_received_tx_outs(&[
                matched_tx_outs[2].clone(),
                matched_tx_outs[3].clone()
            ])
            .unwrap(),);

        assert_eq!(test_ctx.task.pending_tx_outs, orig_pending_tx_outs);
    }

    #[async_test_with_logger]
    async fn submit_pending_tx_outs_behaves_correctly(logger: Logger) {
        let mut test_ctx = TestContext::new(&default_pairs(), &logger);

        let matched_tx_outs = vec![
            test_ctx.create_matched_tx_out(Amount::new(100, TokenId::MOB)),
            test_ctx.create_matched_tx_out(Amount::new(100, TokenId::from(1))),
        ];

        assert!(test_ctx
            .task
            .update_pending_tx_outs_from_received_tx_outs(&matched_tx_outs)
            .unwrap());

        // We now have two pending tx outs, and our test DEQS server currently returns
        // an error response for submit requests. Calling submit_pending_tx_outs
        // is expected to try and submit our two SCIs and when it gets a failure
        // put them back in the pending queue.
        let orig_pending_tx_outs = test_ctx.task.pending_tx_outs.clone();

        assert_matches!(
            test_ctx.task.submit_pending_tx_outs().await,
            Err(Error::Grpc(..))
        );

        assert_eq!(test_ctx.task.pending_tx_outs, orig_pending_tx_outs);

        // Set the test DEQS server to return a quote is stale response for the first
        // quote, and an invalid SCI response for the second quote. In both
        // cases the bot should remove the pending tx out from the queue and not
        // track them in listed_tx_outs.
        let resp = SubmitQuotesResponse {
            status_codes: vec![
                QuoteStatusCode::QUOTE_IS_STALE,
                QuoteStatusCode::INVALID_SCI,
            ],
            quotes: vec![grpc_api::Quote::default(), grpc_api::Quote::default()].into(),
            error_messages: vec!["".to_string(), "".to_string()].into(),
            ..Default::default()
        };
        test_ctx.deqs_server.set_submit_quotes_response(Ok(resp));

        test_ctx.task.submit_pending_tx_outs().await.unwrap();
        assert!(test_ctx.task.pending_tx_outs.is_empty());
        assert!(test_ctx.task.listed_tx_outs.is_empty());

        // Put the two pending tx outs back in the queue and set the test DEQS
        // server to accept one of them and pretend the other one is a
        // duplicate.
        assert!(test_ctx
            .task
            .update_pending_tx_outs_from_received_tx_outs(&matched_tx_outs)
            .unwrap());

        let mtxo = test_ctx.create_matched_tx_out(Amount::new(100, TokenId::from(1)));
        let ptxo = test_ctx.task.create_pending_tx_out(mtxo).unwrap();

        let quote1 = Quote::new(test_ctx.task.pending_tx_outs[0].sci.clone(), None).unwrap();
        let quote2 = Quote::new(ptxo.sci, None).unwrap();

        let resp = SubmitQuotesResponse {
            status_codes: vec![
                QuoteStatusCode::CREATED,
                QuoteStatusCode::QUOTE_ALREADY_EXISTS,
            ],
            quotes: vec![
                grpc_api::Quote::from(&quote1),
                grpc_api::Quote::from(&quote2),
            ]
            .into(),
            error_messages: vec!["".to_string(), "".to_string()].into(),
            ..Default::default()
        };
        test_ctx.deqs_server.set_submit_quotes_response(Ok(resp));

        test_ctx.task.submit_pending_tx_outs().await.unwrap();
        assert!(test_ctx.task.pending_tx_outs.is_empty());

        assert_eq!(test_ctx.task.listed_tx_outs.len(), 2);

        assert_eq!(
            test_ctx.task.listed_tx_outs[0].matched_tx_out,
            matched_tx_outs[0]
        );
        assert_eq!(test_ctx.task.listed_tx_outs[0].quote, quote1);

        assert_eq!(
            test_ctx.task.listed_tx_outs[1].matched_tx_out,
            matched_tx_outs[1]
        );
        assert_eq!(test_ctx.task.listed_tx_outs[1].quote, quote2);
    }

    #[async_test_with_logger]
    async fn update_pending_tx_outs_from_received_tx_outs_ignores_duplicates(logger: Logger) {
        let mut test_ctx = TestContext::new(&default_pairs(), &logger);

        // Note that while they have the same value, they are different TxOuts so not
        // considered duplicates.
        let matched_tx_outs = vec![
            test_ctx.create_matched_tx_out(Amount::new(100, TokenId::MOB)),
            test_ctx.create_matched_tx_out(Amount::new(100, TokenId::MOB)),
        ];

        assert!(test_ctx
            .task
            .update_pending_tx_outs_from_received_tx_outs(&matched_tx_outs)
            .unwrap());

        assert_eq!(test_ctx.task.pending_tx_outs.len(), 2);

        // Trying to add again should return false and nothing should change.
        let orig_pending_tx_outs = test_ctx.task.pending_tx_outs.clone();
        assert!(!test_ctx
            .task
            .update_pending_tx_outs_from_received_tx_outs(&matched_tx_outs)
            .unwrap());
        assert_eq!(orig_pending_tx_outs, test_ctx.task.pending_tx_outs);

        // Adding a new ones should work.
        let matched_tx_outs = vec![
            test_ctx.create_matched_tx_out(Amount::new(100, TokenId::MOB)),
            test_ctx.create_matched_tx_out(Amount::new(100, TokenId::MOB)),
        ];
        assert!(test_ctx
            .task
            .update_pending_tx_outs_from_received_tx_outs(&matched_tx_outs)
            .unwrap());

        assert_eq!(test_ctx.task.pending_tx_outs.len(), 4);

        // We also ignore duplicates in the listed_tx_outs list.
        let matched_tx_outs = vec![
            test_ctx.create_matched_tx_out(Amount::new(100, TokenId::MOB)),
            test_ctx.create_matched_tx_out(Amount::new(100, TokenId::MOB)),
        ];

        test_ctx.task.listed_tx_outs = matched_tx_outs
            .iter()
            .map(|mtxo| {
                let ptxo = test_ctx.task.create_pending_tx_out(mtxo.clone()).unwrap();
                let quote = Quote::new(ptxo.sci, None).unwrap();
                ListedTxOut {
                    matched_tx_out: mtxo.clone(),
                    quote,
                    last_submitted_at: now_since_epoch(),
                }
            })
            .collect();

        let orig_pending_tx_outs = test_ctx.task.pending_tx_outs.clone();
        assert!(!test_ctx
            .task
            .update_pending_tx_outs_from_received_tx_outs(&matched_tx_outs)
            .unwrap());
        assert_eq!(orig_pending_tx_outs, test_ctx.task.pending_tx_outs);
    }

    #[async_test_with_logger]
    async fn resubmit_listed_tx_outs_behaves_correctly(logger: Logger) {
        let mut test_ctx = TestContext::new(&default_pairs(), &logger);

        let mtxo1 = test_ctx.create_matched_tx_out(Amount::new(100, TokenId::MOB));
        let mtxo2 = test_ctx.create_matched_tx_out(Amount::new(100, TokenId::MOB));
        let pending_tx_outs = vec![
            test_ctx.task.create_pending_tx_out(mtxo1).unwrap(),
            test_ctx.task.create_pending_tx_out(mtxo2).unwrap(),
        ];

        test_ctx.task.listed_tx_outs = pending_tx_outs
            .iter()
            .map(|ptxo| {
                let quote = Quote::new(ptxo.sci.clone(), None).unwrap();
                ListedTxOut {
                    matched_tx_out: ptxo.matched_tx_out.clone(),
                    quote,
                    last_submitted_at: now_since_epoch(),
                }
            })
            .collect();

        // When not enough time has passted, the listed tx outs list should not change.
        let orig_listed_tx_outs = test_ctx.task.listed_tx_outs.clone();
        test_ctx
            .task
            .resubmit_listed_tx_outs(Duration::from_secs(10))
            .await
            .unwrap();
        assert_eq!(test_ctx.task.listed_tx_outs, orig_listed_tx_outs);

        // Set one of the listed tx outs to be older than the resubmit threshold and try
        // to resubmit. By default our test DEQS server returns a GRPC error, so while
        // the order of the listed tx outs should change, the contents of each
        // one should not.
        // The order changes because resubmit_listed_tx_outs() first splits
        // the listed_tx_outs list into two parts: the ones that are older than the
        // resubmit threshold, and the ones that are not.
        test_ctx.task.listed_tx_outs[0].last_submitted_at -=
            Duration::from_secs(20).as_millis() as u64;
        let orig_listed_tx_outs = test_ctx.task.listed_tx_outs.clone();
        assert_matches!(
            test_ctx
                .task
                .resubmit_listed_tx_outs(Duration::from_secs(10))
                .await,
            Err(Error::Grpc(..))
        );
        assert_eq!(test_ctx.task.listed_tx_outs.len(), 2);
        assert_eq!(test_ctx.task.listed_tx_outs[0], orig_listed_tx_outs[1]);
        assert_eq!(test_ctx.task.listed_tx_outs[1], orig_listed_tx_outs[0]);

        // Leave only the listed_tx_out that needs to be resubmitted to make testing a
        // bit easier to follow.
        test_ctx.task.listed_tx_outs.remove(0);

        // Set the DEQS server to return a QUOTE_ALREADY_EXISTS response with the same
        // quote.  In this case the last_submitted_at value should update, but
        // everything else should stay the same.
        let resp = SubmitQuotesResponse {
            status_codes: vec![QuoteStatusCode::QUOTE_ALREADY_EXISTS],
            quotes: vec![grpc_api::Quote::from(
                &test_ctx.task.listed_tx_outs[0].quote,
            )]
            .into(),
            error_messages: vec!["".to_string()].into(),
            ..Default::default()
        };
        test_ctx.deqs_server.set_submit_quotes_response(Ok(resp));

        let orig_listed_tx_outs = test_ctx.task.listed_tx_outs.clone();
        test_ctx
            .task
            .resubmit_listed_tx_outs(Duration::from_secs(10))
            .await
            .unwrap();

        // Initially the list will be different, since we expect last_submitted_at to
        // have changed.
        assert_ne!(test_ctx.task.listed_tx_outs, orig_listed_tx_outs);

        // However, if we revert back to the old one, the lists should be identical.
        test_ctx.task.listed_tx_outs[0].last_submitted_at =
            orig_listed_tx_outs[0].last_submitted_at;

        assert_eq!(test_ctx.task.listed_tx_outs, orig_listed_tx_outs);

        // Try again but this time return a different quote. This should result
        // in the listed_tx_out quote getting updated in addition to the
        // last_submitted_at value.
        let mtxo = test_ctx.create_matched_tx_out(Amount::new(100, TokenId::MOB));
        let ptxo = test_ctx.task.create_pending_tx_out(mtxo).unwrap();
        let quote = Quote::new(ptxo.sci, None).unwrap();

        let resp = SubmitQuotesResponse {
            status_codes: vec![QuoteStatusCode::QUOTE_ALREADY_EXISTS],
            quotes: vec![grpc_api::Quote::from(&quote)].into(),
            error_messages: vec!["".to_string()].into(),
            ..Default::default()
        };
        test_ctx.deqs_server.set_submit_quotes_response(Ok(resp));

        let now = now_since_epoch();
        test_ctx
            .task
            .resubmit_listed_tx_outs(Duration::from_secs(10))
            .await
            .unwrap();

        assert_eq!(test_ctx.task.listed_tx_outs.len(), 1);
        assert!(test_ctx.task.listed_tx_outs[0].last_submitted_at >= now);
        assert_eq!(test_ctx.task.listed_tx_outs[0].quote, quote);

        // Test that a CREATED response behaves correctly
        let resp = SubmitQuotesResponse {
            status_codes: vec![QuoteStatusCode::CREATED],
            quotes: vec![grpc_api::Quote::from(
                &test_ctx.task.listed_tx_outs[0].quote,
            )]
            .into(),
            error_messages: vec!["".to_string()].into(),
            ..Default::default()
        };
        test_ctx.deqs_server.set_submit_quotes_response(Ok(resp));

        test_ctx.task.listed_tx_outs[0].last_submitted_at -=
            Duration::from_secs(20).as_millis() as u64;
        let now = now_since_epoch();
        test_ctx
            .task
            .resubmit_listed_tx_outs(Duration::from_secs(10))
            .await
            .unwrap();

        assert_eq!(test_ctx.task.listed_tx_outs.len(), 1);
        assert!(test_ctx.task.listed_tx_outs[0].last_submitted_at >= now);
        assert_eq!(test_ctx.task.listed_tx_outs[0].quote, quote);

        // When a quote is stale, we remove it from the list.
        let resp = SubmitQuotesResponse {
            status_codes: vec![QuoteStatusCode::QUOTE_IS_STALE],
            quotes: vec![grpc_api::Quote::default()].into(),
            error_messages: vec!["".to_string()].into(),
            ..Default::default()
        };
        test_ctx.deqs_server.set_submit_quotes_response(Ok(resp));

        test_ctx.task.listed_tx_outs[0].last_submitted_at -=
            Duration::from_secs(20).as_millis() as u64;
        test_ctx
            .task
            .resubmit_listed_tx_outs(Duration::from_secs(10))
            .await
            .unwrap();

        assert_eq!(test_ctx.task.listed_tx_outs.len(), 0);
    }

    #[async_test_with_logger]
    async fn create_pending_tx_out_errors_on_unconfigured_token(logger: Logger) {
        let mut test_ctx = TestContext::new(&default_pairs(), &logger);

        let token_id = TokenId::from(123);
        let mtxo = test_ctx.create_matched_tx_out(Amount::new(100, token_id));
        assert_matches!(
            test_ctx.task.create_pending_tx_out(mtxo),
            Err(Error::UnknownTokenId(err_token_id)) if err_token_id == token_id
        );
    }

    #[async_test_with_logger]
    async fn create_pending_tx_out_calculates_correct_swap_rate(logger: Logger) {
        let mut test_ctx = TestContext::new(&default_pairs(), &logger);

        // MOB -> eUSD (token id 1) ratio is 2:1 (see default_pairs())
        for (mob_amount, expected_eusd_amount) in [
            (99, 50),
            (100, 50),
            (101, 51),
            (2, 1),
            (1, 1),
            (u64::MAX, u64::MAX / 2 + 1), // +1 becaus u64::MAX is odd
        ] {
            let mtxo = test_ctx.create_matched_tx_out(Amount::new(mob_amount, TokenId::MOB));
            let ptxo = test_ctx.task.create_pending_tx_out(mtxo).unwrap();

            let (amount, _) = ptxo
                .sci
                .tx_in
                .input_rules
                .as_ref()
                .unwrap()
                .partial_fill_outputs[0]
                .reveal_amount()
                .unwrap();
            assert_eq!(amount, Amount::new(expected_eusd_amount, TokenId::from(1)));
        }

        //  eUSD (token id 1) -> MOB ratio is 1:3 (see default_pairs())
        for (eusd_amount, expected_mob_amount) in [(1, 3), (100, 300)] {
            let mtxo = test_ctx.create_matched_tx_out(Amount::new(eusd_amount, TokenId::from(1)));
            let ptxo = test_ctx.task.create_pending_tx_out(mtxo).unwrap();

            let (amount, _) = ptxo
                .sci
                .tx_in
                .input_rules
                .as_ref()
                .unwrap()
                .partial_fill_outputs[0]
                .reveal_amount()
                .unwrap();
            assert_eq!(amount, Amount::new(expected_mob_amount, TokenId::MOB));
        }

        // Try a conversion that overflows u64
        let mtxo = test_ctx.create_matched_tx_out(Amount::new(u64::MAX, TokenId::from(1)));
        assert_matches!(
            test_ctx.task.create_pending_tx_out(mtxo),
            Err(Error::DecimalConversion(..))
        );
    }

    #[async_test_with_logger]
    async fn unlist_spend_tx_outs_behaves_correctly(logger: Logger) {
        let mut test_ctx = TestContext::new(&default_pairs(), &logger);

        // The bot is going to generate an SCI that offers MOB in exchange for eUSD.
        let mob_value_offered = 1000 * MILLIMOB_TO_PICOMOB;
        let mtxo = test_ctx.create_matched_tx_out(Amount::new(mob_value_offered, TokenId::MOB));

        // Get the bot to generate an SCI for the MatchedTxOut and put it in
        // listed_tx_outs.
        assert!(test_ctx
            .task
            .update_pending_tx_outs_from_received_tx_outs(&[mtxo.clone()])
            .unwrap());

        let quote = Quote::new(test_ctx.task.pending_tx_outs[0].sci.clone(), None).unwrap();
        let resp = SubmitQuotesResponse {
            status_codes: vec![QuoteStatusCode::CREATED],
            quotes: vec![grpc_api::Quote::from(&quote)].into(),
            error_messages: vec!["".to_string()].into(),
            ..Default::default()
        };
        test_ctx.deqs_server.set_submit_quotes_response(Ok(resp));

        test_ctx.task.submit_pending_tx_outs().await.unwrap();
        assert!(test_ctx.task.pending_tx_outs.is_empty());

        assert_eq!(test_ctx.task.listed_tx_outs.len(), 1);
        assert_eq!(test_ctx.task.listed_tx_outs[0].matched_tx_out, mtxo);

        // At this point the bot is tracking the matched tx out. We'll now test that
        // feeding it some unrelated spent tx outs doesn't cause it to do
        // anything.
        let orig_listed_tx_outs = test_ctx.task.listed_tx_outs.clone();
        let mtxo2 = test_ctx.create_matched_tx_out(Amount::new(100, TokenId::MOB));
        assert_eq!(test_ctx.task.unlist_spent_tx_outs(&[mtxo2]), vec![]);
        assert_eq!(test_ctx.task.listed_tx_outs, orig_listed_tx_outs);

        // Try again, but this time with the tx out the bot is tracking.
        assert_eq!(
            test_ctx.task.unlist_spent_tx_outs(&[mtxo.clone()]),
            orig_listed_tx_outs,
        );
        // The listed tx out gets removed since it was spent
        assert_eq!(test_ctx.task.listed_tx_outs, vec![]);
    }

    #[async_test_with_logger]
    async fn look_for_fulfilled_scis_identifies_consumed_scis(logger: Logger) {
        let mut test_ctx = TestContext::new(&default_pairs(), &logger);

        // The bot is going to generate an SCI that offers MOB in exchange for eUSD.
        let mob_value_offered = 1000 * MILLIMOB_TO_PICOMOB;
        let mtxo = test_ctx.create_matched_tx_out(Amount::new(mob_value_offered, TokenId::MOB));

        // Get the bot to generate an SCI for the MatchedTxOut and put it in
        // listed_tx_outs.
        assert!(test_ctx
            .task
            .update_pending_tx_outs_from_received_tx_outs(&[mtxo.clone()])
            .unwrap());

        let quote = Quote::new(test_ctx.task.pending_tx_outs[0].sci.clone(), None).unwrap();
        let resp = SubmitQuotesResponse {
            status_codes: vec![QuoteStatusCode::CREATED],
            quotes: vec![grpc_api::Quote::from(&quote)].into(),
            error_messages: vec!["".to_string()].into(),
            ..Default::default()
        };
        test_ctx.deqs_server.set_submit_quotes_response(Ok(resp));

        test_ctx.task.submit_pending_tx_outs().await.unwrap();
        assert!(test_ctx.task.pending_tx_outs.is_empty());

        assert_eq!(test_ctx.task.listed_tx_outs.len(), 1);
        assert_eq!(test_ctx.task.listed_tx_outs[0].matched_tx_out, mtxo);

        let listed_tx_out = test_ctx.task.listed_tx_outs[0].clone();

        // Try to look for fulfilled SCIs with no tx outs received, which should make
        // the bot think it was cancelled (so it will not be returned in the
        // fulfilled list).
        assert_eq!(
            test_ctx
                .task
                .look_for_fulfilled_scis(&[listed_tx_out.clone()], &[])
                .unwrap(),
            vec![]
        );

        // Try again with a real tx that consumes the SCI.
        // Create a transaction that consumes a quarter of the SCI sending half of that
        // in eUSD (the sci's ratio is 1 mob = 0.5 eusd)
        // To keep things a bit simpler, we use a fee value of 0
        let tx = {
            let mut sci = listed_tx_out.quote.sci().clone();

            let fog_resolver = MockFogResolver(Default::default());
            let counterparty = AccountKey::random(&mut test_ctx.rng);

            let mob_amount_to_consume = mob_value_offered / 4;

            let input_credentials = get_input_credentials(
                BlockVersion::MAX,
                Amount::new(mob_amount_to_consume / 2, TokenId::from(1)),
                &counterparty,
                &fog_resolver,
                &mut test_ctx.rng,
            );
            let proofs = input_credentials.membership_proofs.clone();

            let mut builder = TransactionBuilder::new(
                BlockVersion::MAX,
                Amount::new(0, Mob::ID),
                fog_resolver,
                EmptyMemoBuilder::default(),
            )
            .unwrap();

            // Counterparty supplies eUSD
            builder.add_input(input_credentials);

            // Counterparty keeps the Mob that Originator supplies
            builder
                .add_output(
                    Amount::new(mob_amount_to_consume, Mob::ID),
                    &counterparty.default_subaddress(),
                    &mut test_ctx.rng,
                )
                .unwrap();

            // Add the SCI
            sci.tx_in.proofs = proofs;
            builder
                .add_presigned_partial_fill_input(
                    sci,
                    Amount::new(mob_value_offered - mob_amount_to_consume, Mob::ID),
                )
                .unwrap();

            builder
                .build(&NoKeysRingSigner {}, &mut test_ctx.rng)
                .unwrap()
        };

        // View-key scan this tx, our bot should receive the eUSD and some mob change.
        let matched_tx_outs = tx
            .prefix
            .outputs
            .iter()
            .filter_map(|tx_out| {
                MatchedTxOut::view_key_scan(
                    100, // Block index doesnt matter,
                    tx_out,
                    &test_ctx.account_key,
                    &AccountLedgerScanner::default_spsk_to_index_map(&test_ctx.account_key),
                    &logger,
                )
                .unwrap()
            })
            .collect::<Vec<_>>();

        // Feed this whole mess to look_for_fulfilled_scis
        let fulfilled_scis = test_ctx
            .task
            .look_for_fulfilled_scis(&[listed_tx_out.clone()], &matched_tx_outs)
            .unwrap();

        assert_eq!(fulfilled_scis.len(), 1);
        let fulfilled_sci = &fulfilled_scis[0];
        assert_eq!(fulfilled_sci.listed_tx_out, listed_tx_out);
        assert_eq!(
            fulfilled_sci.received_counter_output.amount,
            Amount::new(
                // We consumed 1/4 of the SCI, and the ratio is 1 mob = 0.5 eusd
                mob_value_offered / 4 / 2,
                TokenId::from(1),
            )
        );

        // We should get back 3/4 of out offer.
        let change_output_amount = fulfilled_sci
            .received_base_change_output
            .as_ref()
            .unwrap()
            .amount;
        assert_eq!(
            change_output_amount,
            Amount::new(mob_value_offered * 3 / 4, Mob::ID)
        );
    }
}
