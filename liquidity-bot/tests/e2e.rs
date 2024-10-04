// Copyright (c) 2023 MobileCoin Inc.

use deqs_api::deqs::{GetConfigResponse, Quote, QuoteStatusCode, SubmitQuotesResponse};
use deqs_liquidity_bot::{
    mini_wallet::{MatchedTxOut, WalletEvent},
    LiquidityBot,
};
use deqs_quote_book_api::FeeConfig;
use deqs_test_server::DeqsTestServer;
use mc_account_keys::AccountKey;
use mc_blockchain_types::BlockVersion;
use mc_common::logger::{async_test_with_logger, Logger};
use mc_ledger_db::test_utils::{
    add_txos_and_key_images_to_ledger, create_ledger, initialize_ledger,
};
use mc_transaction_core::{ring_signature::KeyImage, Amount, TokenId};
use mc_transaction_core_test_utils::get_outputs;
use mc_transaction_extra::SignedContingentInput;
use rand::{rngs::StdRng, RngCore, SeedableRng};
use rust_decimal::Decimal;
use rust_decimal_macros::dec;
use std::{collections::HashMap, time::Duration};
use tokio_retry::{strategy::FixedInterval, Retry};

/// Test that out of 3 matched TxOuts, only the one with the token id the bot
/// cares about gets submitted to the DEQS, and that the other two are ignored.
/// Also verify that the partial output is present and contains the correct
/// amount and token id.
#[async_test_with_logger(flavor = "multi_thread")]
async fn test_basic_submission(logger: Logger) {
    let mut rng: StdRng = SeedableRng::from_seed([1u8; 32]);
    let account_key = AccountKey::random(&mut rng);
    let fee_account = AccountKey::random(&mut rng);

    let fee_config = FeeConfig {
        fee_address: fee_account.default_subaddress(),
        fee_basis_points: 20,
        fee_view_private_key: *fee_account.view_private_key(),
    };

    let block_version = BlockVersion::MAX;
    let mut ledger = create_ledger();

    let n_blocks = 3;
    initialize_ledger(block_version, &mut ledger, n_blocks, &account_key, &mut rng);

    let deqs_server = DeqsTestServer::start(logger.clone());
    let token_id = TokenId::from(5);
    let swap_rate = dec!(5);

    let mut config_response = GetConfigResponse::default();
    config_response.set_fee_address((&fee_config.fee_address).into());
    config_response.set_fee_basis_points(fee_config.fee_basis_points as u32);
    deqs_server.set_config_response(Ok(config_response));

    let liquidity_bot = LiquidityBot::new(
        account_key.clone(),
        ledger.clone(),
        HashMap::from_iter([(token_id, (TokenId::MOB, swap_rate))]),
        &deqs_server.client_uri(),
        logger.clone(),
    );

    // Prepare three MatchedTxOut that belongs to the bot's account.
    // One will be for the token id the bot is offering, the other two should get
    // ignored.
    let amount = Amount::new(100, TokenId::from(5));

    let recipient = account_key.default_subaddress();
    let recipient_and_amount = vec![
        (recipient.clone(), Amount::new(100, TokenId::from(100))),
        (recipient.clone(), amount),
        (recipient.clone(), Amount::new(100, TokenId::MOB)),
    ];
    let outputs = get_outputs(block_version, &recipient_and_amount, &mut rng);

    let block_data = add_txos_and_key_images_to_ledger(
        &mut ledger,
        block_version,
        outputs,
        vec![KeyImage::from(rng.next_u64())],
        &mut rng,
    )
    .unwrap();

    let matched_tx_outs = block_data
        .contents()
        .outputs
        .iter()
        .cloned()
        .enumerate()
        .map(|(idx, tx_out)| MatchedTxOut {
            block_index: block_data.block().index,
            tx_out,
            amount: recipient_and_amount[idx].1,
            subaddress_index: 0,
            key_image: KeyImage::from(rng.next_u64()),
        })
        .collect::<Vec<_>>();

    // The actual matched_tx_out we care about is the one that has the amount with
    // the token the bot is offering
    let matched_tx_out = &matched_tx_outs[1];

    // Set up the server response to Stale so that the bot doesn't keep trying to
    // re-submit.
    let resp = SubmitQuotesResponse {
        quotes: vec![Quote::default()].into(),
        status_codes: vec![QuoteStatusCode::QUOTE_IS_STALE],
        error_messages: vec!["".into()].into(),
        ..Default::default()
    };
    deqs_server.set_submit_quotes_response(Ok(resp));

    // Feed the bot a block with a TxOut belonging to its account.
    liquidity_bot
        .interface()
        .notify_wallet_event(WalletEvent::BlockProcessed {
            block_index: block_data.block().index,
            received_tx_outs: matched_tx_outs.clone(),
            spent_tx_outs: vec![],
        });

    // Wait for the bot to process the block. We expect it to submit an SCI to
    // the test server.
    let retry_strategy = FixedInterval::new(Duration::from_millis(100)).take(50);
    let req = Retry::spawn(retry_strategy, || async {
        let reqs = deqs_server.pop_submit_quotes_requests();
        match reqs.len() {
            0 => Err("no requests"),
            1 => Ok(reqs[0].clone()),
            _ => panic!("too many requests"),
        }
    })
    .await
    .unwrap();

    // The SCI should point at the TxOut we handed to the bot.
    let sci = SignedContingentInput::try_from(&req.quotes[0]).unwrap();
    assert!(sci.tx_in.ring.contains(&matched_tx_out.tx_out));

    // The SCI should have two partial fill outputs targetted at the correct
    // accounts, with the correct amounts (one that pays us back and one that
    // pays the DEQS fee).
    // TODO test that the outputs go to the correct accounts.
    let input_rules = sci.tx_in.input_rules.as_ref().unwrap();
    assert_eq!(input_rules.partial_fill_outputs.len(), 2);

    let (amount0, _) = input_rules.partial_fill_outputs[0].reveal_amount().unwrap();
    let (amount1, _) = input_rules.partial_fill_outputs[1].reveal_amount().unwrap();

    assert_eq!(amount0.token_id, TokenId::MOB);
    assert_eq!(amount1.token_id, TokenId::MOB);

    let mut amounts = [Decimal::from(amount0.value), Decimal::from(amount1.value)];
    amounts.sort();

    let expected_fill_amount = Decimal::from(amount.value) * swap_rate;

    let expected_fee_amount = (expected_fill_amount
        * Decimal::new(fee_config.fee_basis_points as i64, 4))
    .round_dp_with_strategy(0, rust_decimal::RoundingStrategy::ToPositiveInfinity);

    assert_eq!(amounts, [expected_fee_amount, expected_fill_amount]);
}
