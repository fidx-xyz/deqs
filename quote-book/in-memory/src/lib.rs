// Copyright (c) 2023 MobileCoin Inc.

#![feature(btree_extract_if)]

use deqs_quote_book_api::{Error as QuoteBookError, FeeConfig, Pair, Quote, QuoteBook, QuoteId};
use mc_blockchain_types::BlockIndex;
use mc_crypto_keys::RistrettoPrivate;
use mc_crypto_ring_signature::KeyImage;
use mc_transaction_core::{validation::validate_tombstone, PublicAddress};
use std::{
    collections::{BTreeSet, HashMap},
    ops::{Bound, RangeBounds},
    sync::{Arc, RwLock},
};

/// A naive in-memory quote book implementation
#[derive(Clone, Debug)]
pub struct InMemoryQuoteBook {
    /// List of all SCIs in the quote book, grouped by trading pair.
    /// Naturally sorted by the time they got added to the book.
    scis: Arc<RwLock<HashMap<Pair, BTreeSet<Quote>>>>,

    /// Fee configuration
    fee_config: FeeConfig,
}

impl InMemoryQuoteBook {
    pub fn new(fee_config: FeeConfig) -> Self {
        Self {
            scis: Arc::new(RwLock::new(HashMap::new())),
            fee_config,
        }
    }
}

impl QuoteBook for InMemoryQuoteBook {
    fn fee_address(&self) -> PublicAddress {
        self.fee_config.fee_address.clone()
    }

    fn fee_basis_points(&self) -> u16 {
        self.fee_config.fee_basis_points
    }

    fn fee_view_private_key(&self) -> RistrettoPrivate {
        self.fee_config.fee_view_private_key
    }

    fn add_quote(&self, quote: &Quote) -> Result<(), QuoteBookError> {
        // Try adding to quote book.
        let mut scis = self.scis.write()?;
        let quotes = scis.entry(*quote.pair()).or_insert_with(Default::default);

        // Make sure quote doesn't already exist. For a single pair we disallow
        // duplicate key images since we don't want the same input with
        // different pricing.
        // This also ensures that we do not encounter a duplicate id, since the id is a
        // hash of the entire SCI including its key image.
        if let Some(existing_quote) = quotes
            .iter()
            .find(|entry| entry.sci().key_image() == quote.sci().key_image())
        {
            return Err(QuoteBookError::QuoteAlreadyExists {
                existing_quote: Box::new(existing_quote.clone()),
            });
        }

        // Add quote. We assert it doesn't fail since we do not expect duplicate quotes
        // due to the key image check above.
        assert!(quotes.insert(quote.clone()));
        Ok(())
    }

    fn remove_quote_by_id(&self, id: &QuoteId) -> Result<Quote, QuoteBookError> {
        let mut scis = self.scis.write()?;

        for entries in scis.values_mut() {
            if let Some(element) = entries.iter().find(|entry| entry.id() == id).cloned() {
                // We return since we expect the id to be unique amongst all quotes across all
                // pairs. This is to be expected because the id is the hash of
                // the entire SCI, and when adding SCIs we ensure uniqueness.
                assert!(entries.remove(&element));
                return Ok(element);
            }
        }

        Err(QuoteBookError::QuoteNotFound)
    }

    fn remove_quotes_by_key_image(
        &self,
        key_image: &KeyImage,
    ) -> Result<Vec<Quote>, QuoteBookError> {
        let mut scis = self.scis.write()?;

        let mut all_removed_quotes = Vec::new();

        for entries in scis.values_mut() {
            let mut removed_entries = entries
                .extract_if(|entry| entry.key_image() == *key_image)
                .collect();

            all_removed_quotes.append(&mut removed_entries);
        }

        Ok(all_removed_quotes)
    }

    fn remove_quotes_by_tombstone_block(
        &self,
        current_block_index: BlockIndex,
    ) -> Result<Vec<Quote>, QuoteBookError> {
        let mut scis = self.scis.write()?;

        let mut all_removed_quotes = Vec::new();

        for entries in scis.values_mut() {
            let mut removed_entries = entries
                .extract_if(|entry| {
                    if let Some(input_rules) = &entry.sci().tx_in.input_rules {
                        input_rules.max_tombstone_block != 0
                            && validate_tombstone(
                                current_block_index,
                                input_rules.max_tombstone_block,
                            )
                            .is_err()
                    } else {
                        false
                    }
                })
                .collect();

            all_removed_quotes.append(&mut removed_entries);
        }

        Ok(all_removed_quotes)
    }

    fn get_quotes(
        &self,
        pair: &Pair,
        base_token_quantity: impl RangeBounds<u64>,
        limit: usize,
    ) -> Result<Vec<Quote>, QuoteBookError> {
        let scis = self.scis.read()?;
        let mut results = Vec::new();

        if let Some(quotes) = scis.get(pair) {
            // NOTE: This implementation relies on quotes being sorted due to being held in
            // a BTreeSet
            for quote in quotes.iter() {
                if range_overlaps(&base_token_quantity, quote.base_range()) {
                    results.push(quote.clone());
                    if results.len() == limit {
                        break;
                    }
                }
            }
        }

        Ok(results)
    }

    fn get_quote_ids(&self, pair: Option<&Pair>) -> Result<Vec<QuoteId>, QuoteBookError> {
        let scis = self.scis.read()?;
        let mut results = Vec::new();

        if let Some(pair) = pair {
            if let Some(quotes) = scis.get(pair) {
                results.extend(quotes.iter().map(|quote| *quote.id()));
            }
        } else {
            for quotes in scis.values() {
                results.extend(quotes.iter().map(|quote| *quote.id()));
            }
        }

        Ok(results)
    }

    fn get_quote_by_id(&self, id: &QuoteId) -> Result<Option<Quote>, QuoteBookError> {
        let scis = self.scis.read()?;

        for entries in scis.values() {
            if let Some(element) = entries.iter().find(|entry| entry.id() == id).cloned() {
                return Ok(Some(element));
            }
        }

        Ok(None)
    }

    fn num_scis(&self) -> Result<u64, QuoteBookError> {
        let scis = self.scis.read()?;
        Ok(scis.values().map(|entries| entries.len() as u64).sum())
    }
}

fn range_overlaps(x: &impl RangeBounds<u64>, y: &impl RangeBounds<u64>) -> bool {
    let x1 = match x.start_bound() {
        Bound::Included(start) => *start,
        Bound::Excluded(start) => start.saturating_add(1),
        Bound::Unbounded => 0,
    };

    let x2 = match x.end_bound() {
        Bound::Included(end) => *end,
        Bound::Excluded(end) => end.saturating_sub(1),
        Bound::Unbounded => u64::MAX,
    };

    let y1 = match y.start_bound() {
        Bound::Included(start) => *start,
        Bound::Excluded(start) => start.saturating_add(1),
        Bound::Unbounded => 0,
    };

    let y2 = match y.end_bound() {
        Bound::Included(end) => *end,
        Bound::Excluded(end) => end.saturating_sub(1),
        Bound::Unbounded => u64::MAX,
    };

    x1 <= y2 && y1 <= x2
}

#[cfg(test)]
mod tests {
    use super::*;
    use deqs_quote_book_test_suite as test_suite;
    use mc_transaction_core::AccountKey;
    use rand::{rngs::StdRng, SeedableRng};

    fn default_fee_config() -> FeeConfig {
        // We use a different seed here than in most other tests so that our fee account
        // does not end up being the same as any other accounts.
        let mut rng: StdRng = SeedableRng::from_seed([251u8; 32]);
        let fee_account = AccountKey::random(&mut rng);

        FeeConfig {
            fee_address: fee_account.default_subaddress(),
            fee_basis_points: 10,
            fee_view_private_key: fee_account.view_private_key().clone(),
        }
    }

    #[test]
    fn basic_happy_flow() {
        let quote_book = InMemoryQuoteBook::new(default_fee_config());
        test_suite::basic_happy_flow(&quote_book, None);
    }

    #[test]
    fn cannot_add_invalid_sci() {
        let quote_book = InMemoryQuoteBook::new(default_fee_config());
        test_suite::cannot_add_invalid_sci(&quote_book, None);
    }

    #[test]
    fn get_quotes_filtering_works() {
        let quote_book = InMemoryQuoteBook::new(default_fee_config());
        test_suite::get_quotes_filtering_works(&quote_book, None);
    }

    #[test]
    fn get_quote_ids_works() {
        let quote_book = InMemoryQuoteBook::new(default_fee_config());
        test_suite::get_quote_ids_works(&quote_book, None);
    }

    #[test]
    fn get_quote_by_id_works() {
        let quote_book = InMemoryQuoteBook::new(default_fee_config());
        test_suite::get_quote_by_id_works(&quote_book, None);
    }
}
