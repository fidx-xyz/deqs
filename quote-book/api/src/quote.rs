// Copyright (c) 2023 MobileCoin Inc.

use crate::{Error, Pair, QuoteId};
use mc_crypto_keys::RistrettoPrivate;
use mc_transaction_core::{Amount, UnmaskedAmount};
use mc_transaction_extra::SignedContingentInput;
use mc_transaction_types::TokenId;
use serde::{Deserialize, Serialize};
use std::{
    cmp::Ordering,
    ops::{Deref, RangeInclusive},
    time::{SystemTime, UNIX_EPOCH},
};

/// Possible SCI types we recognize and details about them
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum SciType {
    /// An SCI exchanging a non-partial input without paying fees
    NonPartialNoFee { counter_amount: UnmaskedAmount },

    /// An SCI exchanging a partial input without paying fees
    PartialNoFee {
        counter_amount: Amount,
        base_change_amount: Option<UnmaskedAmount>,
    },

    /// An SCI exchanging a non-partial input and pays a percentage-based fee
    NonPartialPercentageFee {
        counter_amount: UnmaskedAmount,
        fee_amount: UnmaskedAmount,
    },

    /// An SCI exchanging a partial input and pays a percentage-based fee
    PartialPercentageFee {
        counter_amount: Amount,
        base_change_amount: Option<UnmaskedAmount>,
        fee_amount: Amount,
    },
}

impl SciType {
    pub fn counter_amount(&self) -> Amount {
        match self {
            Self::NonPartialNoFee { counter_amount }
            | Self::NonPartialPercentageFee { counter_amount, .. } => Amount::from(counter_amount),

            Self::PartialNoFee { counter_amount, .. }
            | Self::PartialPercentageFee { counter_amount, .. } => counter_amount.clone(),
        }
    }
}

/// A single "quote" in the book. This is a wrapper around an SCI and some
/// auxiliary data
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Quote {
    /// SCI
    sci: SignedContingentInput,

    /// Unique identifier
    id: QuoteId,

    /// The pair being traded.
    pair: Pair,

    /// The the range of base tokens offered by this quote (the minimum and
    /// maximum amount of base token that can be obtained by fulfiling the
    /// quote)
    base_range: RangeInclusive<u64>,

    /// The number of counter tokens needed to trade the max amount of base
    /// tokens (which can be obtained from base_range).
    max_counter_tokens: u64,

    /// Timestamp at which the quote arrived, in nanoseconds since the Epoch.
    timestamp: u64,

    /// Data that varies based on the type of SCI we have
    sci_type: SciType,
}

impl Quote {
    /// Create a new quote from SCI and timestamp.
    ///
    /// # Arguments
    /// * `sci` - The SCI to add.
    /// * `timestamp` - The timestamp of the block containing the SCI. If not
    ///   provided, the system time is used.
    #[allow(clippy::result_large_err)]
    pub fn new(sci: SignedContingentInput, timestamp: Option<u64>) -> Result<Self, Error> {
        let timestamp = if let Some(timestamp) = timestamp {
            timestamp
        } else {
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map_err(|_| Error::Time)?
                .as_nanos()
                .try_into()
                .map_err(|_| Error::Time)?
        };

        sci.validate()?;

        // The base token being offered in exchange for some other token that the
        // fulfiller will provide.
        let base_token_id = TokenId::from(sci.pseudo_output_amount.token_id);

        // TODO: This is making strong assumptions about the structure of the SCI and
        // doesn't currently take into account the scenario where we would also
        // want a fee output to pay the DEQS.
        let input_rules = if let Some(input_rules) = sci.tx_in.input_rules.as_ref() {
            input_rules
        } else {
            return Err(Error::UnsupportedSci("Missing input rules".into()));
        };

        let (base_range, sci_type) = match (
            input_rules.required_outputs.len(),
            input_rules.partial_fill_outputs.len(),
        ) {
            (0, 0) => return Err(Error::UnsupportedSci("No required/partial outputs".into())),
            (1, 0) => {
                // Single required non-partial output
                (
                    sci.pseudo_output_amount.value..=sci.pseudo_output_amount.value,
                    SciType::NonPartialNoFee {
                        counter_amount: sci.required_output_amounts[0].clone(),
                    },
                )
            }
            (num_required_outputs @ (0 | 1), 1) => {
                // Single partial output or a single partial output + suspected change output
                let (amount, _) = input_rules.partial_fill_outputs[0].reveal_amount()?;
                let min_base_amount = input_rules.min_partial_fill_value;
                let mut max_base_amount = sci.pseudo_output_amount.value;
                let mut base_change_amount = None;

                // If we have a required output in addition to our partial output, we would
                // expect it to be a change output. We assume its change if it
                // is in the same token id as the base token, since it takes
                // away from the amount of base tokens available for consumption
                // by the fulfiller.
                if num_required_outputs == 1 {
                    if sci.required_output_amounts[0].token_id != base_token_id {
                        return Err(Error::UnsupportedSci(format!(
                        "Suspected required-change-output token id {} does not match base token id {}",
                        sci.required_output_amounts[0].token_id, base_token_id,
                    )));
                    }
                    max_base_amount = max_base_amount
                        .checked_sub(sci.required_output_amounts[0].value)
                        .ok_or_else(|| {
                            Error::UnsupportedSci(format!(
                                "max base amount {} is lower than required change {}",
                                max_base_amount, sci.required_output_amounts[0].value
                            ))
                        })?;

                    base_change_amount = Some(sci.required_output_amounts[0].clone());
                }

                (
                    min_base_amount..=max_base_amount,
                    SciType::PartialNoFee {
                        counter_amount: amount,
                        base_change_amount,
                    },
                )
            }
            _ => {
                return Err(Error::UnsupportedSci(format!(
                    "Unsupported number of required/partial outputs {}/{}",
                    input_rules.required_outputs.len(),
                    input_rules.partial_fill_outputs.len()
                )))
            }
        };

        let id = QuoteId::from(&sci);

        let pair = Pair {
            base_token_id,
            counter_token_id: sci_type.counter_amount().token_id,
        };

        Ok(Self {
            sci,
            id,
            pair,
            base_range,
            max_counter_tokens: sci_type.counter_amount().value,
            timestamp,
            sci_type,
        })
    }

    // TODO
    /// Create a new quote from SCI and timestamp.
    ///
    /// # Arguments
    /// * `sci` - The SCI to add.
    /// * `timestamp` - The timestamp of the block containing the SCI. If not
    ///   provided, the system time is used.
    // TODO rename to percentage_fee or something like that
    #[allow(clippy::result_large_err)]
    pub fn new_with_fee_payout(
        sci: SignedContingentInput,
        timestamp: Option<u64>,
        fee_view_private_key: &RistrettoPrivate,
        required_fee_basis_points: u16,
    ) -> Result<Self, Error> {
        let timestamp = if let Some(timestamp) = timestamp {
            timestamp
        } else {
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map_err(|_| Error::Time)?
                .as_nanos()
                .try_into()
                .map_err(|_| Error::Time)?
        };

        sci.validate()?;

        // The base token being offered in exchange for some other token that the
        // fulfiller will provide.
        let base_token_id = TokenId::from(sci.pseudo_output_amount.token_id);

        // TODO: This is making strong assumptions about the structure of the SCI and
        // doesn't currently take into account the scenario where we would also
        // want a fee output to pay the DEQS.
        let input_rules = if let Some(input_rules) = sci.tx_in.input_rules.as_ref() {
            input_rules
        } else {
            return Err(Error::UnsupportedSci("Missing input rules".into()));
        };

        let (base_range, sci_type) = match (
            input_rules.required_outputs.len(),
            input_rules.partial_fill_outputs.len(),
        ) {
            (2, 0) => {
                // Two required non-partial output.
                if sci.required_output_amounts[0].token_id
                    != sci.required_output_amounts[1].token_id
                {
                    return Err(Error::UnsupportedSci(
                        "Both required non-partial outputs should be the same token id".into(),
                    ));
                }

                // One should be the fee output and one should be the output that pays back the
                // SCI creator
                let (fee_index, counter_index) = if input_rules.required_outputs[0]
                    .view_key_match(fee_view_private_key)
                    .is_ok()
                {
                    (0, 1)
                } else if input_rules.required_outputs[1]
                    .view_key_match(fee_view_private_key)
                    .is_ok()
                {
                    (1, 0)
                } else {
                    return Err(Error::UnsupportedSci(
                        "Neither of the required outputs pays the fee address".into(),
                    ));
                };

                // TODO do we want to round up?
                let required_fee_amount = ((sci.required_output_amounts[counter_index].value
                    as u128)
                    * (required_fee_basis_points as u128)
                    / 10000u128) as u64;
                if required_fee_amount > sci.required_output_amounts[fee_index].value {
                    return Err(Error::UnsupportedSci(format!(
                        "Expected a required fee output of at least {required_fee_amount}, got {}",
                        sci.required_output_amounts[fee_index].value
                    )));
                }

                (
                    sci.pseudo_output_amount.value..=sci.pseudo_output_amount.value,
                    SciType::NonPartialPercentageFee {
                        counter_amount: sci.required_output_amounts[counter_index].clone(),
                        fee_amount: sci.required_output_amounts[fee_index].clone(),
                    },
                )
            }

            (num_required_outputs @ (0 | 1), 2) => {
                // Two partial outputs or two partial outputs + suspected change output
                // One of the partial outputs is to pay the provider of the SCI, the other is to
                // pay the fee.
                let (partial_amount0, _) = input_rules.partial_fill_outputs[0]
                    .reveal_amount()
                    .map_err(|err| {
                        Error::UnsupportedSci(format!(
                            "Failed revealing partial output #0 amount: {err}"
                        ))
                    })?;
                let (partial_amount1, _) = input_rules.partial_fill_outputs[1]
                    .reveal_amount()
                    .map_err(|err| {
                        Error::UnsupportedSci(format!(
                            "Failed revealing partial output #1 amount: {err}"
                        ))
                    })?;

                if partial_amount0.token_id != partial_amount1.token_id {
                    return Err(Error::UnsupportedSci(
                        "Both required partial outputs should be the same token id".into(),
                    ));
                }
                let partial_amounts = [partial_amount0, partial_amount1];

                let (fee_index, counter_index) = if input_rules.partial_fill_outputs[0]
                    .tx_out
                    .view_key_match(fee_view_private_key)
                    .is_ok()
                {
                    (0, 1)
                } else if input_rules.partial_fill_outputs[1]
                    .tx_out
                    .view_key_match(fee_view_private_key)
                    .is_ok()
                {
                    (1, 0)
                } else {
                    return Err(Error::UnsupportedSci(
                        "Neither of the partial fill outputs pays the fee address".into(),
                    ));
                };

                let counter_amount = partial_amounts[counter_index];
                let fee_amount = partial_amounts[fee_index];

                // TODO do we want to round up?
                let required_fee_amount = ((counter_amount.value as u128)
                    * (required_fee_basis_points as u128)
                    / 10000u128) as u64;
                if required_fee_amount > fee_amount.value {
                    return Err(Error::UnsupportedSci(format!(
                        "Expected a required fee output of at least {required_fee_amount}, got {}",
                        fee_amount.value
                    )));
                }

                let min_base_amount = input_rules.min_partial_fill_value;
                let mut max_base_amount = sci.pseudo_output_amount.value;
                let mut base_change_amount = None;

                // If we have a required output in addition to our partial output, we would
                // expect it to be a change output. We assume its change if it
                // is in the same token id as the base token, since it takes
                // away from the amount of base tokens available for consumption
                // by the fulfiller.
                if num_required_outputs == 1 {
                    if sci.required_output_amounts[0].token_id != base_token_id {
                        return Err(Error::UnsupportedSci(format!(
                        "Suspected required-change-output token id {} does not match base token id {}",
                        sci.required_output_amounts[0].token_id, base_token_id,
                    )));
                    }
                    max_base_amount = max_base_amount
                        .checked_sub(sci.required_output_amounts[0].value)
                        .ok_or_else(|| {
                            Error::UnsupportedSci(format!(
                                "max base amount {} is lower than required change {}",
                                max_base_amount, sci.required_output_amounts[0].value
                            ))
                        })?;

                    base_change_amount = Some(sci.required_output_amounts[0].clone());
                }

                (
                    min_base_amount..=max_base_amount,
                    SciType::PartialPercentageFee {
                        counter_amount,
                        base_change_amount,
                        fee_amount,
                    },
                )
            }
            _ => {
                return Err(Error::UnsupportedSci(format!(
                    "Unsupported number of required/partial outputs {}/{}",
                    input_rules.required_outputs.len(),
                    input_rules.partial_fill_outputs.len()
                )))
            }
        };

        let id = QuoteId::from(&sci);

        let pair = Pair {
            base_token_id,
            counter_token_id: sci_type.counter_amount().token_id,
        };

        Ok(Self {
            sci,
            id,
            pair,
            base_range,
            max_counter_tokens: sci_type.counter_amount().value,
            timestamp,
            sci_type,
        })
    }

    /// Create a new quote by specifying the exact value for each field.
    pub fn new_from_fields(
        sci: SignedContingentInput,
        id: QuoteId,
        pair: Pair,
        base_range: RangeInclusive<u64>,
        max_counter_tokens: u64,
        timestamp: u64,
        sci_type: SciType,
    ) -> Self {
        Self {
            sci,
            id,
            pair,
            base_range,
            max_counter_tokens,
            timestamp,
            sci_type,
        }
    }

    /// Get underlying SCI.
    pub fn sci(&self) -> &SignedContingentInput {
        &self.sci
    }

    /// Get unique identifier.
    pub fn id(&self) -> &QuoteId {
        &self.id
    }

    /// Get the pair being traded by this quote.
    pub fn pair(&self) -> &Pair {
        &self.pair
    }

    /// Get the range of base tokens offered by this quote (the minimum and
    /// maximum amount of base token that can be obtained by fulfiling the
    /// quote).
    pub fn base_range(&self) -> &RangeInclusive<u64> {
        &self.base_range
    }

    /// Get the maximum amount of base tokens that can be provided by this
    /// quote.
    pub fn max_base_tokens(&self) -> u64 {
        *self.base_range.end()
    }

    /// Get the maximum amount of counter tokens required to completely use all
    /// the available base tokens
    pub fn max_counter_tokens(&self) -> u64 {
        self.max_counter_tokens
    }

    /// Get timestamp.
    pub fn timestamp(&self) -> u64 {
        self.timestamp
    }

    // Get the number of counter tokens we will need to provide in quote to consume
    // this SCI and receive a total of base_tokens back.
    #[allow(clippy::result_large_err)]
    pub fn counter_tokens_cost(&self, base_tokens: u64) -> Result<u64, Error> {
        if !self.base_range.contains(&base_tokens) {
            return Err(Error::InsufficientBaseTokens(base_tokens));
        }

        let input_rules = if let Some(input_rules) = self.sci.tx_in.input_rules.as_ref() {
            input_rules
        } else {
            return Err(Error::UnsupportedSci("Missing input rules".into()));
        };

        match &self.sci_type {
            SciType::NonPartialNoFee { counter_amount }
            | SciType::NonPartialPercentageFee { counter_amount, .. } => {
                // Single required non-partial output. This quote can only execute if are taking
                // the entire amount.
                // The assert here makes sense since we should only get here if base_tokens is a
                // range containing only self.sci.pseudo_output_amount.value
                assert!(base_tokens == self.sci.pseudo_output_amount.value);

                // In a non-partial swap, the fulfiller need to provide the amount specified in
                // the required output.
                Ok(counter_amount.value)
            }

            SciType::PartialNoFee {
                counter_amount,
                base_change_amount,
            }
            | SciType::PartialPercentageFee {
                counter_amount,
                base_change_amount,
                ..
            } => {
                // Single partial output or a single partial output + change amount.
                // The fact that the required output is treated as change has been verified when
                // the Quote was created.

                // The amount we are taking must be above the minimum fill value. It is expected
                // to be, since we checked base_range at the beginning.
                assert!(base_tokens >= input_rules.min_partial_fill_value);

                // The amount we are taking must be below the maximum available. It is expected
                // to be, since we checked base_range at the beginning.
                let mut max_available_amount = self.sci.pseudo_output_amount.value;
                if let Some(base_change_amount) = base_change_amount {
                    assert!(max_available_amount > base_change_amount.value);
                    max_available_amount -= base_change_amount.value;
                };
                assert!(base_tokens <= max_available_amount);

                // The ratio being filled
                let fill_fraction_num: u128 = base_tokens as u128;
                let fill_fractions_denom = self.sci.pseudo_output_amount.value as u128;

                // Calculate the number of counter tokens we need to return as change to the
                // offerer of the SCI. It is calculated as a fraction of the partial fill
                // output.
                let num_128 = counter_amount.value as u128 * fill_fraction_num;
                // Divide and round down
                Ok((num_128 / fill_fractions_denom) as u64)
            }
        }
    }
}

impl TryFrom<SignedContingentInput> for Quote {
    type Error = Error;

    fn try_from(sci: SignedContingentInput) -> Result<Self, Self::Error> {
        Self::new(sci, None)
    }
}

impl Deref for Quote {
    type Target = SignedContingentInput;

    fn deref(&self) -> &Self::Target {
        &self.sci
    }
}

impl Ord for Quote {
    fn cmp(&self, other: &Self) -> Ordering {
        // We sort quotes by the following, in this quote:
        // 1) The pair (so that quotes of the same pair are grouped together)
        // 2) The ratio of base to counter, putting quotes with a more favorable
        // exchange rate (to the fulfiller) first.
        // 3) Timestamp (so that older quotes are filled first)
        // 4) Quote id (in case of quotes where all the above were identical)

        // The rate is calculated as base / counter. We want to sort by:
        // (self_base / self_counter) > (other_base / other_counter)
        // Since we want to avoid division, we multiply both sides by the denominators
        // and get: self_base * other_counter > other_base * self_counter
        let self_rate = other.max_base_tokens() as u128 * self.max_counter_tokens() as u128;
        let other_rate = self.max_base_tokens() as u128 * other.max_counter_tokens() as u128;

        let k1 = (&self.pair, self_rate, &self.timestamp, &self.id);
        let k2 = (&other.pair, other_rate, &other.timestamp, &other.id);

        k1.cmp(&k2)
    }
}

impl PartialOrd for Quote {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mc_transaction_core::{AccountKey, PublicAddress};
    use rand::{prelude::SliceRandom, rngs::StdRng, SeedableRng};
    use rand_core::{CryptoRng, RngCore};
    use std::assert_matches::assert_matches;

    /// Default test pair
    pub fn pair() -> Pair {
        Pair {
            base_token_id: TokenId::from(1),
            counter_token_id: TokenId::from(2),
        }
    }

    /// Create an SCI that offers some amount of a given token in exchange for a
    /// different amount of another token. Returning the builder allows the
    /// caller to customize the SCI further.
    pub fn create_sci(
        pair: &Pair,
        base_amount: u64,
        counter_amount: u64,
        rng: &mut (impl RngCore + CryptoRng),
    ) -> SignedContingentInput {
        deqs_mc_test_utils::create_sci(
            pair.base_token_id,
            pair.counter_token_id,
            base_amount,
            counter_amount,
            rng,
            None,
        )
    }

    /// Create an SCI that offers some amount of a given token in exchange for a
    /// different amount of another token. It also requires that the consumer
    /// of the SCI pays a fee to a specific fee address.
    /// Returning the builder allows the caller to customize the SCI further.
    pub fn create_sci_with_fee_payout(
        pair: &Pair,
        base_amount: u64,
        counter_amount: u64,
        fee_address: &PublicAddress,
        fee_basis_points: u16,
        rng: &mut (impl RngCore + CryptoRng),
    ) -> SignedContingentInput {
        deqs_mc_test_utils::create_sci_with_fee_payout(
            pair.base_token_id,
            pair.counter_token_id,
            base_amount,
            counter_amount,
            fee_address,
            fee_basis_points,
            rng,
            None,
        )
    }

    /// Create a partial fill SCI that offers between
    /// required_base_change_amount and base_amount_offered tokens, with a
    /// minimum required fill of min_base_fill_amount.
    pub fn create_partial_sci(
        pair: &Pair,
        base_amount_offered: u64,
        min_base_fill_amount: u64,
        required_base_change_amount: u64,
        counter_amount: u64,
        rng: &mut (impl RngCore + CryptoRng),
    ) -> SignedContingentInput {
        deqs_mc_test_utils::create_partial_sci(
            pair.base_token_id,
            pair.counter_token_id,
            base_amount_offered,
            min_base_fill_amount,
            required_base_change_amount,
            counter_amount,
            rng,
            None,
        )
    }

    /// Create a partial fill SCI that offers between
    /// required_base_change_amount and base_amount_offered tokens, with a
    /// minimum required fill of min_base_fill_amount.
    /// It also requires that the SCI pays a proportional fee to a fee address.
    pub fn create_partial_sci_with_fee_payout(
        pair: &Pair,
        base_amount_offered: u64,
        min_base_fill_amount: u64,
        required_base_change_amount: u64,
        counter_amount: u64,
        fee_address: &PublicAddress,
        fee_basis_points: u16,
        rng: &mut (impl RngCore + CryptoRng),
    ) -> SignedContingentInput {
        deqs_mc_test_utils::create_partial_sci_with_fee_payout(
            pair.base_token_id,
            pair.counter_token_id,
            base_amount_offered,
            min_base_fill_amount,
            required_base_change_amount,
            counter_amount,
            fee_address,
            fee_basis_points,
            rng,
            None,
        )
    }

    // TODO
    // #[test]
    // fn test_new_without_fees() {
    // }

    #[test]
    fn test_new_with_fee_payout() {
        let mut rng: StdRng = SeedableRng::from_seed([1u8; 32]);
        let fee_account = AccountKey::random(&mut rng);
        let non_fee_account = AccountKey::random(&mut rng);

        // A non-partial fill SCI with one output gets rejected
        let sci = create_sci(&pair(), 10, 20, &mut rng);
        assert_eq!(
            Quote::new_with_fee_payout(sci, None, fee_account.view_private_key(), 100),
            Err(Error::UnsupportedSci(
                "Unsupported number of required/partial outputs 1/0".into()
            ))
        );

        // An SCI with one partial output gets rejected
        let sci = create_partial_sci(&pair(), 10, 0, 0, 100, &mut rng);
        assert_eq!(
            Quote::new_with_fee_payout(sci, None, fee_account.view_private_key(), 100),
            Err(Error::UnsupportedSci(
                "Unsupported number of required/partial outputs 0/1".into()
            ))
        );

        // A non-partial fill SCI paying fees to the wrong address gets rejected.
        let sci = create_sci_with_fee_payout(
            &pair(),
            100,
            200,
            &non_fee_account.default_subaddress(),
            100,
            &mut rng,
        );
        assert_eq!(
            Quote::new_with_fee_payout(sci, None, fee_account.view_private_key(), 100),
            Err(Error::UnsupportedSci(
                "Neither of the required outputs pays the fee address".into()
            ))
        );

        // Helper struct for partial fill tests
        struct PartialSciParams {
            base_amount_offered: u64,
            min_base_fill_amount: u64,
            required_base_change_amount: u64,
            counter_amount: u64,
        }
        let partial_sci_test_cases = &[
            // No required change, no minimum fill
            PartialSciParams {
                base_amount_offered: 1000,
                min_base_fill_amount: 0,
                required_base_change_amount: 0,
                counter_amount: 2000,
            },
            // No required change, minimum required fill
            PartialSciParams {
                base_amount_offered: 1000,
                min_base_fill_amount: 200,
                required_base_change_amount: 0,
                counter_amount: 2000,
            },
            // Required change, no minimum
            PartialSciParams {
                base_amount_offered: 1000,
                min_base_fill_amount: 0,
                required_base_change_amount: 100,
                counter_amount: 2000,
            },
            // Required change, minimum required fill
            PartialSciParams {
                base_amount_offered: 1000,
                min_base_fill_amount: 200,
                required_base_change_amount: 100,
                counter_amount: 2000,
            },
        ];

        for test_case in partial_sci_test_cases {
            // Paying the wrong fee address gets rejected
            let sci = create_partial_sci_with_fee_payout(
                &pair(),
                test_case.base_amount_offered,
                test_case.min_base_fill_amount,
                test_case.required_base_change_amount,
                test_case.counter_amount,
                &non_fee_account.default_subaddress(),
                100,
                &mut rng,
            );
            assert_eq!(
                Quote::new_with_fee_payout(sci, None, fee_account.view_private_key(), 100),
                Err(Error::UnsupportedSci(
                    "Neither of the partial fill outputs pays the fee address".into()
                ))
            );

            // Paying less than the required fee gets rejected
            let sci = create_partial_sci_with_fee_payout(
                &pair(),
                test_case.base_amount_offered,
                test_case.min_base_fill_amount,
                test_case.required_base_change_amount,
                test_case.counter_amount,
                &fee_account.default_subaddress(),
                100,
                &mut rng,
            );
            assert_matches!(
                Quote::new_with_fee_payout(sci.clone(), None, fee_account.view_private_key(), 150),
                Err(Error::UnsupportedSci(
                    err_str
                )) if err_str.starts_with("Expected a required fee output of at least")
            );

            // Paying the right amount of fee works
            assert_matches!(
                Quote::new_with_fee_payout(sci, None, fee_account.view_private_key(), 100),
                Ok(_)
            );

        }
    }

    #[test]
    fn test_max_tokens_with_fee() {
        let mut rng: StdRng = SeedableRng::from_seed([1u8; 32]);
        let fee_account = AccountKey::random(&mut rng);

        // Test max tokens for the non-partial-fill scenario
        let sci = create_sci_with_fee_payout(
            &pair(),
            100,
            200,
            &fee_account.default_subaddress(),
            100,
            &mut rng,
        );
        let quote =
            Quote::new_with_fee_payout(sci, None, fee_account.view_private_key(), 100).unwrap();

        assert_eq!(quote.max_base_tokens(), 100);
        assert_eq!(quote.max_counter_tokens(), 200);

        // Test max tokens for a partial fill with no change and no minimum.
        let sci = create_partial_sci_with_fee_payout(
            &pair(),
            100,
            0,
            0,
            1000,
            &fee_account.default_subaddress(),
            100,
            &mut rng,
        );
        let quote =
            Quote::new_with_fee_payout(sci, None, fee_account.view_private_key(), 100).unwrap();

        assert_eq!(quote.max_base_tokens(), 100);
        assert_eq!(quote.max_counter_tokens(), 1000);

        // Test max tokens for a partial fill with no change and a minimum.
        let sci = create_partial_sci_with_fee_payout(
            &pair(),
            100,
            70,
            0,
            1000,
            &fee_account.default_subaddress(),
            100,
            &mut rng,
        );
        let quote =
            Quote::new_with_fee_payout(sci, None, fee_account.view_private_key(), 100).unwrap();

        assert_eq!(quote.max_base_tokens(), 100);
        assert_eq!(quote.max_counter_tokens(), 1000);

        // Test max tokens for a partial fill with change and no minimum.
        let sci = create_partial_sci_with_fee_payout(
            &pair(),
            100,
            0,
            30,
            1000,
            &fee_account.default_subaddress(),
            100,
            &mut rng,
        );
        let quote =
            Quote::new_with_fee_payout(sci, None, fee_account.view_private_key(), 100).unwrap();

        assert_eq!(quote.max_base_tokens(), 70);
        assert_eq!(quote.max_counter_tokens(), 1000);

        // Test max tokens for a partial fill with change and a minimum.
        let sci = create_partial_sci_with_fee_payout(
            &pair(),
            100,
            30,
            60,
            1000,
            &fee_account.default_subaddress(),
            100,
            &mut rng,
        );

        let quote =
            Quote::new_with_fee_payout(sci, None, fee_account.view_private_key(), 100).unwrap();

        assert_eq!(quote.max_base_tokens(), 40);
        assert_eq!(quote.max_counter_tokens(), 1000);
    }

    #[test]
    fn test_max_tokens_without_fee() {
        let mut rng: StdRng = SeedableRng::from_seed([1u8; 32]);

        // Test max tokens for the non-partial-fill scenario
        let sci = create_sci(&pair(), 10, 20, &mut rng);
        let quote = Quote::try_from(sci).unwrap();

        assert_eq!(quote.max_base_tokens(), 10);
        assert_eq!(quote.max_counter_tokens(), 20);

        // Test max tokens for a partial fill with no change and no minimum.
        let sci = create_partial_sci(&pair(), 10, 0, 0, 100, &mut rng);
        let quote = Quote::try_from(sci).unwrap();

        assert_eq!(quote.max_base_tokens(), 10);
        assert_eq!(quote.max_counter_tokens(), 100);

        // Test max tokens for a partial fill with no change and a minimum.
        let sci = create_partial_sci(&pair(), 10, 7, 0, 100, &mut rng);
        let quote = Quote::try_from(sci).unwrap();

        assert_eq!(quote.max_base_tokens(), 10);
        assert_eq!(quote.max_counter_tokens(), 100);

        // Test max tokens for a partial fill with change and no minimum.
        let sci = create_partial_sci(&pair(), 10, 0, 5, 100, &mut rng);
        let quote = Quote::try_from(sci).unwrap();

        assert_eq!(quote.max_base_tokens(), 5);
        assert_eq!(quote.max_counter_tokens(), 100);

        // Test max tokens for a partial fill with change and a minimum.
        let sci = create_partial_sci(&pair(), 10, 3, 5, 100, &mut rng);
        let quote = Quote::try_from(sci).unwrap();

        assert_eq!(quote.max_base_tokens(), 5);
        assert_eq!(quote.max_counter_tokens(), 100);
    }

    #[test]
    fn test_sorting() {
        let mut rng: StdRng = SeedableRng::from_seed([1u8; 32]);

        let quote_1_for_10 = Quote::try_from(create_sci(&pair(), 1, 10, &mut rng)).unwrap();
        let quote_2_for_10 = Quote::try_from(create_sci(&pair(), 2, 10, &mut rng)).unwrap();
        let quote_3_for_10 = Quote::try_from(create_sci(&pair(), 3, 10, &mut rng)).unwrap();
        let quote_1_for_5 = Quote::try_from(create_sci(&pair(), 1, 5, &mut rng)).unwrap();
        let quote_2_for_5 = Quote::try_from(create_sci(&pair(), 2, 5, &mut rng)).unwrap();
        let quote_3_for_5 = Quote::try_from(create_sci(&pair(), 3, 5, &mut rng)).unwrap();
        let quote_10_for_10 = Quote::try_from(create_sci(&pair(), 10, 10, &mut rng)).unwrap();
        let quote_20_for_10 = Quote::try_from(create_sci(&pair(), 20, 10, &mut rng)).unwrap();
        let quote_30_for_10 = Quote::try_from(create_sci(&pair(), 30, 10, &mut rng)).unwrap();

        let all_quotes = vec![
            &quote_1_for_10,
            &quote_2_for_10,
            &quote_3_for_10,
            &quote_1_for_5,
            &quote_2_for_5,
            &quote_3_for_5,
            &quote_10_for_10,
            &quote_20_for_10,
            &quote_30_for_10,
        ];

        let expected_quotes = vec![
            &quote_30_for_10, // 30/10 = 3
            &quote_20_for_10, // 20/10 = 2
            &quote_10_for_10, // 10/10 = 1
            &quote_3_for_5,   // 3/5 = 0.6
            &quote_2_for_5,   // 2/5 = 0.4
            &quote_3_for_10,  // 3/10 = 0.3
            &quote_2_for_10,  // 2/10 = 0.2 (was created before the next one)
            &quote_1_for_5,   // 1/5 = 0.2
            &quote_1_for_10,  // 1/10 = 0.1
        ];

        let mut quotes = all_quotes.clone();
        quotes.sort();
        assert_eq!(quotes, expected_quotes);

        let mut quotes = all_quotes.clone();
        quotes.reverse();
        quotes.sort();
        assert_eq!(quotes, expected_quotes);

        let mut quotes = all_quotes.clone();
        quotes.shuffle(&mut rng);
        quotes.sort();
        assert_eq!(quotes, expected_quotes);
    }

    #[test]
    fn counter_tokens_cost_works_for_non_partial_fill_scis() {
        let pair = pair();
        let mut rng: StdRng = SeedableRng::from_seed([1u8; 32]);

        // Adding an quote should work
        let sci = create_sci(&pair, 10, 20, &mut rng);
        let quote = Quote::try_from(sci).unwrap();

        // We can only calculate cost for the exact amount of base tokens since this is
        // not a partial fill.
        assert_eq!(quote.counter_tokens_cost(10), Ok(20));
        assert!(quote.counter_tokens_cost(9).is_err());
        assert!(quote.counter_tokens_cost(11).is_err());
        assert!(quote.counter_tokens_cost(0).is_err());
        assert!(quote.counter_tokens_cost(u64::MAX).is_err());
    }

    #[test]
    fn counter_tokens_cost_works_for_partial_fill_no_change_no_min() {
        let pair = pair();
        let mut rng: StdRng = SeedableRng::from_seed([1u8; 32]);

        // Trading at a ratio of 1 base token to 10 counter tokens
        let sci = create_partial_sci(&pair, 10, 0, 0, 100, &mut rng);
        let quote = Quote::try_from(sci).unwrap();
        assert_eq!(quote.counter_tokens_cost(10), Ok(100));
        assert_eq!(quote.counter_tokens_cost(5), Ok(50));
        assert_eq!(quote.counter_tokens_cost(0), Ok(0));

        assert!(quote.counter_tokens_cost(11).is_err());
        assert!(quote.counter_tokens_cost(u64::MAX).is_err());

        // Trading at a ratio of 10 base token to 1 counter tokens
        let sci = create_partial_sci(&pair, 100, 0, 0, 10, &mut rng);
        let quote = Quote::try_from(sci).unwrap();
        assert_eq!(quote.counter_tokens_cost(100), Ok(10));
        assert_eq!(quote.counter_tokens_cost(50), Ok(5));
        assert_eq!(quote.counter_tokens_cost(51), Ok(5));
        assert_eq!(quote.counter_tokens_cost(59), Ok(5));
        assert_eq!(quote.counter_tokens_cost(60), Ok(6));
        assert_eq!(quote.counter_tokens_cost(1), Ok(0)); // rounding down, 1 token is not enough to get any counter tokens
        assert_eq!(quote.counter_tokens_cost(0), Ok(0));

        assert!(quote.counter_tokens_cost(101).is_err());
        assert!(quote.counter_tokens_cost(u64::MAX).is_err());
    }

    #[test]
    fn counter_tokens_cost_works_for_partial_fill_no_change_with_min() {
        let pair = pair();
        let mut rng: StdRng = SeedableRng::from_seed([1u8; 32]);

        // Trading at a ratio of 1 base token to 10 counter tokens
        let sci = create_partial_sci(&pair, 10, 7, 0, 100, &mut rng);
        let quote = Quote::try_from(sci).unwrap();
        assert_eq!(quote.counter_tokens_cost(10), Ok(100));
        assert_eq!(quote.counter_tokens_cost(7), Ok(70));

        assert!(quote.counter_tokens_cost(6).is_err()); // below the min fill amount
        assert!(quote.counter_tokens_cost(0).is_err()); // below the min fill amount
        assert!(quote.counter_tokens_cost(11).is_err()); // above the max amount offered
        assert!(quote.counter_tokens_cost(u64::MAX).is_err()); // above the max amount offered

        // Trading at a ratio of 10 base token to 1 counter tokens
        let sci = create_partial_sci(&pair, 100, 55, 0, 10, &mut rng);
        let quote = Quote::try_from(sci).unwrap();
        assert_eq!(quote.counter_tokens_cost(100), Ok(10));
        assert_eq!(quote.counter_tokens_cost(55), Ok(5)); // rounding down
        assert_eq!(quote.counter_tokens_cost(59), Ok(5)); // rounding down
        assert_eq!(quote.counter_tokens_cost(60), Ok(6));

        assert!(quote.counter_tokens_cost(0).is_err()); // below the min fill amount
        assert!(quote.counter_tokens_cost(1).is_err()); // below the min fill amount
        assert!(quote.counter_tokens_cost(54).is_err()); // below the min fill amount
        assert!(quote.counter_tokens_cost(101).is_err()); // above the max amount offered
        assert!(quote.counter_tokens_cost(u64::MAX).is_err()); // above the max
                                                               // amount offered
    }

    #[test]
    fn counter_tokens_cost_works_for_partial_fill_with_change_no_min() {
        let pair = pair();
        let mut rng: StdRng = SeedableRng::from_seed([1u8; 32]);

        // Trading at a ratio of 1 base token to 10 counter tokens
        let sci = create_partial_sci(&pair, 10, 0, 3, 100, &mut rng);
        let quote = Quote::try_from(sci).unwrap();
        assert_eq!(quote.counter_tokens_cost(7), Ok(70));
        assert_eq!(quote.counter_tokens_cost(6), Ok(60));
        assert_eq!(quote.counter_tokens_cost(1), Ok(10));
        assert_eq!(quote.counter_tokens_cost(0), Ok(0));

        assert!(quote.counter_tokens_cost(8).is_err()); // we need to be able to pay 3 out of the 10 back, 8 will only leave out 2
        assert!(quote.counter_tokens_cost(u64::MAX).is_err());

        // Trading at a ratio of 10 base token to 1 counter tokens
        let sci = create_partial_sci(&pair, 100, 0, 30, 10, &mut rng);
        let quote = Quote::try_from(sci).unwrap();
        assert_eq!(quote.counter_tokens_cost(70), Ok(7));
        assert_eq!(quote.counter_tokens_cost(60), Ok(6));
        assert_eq!(quote.counter_tokens_cost(61), Ok(6));
        assert_eq!(quote.counter_tokens_cost(69), Ok(6));
        assert_eq!(quote.counter_tokens_cost(1), Ok(0)); // rounding down, 1 token is not enough to get any counter tokens
        assert_eq!(quote.counter_tokens_cost(0), Ok(0));

        assert!(quote.counter_tokens_cost(71).is_err()); // exceeds max available (since we require a change of 30 this allows for up to
                                                         // 70 to be swapped)
        assert!(quote.counter_tokens_cost(101).is_err()); // exceeds max available
        assert!(quote.counter_tokens_cost(u64::MAX).is_err());
    }

    #[test]
    fn counter_tokens_cost_works_for_partial_fill_with_change_and_min() {
        let pair = pair();
        let mut rng: StdRng = SeedableRng::from_seed([1u8; 32]);

        // Trading at a ratio of 1 base token to 10 counter tokens
        // Allowing a trade of between 5 and 7 tokens (since min_base_fill_amount is 5
        // and required change is 3, leaving 7)
        let sci = create_partial_sci(&pair, 10, 5, 3, 100, &mut rng);
        let quote = Quote::try_from(sci).unwrap();
        assert_eq!(quote.counter_tokens_cost(7), Ok(70));
        assert_eq!(quote.counter_tokens_cost(6), Ok(60));
        assert_eq!(quote.counter_tokens_cost(5), Ok(50));

        assert!(quote.counter_tokens_cost(8).is_err()); // we need to be able to pay 3 out of the 10 back, 8 will only leave out 2
        assert!(quote.counter_tokens_cost(4).is_err()); // below the minimum of 5 required
        assert!(quote.counter_tokens_cost(u64::MAX).is_err());

        // Trading at a ratio of 10 base token to 1 counter tokens
        // Allowing a trade between 50 and 70 tokens (since min_base_fill_amount is 50,
        // and required change is 30, leaving up to 70)
        let sci = create_partial_sci(&pair, 100, 50, 30, 10, &mut rng);
        let quote = Quote::try_from(sci).unwrap();
        assert_eq!(quote.counter_tokens_cost(70), Ok(7));
        assert_eq!(quote.counter_tokens_cost(50), Ok(5));
        assert_eq!(quote.counter_tokens_cost(51), Ok(5));
        assert_eq!(quote.counter_tokens_cost(59), Ok(5));
        assert!(quote.counter_tokens_cost(71).is_err()); // exceeds max available (since we require a change of 30 this allows for up to
                                                         // 70 to be swapped)
        assert!(quote.counter_tokens_cost(101).is_err()); // exceeds max available
        assert!(quote.counter_tokens_cost(u64::MAX).is_err());
        assert!(quote.counter_tokens_cost(49).is_err()); // below min_partial_fill_value
        assert!(quote.counter_tokens_cost(1).is_err()); // below min_partial_fill_value
        assert!(quote.counter_tokens_cost(0).is_err()); // below min_partial_fill_value
    }
}
