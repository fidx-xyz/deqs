// Copyright (c) 2023 MobileCoin Inc.

#![feature(assert_matches)]

mod basic_types;
mod error;
mod quote;
mod quote_book;

pub use basic_types::{Pair, QuoteId};
pub use error::Error;
pub use quote::Quote;
pub use quote_book::QuoteBook;

/// A helper for calculating the fee amount from a given amount.
/// This is a simple percentage calculation that rounds up.
pub fn calc_fee_amount(counter_amount: u64, fee_basis_points: u16) -> u64 {
    (counter_amount as u128)
        .checked_mul(fee_basis_points as u128)
        .expect("multiplication of u64 to u16 should not overflow")
        .checked_add(9999u128)
        .expect("adding 9999 should not overflow")
        .checked_div(10000u128)
        .expect("division by 10000 should always succeed")
        .try_into()
        .expect("result should fit in u64")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::u64;

    #[test]
    fn test_calc_fee_amount() {
        // 1%
        assert_eq!(calc_fee_amount(100, 100), 1);
        assert_eq!(calc_fee_amount(99, 100), 1);
        assert_eq!(calc_fee_amount(9, 100), 1);
        assert_eq!(calc_fee_amount(1, 100), 1);

        assert_eq!(calc_fee_amount(0, 100), 0);

        assert_eq!(calc_fee_amount(u64::MAX, 100), u64::MAX / 100 + 1);

        // 10%
        assert_eq!(calc_fee_amount(100, 1000), 10);
        assert_eq!(calc_fee_amount(99, 1000), 10);
        assert_eq!(calc_fee_amount(9, 1000), 1);
        assert_eq!(calc_fee_amount(1, 1000), 1);

        assert_eq!(calc_fee_amount(0, 1000), 0);

        assert_eq!(calc_fee_amount(u64::MAX, 1000), u64::MAX / 10 + 1);

        // 0.2%
        assert_eq!(calc_fee_amount(100, 20), 1);
        assert_eq!(calc_fee_amount(99, 20), 1);
        assert_eq!(calc_fee_amount(9, 20), 1);
        assert_eq!(calc_fee_amount(1, 20), 1);

        assert_eq!(calc_fee_amount(1000, 20), 2);
        assert_eq!(calc_fee_amount(1500, 20), 3);
        assert_eq!(calc_fee_amount(1501, 20), 4);
        assert_eq!(calc_fee_amount(9000, 20), 18);
        assert_eq!(calc_fee_amount(9900, 20), 20);

        assert_eq!(calc_fee_amount(u64::MAX, 20), u64::MAX / 500 + 1);

        // 0.02%
        assert_eq!(calc_fee_amount(100, 2), 1);
        assert_eq!(calc_fee_amount(99, 2), 1);
        assert_eq!(calc_fee_amount(9, 2), 1);
        assert_eq!(calc_fee_amount(1, 2), 1);

        assert_eq!(calc_fee_amount(1000, 2), 1);
        assert_eq!(calc_fee_amount(1500, 2), 1);
        assert_eq!(calc_fee_amount(9000, 2), 2);
        assert_eq!(calc_fee_amount(9999, 2), 2);
        assert_eq!(calc_fee_amount(10000, 2), 2);
        assert_eq!(calc_fee_amount(10001, 2), 3);

        assert_eq!(calc_fee_amount(u64::MAX, 2), u64::MAX / 5000 + 1);
    }
}
