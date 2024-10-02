//! A helper struct for grouping together fee configuration fields.

use mc_crypto_keys::RistrettoPrivate;
use mc_transaction_core::PublicAddress;

/// A helper struct for grouping together fee configuration fields.
#[derive(Clone, Debug)]
pub struct FeeConfig {
    /// The public address this quote book expects fees at
    pub fee_address: PublicAddress,

    /// The number of basis points each quote needs to pay the fee address.
    pub fee_basis_points: u16,

    /// The private view key of the fee address.
    /// This is needed to make the interface of `add_sci` more ergonomic.
    pub fee_view_private_key: RistrettoPrivate,
}
