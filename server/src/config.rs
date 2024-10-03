// Copyright (c) 2023 MobileCoin Inc.

//! Configuration parameters for the DEQS server

use clap::Parser;
use deqs_api::DeqsClientUri;
use deqs_p2p::libp2p::Multiaddr;
use mc_account_keys::PublicAddress;
use mc_api::printable::PrintableWrapper;
use mc_crypto_keys::RistrettoPrivate;
use mc_transaction_types::TokenId;
use mc_util_uri::AdminUri;
use std::{error::Error, path::PathBuf};

/// Command-line configuration options for the DEQS server
// Do not derive Serialize, this has a sensitive private key
#[derive(Parser)]
#[clap(version)]
pub struct ServerConfig {
    /// Path to sqlite database
    #[clap(long)]
    pub db_path: PathBuf,

    /// gRPC listening URI for client requests.
    #[clap(long, env = "MC_CLIENT_LISTEN_URI")]
    pub client_listen_uri: DeqsClientUri,

    /// Optional admin listening URI.
    #[clap(long, env = "MC_ADMIN_LISTEN_URI")]
    pub admin_listen_uri: Option<AdminUri>,

    /// Path to ledgerdb
    #[clap(long = "ledger-db", env = "MC_LEDGER_DB")]
    pub ledger_db: PathBuf,

    /// Bootstrap p2p peers. Need to include a `/p2p/<hash>` postfix, e.g.
    /// `/ip4/127.0.0.1/tcp/49946/p2p/
    /// 12D3KooWDExx59EUZCN3kBJXKNHHmfWb1HShvMmzGxGWWpeWXHEp`
    #[clap(long = "p2p-bootstrap-peer", env = "MC_P2P_BOOTSTRAP_PEER")]
    pub p2p_bootstrap_peers: Vec<Multiaddr>,

    /// The p2p listen address. Provide in order to enable p2p.
    #[clap(long = "p2p-listen", env = "MC_P2P_LISTEN")]
    pub p2p_listen: Option<Multiaddr>,

    /// External p2p address to announce.
    #[clap(long = "p2p-external-address", env = "MC_P2P_EXTERNAL_ADDRESS")]
    pub p2p_external_address: Option<Multiaddr>,

    /// The p2p keypair file. A random one will be generated if not provided.
    #[clap(long = "p2p-keypair", env = "MC_P2P_KEYPAIR")]
    pub p2p_keypair_path: Option<PathBuf>,

    /// This is a vector corresponding to a map from token ids to the minimum
    /// amount required for that token in order for a quote to be accepted by
    /// the deqs.
    /// An example value would be: --quote-minimum-map
    /// 0=1000,1=200. This would correspond to a minimum amount of 1000 for
    /// TokenId 0 and a minimum amount of 200 for TokenId 1
    #[clap(long = "quote-minimum-map", use_value_delimiter = true, value_parser = parse_key_val::<TokenId, u64>)]
    pub quote_minimum_map: Vec<(TokenId, u64)>,

    /// Fee public address in B58 format
    #[clap(long, value_parser = parse_public_address, env = "MC_FEE_B58_ADDRESS")]
    pub fee_b58_address: PublicAddress,

    /// Fee basis points
    #[clap(long, env = "MC_FEE_BASIS_POINTS")]
    pub fee_basis_points: u16,

    /// Fee private view key (hex-encoded)
    #[clap(long, value_parser = parse_ristretto_private, env = "MC_FEE_PRIVATE_VIEW_KEY")]
    pub fee_private_view_key: RistrettoPrivate,
}

/// Parse a single key-value pair
fn parse_key_val<T, U>(s: &str) -> Result<(T, U), Box<dyn Error + Send + Sync + 'static>>
where
    T: std::str::FromStr,
    T::Err: Error + Send + Sync + 'static,
    U: std::str::FromStr,
    U::Err: Error + Send + Sync + 'static,
{
    let pos = s
        .find('=')
        .ok_or_else(|| format!("invalid KEY=value: no `=` found in `{s}`"))?;
    Ok((s[..pos].parse()?, s[pos + 1..].parse()?))
}

fn parse_public_address(b58: &str) -> Result<PublicAddress, String> {
    let printable_wrapper = PrintableWrapper::b58_decode(b58.into())
        .map_err(|err| format!("failed parsing b58 address '{b58}': {err}"))?;

    if printable_wrapper.has_public_address() {
        let public_address = PublicAddress::try_from(printable_wrapper.get_public_address())
            .map_err(|err| format!("failed converting b58 public address '{b58}': {err}"))?;

        Ok(public_address)
    } else {
        Err(format!("b58 address '{b58}' is not a public address"))
    }
}

fn parse_ristretto_private(src: &str) -> Result<RistrettoPrivate, String> {
    let bytes: [u8; 32] =
        mc_util_parse::parse_hex(src).map_err(|_e| "Failed parsing private key".to_string())?;
    RistrettoPrivate::try_from(&bytes).map_err(|_e| "Failed parsing private key".into())
}
