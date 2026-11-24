//! Model of `keystore2/rkpd_client`: the `Error` enum is copied from upstream, the two functions
//! keep their signatures and have no body. The upstream crate needs `tokio`, a `Mutex` and
//! binder service implementations.
#![feature(register_tool)]
#![register_tool(charon)]

use android_security_rkp_aidl::aidl::android::security::rkp::{
    IGetKeyCallback::ErrorCode::ErrorCode as GetKeyErrorCode,
    RemotelyProvisionedKey::RemotelyProvisionedKey,
};
use anyhow::Result;
use binder::StatusCode;

/// Errors occurred during the interaction with RKPD.
#[derive(Debug, Clone, Copy, thiserror::Error, PartialEq, Eq)]
pub enum Error {
    /// An RKPD request gets cancelled.
    #[error("RKP request was cancelled")]
    RequestCancelled,

    /// Failed to get registration.
    #[error("Failed to get registration")]
    GetRegistrationFailed,

    /// Failed to get key.
    #[error("Failed to get key: {0:?}")]
    GetKeyFailed(GetKeyErrorCode),

    /// Failed to store upgraded key.
    #[error("Failed to store upgraded key")]
    StoreUpgradedKeyFailed,

    /// Retryable timeout when waiting for a callback.
    #[error("Retryable timeout when waiting for a callback")]
    RetryableTimeout,

    /// Timeout when waiting for a callback.
    #[error("Timeout when waiting for a callback")]
    Timeout,

    /// Wraps a Binder status code.
    #[error("Binder transaction error {0:?}")]
    BinderTransaction(StatusCode),

    /// Too many concurrent operations.
    #[error("Too many concurrent operations")]
    TooManyConcurrentOperations,
}

impl From<StatusCode> for Error {
    fn from(s: StatusCode) -> Self {
        Self::BinderTransaction(s)
    }
}

/// Gets an attestation key from RKPD. An oracle.
#[charon::opaque]
pub fn get_rkpd_attestation_key(_rpc_name: &str, _caller_uid: u32) -> Result<RemotelyProvisionedKey> {
    unimplemented!("model: get_rkpd_attestation_key")
}

/// Stores an upgraded key blob with RKPD. An oracle.
#[charon::opaque]
pub fn store_rkpd_attestation_key(
    _rpc_name: &str,
    _key_blob: &[u8],
    _upgraded_blob: &[u8],
) -> Result<()> {
    unimplemented!("model: store_rkpd_attestation_key")
}
