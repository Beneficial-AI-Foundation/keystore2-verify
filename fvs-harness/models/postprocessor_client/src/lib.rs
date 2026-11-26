//! Model of `keystore2/postprocessor_client`: `Error` is copied from upstream, the function keeps
//! its signature and has no body. The upstream crate uses a thread and an `mpsc` channel.
#![feature(register_tool)]
#![register_tool(charon)]

use android_hardware_security_keymint::aidl::android::hardware::security::keymint::Certificate::Certificate;
use binder::StatusCode;

/// Errors occurred during the interaction with Certificate Processor.
///
/// Upstream names this type `Error`; it is re-exported under that name below. The definition has its
/// own name because Aeneas names a trait impl after the last segment of its type arguments, and
/// keystore2's `From<rkpd_client::Error>` and `From<postprocessor_client::Error>` impls would clash.
#[derive(Clone, Copy, thiserror::Error, PartialEq, Eq)]
#[error("Binder transaction error {0:?}")]
pub struct PostProcessorError(pub StatusCode);

pub use PostProcessorError as Error;

/// Prints what `#[derive(Debug)]` printed for upstream's `Error`.
impl core::fmt::Debug for PostProcessorError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("Error").field(&self.0).finish()
    }
}

/// Passes the certificate chain through the certificate processor. An oracle.
#[charon::opaque]
pub fn process_certificate_chain(
    _certificates: Vec<Certificate>,
    _attestation_certs: Vec<u8>,
) -> Vec<Certificate> {
    unimplemented!("model: process_certificate_chain")
}
