//! Model of `keystore2/postprocessor_client`: `Error` is copied from upstream, the function keeps
//! its signature and has no body. The upstream crate uses a thread and an `mpsc` channel.
#![feature(register_tool)]
#![register_tool(charon)]

use android_hardware_security_keymint::aidl::android::hardware::security::keymint::Certificate::Certificate;
use binder::StatusCode;

/// Errors occurred during the interaction with Certificate Processor.
#[derive(Debug, Clone, Copy, thiserror::Error, PartialEq, Eq)]
#[error("Binder transaction error {0:?}")]
pub struct Error(pub StatusCode);

/// Passes the certificate chain through the certificate processor. An oracle.
#[charon::opaque]
pub fn process_certificate_chain(
    _certificates: Vec<Certificate>,
    _attestation_certs: Vec<u8>,
) -> Vec<Certificate> {
    unimplemented!("model: process_certificate_chain")
}
