//! Model of `keystore2/aaid`: same API, no body. The upstream crate is 12 lines over a bindgen
//! layer into C++.
#![feature(register_tool)]
#![register_tool(charon)]

/// Returns the attestation application id for `uid`, or an error code corresponding to
/// `::android::status_t`. An oracle.
#[charon::opaque]
pub fn get_aaid(_uid: u32) -> Result<Vec<u8>, u32> {
    unimplemented!("model: attestation application id")
}
