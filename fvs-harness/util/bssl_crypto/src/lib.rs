//! Stand-in for the BoringSSL `bssl_crypto` crate. keystore2 uses SHA-256 only.
#![feature(register_tool)]
#![register_tool(charon)]

pub mod digest {
    pub struct Sha256;

    impl Sha256 {
        /// SHA-256 of `data`. An oracle: the digest is not computed.
        #[charon::opaque]
        pub fn hash(_data: &[u8]) -> [u8; 32] {
            unimplemented!("stand-in: SHA-256")
        }
    }
}
