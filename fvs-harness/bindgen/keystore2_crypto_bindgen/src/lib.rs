//! Stand-in for the bindgen output of `keystore2/src/crypto/crypto.hpp`. It holds the allowlist
//! of the Soong bindgen rule: 18 functions, the two BoringSSL types and `EVP_MAX_MD_SIZE`. The
//! functions are declarations only, so nothing is linked.
#![allow(non_camel_case_types, non_snake_case)]

use std::os::raw::{c_char, c_int, c_void};

pub type km_id_t = u64;

/// Opaque `EC_KEY` (BoringSSL `struct ec_key_st`).
#[repr(C)]
pub struct ec_key_st {
    _private: [u8; 0],
}
pub type EC_KEY = ec_key_st;

/// Opaque `EC_POINT` (BoringSSL `struct ec_point_st`).
#[repr(C)]
pub struct ec_point_st {
    _private: [u8; 0],
}
pub type EC_POINT = ec_point_st;

pub const EVP_MAX_MD_SIZE: u32 = 64;

extern "C" {
    pub fn hmacSha256(
        key: *const u8,
        key_size: usize,
        msg: *const u8,
        msg_size: usize,
        out: *mut u8,
        out_size: usize,
    ) -> bool;
    pub fn randomBytes(out: *mut u8, len: usize) -> bool;
    pub fn AES_gcm_encrypt(
        in_: *const u8,
        out: *mut u8,
        len: usize,
        key: *const u8,
        key_size: usize,
        iv: *const u8,
        tag: *mut u8,
    ) -> bool;
    pub fn AES_gcm_decrypt(
        in_: *const u8,
        out: *mut u8,
        len: usize,
        key: *const u8,
        key_size: usize,
        iv: *const u8,
        tag: *const u8,
    ) -> bool;
    pub fn CreateKeyId(key_blob: *const u8, len: usize, out_id: *mut km_id_t) -> bool;
    pub fn PBKDF2(
        key: *mut u8,
        key_len: usize,
        pw: *const c_char,
        pw_len: usize,
        salt: *const u8,
    );
    pub fn HKDFExtract(
        out_key: *mut u8,
        out_len: *mut usize,
        secret: *const u8,
        secret_len: usize,
        salt: *const u8,
        salt_len: usize,
    ) -> bool;
    pub fn HKDFExpand(
        out_key: *mut u8,
        out_len: usize,
        prk: *const u8,
        prk_len: usize,
        info: *const u8,
        info_len: usize,
    ) -> bool;
    pub fn ECDHComputeKey(
        out: *mut c_void,
        out_len: usize,
        pub_key: *const EC_POINT,
        priv_key: *const EC_KEY,
    ) -> c_int;
    pub fn ECKEYGenerateKey() -> *mut EC_KEY;
    pub fn ECKEYMarshalPrivateKey(priv_key: *const EC_KEY, buf: *mut u8, len: usize) -> usize;
    pub fn ECKEYParsePrivateKey(buf: *const u8, len: usize) -> *mut EC_KEY;
    pub fn ECPOINTPoint2Oct(point: *const EC_POINT, buf: *mut u8, len: usize) -> usize;
    pub fn ECPOINTOct2Point(buf: *const u8, len: usize) -> *mut EC_POINT;
    pub fn EC_KEY_free(key: *mut EC_KEY);
    pub fn EC_KEY_get0_public_key(key: *const EC_KEY) -> *const EC_POINT;
    pub fn EC_POINT_free(point: *mut EC_POINT);
    pub fn extractSubjectFromCertificate(
        cert_buf: *const u8,
        cert_len: usize,
        subject_buf: *mut u8,
        subject_buf_len: usize,
    ) -> c_int;
}
