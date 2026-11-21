//! Stand-in for the bindgen output of libselinux. It declares the 14 items that
//! `keystore2_selinux` uses, with the types bindgen gives them. The functions are declarations
//! only, so nothing is linked.
#![allow(non_camel_case_types)]

use std::os::raw::{c_char, c_int, c_void};

pub type pid_t = c_int;

/// Opaque label handle (`struct selabel_handle`).
#[repr(C)]
pub struct selabel_handle {
    _private: [u8; 0],
}

/// Callback table of `selinux_set_callback`. Only the log callback is used.
#[repr(C)]
#[derive(Copy, Clone)]
pub union selinux_callback {
    pub func_log: Option<unsafe extern "C" fn(type_: c_int, fmt: *const c_char, ...) -> c_int>,
}

/// `SELINUX_CB_LOG` (first value of the callback type enum).
pub const SELINUX_CB_LOG: u32 = 0;
/// `SELABEL_CTX_ANDROID_KEYSTORE2_KEY`. The value is not load-bearing here.
pub const SELABEL_CTX_ANDROID_KEYSTORE2_KEY: u32 = 6;

extern "C" {
    pub fn getcon(con: *mut *mut c_char) -> c_int;
    pub fn setcon(con: *const c_char) -> c_int;
    pub fn freecon(con: *mut c_char);
    pub fn selinux_check_access(
        scon: *const c_char,
        tcon: *const c_char,
        tclass: *const c_char,
        perm: *const c_char,
        auditdata: *mut c_void,
    ) -> c_int;
    pub fn selinux_set_callback(type_: c_int, cb: selinux_callback);
    pub fn selinux_log_callback(type_: c_int, fmt: *const c_char, ...) -> c_int;
    pub fn selinux_android_keystore2_key_context_handle() -> *mut selabel_handle;
    pub fn selabel_lookup(
        handle: *mut selabel_handle,
        con: *mut *mut c_char,
        key: *const c_char,
        type_: c_int,
    ) -> c_int;
    pub fn selabel_close(handle: *mut selabel_handle);
}
