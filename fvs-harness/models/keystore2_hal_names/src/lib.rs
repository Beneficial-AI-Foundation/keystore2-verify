//! Model of `keystore2/src/hal_instance_names`: same API, no body. The upstream crate is a `cxx`
//! bridge into C++.
#![feature(register_tool)]
#![register_tool(charon)]

/// The instances of the given package, version and interface tuple. An oracle.
#[charon::opaque]
pub fn get_hidl_instances(
    _package: &str,
    _major_version: usize,
    _minor_version: usize,
    _interface_name: &str,
) -> Vec<String> {
    unimplemented!("model: HIDL instance names")
}
