//! Stand-in for the Android `rustutils` crate (system properties and user ids).
//!
//! Signatures follow the call sites in keystore2 at android-17.0.0_r1. System property reads and
//! waits are oracles: the functions are marked `#[charon::opaque]`, so Charon emits a signature
//! and no body. The constants are the values of `android_filesystem_config.h`.
#![feature(register_tool)]
#![register_tool(charon)]

pub mod android {
    pub mod system_properties {
        use std::time::Duration;

        /// Error of a system property operation. Its payload is not modelled.
        #[derive(Debug)]
        pub struct PropertyWatcherError;

        impl std::fmt::Display for PropertyWatcherError {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.write_str("system property error")
            }
        }

        impl std::error::Error for PropertyWatcherError {}

        pub type Result<T> = std::result::Result<T, PropertyWatcherError>;

        /// Reads a property. `None` when it is not set.
        #[charon::opaque]
        pub fn read(_name: &str) -> Result<Option<String>> {
            unimplemented!("stand-in: system property read")
        }

        /// Reads a boolean property, with `default_value` when it is not set.
        #[charon::opaque]
        pub fn read_bool(_name: &str, _default_value: bool) -> Result<bool> {
            unimplemented!("stand-in: system property read_bool")
        }

        /// Writes a property.
        #[charon::opaque]
        pub fn write(_name: &str, _value: &str) -> Result<()> {
            unimplemented!("stand-in: system property write")
        }

        /// Watches one property for changes.
        pub struct PropertyWatcher {
            _private: (),
        }

        impl PropertyWatcher {
            #[charon::opaque]
            pub fn new(_name: &str) -> Result<Self> {
                unimplemented!("stand-in: PropertyWatcher::new")
            }

            /// Applies `f` to the property name and its current value.
            #[charon::opaque]
            pub fn read<F, T>(&self, _f: F) -> Result<T>
            where
                F: FnOnce(&str, &str) -> T,
            {
                unimplemented!("stand-in: PropertyWatcher::read")
            }

            /// Blocks until the property changes or `timeout` elapses.
            #[charon::opaque]
            pub fn wait(&mut self, _timeout: Option<Duration>) -> Result<()> {
                unimplemented!("stand-in: PropertyWatcher::wait")
            }

            /// Blocks until the property equals `expected` or `timeout` elapses.
            #[charon::opaque]
            pub fn wait_for_value(
                &mut self,
                _expected: &str,
                _timeout: Option<Duration>,
            ) -> Result<()> {
                unimplemented!("stand-in: PropertyWatcher::wait_for_value")
            }
        }
    }

    pub mod users {
        /// Uids of one Android user span this range.
        pub const AID_USER_OFFSET: u32 = 100000;
        pub const AID_SYSTEM: u32 = 1000;
        pub const AID_KEYSTORE: u32 = 1017;

        /// The user id that owns `uid`.
        pub fn multiuser_get_user_id(uid: u32) -> u32 {
            uid / AID_USER_OFFSET
        }
    }
}
