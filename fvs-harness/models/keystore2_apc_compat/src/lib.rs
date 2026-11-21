//! Model of `keystore2/apc_compat`: same public items, no body. The upstream crate wraps a C++
//! HIDL client with `unsafe` callbacks. The constants are the values of `apc_compat.hpp`.
#![feature(register_tool)]
#![register_tool(charon)]

pub const APC_COMPAT_ERROR_OK: u32 = 0;
pub const APC_COMPAT_ERROR_CANCELLED: u32 = 1;
pub const APC_COMPAT_ERROR_ABORTED: u32 = 2;
pub const APC_COMPAT_ERROR_OPERATION_PENDING: u32 = 3;
pub const APC_COMPAT_ERROR_IGNORED: u32 = 4;
pub const APC_COMPAT_ERROR_SYSTEM_ERROR: u32 = 5;

/// UI options of a confirmation prompt (`struct ApcCompatUiOptions`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ApcCompatUiOptions {
    pub inverted: bool,
    pub magnified: bool,
}

/// Handle to the confirmation UI backend.
pub struct ApcHal {
    _private: (),
}

impl ApcHal {
    /// Connects to the backend, or `None` when there is none.
    #[charon::opaque]
    pub fn try_get_service() -> Option<Self> {
        unimplemented!("model: ApcHal::try_get_service")
    }

    /// Starts a prompt. `cb` runs once if and only if this returns `Ok`.
    #[charon::opaque]
    pub fn prompt_user_confirmation<F>(
        &self,
        _prompt_text: &str,
        _extra_data: &[u8],
        _locale: &str,
        _ui_opts: ApcCompatUiOptions,
        _cb: F,
    ) -> Result<(), u32>
    where
        F: FnOnce(u32, Option<&[u8]>, Option<&[u8]>) + 'static,
    {
        unimplemented!("model: ApcHal::prompt_user_confirmation")
    }

    /// Aborts a running prompt. Does nothing when none runs.
    #[charon::opaque]
    pub fn abort(&self) {
        unimplemented!("model: ApcHal::abort")
    }
}
