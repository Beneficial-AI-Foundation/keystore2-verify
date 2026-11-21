//! Stand-in for the Android `binder` crate (frameworks/native/libs/binder/rust, android-17.0.0_r1).
//!
//! Only the items the keystore2 core and the generated AIDL stand-in crates use are here. Signatures
//! are copied from the real crate; bodies panic, because nothing in the harness runs them. Every
//! function that talks to the binder driver, the service manager or a remote object is an assumption
//! of the verification, not a modelled behaviour.
#![allow(dead_code, unused_variables, non_camel_case_types, non_upper_case_globals)]

use std::ffi::CStr;
use std::fmt;
use std::ops::Deref;

/// `Result<T>` as the real crate defines it: the error is a binder `Status`.
pub type Result<T> = std::result::Result<T, Status>;

/// The result of the real crate's internal modules (`crate::error::Result`): the error is a
/// `StatusCode`. Service lookup, `FromIBinder`, `IBinder` and `Weak::upgrade` use it.
type SResult<T> = std::result::Result<T, StatusCode>;

// ---------------------------------------------------------------- errors

/// Transaction-level status code (the real crate re-exports a bindgen enum of this name).
#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StatusCode {
    OK = 0,
    NO_MEMORY = -12,
    INVALID_OPERATION = -38,
    BAD_VALUE = -22,
    BAD_TYPE = i32::MIN + 1,
    NAME_NOT_FOUND = -2,
    PERMISSION_DENIED = -1,
    NO_INIT = -19,
    ALREADY_EXISTS = -17,
    DEAD_OBJECT = -32,
    FAILED_TRANSACTION = i32::MIN + 2,
    BAD_INDEX = -75,
    NOT_ENOUGH_DATA = -61,
    WOULD_BLOCK = -11,
    TIMED_OUT = -110,
    UNKNOWN_TRANSACTION = -74,
    FDS_NOT_ALLOWED = i32::MIN + 7,
    UNEXPECTED_NULL = i32::MIN + 8,
    UNKNOWN_ERROR = i32::MIN,
}

impl fmt::Display for StatusCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for StatusCode {}

/// Exception code carried by a `Status` (the real crate re-exports a bindgen enum of this name).
#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ExceptionCode {
    NONE = 0,
    SECURITY = -1,
    BAD_PARCELABLE = -2,
    ILLEGAL_ARGUMENT = -3,
    NULL_POINTER = -4,
    ILLEGAL_STATE = -5,
    NETWORK_ON_MAIN_THREAD = -6,
    UNSUPPORTED_OPERATION = -7,
    SERVICE_SPECIFIC = -8,
    PARCELABLE = -9,
    TRANSACTION_FAILED = -129,
}

/// The error type of every binder call: an exception, a service-specific error or a transaction error.
#[derive(Clone, PartialEq, Eq)]
pub struct Status {
    exception: ExceptionCode,
    service_specific: i32,
    transaction: StatusCode,
    message: Option<String>,
}

impl Status {
    pub fn ok() -> Self {
        Status {
            exception: ExceptionCode::NONE,
            service_specific: 0,
            transaction: StatusCode::OK,
            message: None,
        }
    }

    pub fn new_service_specific_error(err: i32, message: Option<&CStr>) -> Status {
        Status {
            exception: ExceptionCode::SERVICE_SPECIFIC,
            service_specific: err,
            transaction: StatusCode::OK,
            message: message.map(|m| m.to_string_lossy().into_owned()),
        }
    }

    pub fn new_service_specific_error_str<T: AsRef<str>>(err: i32, message: Option<T>) -> Status {
        Status {
            exception: ExceptionCode::SERVICE_SPECIFIC,
            service_specific: err,
            transaction: StatusCode::OK,
            message: message.map(|m| m.as_ref().to_owned()),
        }
    }

    pub fn new_exception(exception: ExceptionCode, message: Option<&CStr>) -> Status {
        Status {
            exception,
            service_specific: 0,
            transaction: StatusCode::OK,
            message: message.map(|m| m.to_string_lossy().into_owned()),
        }
    }

    pub fn new_exception_str<T: AsRef<str>>(exception: ExceptionCode, message: Option<T>) -> Status {
        Status {
            exception,
            service_specific: 0,
            transaction: StatusCode::OK,
            message: message.map(|m| m.as_ref().to_owned()),
        }
    }

    pub fn is_ok(&self) -> bool {
        self.exception == ExceptionCode::NONE && self.transaction == StatusCode::OK
    }

    pub fn get_description(&self) -> String {
        format!("{:?}", self)
    }

    pub fn exception_code(&self) -> ExceptionCode {
        self.exception
    }

    pub fn transaction_error(&self) -> StatusCode {
        self.transaction
    }

    pub fn service_specific_error(&self) -> i32 {
        self.service_specific
    }

    pub fn and_then<T, F>(self, op: F) -> std::result::Result<T, Status>
    where
        F: FnOnce() -> std::result::Result<T, Status>,
    {
        if self.is_ok() {
            op()
        } else {
            Err(self)
        }
    }
}

impl std::error::Error for Status {}

impl fmt::Display for Status {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl fmt::Debug for Status {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Status({:?}, service_specific={}, transaction={:?}, message={:?})",
            self.exception, self.service_specific, self.transaction, self.message
        )
    }
}

impl From<StatusCode> for Status {
    fn from(status: StatusCode) -> Status {
        Status {
            exception: ExceptionCode::TRANSACTION_FAILED,
            service_specific: 0,
            transaction: status,
            message: None,
        }
    }
}

impl From<ExceptionCode> for Status {
    fn from(code: ExceptionCode) -> Status {
        Status::new_exception(code, None)
    }
}

impl From<Status> for std::result::Result<(), Status> {
    fn from(status: Status) -> std::result::Result<(), Status> {
        if status.is_ok() {
            Ok(())
        } else {
            Err(status)
        }
    }
}

// ---------------------------------------------------------------- objects and interfaces

/// Base of every binder interface trait.
pub trait Interface: Send + Sync {
    fn dump(&self, _writer: &mut dyn std::io::Write, _args: &[&std::ffi::CStr]) -> SResult<()> {
        Ok(())
    }

    fn as_binder(&self) -> SpIBinder {
        panic!("This object was not a Binder object and cannot be converted into an SpIBinder.")
    }
}

/// An interface that can be rebuilt from a remote object.
pub trait FromIBinder: Interface {
    fn try_from(ibinder: SpIBinder) -> SResult<Strong<Self>>;
}

/// Operations of a remote object.
pub trait IBinder {
    fn link_to_death(&mut self, recipient: &mut DeathRecipient) -> SResult<()>;
    fn unlink_to_death(&mut self, recipient: &mut DeathRecipient) -> SResult<()>;
    fn ping_binder(&mut self) -> SResult<()>;
}

/// A strong reference to a remote interface.
pub struct Strong<I: FromIBinder + ?Sized>(Box<I>);

impl<I: FromIBinder + ?Sized> Strong<I> {
    pub fn downgrade(this: &Strong<I>) -> Weak<I> {
        unimplemented!("stand-in")
    }
}

impl<I: FromIBinder + ?Sized> Clone for Strong<I> {
    fn clone(&self) -> Self {
        unimplemented!("stand-in")
    }
}

impl<I: FromIBinder + ?Sized> std::borrow::Borrow<I> for Strong<I> {
    fn borrow(&self) -> &I {
        &self.0
    }
}

impl<I: FromIBinder + ?Sized> AsRef<I> for Strong<I> {
    fn as_ref(&self) -> &I {
        &self.0
    }
}

impl<I: FromIBinder + ?Sized> Deref for Strong<I> {
    type Target = I;
    fn deref(&self) -> &I {
        &self.0
    }
}

impl<I: FromIBinder + fmt::Debug + ?Sized> fmt::Debug for Strong<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<I: FromIBinder + ?Sized> Ord for Strong<I> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        unimplemented!("stand-in")
    }
}

impl<I: FromIBinder + ?Sized> PartialOrd for Strong<I> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<I: FromIBinder + ?Sized> PartialEq for Strong<I> {
    fn eq(&self, other: &Self) -> bool {
        unimplemented!("stand-in")
    }
}

impl<I: FromIBinder + ?Sized> Eq for Strong<I> {}

/// A weak reference to a remote interface.
pub struct Weak<I: FromIBinder + ?Sized>(std::marker::PhantomData<Box<I>>);

impl<I: FromIBinder + ?Sized> Weak<I> {
    pub fn upgrade(&self) -> SResult<Strong<I>> {
        unimplemented!("stand-in")
    }
}

impl<I: FromIBinder + ?Sized> Clone for Weak<I> {
    fn clone(&self) -> Self {
        unimplemented!("stand-in")
    }
}

/// A strong reference to a remote object.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SpIBinder(());

impl SpIBinder {
    /// Turns the object into a strong reference to the interface `I`.
    pub fn into_interface<I: FromIBinder + Interface + ?Sized>(self) -> SResult<Strong<I>> {
        FromIBinder::try_from(self)
    }
}

impl IBinder for SpIBinder {
    fn link_to_death(&mut self, recipient: &mut DeathRecipient) -> SResult<()> {
        unimplemented!("stand-in")
    }
    fn unlink_to_death(&mut self, recipient: &mut DeathRecipient) -> SResult<()> {
        unimplemented!("stand-in")
    }
    fn ping_binder(&mut self) -> SResult<()> {
        unimplemented!("stand-in")
    }
}

/// A weak reference to a remote object.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct WpIBinder(());

/// Death notification handle.
pub struct DeathRecipient(());

/// Options for a binder object that a service creates.
#[derive(Clone, Copy, Debug)]
pub struct BinderFeatures {
    /// Indicates that the service intends to receive caller security contexts.
    pub set_requesting_sid: bool,
    /// Allow the binder to inherit realtime scheduling policies from its caller.
    pub set_inherit_rt: bool,
    #[doc(hidden)]
    pub _non_exhaustive: (),
}

impl Default for BinderFeatures {
    fn default() -> Self {
        BinderFeatures { set_requesting_sid: false, set_inherit_rt: false, _non_exhaustive: () }
    }
}

/// A file descriptor sent over binder.
#[derive(Debug)]
pub struct ParcelFileDescriptor(std::fs::File);

/// Container for a parcelable of any type.
#[derive(Debug)]
pub struct ParcelableHolder<T: binder_impl::StabilityType>(std::marker::PhantomData<T>);

/// Items of the real `binder_impl` module that generated code or the macros below name.
pub mod binder_impl {
    pub trait StabilityType {}
    #[derive(Debug)]
    pub struct LocalStabilityType;
    #[derive(Debug)]
    pub struct VintfStabilityType;
    impl StabilityType for LocalStabilityType {}
    impl StabilityType for VintfStabilityType {}
}

// ---------------------------------------------------------------- process and thread state

/// Process-wide binder state.
pub struct ProcessState;

impl ProcessState {
    pub fn start_thread_pool() {
        unimplemented!("stand-in")
    }
    pub fn set_thread_pool_max_thread_count(num_threads: u32) {
        unimplemented!("stand-in")
    }
    pub fn join_thread_pool() {
        unimplemented!("stand-in")
    }
}

/// State of the thread that handles a transaction.
pub struct ThreadState;

impl ThreadState {
    pub fn get_calling_uid() -> u32 {
        unimplemented!("stand-in")
    }
    pub fn get_calling_pid() -> i32 {
        unimplemented!("stand-in")
    }
    pub fn is_handling_transaction() -> bool {
        unimplemented!("stand-in")
    }
    pub fn with_calling_sid<T, F>(check_permission: F) -> T
    where
        for<'a> F: FnOnce(Option<&'a CStr>) -> T,
    {
        unimplemented!("stand-in")
    }
}

// ---------------------------------------------------------------- service manager

pub fn add_service(identifier: &str, mut binder: SpIBinder) -> SResult<()> {
    unimplemented!("stand-in")
}

pub fn register_lazy_service(identifier: &str, mut binder: SpIBinder) -> SResult<()> {
    unimplemented!("stand-in")
}

pub fn force_lazy_services_persist(persist: bool) {
    unimplemented!("stand-in")
}

pub fn is_handling_transaction() -> bool {
    unimplemented!("stand-in")
}

pub fn get_service(name: &str) -> Option<SpIBinder> {
    unimplemented!("stand-in")
}

pub fn check_service(name: &str) -> Option<SpIBinder> {
    unimplemented!("stand-in")
}

pub fn wait_for_service(name: &str) -> Option<SpIBinder> {
    unimplemented!("stand-in")
}

pub fn get_interface<T: FromIBinder + ?Sized>(name: &str) -> SResult<Strong<T>> {
    unimplemented!("stand-in")
}

pub fn check_interface<T: FromIBinder + ?Sized>(name: &str) -> SResult<Strong<T>> {
    unimplemented!("stand-in")
}

pub fn wait_for_interface<T: FromIBinder + ?Sized>(name: &str) -> SResult<Strong<T>> {
    unimplemented!("stand-in")
}

pub fn is_declared(interface: &str) -> SResult<bool> {
    unimplemented!("stand-in")
}

pub fn get_declared_instances(interface: &str) -> SResult<Vec<String>> {
    unimplemented!("stand-in")
}

// ---------------------------------------------------------------- generated-code helpers

/// Declares an AIDL enum as a newtype over its backing integer, as the real macro does. The real
/// macro also implements the parcel (de)serialisation traits; nothing here uses a parcel.
#[macro_export]
macro_rules! declare_binder_enum {
    {
        $( #[$attr:meta] )*
        $enum:ident : [$backing:ty; $size:expr] {
            $( $( #[$value_attr:meta] )* $name:ident = $value:expr, )*
        }
    } => {
        $( #[$attr] )*
        #[derive(Default, Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
        #[allow(missing_docs)]
        #[repr(C)]
        pub struct $enum(pub $backing);
        impl $enum {
            $( $( #[$value_attr] )* #[allow(missing_docs)] pub const $name: Self = Self($value); )*

            #[inline(always)]
            #[allow(missing_docs)]
            pub const fn enum_values() -> [Self; $size] {
                [$(Self::$name),*]
            }

            #[inline(always)]
            #[allow(missing_docs)]
            pub const fn get(&self) -> $backing {
                self.0
            }
        }

        impl core::fmt::Debug for $enum {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                match self.0 {
                    $($value => f.write_str(stringify!($name)),)*
                    _ => f.write_fmt(format_args!("{}", self.0))
                }
            }
        }
    }
}
