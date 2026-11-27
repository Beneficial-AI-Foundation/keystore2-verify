import Keystore2Verify.Specs.Defs.Externals

/-!
# Definitions for the statements about `error.rs`

Assumptions about the equality functions of the four types that `keystore2::error::Error`
wraps. Nothing here is an axiom.
-/

namespace Keystore2Verify.Error
open Aeneas Aeneas.Std Result keystore2
open android_system_keystore2.aidl.android.system.keystore2.ResponseCode.ResponseCode.Insts
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open ErrorCode.ErrorCode.Insts
open binder.StatusCode.Insts binder.ExceptionCode.Insts
open keystore2.core.option.Option renaming as_deref → optionAsDeref
open alloc.ffi.c_str.CString.Insts renaming CoreOpsDerefDerefCStr → cstringDeref

/-- An `eq` function never panics and returns `true` exactly when its two arguments are equal. -/
def EqAssumption {A : Type} (eq : A → A → Result Bool) : Prop :=
  ∀ a b, ∃ r, eq a b = ok r ∧ (r = true ↔ a = b)

/-- Assumption about an external function (`ResponseCode::eq`, register record
`ks2-ext-android-system-keystore2-aidl-android-system-keystore2-responsecode-responsecode-insts-corecmppartialeqresponsecode-eq`).
It never panics and returns `true` exactly when the two codes are equal. -/
def ResponseCodeEqSpec : Prop :=
  EqAssumption CoreCmpPartialEqResponseCode.eq

/-- Assumption about an external function (`ErrorCode::eq`, register record
`ks2-ext-android-hardware-security-keymint-aidl-android-hardware-security-keymint-errorcode-errorcode-insts-corecmppartialeqerrorcode-eq`).
It never panics and returns `true` exactly when the two codes are equal. -/
def ErrorCodeEqSpec : Prop :=
  EqAssumption CoreCmpPartialEqErrorCode.eq

/-- Assumption about an external function (`StatusCode::eq`, register record
`ks2-ext-binder-statuscode-insts-corecmppartialeqstatuscode-eq`).
It never panics and returns `true` exactly when the two status codes are equal. -/
def StatusCodeEqSpec : Prop :=
  EqAssumption CoreCmpPartialEqStatusCode.eq

/-- Assumption about an external function (`ExceptionCode::eq`, register record
`ks2-ext-binder-exceptioncode-insts-corecmppartialeqexceptioncode-eq`).
It never panics and returns `true` exactly when the two exception codes are equal. -/
def ExceptionCodeEqSpec : Prop :=
  EqAssumption CoreCmpPartialEqExceptionCode.eq

/-- `as_deref` returns `None` for `None`, and `Some` of the dereferenced value for `Some x`
when `deref x` returns a value. -/
def AsDerefAssumption {T U : Type} (deref : T → Result U)
    (as_deref : Option T → Result (Option U)) : Prop :=
  as_deref none = ok none ∧ ∀ x y, deref x = ok y → as_deref (some x) = ok (some y)

/-- Assumption about an external function (`Option::as_deref` at `CString`, register record
`ks2-ext-core-option-option-as-deref`). It returns `None` for `None`, and `Some` of the
dereferenced string for `Some`. -/
def CStringAsDerefSpec : Prop :=
  AsDerefAssumption cstringDeref.deref (optionAsDeref cstringDeref)

end Keystore2Verify.Error
