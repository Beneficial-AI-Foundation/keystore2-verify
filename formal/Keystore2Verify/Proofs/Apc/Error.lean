import Keystore2Verify.Specs.Defs.Externals

namespace Keystore2Verify.Apc
open Aeneas Aeneas.Std Result keystore2
open keystore2.android_security_apc.aidl.android.security.apc
open keystore2.std.collections.hash.map.HashMapKVSGlobal.Insts.CoreDefaultDefault
  renaming default → hashMapDefault
open keystore2.core.time.Duration
  renaming from_secs → durationFromSecs, checked_sub → durationCheckedSub,
    checked_mul → durationCheckedMul
open keystore2.std.time.Instant renaming elapsed → instantElapsed
open Aeneas.Std.core.option.Option renaming unwrap_or → optionUnwrapOr
open keystore2.std.sync.mpsc (Sender)
open keystore2.std.collections.hash.map (HashMap)
open keystore2.std.hash.random (RandomState)
open keystore2.std.hash.random.RandomState.Insts renaming CoreDefaultDefault → randomStateDefault

/-- conditional: if the constant `ResponseCode::SYSTEM_ERROR` evaluates to `c`, then `Error::sys`
returns `Error::Rc c`. Hypothesis: the value of the constant. -/
theorem apc_error_sys_ok (c : ResponseCode.ResponseCode)
    (h :
      ResponseCode.ResponseCode.SYSTEM_ERROR = ok c) :
    apc.Error.sys = ok (apc.Error.Rc c) := by
  sorry

/-- conditional: if the constant `ResponseCode::SYSTEM_ERROR` fails, `Error::sys` fails with the
same error `x`. Hypothesis: the outcome of the constant. -/
theorem apc_error_sys_fail (x : Error)
    (h :
      ResponseCode.ResponseCode.SYSTEM_ERROR = fail x) :
    apc.Error.sys = fail x := by
  sorry

/-- conditional: if the constant `ResponseCode::OPERATION_PENDING` evaluates to `c`, then
`Error::pending` returns `Error::Rc c`. Hypothesis: the value of the constant. -/
theorem apc_error_pending_ok (c : ResponseCode.ResponseCode)
    (h :
      ResponseCode.ResponseCode.OPERATION_PENDING = ok c) :
    apc.Error.pending = ok (apc.Error.Rc c) := by
  sorry

/-- conditional: if the constant `ResponseCode::OPERATION_PENDING` fails, `Error::pending` fails
with the same error `x`. Hypothesis: the outcome of the constant. -/
theorem apc_error_pending_fail (x : Error)
    (h :
      ResponseCode.ResponseCode.OPERATION_PENDING = fail x) :
    apc.Error.pending = fail x := by
  sorry

/-- conditional: if the constant `ResponseCode::IGNORED` evaluates to `c`, then `Error::ignored`
returns `Error::Rc c`. Hypothesis: the value of the constant. -/
theorem apc_error_ignored_ok (c : ResponseCode.ResponseCode)
    (h :
      ResponseCode.ResponseCode.IGNORED = ok c) :
    apc.Error.ignored = ok (apc.Error.Rc c) := by
  sorry

/-- conditional: if the constant `ResponseCode::IGNORED` fails, `Error::ignored` fails with the same
error `x`. Hypothesis: the outcome of the constant. -/
theorem apc_error_ignored_fail (x : Error)
    (h :
      ResponseCode.ResponseCode.IGNORED = fail x) :
    apc.Error.ignored = fail x := by
  sorry

/-- conditional: if the constant `ResponseCode::UNIMPLEMENTED` evaluates to `c`, then
`Error::unimplemented` returns `Error::Rc c`. Hypothesis: the value of the constant. -/
theorem apc_error_unimplemented_ok (c : ResponseCode.ResponseCode)
    (h :
      ResponseCode.ResponseCode.UNIMPLEMENTED = ok c) :
    apc.Error.unimplemented = ok (apc.Error.Rc c) := by
  sorry

/-- conditional: if the constant `ResponseCode::UNIMPLEMENTED` fails, `Error::unimplemented` fails
with the same error `x`. Hypothesis: the outcome of the constant. -/
theorem apc_error_unimplemented_fail (x : Error)
    (h :
      ResponseCode.ResponseCode.UNIMPLEMENTED = fail x) :
    apc.Error.unimplemented = fail x := by
  sorry

end Keystore2Verify.Apc
