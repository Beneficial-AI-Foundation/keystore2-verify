import Keystore2Verify.Specs.Defs.Operation

namespace Keystore2Verify.Operation
open Aeneas Aeneas.Std Result keystore2
open android_system_keystore2.aidl.android.system.keystore2
open operation.Operation renaming update_outcome → updateOutcome

/-- exact: if the result is `Ok v`, `update_outcome` returns it unchanged, with the outcome
unchanged. -/
theorem update_outcome_ok {T : Type} (self : operation.Operation) (o : operation.Outcome)
    (v : T) :
    updateOutcome self o (.Ok v) = ok (.Ok v, o) := by
  sorry

/-- exact: if the result is `Err e`, `update_outcome` returns it unchanged, and the outcome
becomes `ErrorCode se`, whatever it was before. The serialized error `se` is the response code `r`
for `Rc r`, the error code `ec` for `Km ec`, and `ResponseCode::SYSTEM_ERROR` for the two binder
errors (`Binder` and `BinderTransaction`). -/
theorem update_outcome_err {T : Type} (self : operation.Operation) (o : operation.Outcome)
    (e : error.Error) :
    ∃ se, updateOutcome self o (.Err e : core.result.Result T error.Error) =
        ok (.Err e, .ErrorCode se) ∧
      (∀ r, e = .Rc r → se = r) ∧ (∀ ec, e = .Km ec → se = ec) ∧
      (∀ a b, e = .Binder a b → se = ResponseCode.ResponseCode.SYSTEM_ERROR) ∧
      (∀ a, e = .BinderTransaction a → se = ResponseCode.ResponseCode.SYSTEM_ERROR) := by
  sorry
