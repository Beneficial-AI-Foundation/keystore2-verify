import Keystore2Verify.Specs.Defs.Error

namespace Keystore2Verify.Error
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open error.Error.Insts.CoreCmpPartialEqError renaming eq → errorEq
open error.Error.BinderTransaction renaming constructor → binderTransactionNew

/-- exact: `Error::eq` on two values of different variants returns `false`. In the Rust source
neither wrapped field is compared on this path. -/
theorem Error_eq_different_variants (x y : error.Error)
    (h : error.Error.read_discriminant x ≠ error.Error.read_discriminant y) :
    errorEq x y = ok false := by
  sorry

/-- conditional: `Error::eq` on two `Rc` values returns `true` exactly when the response codes
are equal. Hypothesis: the assumption about `ResponseCode::eq`. -/
theorem Error_eq_rc (a b : Std.I32)
    (hrc : ResponseCodeEqSpec) :
    ∃ r, errorEq (error.Error.Rc a) (error.Error.Rc b) = ok r ∧ (r = true ↔ a = b) := by
  sorry

/-- conditional: `Error::eq` on two `Km` values returns `true` exactly when the error codes are
equal. Hypothesis: the assumption about `ErrorCode::eq`. -/
theorem Error_eq_km (a b : Std.I32)
    (hec : ErrorCodeEqSpec) :
    ∃ r, errorEq (error.Error.Km a) (error.Error.Km b) = ok r ∧ (r = true ↔ a = b) := by
  sorry

/-- exact: `Error::eq` on two `Binder` values with different numbers returns `false`. -/
theorem Error_eq_binder_number_differs (c c' : binder.ExceptionCode) (n n' : Std.I32)
    (h : n ≠ n') :
    errorEq (error.Error.Binder c n) (error.Error.Binder c' n') = ok false := by
  sorry

/-- conditional: `Error::eq` on two `Binder` values with the same number returns `true` exactly
when the exception codes are equal. Hypothesis: the assumption about `ExceptionCode::eq`. -/
theorem Error_eq_binder_same_number (c c' : binder.ExceptionCode) (n : Std.I32)
    (hex : ExceptionCodeEqSpec) :
    ∃ r, errorEq (error.Error.Binder c n) (error.Error.Binder c' n) = ok r ∧
      (r = true ↔ c = c') := by
  sorry

/-- conditional: `Error::eq` on two `BinderTransaction` values returns `true` exactly when the
status codes are equal. Hypothesis: the assumption about `StatusCode::eq`. -/
theorem Error_eq_binder_transaction (s s' : binder.StatusCode) (hsc : StatusCodeEqSpec) :
    ∃ r, errorEq (error.Error.BinderTransaction s) (error.Error.BinderTransaction s') = ok r ∧
      (r = true ↔ s = s') := by
  sorry

/-- exact: the constructor function `Error::BinderTransaction` returns the variant that wraps
its argument. -/
theorem Error_BinderTransaction_constructor (s : binder.StatusCode) :
    binderTransactionNew s = ok (error.Error.BinderTransaction s) := by
  sorry

end Keystore2Verify.Error
