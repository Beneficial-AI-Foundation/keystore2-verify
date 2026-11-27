import Keystore2Verify.Specs.Defs.Error

namespace Keystore2Verify.Error
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

/-- exact: `Error::log_level` of `Rc c` is `None` for `KEY_NOT_FOUND` (7) and `Some Error` for
every other code. -/
theorem Error_log_level_rc (c : Std.I32) :
    error.Error.log_level (error.Error.Rc c) =
      ok (if c = 7#i32 then none else some log.Level.Error) := by
  sorry

/-- exact: `Error::log_level` of `Km c` is `Some Info` for `KEY_USER_NOT_AUTHENTICATED` (-26) and
`ROLLBACK_RESISTANCE_UNAVAILABLE` (-67), and `Some Error` for every other code. -/
theorem Error_log_level_km (c : Std.I32) :
    error.Error.log_level (error.Error.Km c) =
      ok (if c = (-26)#i32 ∨ c = (-67)#i32 then some log.Level.Info
        else some log.Level.Error) := by
  sorry

/-- exact: `Error::log_level` of a `Binder` error is `Some Error`. -/
theorem Error_log_level_binder (c : binder.ExceptionCode) (n : Std.I32) :
    error.Error.log_level (error.Error.Binder c n) = ok (some log.Level.Error) := by
  sorry

/-- exact: `Error::log_level` of a `BinderTransaction` error is `Some Error`. -/
theorem Error_log_level_binder_transaction (s : binder.StatusCode) :
    error.Error.log_level (error.Error.BinderTransaction s) = ok (some log.Level.Error) := by
  sorry

end Keystore2Verify.Error
