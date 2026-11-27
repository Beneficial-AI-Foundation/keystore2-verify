import Keystore2Verify.Specs.Defs.Error

namespace Keystore2Verify.Error
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

/-- exact: `error_to_serialized_error` keeps the code of an `Rc` error. -/
theorem error_to_serialized_error_rc (c : Std.I32) :
    error.error_to_serialized_error (error.Error.Rc c) = ok c := by
  sorry

/-- exact: `error_to_serialized_error` keeps the code of a `Km` error. -/
theorem error_to_serialized_error_km (c : Std.I32) :
    error.error_to_serialized_error (error.Error.Km c) = ok c := by
  sorry

/-- exact: `error_to_serialized_error` maps a `Binder` error to `SYSTEM_ERROR`, the code 4. -/
theorem error_to_serialized_error_binder (c : binder.ExceptionCode) (n : Std.I32) :
    error.error_to_serialized_error (error.Error.Binder c n) = ok 4#i32 := by
  sorry

/-- exact: `error_to_serialized_error` maps a `BinderTransaction` error to `SYSTEM_ERROR`, the
code 4. -/
theorem error_to_serialized_error_binder_transaction (s : binder.StatusCode) :
    error.error_to_serialized_error (error.Error.BinderTransaction s) = ok 4#i32 := by
  sorry

end Keystore2Verify.Error
