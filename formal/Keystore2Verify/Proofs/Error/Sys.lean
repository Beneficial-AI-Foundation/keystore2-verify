import Keystore2Verify.Specs.Defs.Error

namespace Keystore2Verify.Error
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

/-- exact: `Error::sys()` returns `Error::Rc` with the code 4, `ResponseCode::SYSTEM_ERROR`. -/
theorem Error_sys : error.Error.sys = ok (error.Error.Rc 4#i32) := by
  sorry

end Keystore2Verify.Error
