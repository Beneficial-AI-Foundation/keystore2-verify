import Keystore2Verify.Specs.Defs.Utils

namespace Keystore2Verify.Utils
open Aeneas Aeneas.Std Result keystore2
open utils.AppInfo.Insts
open CoreDefaultDefault renaming default → appInfoDefault
open CoreCloneClone renaming clone → appInfoClone
open CoreCmpPartialEqAppInfo renaming eq → appInfoEq

/-- conditional: `AppInfo::default` returns the struct with no target SDK and `is_system_app`
set to `false`. Hypothesis: the assumption about an external function `OptionDefaultI32Spec`
(`Option::<i32>::default()` is `None`). -/
theorem AppInfo_default (hdef : OptionDefaultI32Spec) :
    appInfoDefault = ok { target_sdk := none, is_system_app := false } := by
  sorry

/-- exact: `AppInfo::clone` never fails and returns its argument. -/
theorem AppInfo_clone (x : utils.AppInfo) : appInfoClone x = ok x := by
  sorry

/-- exact: if the two values differ in `is_system_app`, `AppInfo::eq` returns `false`. In the
Rust source, the derived comparison of `target_sdk` is not made on this path. -/
theorem AppInfo_eq_ne_system (x y : utils.AppInfo) (h : x.is_system_app ≠ y.is_system_app) :
    appInfoEq x y = ok false := by
  sorry

/-- conditional: if the two values have the same `is_system_app`, `AppInfo::eq` returns `true`
exactly when the two `target_sdk` are equal. Hypothesis: the assumption about an external
function `OptionEqI32Spec` (`Option::<i32>::eq` is the equality of the two options). -/
theorem AppInfo_eq_same_system (heq : OptionEqI32Spec) (x y : utils.AppInfo)
    (h : x.is_system_app = y.is_system_app) :
    appInfoEq x y = ok (decide (x.target_sdk = y.target_sdk)) := by
  sorry

end Keystore2Verify.Utils
