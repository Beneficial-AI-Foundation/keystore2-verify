import Keystore2Verify.Specs.Defs.SuperKey

namespace Keystore2Verify.SuperKey
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

open super_key.WipeKeyOption.Insts renaming CoreCmpPartialEqWipeKeyOption → wipeEq

/-- exact: `==` on `WipeKeyOption` never fails and returns `true` exactly when both arguments are
the same variant (`PlaintextAndBiometric` or `PlaintextOnly`). -/
theorem WipeKeyOption_eq (a b : super_key.WipeKeyOption) :
    ∃ r, wipeEq.eq a b = ok r ∧ (r = true ↔ a = b) := by
  sorry

end Keystore2Verify.SuperKey
