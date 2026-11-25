import Keystore2Verify.Specs.Defs.BootLevelKeys

namespace Keystore2Verify.BootLevelKeys
open Aeneas Aeneas.Std Result

/-- A bind returns `ok y` exactly when its first part returns some `ok a` and the rest returns
`ok y` from `a`. -/
theorem bind_eq_ok_iff {α β : Type} {x : Result α} {f : α → Result β} {y : β} :
    Std.bind x f = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp

end Keystore2Verify.BootLevelKeys
