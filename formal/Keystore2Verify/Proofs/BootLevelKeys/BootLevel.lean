import Keystore2Verify.Specs.Defs.BootLevelKeys

namespace Keystore2Verify.BootLevelKeys
open Aeneas Aeneas.Std Result keystore2 keystore2.boot_level_keys
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open keystore2.boot_level_keys.BootLevel.Insts
open CoreCloneClone renaming clone → bootLevelClone
open CoreCmpPartialEqBootLevel renaming eq → bootLevelEq
open CoreCmpOrd renaming cmp → bootLevelCmp
open CoreCmpPartialOrdBootLevel renaming partial_cmp → bootLevelPartialCmp

/-- exact: `clone` of a boot level returns the same level and never fails. -/
theorem boot_level_clone (a : BootLevel) :
    bootLevelClone a = ok a := by
  sorry

/-- exact: `==` on boot levels never fails and returns `true` exactly when the two `usize`
values are equal. -/
theorem boot_level_eq (a b : BootLevel) :
    ∃ r, bootLevelEq a b = ok r ∧ (r = true ↔ a.val = b.val) := by
  sorry

/-- exact: `cmp` on boot levels never fails and orders them as their `usize` values. -/
theorem boot_level_cmp (a b : BootLevel) :
    ∃ o, bootLevelCmp a b = ok o ∧
      (o = .lt ↔ a.val < b.val) ∧ (o = .eq ↔ a.val = b.val) ∧ (o = .gt ↔ b.val < a.val) := by
  sorry

/-- exact: `partial_cmp` on boot levels never fails, is never `None`, and orders them as their
`usize` values. -/
theorem boot_level_partial_cmp (a b : BootLevel) :
    ∃ o, bootLevelPartialCmp a b = ok (some o) ∧
      (o = .lt ↔ a.val < b.val) ∧ (o = .eq ↔ a.val = b.val) ∧ (o = .gt ↔ b.val < a.val) := by
  sorry

end Keystore2Verify.BootLevelKeys
