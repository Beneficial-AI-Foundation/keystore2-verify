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
  simp [bootLevelClone, CoreCloneClone.clone]

/-- exact: `==` on boot levels never fails and returns `true` exactly when the two `usize`
values are equal. -/
theorem boot_level_eq (a b : BootLevel) :
    ∃ r, bootLevelEq a b = ok r ∧ (r = true ↔ a.val = b.val) := by
  refine ⟨decide (a = b), by simp [bootLevelEq, CoreCmpPartialEqBootLevel.eq], ?_⟩
  rw [decide_eq_true_iff]
  refine ⟨fun h => by rw [h], fun h => ?_⟩
  cases a; cases b
  simp_all [UScalar.val]
  exact BitVec.eq_of_toNat_eq h

/-- exact: `cmp` on boot levels never fails and orders them as their `usize` values. -/
theorem boot_level_cmp (a b : BootLevel) :
    bootLevelCmp a b = ok (compare a.val b.val) := by
  simp [bootLevelCmp, CoreCmpOrd.cmp]

/-- exact: `partial_cmp` on boot levels never fails, is never `None`, and orders them as their
`usize` values. -/
theorem boot_level_partial_cmp (a b : BootLevel) :
    bootLevelPartialCmp a b = ok (some (compare a.val b.val)) := by
  simp [bootLevelPartialCmp, CoreCmpPartialOrdBootLevel.partial_cmp, boot_level_cmp]

end Keystore2Verify.BootLevelKeys
