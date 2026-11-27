import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open database.KeyLifeCycle.Insts
open CoreCloneClone renaming clone → keyLifeCycleClone
open CoreCmpPartialEqKeyLifeCycle renaming eq → keyLifeCycleEq
open CoreCmpOrd renaming cmp → keyLifeCycleCmp
open CoreCmpPartialOrdKeyLifeCycle renaming partial_cmp → keyLifeCyclePartialCmp

/-- exact: `clone` never fails and returns its argument. -/
theorem key_life_cycle_clone (x : database.KeyLifeCycle) : keyLifeCycleClone x = ok x := by
  sorry

/-- exact: `eq` never fails. It returns `true` exactly when the two values are the same
variant. -/
theorem key_life_cycle_eq (a b : database.KeyLifeCycle) :
    ∃ r, keyLifeCycleEq a b = ok r ∧ (r = true ↔ a = b) := by
  sorry

/-- exact: `cmp` never fails. It compares the position of the variants: `Existing` is smaller
than `Live`, which is smaller than `Unreferenced`. -/
theorem key_life_cycle_cmp (a b : database.KeyLifeCycle) :
    keyLifeCycleCmp a b = ok (compare (keyLifeCycleRank a) (keyLifeCycleRank b)) := by
  sorry

/-- exact: `partial_cmp` never fails and returns `Some` of the result of `cmp`. -/
theorem key_life_cycle_partial_cmp (a b : database.KeyLifeCycle) :
    keyLifeCyclePartialCmp a b =
      ok (some (compare (keyLifeCycleRank a) (keyLifeCycleRank b))) := by
  sorry
