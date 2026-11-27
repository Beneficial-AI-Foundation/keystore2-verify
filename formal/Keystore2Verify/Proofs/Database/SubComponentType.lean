import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open database.SubComponentType.Insts
open CoreCloneClone renaming clone → subComponentTypeClone
open CoreCmpPartialEqSubComponentType renaming eq → subComponentTypeEq
open CoreCmpOrd renaming cmp → subComponentTypeCmp
open CoreCmpPartialOrdSubComponentType renaming partial_cmp → subComponentTypePartialCmp

/-- exact: `clone` never fails and returns its argument. -/
theorem sub_component_type_clone (x : database.SubComponentType) :
    subComponentTypeClone x = ok x := by
  sorry

/-- exact: `eq` never fails. It returns `true` exactly when the two numbers are equal. -/
theorem sub_component_type_eq (a b : database.SubComponentType) :
    ∃ r, subComponentTypeEq a b = ok r ∧ (r = true ↔ a = b) := by
  sorry

/-- exact: `cmp` never fails. It compares the two `u32` numbers. -/
theorem sub_component_type_cmp (a b : database.SubComponentType) :
    subComponentTypeCmp a b = ok (compare a.val b.val) := by
  sorry

/-- exact: `partial_cmp` never fails and returns `Some` of the result of `cmp`. -/
theorem sub_component_type_partial_cmp (a b : database.SubComponentType) :
    subComponentTypePartialCmp a b = ok (some (compare a.val b.val)) := by
  sorry
