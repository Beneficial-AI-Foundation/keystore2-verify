import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open database.KeyType.Insts
open CoreCloneClone renaming clone → keyTypeClone
open CoreCmpPartialEqKeyType renaming eq → keyTypeEq
open CoreCmpOrd renaming cmp → keyTypeCmp
open CoreCmpPartialOrdKeyType renaming partial_cmp → keyTypePartialCmp

/-- exact: `clone` never fails and returns its argument. -/
theorem key_type_clone (x : database.KeyType) : keyTypeClone x = ok x := by
  sorry

/-- exact: `eq` never fails. It returns `true` exactly when the two values are the same
variant. -/
theorem key_type_eq (a b : database.KeyType) :
    ∃ r, keyTypeEq a b = ok r ∧ (r = true ↔ a = b) := by
  sorry

/-- exact: `cmp` never fails. It compares the position of the variants: `Client` is smaller
than `Super`. -/
theorem key_type_cmp (a b : database.KeyType) :
    keyTypeCmp a b = ok (compare (keyTypeRank a) (keyTypeRank b)) := by
  sorry

/-- exact: `partial_cmp` never fails and returns `Some` of the result of `cmp`. -/
theorem key_type_partial_cmp (a b : database.KeyType) :
    keyTypePartialCmp a b = ok (some (compare (keyTypeRank a) (keyTypeRank b))) := by
  sorry
