import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open database.KeyEntryLoadBits.Insts
open CoreCloneClone renaming clone → loadBitsClone
open CoreCmpPartialEqKeyEntryLoadBits renaming eq → loadBitsEq
open CoreCmpOrd renaming cmp → loadBitsCmp
open CoreCmpPartialOrdKeyEntryLoadBits renaming partial_cmp → loadBitsPartialCmp
open database.KeyEntryLoadBits renaming load_public → loadBitsPublic
open database.KeyEntryLoadBits renaming load_km → loadBitsKm

/-- exact: `clone` never fails and returns its argument. -/
theorem key_entry_load_bits_clone (x : database.KeyEntryLoadBits) :
    loadBitsClone x = ok x := by
  sorry

/-- exact: `eq` never fails. It returns `true` exactly when the two numbers are equal. -/
theorem key_entry_load_bits_eq (a b : database.KeyEntryLoadBits) :
    ∃ r, loadBitsEq a b = ok r ∧ (r = true ↔ a = b) := by
  sorry

/-- exact: `cmp` never fails. It compares the two `u32` numbers. -/
theorem key_entry_load_bits_cmp (a b : database.KeyEntryLoadBits) :
    loadBitsCmp a b = ok (compare a.val b.val) := by
  sorry

/-- exact: `partial_cmp` never fails and returns `Some` of the result of `cmp`. -/
theorem key_entry_load_bits_partial_cmp (a b : database.KeyEntryLoadBits) :
    loadBitsPartialCmp a b = ok (some (compare a.val b.val)) := by
  sorry

/-- exact: `load_public` never fails. It returns `true` exactly when bit 1 (value 2) is set. -/
theorem key_entry_load_bits_load_public (x : database.KeyEntryLoadBits) :
    ∃ b, loadBitsPublic x = ok b ∧ (b = true ↔ (x &&& 2#u32) ≠ 0#u32) := by
  sorry

/-- exact: `load_km` never fails. It returns `true` exactly when bit 0 (value 1) is set. -/
theorem key_entry_load_bits_load_km (x : database.KeyEntryLoadBits) :
    ∃ b, loadBitsKm x = ok b ∧ (b = true ↔ (x &&& 1#u32) ≠ 0#u32) := by
  sorry

/-- exact: the four constants `NONE`, `KM`, `PUBLIC` and `BOTH` ask for no component, the
KeyMint component, the public components and both, respectively. -/
theorem key_entry_load_bits_constants :
    loadBitsPublic database.KeyEntryLoadBits.NONE = ok false ∧
    loadBitsKm database.KeyEntryLoadBits.NONE = ok false ∧
    loadBitsPublic database.KeyEntryLoadBits.KM = ok false ∧
    loadBitsKm database.KeyEntryLoadBits.KM = ok true ∧
    loadBitsPublic database.KeyEntryLoadBits.PUBLIC = ok true ∧
    loadBitsKm database.KeyEntryLoadBits.PUBLIC = ok false ∧
    loadBitsPublic database.KeyEntryLoadBits.BOTH = ok true ∧
    loadBitsKm database.KeyEntryLoadBits.BOTH = ok true := by
  sorry
