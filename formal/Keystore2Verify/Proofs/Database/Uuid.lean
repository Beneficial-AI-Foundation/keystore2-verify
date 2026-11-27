import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open database.Uuid.Insts
open CoreCloneClone renaming clone → uuidClone
open CoreCmpPartialEqUuid renaming eq → uuidEq
open CoreCmpOrd renaming cmp → uuidCmp
open CoreCmpPartialOrdUuid renaming partial_cmp → uuidPartialCmp
open CoreDefaultDefault renaming default → uuidDefault
open CoreOpsDerefDerefArrayU816 renaming deref → uuidDeref
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open CoreConvertFromSecurityLevel renaming «from» → uuidFromSecurityLevel

/-- exact: `clone` never fails and returns its argument. -/
theorem uuid_clone (x : database.Uuid) : uuidClone x = ok x := by
  sorry

/-- exact: `default` never fails and returns the 16 zero bytes. -/
theorem uuid_default :
    ∃ u, uuidDefault = ok u ∧ u.val = List.replicate 16 (0#u8) := by
  sorry

/-- exact: `eq` never fails. It returns `true` exactly when the 16 bytes are equal. -/
theorem uuid_eq (a b : database.Uuid) :
    ∃ r, uuidEq a b = ok r ∧ (r = true ↔ a = b) := by
  sorry

/-- conditional: `cmp` returns the lexicographic order of the 16 bytes. Hypothesis:
`ArrayU8Cmp16Spec` (assumption about the `cmp` of byte arrays). -/
theorem uuid_cmp (h : ArrayU8Cmp16Spec) (a b : database.Uuid) :
    uuidCmp a b = ok (lexCmp a.val b.val) := by
  sorry

/-- conditional: `partial_cmp` returns `Some` of the lexicographic order of the 16 bytes.
Hypothesis: `ArrayU8Cmp16Spec`. -/
theorem uuid_partial_cmp (h : ArrayU8Cmp16Spec) (a b : database.Uuid) :
    uuidPartialCmp a b = ok (some (lexCmp a.val b.val)) := by
  sorry

/-- exact: `deref` never fails and returns the 16 bytes. -/
theorem uuid_deref (x : database.Uuid) : uuidDeref x = ok x := by
  sorry

/-- exact: `Uuid::from(SecurityLevel)` never fails. It returns 16 bytes that hold the level, taken
as a 128-bit number modulo 2^128 (a negative level is sign-extended), most significant byte
first. For a level from 0 to 255 these are 15 zero bytes and then the level. -/
theorem uuid_from_security_level (s : SecurityLevel.SecurityLevel) :
    ∃ u, uuidFromSecurityLevel s = ok u ∧ u.val.length = 16 ∧
      (beNat u.val : Int) = s.val % 2 ^ 128 := by
  sorry
