import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open database.EncryptedBy.Insts
open CoreCmpPartialEqEncryptedBy renaming eq → encryptedByEq
open CoreCmpOrd renaming cmp → encryptedByCmpFn
open CoreCmpPartialOrdEncryptedBy renaming partial_cmp → encryptedByPartialCmp

/-- exact: `eq` never fails. It returns `true` exactly when both are `Password`, or both are
`KeyId` with the same id. -/
theorem encrypted_by_eq (a b : database.EncryptedBy) :
    ∃ r, encryptedByEq a b = ok r ∧ (r = true ↔ a = b) := by
  sorry

/-- exact: `cmp` never fails. `Password` is smaller than every `KeyId`, and two `KeyId` are
ordered by their ids. -/
theorem encrypted_by_cmp (a b : database.EncryptedBy) :
    encryptedByCmpFn a b = ok (encryptedByCmp a b) := by
  sorry

/-- exact: `partial_cmp` never fails and returns `Some` of the result of `cmp`. -/
theorem encrypted_by_partial_cmp (a b : database.EncryptedBy) :
    encryptedByPartialCmp a b = ok (some (encryptedByCmp a b)) := by
  sorry
