import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open database.BlobState.Insts
open CoreCloneClone renaming clone → blobStateClone
open CoreCmpPartialEqBlobState renaming eq → blobStateEq
open CoreCmpOrd renaming cmp → blobStateCmp
open CoreCmpPartialOrdBlobState renaming partial_cmp → blobStatePartialCmp
open CoreDefaultDefault renaming default → blobStateDefault

/-- exact: `clone` never fails and returns its argument. -/
theorem blob_state_clone (x : database.BlobState) : blobStateClone x = ok x := by
  sorry

/-- exact: `default` never fails and returns `Current` (the variant marked `#[default]`). -/
theorem blob_state_default : blobStateDefault = ok database.BlobState.Current := by
  sorry

/-- exact: `eq` never fails. It returns `true` exactly when the two values are the same
variant. -/
theorem blob_state_eq (a b : database.BlobState) :
    ∃ r, blobStateEq a b = ok r ∧ (r = true ↔ a = b) := by
  sorry

/-- exact: `cmp` never fails. It compares the position of the variants: `Current` is smaller
than `Superseded`, which is smaller than `Orphaned`. -/
theorem blob_state_cmp (a b : database.BlobState) :
    blobStateCmp a b = ok (compare (blobStateRank a) (blobStateRank b)) := by
  sorry

/-- exact: `partial_cmp` never fails and returns `Some` of the result of `cmp`. -/
theorem blob_state_partial_cmp (a b : database.BlobState) :
    blobStatePartialCmp a b = ok (some (compare (blobStateRank a) (blobStateRank b))) := by
  sorry
