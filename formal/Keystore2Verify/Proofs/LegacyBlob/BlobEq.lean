import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open legacy_blob.Blob.Insts renaming CoreCmpPartialEqBlob.eq → blobEq
open legacy_blob.BlobValue.Insts renaming CoreCmpPartialEqBlobValue.eq → blobValueEq

/-- exact: two blobs with different flags are not equal. The comparison returns `false` and
looks at no value. -/
theorem blob_eq_flags_ne (a b : legacy_blob.Blob) (h : a.flags ≠ b.flags) :
    blobEq a b = ok false := by
  sorry

/-- exact: two blobs with the same flags are equal exactly when their values are: the result is
that of the comparison of the two values. -/
theorem blob_eq_flags_eq (a b : legacy_blob.Blob) (h : a.flags = b.flags) :
    blobEq a b = blobValueEq a.value b.value := by
  sorry

end Keystore2Verify.LegacyBlob
