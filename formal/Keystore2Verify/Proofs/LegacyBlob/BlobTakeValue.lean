import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
/-- exact: `take_value` never fails. It returns the payload of the blob and drops the flags. -/
theorem blob_take_value (b : legacy_blob.Blob) : legacy_blob.Blob.take_value b = ok b.value := by
  sorry

end Keystore2Verify.LegacyBlob
