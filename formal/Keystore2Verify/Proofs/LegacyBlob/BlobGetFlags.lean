import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
/-- exact: `get_flags` never fails. It returns the flag byte. -/
theorem blob_get_flags (b : legacy_blob.Blob) : legacy_blob.Blob.get_flags b = ok b.flags := by
  sorry

end Keystore2Verify.LegacyBlob
