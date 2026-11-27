import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
/-- exact: `is_encrypted` never fails. It returns whether bit 2 (`SUPER_ENCRYPTED`, value 4) or bit
0 (`ENCRYPTED`, value 1) of the flags is set. -/
theorem blob_is_encrypted (b : legacy_blob.Blob) :
    legacy_blob.Blob.is_encrypted b = ok (flagSet b 2 || flagSet b 0) := by
  sorry

end Keystore2Verify.LegacyBlob
