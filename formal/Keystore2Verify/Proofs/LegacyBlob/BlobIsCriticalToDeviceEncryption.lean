import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
/-- exact: `is_critical_to_device_encryption` never fails. It returns whether bit 3
(`CRITICAL_TO_DEVICE_ENCRYPTION`, value 8) of the flags is set. -/
theorem blob_is_critical_to_device_encryption (b : legacy_blob.Blob) :
    legacy_blob.Blob.is_critical_to_device_encryption b = ok (flagSet b 3) := by
  sorry

end Keystore2Verify.LegacyBlob
