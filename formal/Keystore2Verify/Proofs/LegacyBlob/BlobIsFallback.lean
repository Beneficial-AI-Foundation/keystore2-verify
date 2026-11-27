import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
/-- exact: `is_fallback` never fails. It returns whether bit 1 of the flags (`FALLBACK`, value 2)
is set. -/
theorem blob_is_fallback (b : legacy_blob.Blob) :
    legacy_blob.Blob.is_fallback b = ok (flagSet b 1) := by
  sorry

end Keystore2Verify.LegacyBlob
