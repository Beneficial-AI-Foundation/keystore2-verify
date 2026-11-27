import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
/-- exact: `is_strongbox` never fails. It returns whether bit 4 (`STRONGBOX`, value 16) of the flags
is set. -/
theorem blob_is_strongbox (b : legacy_blob.Blob) :
    legacy_blob.Blob.is_strongbox b = ok (flagSet b 4) := by
  sorry

end Keystore2Verify.LegacyBlob
