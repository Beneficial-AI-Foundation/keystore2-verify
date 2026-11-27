import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open legacy_blob.Blob.impl renaming value → implValue
/-- exact: `value` never fails. It returns the payload of the blob. In Rust it is a reference; the
translation returns the value. -/
theorem blob_value (b : legacy_blob.Blob) : implValue b = ok b.value := by
  sorry

end Keystore2Verify.LegacyBlob
