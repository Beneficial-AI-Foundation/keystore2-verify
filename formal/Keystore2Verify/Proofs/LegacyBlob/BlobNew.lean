import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
/-- exact: `new` never fails. It stores the flags and the value as they are, with no check. -/
theorem blob_new (flags : Std.U8) (value : legacy_blob.BlobValue) :
    legacy_blob.Blob.new flags value = ok { flags := flags, value := value } := by
  sorry

end Keystore2Verify.LegacyBlob
