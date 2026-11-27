import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open legacy_blob.LegacyBlobLoader
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
/-- exact: `tag_type` never fails. It keeps the top byte of the tag and clears the other 24 bits:
the result has the bits of `tag` and `0xFF000000`. -/
theorem legacy_blob_tag_type
    (tag : Tag.Tag) :
    ∃ r, tag_type tag = ok r ∧ r.bv = tag.bv &&& 4278190080#32 := by
  sorry

end Keystore2Verify.LegacyBlob
