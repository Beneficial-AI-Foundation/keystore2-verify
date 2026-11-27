import Keystore2Verify.Specs.Defs.Utils

namespace Keystore2Verify.Utils
open Aeneas Aeneas.Std Result keystore2
open android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- exact: `is_imei_attestation_tag` never fails. It returns `true` exactly for the two IMEI
attestation tags, `ATTESTATION_ID_IMEI` (`-1879047478`) and `ATTESTATION_ID_SECOND_IMEI`
(`-1879047469`), and `false` for every other `i32`. The translation has folded the two tag
constants into these numbers. -/
theorem is_imei_attestation_tag_iff
    (tag : Tag.Tag) :
    utils.is_imei_attestation_tag tag =
      ok (decide (tag.val = -1879047478 ∨ tag.val = -1879047469)) := by
  sorry

end Keystore2Verify.Utils
