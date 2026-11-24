import Keystore2Verify.Specs.Defs.SwKeyblob

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- exact: `tag_type` never fails. The result keeps the top 4 bits of the tag and clears the low
28 bits, as bit patterns of 32 bits. -/
theorem tag_type_bv (tag : Tag.Tag) :
    ∃ t, sw_keyblob.tag_type tag = ok t ∧ t.bv = tag.bv &&& 0xF0000000#32 := by
  sorry

/-- exact: two tags with the same top 4 bits give the same tag type. The low 28 bits do not
matter. -/
theorem tag_type_same_top_bits (t1 t2 : Tag.Tag) (h : t1.bv >>> 28 = t2.bv >>> 28) :
    ∃ r, sw_keyblob.tag_type t1 = ok r ∧ sw_keyblob.tag_type t2 = ok r := by
  sorry
end Keystore2Verify.SwKeyblob
