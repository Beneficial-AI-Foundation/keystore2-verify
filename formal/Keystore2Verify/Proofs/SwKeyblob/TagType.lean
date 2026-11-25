import Keystore2Verify.Specs.Defs.SwKeyblob

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- exact: `tag_type` never fails. The result keeps the top 4 bits of the tag and clears the low
28 bits, as bit patterns of 32 bits. -/
theorem tag_type_bv (tag : Tag.Tag) :
    ∃ t, sw_keyblob.tag_type tag = ok t ∧ t.bv = tag.bv &&& 0xF0000000#32 := by
  refine ⟨UScalar.hcast .I32 (IScalar.hcast .U32 tag &&& 4026531840#u32),
    by simp [sw_keyblob.tag_type, lift], ?_⟩
  simp [UScalar.hcast_bv_eq, IScalar.hcast_bv_eq]

/-- exact: two tags with the same top 4 bits give the same tag type. The low 28 bits do not
matter. -/
theorem tag_type_same_top_bits (t1 t2 : Tag.Tag) (h : t1.bv >>> 28 = t2.bv >>> 28) :
    ∃ r, sw_keyblob.tag_type t1 = ok r ∧ sw_keyblob.tag_type t2 = ok r := by
  obtain ⟨r1, h1, hb1⟩ := tag_type_bv t1
  obtain ⟨r2, h2, hb2⟩ := tag_type_bv t2
  have hmask : ∀ a : BitVec 32, a &&& 0xF0000000#32 = (a >>> 28) <<< 28 := by
    intro a
    have hm : ∀ j, j < 28 → (0xF0000000#32).getLsbD j = false := by decide
    have hm2 : ∀ j, 28 ≤ j → j < 32 → (0xF0000000#32).getLsbD j = true := by decide
    ext i hi
    simp only [← BitVec.getLsbD_eq_getElem]
    by_cases h28 : i < 28
    · simp [h28, hm i h28]
    · have : 28 + (i - 28) = i := by omega
      simp [h28, hm2 i (by omega) hi, this, hi]
  have hr : r1 = r2 := by
    have e : r1.bv = r2.bv := by rw [hb1, hb2, hmask, hmask, h]
    cases r1; cases r2; simp_all
  exact ⟨r1, h1, hr ▸ h2⟩
end Keystore2Verify.SwKeyblob
