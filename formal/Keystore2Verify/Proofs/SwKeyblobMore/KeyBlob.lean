import Keystore2Verify.Specs.Defs.SwKeyblobMore

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open sw_keyblob.KeyBlob.Insts.CoreCmpPartialEqKeyBlob renaming eq → keyBlobEq

/-- exact: if the key material of the two blobs differs, `eq` returns `false`. In the Rust source
the two parameter lists are not compared on this path. -/
theorem key_blob_eq_key_material_differs (a b : sw_keyblob.KeyBlob)
    (h : a.key_material.val ≠ b.key_material.val) :
    keyBlobEq a b = ok false := by
  sorry

/-- conditional: `eq` never fails and is `true` exactly when the key material, the hardware
enforced parameters and the software enforced parameters are all equal. If the key material or the
hardware enforced parameters differ, the result is `false`. Hypothesis:
`KeyParameterEqSpec`. -/
theorem key_blob_eq (hEq : KeyParameterEqSpec) (a b : sw_keyblob.KeyBlob) :
    ∃ r, keyBlobEq a b = ok r ∧
      (r = true ↔ a.key_material.val = b.key_material.val ∧
        a.hw_enforced.val = b.hw_enforced.val ∧ a.sw_enforced.val = b.sw_enforced.val) := by
  sorry

end Keystore2Verify.SwKeyblob
