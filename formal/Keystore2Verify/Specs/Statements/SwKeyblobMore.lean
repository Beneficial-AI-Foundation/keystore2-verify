import Keystore2Verify.Proofs.SwKeyblobMore.KeyBlob

namespace Keystore2Verify.SwKeyblob

section KeyBlob
open Aeneas Aeneas.Std Result keystore2
open sw_keyblob.KeyBlob.Insts.CoreCmpPartialEqKeyBlob renaming eq → keyBlobEq

recall key_blob_eq_key_material_differs (a b : sw_keyblob.KeyBlob)
    (h : a.key_material.val ≠ b.key_material.val) :
    keyBlobEq a b = ok false

recall key_blob_eq (hEq : KeyParameterEqSpec) (a b : sw_keyblob.KeyBlob) :
    ∃ r, keyBlobEq a b = ok r ∧
      (r = true ↔ a.key_material.val = b.key_material.val ∧
        a.hw_enforced.val = b.hw_enforced.val ∧ a.sw_enforced.val = b.sw_enforced.val)

end KeyBlob

end Keystore2Verify.SwKeyblob
