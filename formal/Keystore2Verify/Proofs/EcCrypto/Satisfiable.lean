import Keystore2Verify.Specs.Defs.EcCrypto

namespace Keystore2Verify.EcCrypto
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

/-!
# The crypto laws of `ec_crypto.rs` can hold together

The laws about the secret vector are stated over one view `deref` of the vector as a slice. A set
of laws that cannot hold together, or that hold only when no crypto call succeeds, would make
every statement that assumes them empty. The statement below gives one carrier and one set of
functions for which the shared length laws and the four laws of `Specs/Defs/EcCrypto.lean` hold
together, and in which every function has a call that returns `Ok`.
-/

/-- exact: there are a carrier `Z` for the secret vector, a view `deref` of it as a slice and one
function for each of the eight external calls, such that `TotalLaw deref`, `HkdfExpandLenLaw`,
`HkdfExtractLenLaw`, `SaltLenLaw` and the four laws `EcKeyMarshalLenLaw`, `PointToOctLenLaw`,
`AesGcmEncryptLenLaw` and `AesGcmDecryptLenLaw` hold together, and each function has a call that
returns `Ok`. The model is `Z := Slice U8` with `deref` the identity: every function always returns
`Ok`, with a vector of zeros of the length that its law asks for (the ciphertext of the encryption
is the message, and the plaintext of the decryption is the ciphertext). For `marshal` and `to_oct`
the statement asks for `Ok` on every input, because their argument types are opaque and Lean cannot
show that they have an element. -/
theorem ec_crypto_laws_satisfiable :
    ∃ (Z : Type) (deref : Z → Result (Slice Std.U8))
      (expand : Std.Usize → Slice Std.U8 → Slice Std.U8 →
        Result (core.result.Result Z keystore2_crypto.error.Error))
      (extract : Slice Std.U8 → Slice Std.U8 →
        Result (core.result.Result Z keystore2_crypto.error.Error))
      (salt : Result (core.result.Result (alloc.vec.Vec Std.U8) keystore2_crypto.error.Error))
      (marshal : keystore2_crypto.ECKey →
        Result (core.result.Result Z keystore2_crypto.error.Error))
      (to_oct : keystore2_crypto_bindgen.ec_point_st →
        Result (core.result.Result (alloc.vec.Vec Std.U8) keystore2_crypto.error.Error))
      (enc : Slice Std.U8 → Slice Std.U8 → Result (core.result.Result
        (alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8)
        keystore2_crypto.error.Error))
      (dec : Slice Std.U8 → Slice Std.U8 → Slice Std.U8 → Slice Std.U8 →
        Result (core.result.Result Z keystore2_crypto.error.Error)),
      TotalLaw deref ∧ HkdfExpandLenLaw deref expand ∧ HkdfExtractLenLaw deref extract ∧
      SaltLenLaw salt ∧ EcKeyMarshalLenLaw deref marshal ∧ PointToOctLenLaw to_oct ∧
      AesGcmEncryptLenLaw enc ∧ AesGcmDecryptLenLaw deref dec ∧
      (∃ n prk info z, expand n prk info = ok (.Ok z)) ∧
      (∃ secret salt' z, extract secret salt' = ok (.Ok z)) ∧
      (∃ s, salt = ok (.Ok s)) ∧
      (∀ key, ∃ z, marshal key = ok (.Ok z)) ∧
      (∀ pt, ∃ v, to_oct pt = ok (.Ok v)) ∧
      (∃ m k ct iv tag, enc m k = ok (.Ok (ct, iv, tag))) ∧
      (∃ data iv tag key p, dec data iv tag key = ok (.Ok p)) := by
  sorry

end Keystore2Verify.EcCrypto
