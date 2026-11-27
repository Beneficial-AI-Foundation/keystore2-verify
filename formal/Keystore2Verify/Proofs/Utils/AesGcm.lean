import Keystore2Verify.Specs.Defs.Utils

namespace Keystore2Verify.Utils
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open utils.AesGcm renaming Blanket.decrypt → aesGcmDecrypt, Blanket.encrypt → aesGcmEncrypt
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr

/-- conditional: let `k` be the key of `self` and let `aes_gcm_decrypt data iv tag k` return
`Ok z`. Then `decrypt` returns `Ok z`. Hypotheses: the key call returns `k` (`hk`) and the
decryption call returns `ok (Ok z)` (`hdec`); the shared assumptions about `from_str_nonconst`
and `format` (the message is built before the call to `context`), and `CryptoCtxLaw` for the
`context` call, which keeps an `Ok`. -/
theorem AesGcm_decrypt_ok {T : Type} (inst : utils.AesGcmKey T) (self : T)
    (data iv tag k : Slice Std.U8) (z : keystore2_crypto.zvec.ZVec)
    (root : anyhow.Error → ErrRoot) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hk : inst.key self = ok k)
    (hdec : keystore2_crypto.aes_gcm_decrypt data iv tag k = ok (ROk z)) :
    aesGcmDecrypt inst self data iv tag = ok (ROk z) := by
  sorry

/-- conditional: let `aes_gcm_decrypt data iv tag k` return `Err x`, for the key `k` of `self`.
Then `decrypt` returns an `Err` whose root cause is `x`, a `keystore2_crypto::error::Error`.
Hypotheses: as for `AesGcm_decrypt_ok`, with `hdec` returning `ok (Err x)`. -/
theorem AesGcm_decrypt_err {T : Type} (inst : utils.AesGcmKey T) (self : T)
    (data iv tag k : Slice Std.U8) (x : keystore2_crypto.error.Error)
    (root : anyhow.Error → ErrRoot) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hk : inst.key self = ok k)
    (hdec : keystore2_crypto.aes_gcm_decrypt data iv tag k = ok (RErr x)) :
    ∃ e, aesGcmDecrypt inst self data iv tag = ok (RErr e) ∧ root e = ErrRoot.crypto x := by
  sorry

/-- conditional: let `aes_gcm_encrypt plaintext k` return `Ok r`, for the key `k` of `self`.
Then `encrypt` returns `Ok r`, the triple of ciphertext, IV and tag. Hypotheses: the key call
returns `k` (`hk`) and the encryption call returns `ok (Ok r)` (`henc`); the shared assumptions
about `from_str_nonconst` and `format`, and `CryptoCtxLaw` for the `context` call. -/
theorem AesGcm_encrypt_ok {T : Type} (inst : utils.AesGcmKey T) (self : T)
    (plaintext k : Slice Std.U8)
    (r : alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8)
    (root : anyhow.Error → ErrRoot) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : CryptoCtxLaw root
      (alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8))
    (hk : inst.key self = ok k)
    (henc : keystore2_crypto.aes_gcm_encrypt plaintext k = ok (ROk r)) :
    aesGcmEncrypt inst self plaintext = ok (ROk r) := by
  sorry

/-- conditional: let `aes_gcm_encrypt plaintext k` return `Err x`, for the key `k` of `self`.
Then `encrypt` returns an `Err` whose root cause is `x`, a `keystore2_crypto::error::Error`.
Hypotheses: as for `AesGcm_encrypt_ok`, with `henc` returning `ok (Err x)`. -/
theorem AesGcm_encrypt_err {T : Type} (inst : utils.AesGcmKey T) (self : T)
    (plaintext k : Slice Std.U8) (x : keystore2_crypto.error.Error)
    (root : anyhow.Error → ErrRoot) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : CryptoCtxLaw root
      (alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8))
    (hk : inst.key self = ok k)
    (henc : keystore2_crypto.aes_gcm_encrypt plaintext k = ok (RErr x)) :
    ∃ e, aesGcmEncrypt inst self plaintext = ok (RErr e) ∧ root e = ErrRoot.crypto x := by
  sorry

end Keystore2Verify.Utils
