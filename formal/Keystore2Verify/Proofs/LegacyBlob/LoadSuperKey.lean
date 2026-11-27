import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open legacy_blob.LegacyBlobLoader
open android_system_keystore2.aidl.android.system.keystore2.ResponseCode.ResponseCode
open Aeneas.Std.alloc.vec.Vec renaming deref → vecDeref
open keystore2_crypto.zvec.ZVec.Insts.CoreConvertTryFromVecU8Error renaming try_from → tryFromVec
open keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8 renaming deref → zvecDerefFn

/-! In each theorem the file is read as follows: `make_super_key_filename` returns `path`,
`deref` returns `p`, and `read_generic_blob` (an item the extraction could not translate) returns
`r`. -/

/-- conditional: if the file is absent, `load_super_key` returns `Ok None`. Hypotheses: the
outcomes of `make_super_key_filename`, `deref` and `read_generic_blob`; the `context` assumption
for an `anyhow::Error`; and the message assumptions. -/
theorem load_super_key_absent (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob)) (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (pw : keystore2_crypto.Password) (path : std.path.PathBuf)
    (p : std.path.Path) (hmk : make_super_key_filename self user = ok path)
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob p = ok (.Ok none)) :
    load_super_key self user pw = ok (.Ok none) := by
  sorry

/-- conditional: if reading the file returns an error `e`, `load_super_key` returns an error with
the same root cause. Hypotheses: those of `load_super_key_absent`, with the outcome `Err e`. -/
theorem load_super_key_read_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob)) (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (pw : keystore2_crypto.Password) (path : std.path.PathBuf)
    (p : std.path.Path) (e : anyhow.Error)
    (hmk : make_super_key_filename self user = ok path)
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob p = ok (.Err e)) :
    ∃ e', load_super_key self user pw = ok (.Err e') ∧ root e' = root e := by
  sorry

/-- conditional: if the file holds a `PwEncrypted` blob with the bit `ENCRYPTED` (bit 0) set,
`derive_key_pbkdf2` returns the key `key` for the salt and the key size, and `aes_gcm_decrypt`
(called with the data, the `iv`, the `tag` and the bytes of `key`, in that order) returns `plain`,
then `load_super_key` returns `Ok (Some plain)`. The bit `SUPER_ENCRYPTED` is not tested.
Hypotheses: the outcomes of the file read, of the key derivation, of the view of `key` as a slice
and of the decryption; the `context` assumptions for an `anyhow::Error` and for a crypto error; and
the message assumptions. -/
theorem load_super_key_decrypted (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hcc : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId)
    (pw : keystore2_crypto.Password) (path : std.path.PathBuf) (p : std.path.Path)
    (blob : legacy_blob.Blob) (iv tag data salt : alloc.vec.Vec Std.U8) (n : Std.Usize)
    (key plain : keystore2_crypto.zvec.ZVec) (ks : Slice Std.U8)
    (hmk : make_super_key_filename self user = ok path)
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hv : blob.value = .PwEncrypted iv tag data salt n) (hfl : flagSet blob 0 = true)
    (hder : keystore2_crypto.Password.derive_key_pbkdf2 pw (vecDeref salt) n =
      ok (.Ok key))
    (hk : zvecDerefFn key = ok ks)
    (hdec : keystore2_crypto.aes_gcm_decrypt (vecDeref data) (vecDeref iv)
      (vecDeref tag) ks = ok (.Ok plain)) :
    load_super_key self user pw = ok (.Ok (some plain)) := by
  sorry

/-- conditional: if the file holds a `PwEncrypted` blob with the bit `ENCRYPTED` set and the key
derivation returns an error `e`, `load_super_key` returns an error whose root cause is `e` (class
`crypto`). In the Rust source this path returns before `aes_gcm_decrypt` is called. Hypotheses:
the outcomes of the file read and of the key derivation; the `context` assumptions for an
`anyhow::Error` and for a crypto error; and the message assumptions. -/
theorem load_super_key_derive_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hcc : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId)
    (pw : keystore2_crypto.Password) (path : std.path.PathBuf) (p : std.path.Path)
    (blob : legacy_blob.Blob) (iv tag data salt : alloc.vec.Vec Std.U8) (n : Std.Usize)
    (e : keystore2_crypto.error.Error)
    (hmk : make_super_key_filename self user = ok path)
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hv : blob.value = .PwEncrypted iv tag data salt n) (hfl : flagSet blob 0 = true)
    (hder : keystore2_crypto.Password.derive_key_pbkdf2 pw (vecDeref salt) n =
      ok (.Err e)) :
    ∃ e', load_super_key self user pw = ok (.Err e') ∧ root e' = ErrRoot.crypto e := by
  sorry

/-- conditional: if the file holds a `PwEncrypted` blob with the bit `ENCRYPTED` set, the key
derivation returns `key`, and `aes_gcm_decrypt` returns an error `e`, `load_super_key` returns an
error whose root cause is `e` (class `crypto`). Hypotheses: those of `load_super_key_decrypted`,
with the outcome `Err e` of the decryption. -/
theorem load_super_key_decrypt_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hcc : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId)
    (pw : keystore2_crypto.Password) (path : std.path.PathBuf) (p : std.path.Path)
    (blob : legacy_blob.Blob) (iv tag data salt : alloc.vec.Vec Std.U8) (n : Std.Usize)
    (key : keystore2_crypto.zvec.ZVec) (ks : Slice Std.U8) (e : keystore2_crypto.error.Error)
    (hmk : make_super_key_filename self user = ok path)
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hv : blob.value = .PwEncrypted iv tag data salt n) (hfl : flagSet blob 0 = true)
    (hder : keystore2_crypto.Password.derive_key_pbkdf2 pw (vecDeref salt) n =
      ok (.Ok key))
    (hk : zvecDerefFn key = ok ks)
    (hdec : keystore2_crypto.aes_gcm_decrypt (vecDeref data) (vecDeref iv)
      (vecDeref tag) ks = ok (.Err e)) :
    ∃ e', load_super_key self user pw = ok (.Err e') ∧ root e' = ErrRoot.crypto e := by
  sorry

/-- conditional: if the file holds a `PwEncrypted` blob with the bit `ENCRYPTED` clear (an
unencrypted super key, from b/141955555) and `ZVec::try_from` returns `z` for the data,
`load_super_key` returns `Ok (Some z)`. In the Rust source this path does not derive a key.
Hypotheses: the outcomes of the file read and of `try_from`; the `context` assumptions for an
`anyhow::Error` and for a `ZVec` error; and the message assumptions. -/
theorem load_super_key_unencrypted (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hz : ZVecErrCtxLaw root keystore2_crypto.zvec.ZVec) (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (pw : keystore2_crypto.Password) (path : std.path.PathBuf)
    (p : std.path.Path) (blob : legacy_blob.Blob) (iv tag data salt : alloc.vec.Vec Std.U8)
    (n : Std.Usize) (z : keystore2_crypto.zvec.ZVec)
    (hmk : make_super_key_filename self user = ok path)
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hv : blob.value = .PwEncrypted iv tag data salt n) (hfl : flagSet blob 0 = false)
    (ht : tryFromVec data =
      ok (.Ok z)) :
    load_super_key self user pw = ok (.Ok (some z)) := by
  sorry

/-- conditional: if the file holds a `PwEncrypted` blob with the bit `ENCRYPTED` clear and
`ZVec::try_from` returns an error `e`, `load_super_key` returns an error whose root cause is a
`ZVec` error (class `other`). Hypotheses: those of `load_super_key_unencrypted`, with the outcome
`Err e` of `try_from`. -/
theorem load_super_key_try_from_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hz : ZVecErrCtxLaw root keystore2_crypto.zvec.ZVec) (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (pw : keystore2_crypto.Password) (path : std.path.PathBuf)
    (p : std.path.Path) (blob : legacy_blob.Blob) (iv tag data salt : alloc.vec.Vec Std.U8)
    (n : Std.Usize) (e : keystore2_crypto.zvec.Error)
    (hmk : make_super_key_filename self user = ok path)
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hv : blob.value = .PwEncrypted iv tag data salt n) (hfl : flagSet blob 0 = false)
    (ht : tryFromVec data =
      ok (.Err e)) :
    ∃ e', load_super_key self user pw = ok (.Err e') ∧ root e' = ErrRoot.other := by
  sorry

/-- conditional: if the file holds any other blob value, `load_super_key` returns an error whose
root cause is `Rc VALUE_CORRUPTED` (class `ks`). Hypotheses: the outcomes of the file read and of
the constant `VALUE_CORRUPTED`; `blob.value` is not a `PwEncrypted` value; the `context`
assumptions for an `anyhow::Error` and for a `keystore2::error::Error`; and the message
assumptions. -/
theorem load_super_key_wrong_type (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hks : KsErrCtxLaw root (Option keystore2_crypto.zvec.ZVec))
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId)
    (pw : keystore2_crypto.Password) (path : std.path.PathBuf) (p : std.path.Path)
    (blob : legacy_blob.Blob) (rc : Std.I32)
    (hmk : make_super_key_filename self user = ok path)
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hv : ∀ iv tag data salt n, blob.value ≠ .PwEncrypted iv tag data salt n)
    (hrc : VALUE_CORRUPTED = ok rc) :
    ∃ e', load_super_key self user pw = ok (.Err e') ∧
      root e' = ErrRoot.ks (error.Error.Rc rc) := by
  sorry

end Keystore2Verify.LegacyBlob
