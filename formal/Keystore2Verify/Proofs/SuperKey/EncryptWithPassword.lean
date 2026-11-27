import Keystore2Verify.Specs.Defs.SuperKey

namespace Keystore2Verify.SuperKey
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals
open alloc.vec
open keystore2_crypto.zvec.ZVec.Insts

/-! The metadata of the result is `BlobMetaData::new()` (an item of keystore2 that the
translation does not contain; `m0` is its outcome) with four entries added: `EncryptedBy`
(tag 0), `Salt` (tag 1), `Iv` (tag 2) and `AeadTag` (tag 3). The salt and the IV are random in
the Rust, so the statements quantify over them. The context texts of the Rust source are
`In encrypt_with_password: Failed to generate salt.`,
`keystore2/src/super_key.rs:596: Failed to derive key from password.` and
`keystore2/src/super_key.rs:601: Failed to encrypt new super key.`. The root cause of each error is
a `keystore2_crypto` error. The empty `super_key` slice is not checked here. -/

/-- conditional: if `generate_salt` returns the salt, `derive_key_hkdf` returns the key `dk`, and
`aes_gcm_encrypt` returns `(ct, iv, tag)`, the function returns `Ok((ct, m))`, where `m` is
`m0` with the four entries added (an entry of `m0` with one of these tags is replaced). The
view of `dk` as a slice is `s`. Hypotheses: the outcomes of the calls, the assumptions about
`HashMap::insert` on the metadata map (read through `ents`), `format`, `from_str_nonconst` and
`Result::context` at the three calls. -/
theorem SuperKeyManager_encrypt_with_password_ok (root : anyhow.Error → ErrRoot)
    (hc1 : CryptoStrCtxSpec root (alloc.vec.Vec Std.U8))
    (hc2 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc3 : CryptoCtxLaw root ((alloc.vec.Vec Std.U8) × (alloc.vec.Vec Std.U8) ×
      (alloc.vec.Vec Std.U8)))
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (ents : MetaEntries) (hins : MetaInsertSpec ents)
    (sk : Slice Std.U8) (pw : keystore2_crypto.Password)
    (salt ct iv tag : alloc.vec.Vec Std.U8) (dk : keystore2_crypto.zvec.ZVec) (s : Slice Std.U8)
    (m0 : database.BlobMetaData)
    (hsalt : keystore2_crypto.generate_salt = ok (.Ok salt))
    (hdk : keystore2_crypto.Password.derive_key_hkdf pw (Vec.deref salt)
      keystore2_crypto.AES_256_KEY_LENGTH = ok (.Ok dk))
    (hnew : database.BlobMetaData.new = ok m0)
    (hview : CoreOpsDerefDerefSliceU8.deref dk = ok s)
    (haes : keystore2_crypto.aes_gcm_encrypt sk s = ok (.Ok (ct, iv, tag))) :
    ∃ m, super_key.SuperKeyManager.encrypt_with_password sk pw = ok (.Ok (ct, m)) ∧
      MetaEntriesAre ents m0 m
        [(0#i64, database.BlobMetaEntry.EncryptedBy database.EncryptedBy.Password),
         (1#i64, database.BlobMetaEntry.Salt salt), (2#i64, database.BlobMetaEntry.Iv iv),
         (3#i64, database.BlobMetaEntry.AeadTag tag)] := by
  sorry

/-- conditional: if `generate_salt` returns a `keystore2_crypto` error `e`, the function returns
an error whose root cause is `e`. In the Rust source this path returns before the key is derived.
Hypotheses: the outcome of `generate_salt` and the assumption about `Result::context` at the
first call. -/
theorem SuperKeyManager_encrypt_with_password_salt_error (root : anyhow.Error → ErrRoot)
    (hc1 : CryptoStrCtxSpec root (alloc.vec.Vec Std.U8))
    (sk : Slice Std.U8) (pw : keystore2_crypto.Password)
    (e : keystore2_crypto.error.Error)
    (hsalt : keystore2_crypto.generate_salt = ok (.Err e)) :
    ∃ e', super_key.SuperKeyManager.encrypt_with_password sk pw = ok (.Err e') ∧
      root e' = ErrRoot.crypto e := by
  sorry

/-- conditional: if `generate_salt` returns the salt and `derive_key_hkdf` returns a
`keystore2_crypto` error `e`, the function returns an error whose root cause is `e`. In the Rust
source this path returns before the metadata is built. Hypotheses: the outcomes of the two calls,
the assumptions about `format`, `from_str_nonconst` and `Result::context` at the first two
calls. -/
theorem SuperKeyManager_encrypt_with_password_derive_error (root : anyhow.Error → ErrRoot)
    (hc1 : CryptoStrCtxSpec root (alloc.vec.Vec Std.U8))
    (hc2 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (sk : Slice Std.U8) (pw : keystore2_crypto.Password) (salt : alloc.vec.Vec Std.U8)
    (e : keystore2_crypto.error.Error)
    (hsalt : keystore2_crypto.generate_salt = ok (.Ok salt))
    (hdk : keystore2_crypto.Password.derive_key_hkdf pw (Vec.deref salt)
      keystore2_crypto.AES_256_KEY_LENGTH = ok (.Err e)) :
    ∃ e', super_key.SuperKeyManager.encrypt_with_password sk pw = ok (.Err e') ∧
      root e' = ErrRoot.crypto e := by
  sorry

/-- conditional: if the salt and the key `dk` are made and `aes_gcm_encrypt` returns a
`keystore2_crypto` error `e`, the function returns an error whose root cause is `e`. Hypotheses:
the outcomes of the calls (including `BlobMetaData::new` and the view of `dk`), the assumptions
about `HashMap::insert` on the metadata map, `format`, `from_str_nonconst` and
`Result::context` at the three calls. -/
theorem SuperKeyManager_encrypt_with_password_aes_error (root : anyhow.Error → ErrRoot)
    (hc1 : CryptoStrCtxSpec root (alloc.vec.Vec Std.U8))
    (hc2 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc3 : CryptoCtxLaw root ((alloc.vec.Vec Std.U8) × (alloc.vec.Vec Std.U8) ×
      (alloc.vec.Vec Std.U8)))
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (ents : MetaEntries) (hins : MetaInsertSpec ents)
    (sk : Slice Std.U8) (pw : keystore2_crypto.Password) (salt : alloc.vec.Vec Std.U8)
    (dk : keystore2_crypto.zvec.ZVec) (s : Slice Std.U8) (m0 : database.BlobMetaData)
    (e : keystore2_crypto.error.Error)
    (hsalt : keystore2_crypto.generate_salt = ok (.Ok salt))
    (hdk : keystore2_crypto.Password.derive_key_hkdf pw (Vec.deref salt)
      keystore2_crypto.AES_256_KEY_LENGTH = ok (.Ok dk))
    (hnew : database.BlobMetaData.new = ok m0)
    (hview : CoreOpsDerefDerefSliceU8.deref dk = ok s)
    (haes : keystore2_crypto.aes_gcm_encrypt sk s = ok (.Err e)) :
    ∃ e', super_key.SuperKeyManager.encrypt_with_password sk pw = ok (.Err e') ∧
      root e' = ErrRoot.crypto e := by
  sorry

end Keystore2Verify.SuperKey
