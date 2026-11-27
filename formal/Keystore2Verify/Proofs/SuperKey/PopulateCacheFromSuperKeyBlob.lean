import Keystore2Verify.Specs.Defs.SuperKey

namespace Keystore2Verify.SuperKey
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

/-! The context texts of the Rust source are
`keystore2/src/super_key.rs:527: Failed to extract super key from key entry` and
`keystore2/src/super_key.rs:529: Failed to install CredentialEncrypted super key for user!`.
`extract_super_key_from_key_entry` and `install_credential_encrypted_key_for_user` are items of
keystore2 that the translation does not contain; the statements take their outcome as a
hypothesis. -/

/-- conditional: if `extract_super_key_from_key_entry(algorithm, entry, pw, None)` returns `Ok(k)`
and `install_credential_encrypted_key_for_user(user, k.clone())` returns `Ok(())` with the new
manager `self'`, the function returns `Ok(k)` and `self'`. Hypotheses: the outcomes of the two
calls, the assumptions about `Arc::clone`, `format`, `from_str_nonconst` and the assumptions
about `Result::context` at the two calls. -/
theorem SuperKeyManager_populate_cache_from_super_key_blob_ok (root : anyhow.Error → ErrRoot)
    (hc1 : AnyCtxLaw root SuperKeyArc) (hc2 : AnyCtxLaw root Unit)
    (harc : ArcCloneSpec) (hfmt : AllocFmtFormatSpec)
    (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (self self' : super_key.SuperKeyManager) (user : utils.AndroidUserId)
    (algorithm : super_key.SuperEncryptionAlgorithm) (entry : database.KeyEntry)
    (pw : keystore2_crypto.Password) (k : SuperKeyArc)
    (hext : super_key.SuperKeyManager.extract_super_key_from_key_entry algorithm entry pw none =
      ok (.Ok k))
    (hinst : super_key.SuperKeyManager.install_credential_encrypted_key_for_user self user k =
      ok (.Ok (), self')) :
    super_key.SuperKeyManager.populate_cache_from_super_key_blob self user algorithm entry pw =
      ok (.Ok k, self') := by
  sorry

/-- conditional: if `extract_super_key_from_key_entry` returns an error, the function returns an
error with the same root cause, and the manager `self` unchanged. In the Rust source this path
returns before `install_credential_encrypted_key_for_user` is called. Hypotheses: the outcome of
the extraction, the assumptions about `format` and `from_str_nonconst`, and the assumption about
`Result::context` at the first call. -/
theorem SuperKeyManager_populate_cache_from_super_key_blob_extract_error
    (root : anyhow.Error → ErrRoot) (hc1 : AnyCtxLaw root SuperKeyArc)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (self : super_key.SuperKeyManager) (user : utils.AndroidUserId)
    (algorithm : super_key.SuperEncryptionAlgorithm) (entry : database.KeyEntry)
    (pw : keystore2_crypto.Password) (e : anyhow.Error)
    (hext : super_key.SuperKeyManager.extract_super_key_from_key_entry algorithm entry pw none =
      ok (.Err e)) :
    ∃ e', super_key.SuperKeyManager.populate_cache_from_super_key_blob self user algorithm entry
        pw = ok (.Err e', self) ∧ root e' = root e := by
  sorry

/-- conditional: if the extraction returns `Ok(k)` and `install_credential_encrypted_key_for_user`
returns an error with the new manager `self'`, the function returns an error with the same root
cause, and `self'`, which can differ from `self` although the call failed. Hypotheses: the
outcomes of the two calls, the assumptions about `Arc::clone`, `format`, `from_str_nonconst` and
the assumptions about `Result::context` at the two calls. -/
theorem SuperKeyManager_populate_cache_from_super_key_blob_install_error
    (root : anyhow.Error → ErrRoot) (hc1 : AnyCtxLaw root SuperKeyArc)
    (hc2 : AnyCtxLaw root Unit) (harc : ArcCloneSpec) (hfmt : AllocFmtFormatSpec)
    (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (self self' : super_key.SuperKeyManager) (user : utils.AndroidUserId)
    (algorithm : super_key.SuperEncryptionAlgorithm) (entry : database.KeyEntry)
    (pw : keystore2_crypto.Password) (k : SuperKeyArc) (e : anyhow.Error)
    (hext : super_key.SuperKeyManager.extract_super_key_from_key_entry algorithm entry pw none =
      ok (.Ok k))
    (hinst : super_key.SuperKeyManager.install_credential_encrypted_key_for_user self user k =
      ok (.Err e, self')) :
    ∃ e', super_key.SuperKeyManager.populate_cache_from_super_key_blob self user algorithm entry
        pw = ok (.Err e', self') ∧ root e' = root e := by
  sorry

end Keystore2Verify.SuperKey
