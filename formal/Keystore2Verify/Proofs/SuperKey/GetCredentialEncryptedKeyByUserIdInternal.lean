import Keystore2Verify.Specs.Defs.SuperKey

namespace Keystore2Verify.SuperKey
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

/-- conditional: if `user_keys` has an entry for `user` whose `credential_encrypted` is
`Some(k)`, the function returns `Some(k)`: a clone of the same `Arc`. Nothing else changes (the
Rust takes `&self`). Hypotheses: the assumptions about `HashMap::get` on `user_keys` (read through
`ents`), `Option::and_then` at the closure of this function, `Option::as_ref` and
`Option::cloned` at `Arc<SuperKey>`. -/
theorem SuperKeyManager_get_credential_encrypted_key_by_user_id_internal_some
    (ents : UserKeyEntries) (hget : UserKeysGetSpec ents) (hand : CredentialAndThenSpec)
    (hasref : OptionAsRefSpec SuperKeyArc) (hcl : OptionClonedArcSpec)
    (self : super_key.SuperKeyManager) (user : utils.AndroidUserId)
    (e : super_key.UserSuperKeys) (k : SuperKeyArc)
    (he : (user, e) ∈ ents self.data.user_keys) (hk : e.credential_encrypted = some k) :
    super_key.SuperKeyManager.get_credential_encrypted_key_by_user_id_internal self user =
      ok (some k) := by
  sorry

/-- conditional: if `user` is not a key of `user_keys`, the function returns `None`.
Hypotheses: the assumptions about `HashMap::get` on `user_keys` and about `Option::and_then` at
the closure of this function. -/
theorem SuperKeyManager_get_credential_encrypted_key_by_user_id_internal_no_user
    (ents : UserKeyEntries) (hget : UserKeysGetSpec ents) (hand : CredentialAndThenSpec)
    (self : super_key.SuperKeyManager) (user : utils.AndroidUserId)
    (h : ∀ e, (user, e) ∉ ents self.data.user_keys) :
    super_key.SuperKeyManager.get_credential_encrypted_key_by_user_id_internal self user =
      ok none := by
  sorry

/-- conditional: if `user_keys` has an entry for `user` whose `credential_encrypted` is `None`,
the function returns `None`. Hypotheses: the assumptions about `HashMap::get` on `user_keys`,
`Option::and_then` at the closure of this function, `Option::as_ref` and `Option::cloned` at
`Arc<SuperKey>`. -/
theorem SuperKeyManager_get_credential_encrypted_key_by_user_id_internal_none
    (ents : UserKeyEntries) (hget : UserKeysGetSpec ents) (hand : CredentialAndThenSpec)
    (hasref : OptionAsRefSpec SuperKeyArc) (hcl : OptionClonedArcSpec)
    (self : super_key.SuperKeyManager) (user : utils.AndroidUserId)
    (e : super_key.UserSuperKeys)
    (he : (user, e) ∈ ents self.data.user_keys) (hk : e.credential_encrypted = none) :
    super_key.SuperKeyManager.get_credential_encrypted_key_by_user_id_internal self user =
      ok none := by
  sorry

end Keystore2Verify.SuperKey
