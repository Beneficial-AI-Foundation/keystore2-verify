import Keystore2Verify.Specs.Defs.SuperKey

namespace Keystore2Verify.SuperKey
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

/-! `load_super_key`, `extract_super_key_from_key_entry` and `create_super_key` are
keystore2 items or database calls whose outcome the statements take as a hypothesis. The caller
must hold the lock on the manager (a comment in the Rust source, not code). -/

/-- conditional: if `db.load_super_key(key_type, user)` returns a key (`Some((g, ke))`, new
database `db1`) and `extract_super_key_from_key_entry` returns `Ok(k)`, the function returns
`Ok(k)`, the manager `self` unchanged and `db1`. Hypotheses: the outcomes of the two calls. -/
theorem SuperKeyManager_get_or_create_super_key_found
    (self : super_key.SuperKeyManager) (db db1 : database.KeystoreDB)
    (user : utils.AndroidUserId) (key_type : super_key.SuperKeyType)
    (password : keystore2_crypto.Password) (reencrypt_with : Option SuperKeyArc)
    (g : database.KeyIdGuard) (ke : database.KeyEntry) (k : SuperKeyArc)
    (hload : database.KeystoreDB.load_super_key db key_type user = ok (.Ok (some (g, ke)), db1))
    (hext : super_key.SuperKeyManager.extract_super_key_from_key_entry key_type.algorithm ke
      password reencrypt_with = ok (.Ok k)) :
    super_key.SuperKeyManager.get_or_create_super_key self db user key_type password
      reencrypt_with = ok (.Ok k, self, db1) := by
  sorry

/-- conditional: if `db.load_super_key(key_type, user)` returns `None` (new database `db1`) and
`create_super_key(self, db1, user, key_type, password, reencrypt_with)` returns `Ok(k)` with the
manager `self2` and the database `db2`, the function returns `Ok(k)`, `self2` and `db2`.
Hypotheses: the outcomes of the two calls. -/
theorem SuperKeyManager_get_or_create_super_key_create
    (self self2 : super_key.SuperKeyManager) (db db1 db2 : database.KeystoreDB)
    (user : utils.AndroidUserId) (key_type : super_key.SuperKeyType)
    (password : keystore2_crypto.Password) (reencrypt_with : Option SuperKeyArc)
    (k : SuperKeyArc)
    (hload : database.KeystoreDB.load_super_key db key_type user = ok (.Ok none, db1))
    (hcreate : super_key.SuperKeyManager.create_super_key self db1 user key_type password
      reencrypt_with = ok (.Ok k, self2, db2)) :
    super_key.SuperKeyManager.get_or_create_super_key self db user key_type password
      reencrypt_with = ok (.Ok k, self2, db2) := by
  sorry

/-- conditional: if `db.load_super_key(key_type, user)` returns `None` (new database `db1`) and
`create_super_key(self, db1, user, key_type, password, reencrypt_with)` returns an error `e` with
the manager `self2` and the database `db2`, the function returns an error with the same root
cause, `self2` and `db2`. Hypotheses: the outcomes of the two calls. -/
theorem SuperKeyManager_get_or_create_super_key_create_error (root : anyhow.Error → ErrRoot)
    (self self2 : super_key.SuperKeyManager) (db db1 db2 : database.KeystoreDB)
    (user : utils.AndroidUserId) (key_type : super_key.SuperKeyType)
    (password : keystore2_crypto.Password) (reencrypt_with : Option SuperKeyArc)
    (e : anyhow.Error)
    (hload : database.KeystoreDB.load_super_key db key_type user = ok (.Ok none, db1))
    (hcreate : super_key.SuperKeyManager.create_super_key self db1 user key_type password
      reencrypt_with = ok (.Err e, self2, db2)) :
    ∃ e', super_key.SuperKeyManager.get_or_create_super_key self db user key_type password
      reencrypt_with = ok (.Err e', self2, db2) ∧ root e' = root e := by
  sorry

/-- conditional: if `db.load_super_key(key_type, user)` returns an error (new database `db1`),
the function returns an error with the same root cause (the `?` adds no context), the manager
`self` unchanged and `db1`. In the Rust source this path returns before the extraction.
Hypothesis: the outcome of the load. -/
theorem SuperKeyManager_get_or_create_super_key_load_error (root : anyhow.Error → ErrRoot)
    (self : super_key.SuperKeyManager) (db db1 : database.KeystoreDB)
    (user : utils.AndroidUserId) (key_type : super_key.SuperKeyType)
    (password : keystore2_crypto.Password) (reencrypt_with : Option SuperKeyArc)
    (e : anyhow.Error)
    (hload : database.KeystoreDB.load_super_key db key_type user = ok (.Err e, db1)) :
    ∃ e', super_key.SuperKeyManager.get_or_create_super_key self db user key_type password
      reencrypt_with = ok (.Err e', self, db1) ∧ root e' = root e := by
  sorry

/-- conditional: if the load returns a key and `extract_super_key_from_key_entry` returns an error,
the function returns an error with the same root cause (no context), the manager `self` unchanged
and `db1`. Hypotheses: the outcomes of the two calls. -/
theorem SuperKeyManager_get_or_create_super_key_extract_error (root : anyhow.Error → ErrRoot)
    (self : super_key.SuperKeyManager) (db db1 : database.KeystoreDB)
    (user : utils.AndroidUserId) (key_type : super_key.SuperKeyType)
    (password : keystore2_crypto.Password) (reencrypt_with : Option SuperKeyArc)
    (g : database.KeyIdGuard) (ke : database.KeyEntry) (e : anyhow.Error)
    (hload : database.KeystoreDB.load_super_key db key_type user = ok (.Ok (some (g, ke)), db1))
    (hext : super_key.SuperKeyManager.extract_super_key_from_key_entry key_type.algorithm ke
      password reencrypt_with = ok (.Err e)) :
    ∃ e', super_key.SuperKeyManager.get_or_create_super_key self db user key_type password
      reencrypt_with = ok (.Err e', self, db1) ∧ root e' = root e := by
  sorry

end Keystore2Verify.SuperKey
