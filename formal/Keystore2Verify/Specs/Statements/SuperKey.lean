import Keystore2Verify.Proofs.SuperKey.WipeKeyOption
import Keystore2Verify.Proofs.SuperKey.SuperEncryptionAlgorithm
import Keystore2Verify.Proofs.SuperKey.SuperEncryptionType
import Keystore2Verify.Proofs.SuperKey.SuperKeyIdentifier
import Keystore2Verify.Proofs.SuperKey.FromMetadata
import Keystore2Verify.Proofs.SuperKey.AddToMetadata
import Keystore2Verify.Proofs.SuperKey.UserSuperKeys
import Keystore2Verify.Proofs.SuperKey.SkmState
import Keystore2Verify.Proofs.SuperKey.SuperKeyManagerDefault
import Keystore2Verify.Proofs.SuperKey.LevelAccessible
import Keystore2Verify.Proofs.SuperKey.GetCredentialEncryptedKeyByUserIdInternal
import Keystore2Verify.Proofs.SuperKey.PopulateCacheFromSuperKeyBlob
import Keystore2Verify.Proofs.SuperKey.EncryptWithPassword
import Keystore2Verify.Proofs.SuperKey.GetOrCreateSuperKey
import Keystore2Verify.Proofs.SuperKey.LogStatusOfUnlockedDeviceRequiredKeys

namespace Keystore2Verify.SuperKey

section WipeKeyOption
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

open super_key.WipeKeyOption.Insts renaming CoreCmpPartialEqWipeKeyOption → wipeEq

recall WipeKeyOption_eq (a b : super_key.WipeKeyOption) :
    ∃ r, wipeEq.eq a b = ok r ∧ (r = true ↔ a = b)

end WipeKeyOption

section SuperEncryptionAlgorithm
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

open super_key.SuperEncryptionAlgorithm.Insts renaming
  CoreCloneClone → algorithmClone, CoreCmpPartialEqSuperEncryptionAlgorithm → algorithmEq

recall SuperEncryptionAlgorithm_clone (a : super_key.SuperEncryptionAlgorithm) :
    algorithmClone.clone a = ok a

recall SuperEncryptionAlgorithm_eq (a b : super_key.SuperEncryptionAlgorithm) :
    ∃ r, algorithmEq.eq a b = ok r ∧ (r = true ↔ a = b)

end SuperEncryptionAlgorithm

section SuperEncryptionType
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

open super_key.SuperEncryptionType.Insts renaming CoreCloneClone → typeClone

recall SuperEncryptionType_clone (t : super_key.SuperEncryptionType) :
    typeClone.clone t = ok t

end SuperEncryptionType

section SuperKeyIdentifier
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

open super_key.SuperKeyIdentifier.Insts renaming CoreCloneClone → identifierClone

recall SuperKeyIdentifier_clone (i : super_key.SuperKeyIdentifier) :
    identifierClone.clone i = ok i

end SuperKeyIdentifier

section FromMetadata
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

recall SuperKeyIdentifier_from_metadata_key_id (ents : MetaEntries) (hget : MetaGetSpec ents)
    (metadata : database.BlobMetaData) (k : Std.I64)
    (h : (0#i64, database.BlobMetaEntry.EncryptedBy (database.EncryptedBy.KeyId k)) ∈
      ents metadata.data) :
    super_key.SuperKeyIdentifier.from_metadata metadata =
      ok (some (super_key.SuperKeyIdentifier.DatabaseId k))

recall SuperKeyIdentifier_from_metadata_boot_level (ents : MetaEntries)
    (hget : MetaGetSpec ents) (metadata : database.BlobMetaData) (n : Std.I32)
    (hno : ∀ k, (0#i64, database.BlobMetaEntry.EncryptedBy (database.EncryptedBy.KeyId k)) ∉
      ents metadata.data)
    (h : (6#i64, database.BlobMetaEntry.MaxBootLevel n) ∈ ents metadata.data) :
    super_key.SuperKeyIdentifier.from_metadata metadata =
      ok (some (super_key.SuperKeyIdentifier.BootLevel (IScalar.hcast .Usize n)))

recall SuperKeyIdentifier_from_metadata_none (ents : MetaEntries) (hget : MetaGetSpec ents)
    (metadata : database.BlobMetaData)
    (hno : ∀ k, (0#i64, database.BlobMetaEntry.EncryptedBy (database.EncryptedBy.KeyId k)) ∉
      ents metadata.data)
    (hnb : ∀ n, (6#i64, database.BlobMetaEntry.MaxBootLevel n) ∉ ents metadata.data) :
    super_key.SuperKeyIdentifier.from_metadata metadata = ok none

end FromMetadata

section AddToMetadata
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

recall SuperKeyIdentifier_add_to_metadata_database_id (ents : MetaEntries)
    (hins : MetaInsertSpec ents) (id : Std.I64) (metadata : database.BlobMetaData) :
    ∃ m, super_key.SuperKeyIdentifier.add_to_metadata
        (super_key.SuperKeyIdentifier.DatabaseId id) metadata = ok m ∧
      MetaEntriesAre ents metadata m
        [(0#i64, database.BlobMetaEntry.EncryptedBy (database.EncryptedBy.KeyId id))]

recall SuperKeyIdentifier_add_to_metadata_boot_level (ents : MetaEntries)
    (hins : MetaInsertSpec ents) (level : boot_level_keys.BootLevel)
    (metadata : database.BlobMetaData) :
    ∃ m, super_key.SuperKeyIdentifier.add_to_metadata
        (super_key.SuperKeyIdentifier.BootLevel level) metadata = ok m ∧
      MetaEntriesAre ents metadata m
        [(6#i64, database.BlobMetaEntry.MaxBootLevel (UScalar.hcast .I32 level))]

end AddToMetadata

section UserSuperKeys
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals
open super_key.UserSuperKeys.Insts

recall UserSuperKeys_default (harc : OptionDefaultSpec SuperKeyArc)
    (hbio : OptionDefaultSpec super_key.BiometricUnlock) :
    CoreDefaultDefault.default =
      ok { credential_encrypted := none, unlocked_device_required_symmetric := none,
           unlocked_device_required_private := none, biometric_unlock := none }

end UserSuperKeys

section SkmState
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals
open std.sync.poison.mutex
open super_key.SkmState.Insts

recall SkmState_default (entsU : UserKeyEntries)
    (entsK : Entries Std.I64 (alloc.sync.Weak super_key.SuperKey alloc.alloc.Global))
    (hu : UserKeysEmptySpec entsU) (hk : KeyIndexEmptySpec entsK)
    (hm : OptionDefaultSpec (Mutex boot_level_keys.BootLevelKeyCache)) :
    ∃ s, CoreDefaultDefault.default = ok s ∧
      entsU s.user_keys = [] ∧ entsK s.key_index = [] ∧ s.boot_level_key_cache = none

end SkmState

section SuperKeyManagerDefault
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals
open std.sync.poison.mutex
open super_key.SuperKeyManager.Insts

recall SuperKeyManager_default (entsU : UserKeyEntries)
    (entsK : Entries Std.I64 (alloc.sync.Weak super_key.SuperKey alloc.alloc.Global))
    (hu : UserKeysEmptySpec entsU) (hk : KeyIndexEmptySpec entsK)
    (hm : OptionDefaultSpec (Mutex boot_level_keys.BootLevelKeyCache)) :
    ∃ m, CoreDefaultDefault.default = ok m ∧
      entsU m.data.user_keys = [] ∧ entsK m.data.key_index = [] ∧
      m.data.boot_level_key_cache = none

end SuperKeyManagerDefault

section LevelAccessible
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals
open std.sync.poison
open std.sync.poison.mutex
open std.sync.poison.mutex.MutexGuard.Insts

recall SuperKeyManager_level_accessible_no_cache
    (hasref : OptionAsRefSpec (Mutex boot_level_keys.BootLevelKeyCache))
    (self : super_key.SuperKeyManager) (L : boot_level_keys.BootLevel)
    (h : self.data.boot_level_key_cache = none) :
    super_key.SuperKeyManager.level_accessible self L = ok false

recall SuperKeyManager_level_accessible_poisoned
    (hasref : OptionAsRefSpec (Mutex boot_level_keys.BootLevelKeyCache))
    (self : super_key.SuperKeyManager) (L : boot_level_keys.BootLevel)
    (m : Mutex boot_level_keys.BootLevelKeyCache)
    (p : PoisonError
      (MutexGuard boot_level_keys.BootLevelKeyCache))
    (hc : self.data.boot_level_key_cache = some m)
    (hlock : Mutex.lock m = ok (.Err p)) :
    super_key.SuperKeyManager.level_accessible self L = fail Error.panic

recall SuperKeyManager_level_accessible_iff
    (hasref : OptionAsRefSpec (Mutex boot_level_keys.BootLevelKeyCache))
    (view : ZVecQueue → List keystore2_crypto.zvec.ZVec) (hempty : ZVecQueueIsEmptyLaw view)
    (self : super_key.SuperKeyManager) (L : boot_level_keys.BootLevel)
    (m : Mutex boot_level_keys.BootLevelKeyCache)
    (g : MutexGuard boot_level_keys.BootLevelKeyCache)
    (c : boot_level_keys.BootLevelKeyCache)
    (hc : self.data.boot_level_key_cache = some m)
    (hlock : Mutex.lock m = ok (.Ok g))
    (hderef : CoreOpsDerefDeref.deref g = ok c) :
    ∃ b, super_key.SuperKeyManager.level_accessible self L = ok b ∧
      (b = true ↔ c.current.val ≤ L.val ∧ view c.cache ≠ [])

end LevelAccessible

section GetCredentialEncryptedKeyByUserIdInternal
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

recall SuperKeyManager_get_credential_encrypted_key_by_user_id_internal_some
    (ents : UserKeyEntries) (hget : UserKeysGetSpec ents) (hand : CredentialAndThenSpec)
    (hasref : OptionAsRefSpec SuperKeyArc) (hcl : OptionClonedArcSpec)
    (self : super_key.SuperKeyManager) (user : utils.AndroidUserId)
    (e : super_key.UserSuperKeys) (k : SuperKeyArc)
    (he : (user, e) ∈ ents self.data.user_keys) (hk : e.credential_encrypted = some k) :
    super_key.SuperKeyManager.get_credential_encrypted_key_by_user_id_internal self user =
      ok (some k)

recall SuperKeyManager_get_credential_encrypted_key_by_user_id_internal_no_user
    (ents : UserKeyEntries) (hget : UserKeysGetSpec ents) (hand : CredentialAndThenSpec)
    (self : super_key.SuperKeyManager) (user : utils.AndroidUserId)
    (h : ∀ e, (user, e) ∉ ents self.data.user_keys) :
    super_key.SuperKeyManager.get_credential_encrypted_key_by_user_id_internal self user =
      ok none

recall SuperKeyManager_get_credential_encrypted_key_by_user_id_internal_none
    (ents : UserKeyEntries) (hget : UserKeysGetSpec ents) (hand : CredentialAndThenSpec)
    (hasref : OptionAsRefSpec SuperKeyArc) (hcl : OptionClonedArcSpec)
    (self : super_key.SuperKeyManager) (user : utils.AndroidUserId)
    (e : super_key.UserSuperKeys)
    (he : (user, e) ∈ ents self.data.user_keys) (hk : e.credential_encrypted = none) :
    super_key.SuperKeyManager.get_credential_encrypted_key_by_user_id_internal self user =
      ok none

end GetCredentialEncryptedKeyByUserIdInternal

section PopulateCacheFromSuperKeyBlob
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

recall SuperKeyManager_populate_cache_from_super_key_blob_ok (root : anyhow.Error → ErrRoot)
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
      ok (.Ok k, self')

recall SuperKeyManager_populate_cache_from_super_key_blob_extract_error
    (root : anyhow.Error → ErrRoot) (hc1 : AnyCtxLaw root SuperKeyArc)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (self : super_key.SuperKeyManager) (user : utils.AndroidUserId)
    (algorithm : super_key.SuperEncryptionAlgorithm) (entry : database.KeyEntry)
    (pw : keystore2_crypto.Password) (e : anyhow.Error)
    (hext : super_key.SuperKeyManager.extract_super_key_from_key_entry algorithm entry pw none =
      ok (.Err e)) :
    ∃ e', super_key.SuperKeyManager.populate_cache_from_super_key_blob self user algorithm entry
        pw = ok (.Err e', self) ∧ root e' = root e

recall SuperKeyManager_populate_cache_from_super_key_blob_install_error
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
        pw = ok (.Err e', self') ∧ root e' = root e

end PopulateCacheFromSuperKeyBlob

section EncryptWithPassword
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals
open alloc.vec
open keystore2_crypto.zvec.ZVec.Insts

recall SuperKeyManager_encrypt_with_password_ok (root : anyhow.Error → ErrRoot)
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
         (3#i64, database.BlobMetaEntry.AeadTag tag)]

recall SuperKeyManager_encrypt_with_password_salt_error (root : anyhow.Error → ErrRoot)
    (hc1 : CryptoStrCtxSpec root (alloc.vec.Vec Std.U8))
    (sk : Slice Std.U8) (pw : keystore2_crypto.Password)
    (e : keystore2_crypto.error.Error)
    (hsalt : keystore2_crypto.generate_salt = ok (.Err e)) :
    ∃ e', super_key.SuperKeyManager.encrypt_with_password sk pw = ok (.Err e') ∧
      root e' = ErrRoot.crypto e

recall SuperKeyManager_encrypt_with_password_derive_error (root : anyhow.Error → ErrRoot)
    (hc1 : CryptoStrCtxSpec root (alloc.vec.Vec Std.U8))
    (hc2 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (sk : Slice Std.U8) (pw : keystore2_crypto.Password) (salt : alloc.vec.Vec Std.U8)
    (e : keystore2_crypto.error.Error)
    (hsalt : keystore2_crypto.generate_salt = ok (.Ok salt))
    (hdk : keystore2_crypto.Password.derive_key_hkdf pw (Vec.deref salt)
      keystore2_crypto.AES_256_KEY_LENGTH = ok (.Err e)) :
    ∃ e', super_key.SuperKeyManager.encrypt_with_password sk pw = ok (.Err e') ∧
      root e' = ErrRoot.crypto e

recall SuperKeyManager_encrypt_with_password_aes_error (root : anyhow.Error → ErrRoot)
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
      root e' = ErrRoot.crypto e

end EncryptWithPassword

section GetOrCreateSuperKey
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

recall SuperKeyManager_get_or_create_super_key_found
    (self : super_key.SuperKeyManager) (db db1 : database.KeystoreDB)
    (user : utils.AndroidUserId) (key_type : super_key.SuperKeyType)
    (password : keystore2_crypto.Password) (reencrypt_with : Option SuperKeyArc)
    (g : database.KeyIdGuard) (ke : database.KeyEntry) (k : SuperKeyArc)
    (hload : database.KeystoreDB.load_super_key db key_type user = ok (.Ok (some (g, ke)), db1))
    (hext : super_key.SuperKeyManager.extract_super_key_from_key_entry key_type.algorithm ke
      password reencrypt_with = ok (.Ok k)) :
    super_key.SuperKeyManager.get_or_create_super_key self db user key_type password
      reencrypt_with = ok (.Ok k, self, db1)

recall SuperKeyManager_get_or_create_super_key_create
    (self self2 : super_key.SuperKeyManager) (db db1 db2 : database.KeystoreDB)
    (user : utils.AndroidUserId) (key_type : super_key.SuperKeyType)
    (password : keystore2_crypto.Password) (reencrypt_with : Option SuperKeyArc)
    (k : SuperKeyArc)
    (hload : database.KeystoreDB.load_super_key db key_type user = ok (.Ok none, db1))
    (hcreate : super_key.SuperKeyManager.create_super_key self db1 user key_type password
      reencrypt_with = ok (.Ok k, self2, db2)) :
    super_key.SuperKeyManager.get_or_create_super_key self db user key_type password
      reencrypt_with = ok (.Ok k, self2, db2)

recall SuperKeyManager_get_or_create_super_key_create_error (root : anyhow.Error → ErrRoot)
    (self self2 : super_key.SuperKeyManager) (db db1 db2 : database.KeystoreDB)
    (user : utils.AndroidUserId) (key_type : super_key.SuperKeyType)
    (password : keystore2_crypto.Password) (reencrypt_with : Option SuperKeyArc)
    (e : anyhow.Error)
    (hload : database.KeystoreDB.load_super_key db key_type user = ok (.Ok none, db1))
    (hcreate : super_key.SuperKeyManager.create_super_key self db1 user key_type password
      reencrypt_with = ok (.Err e, self2, db2)) :
    ∃ e', super_key.SuperKeyManager.get_or_create_super_key self db user key_type password
      reencrypt_with = ok (.Err e', self2, db2) ∧ root e' = root e

recall SuperKeyManager_get_or_create_super_key_load_error (root : anyhow.Error → ErrRoot)
    (self : super_key.SuperKeyManager) (db db1 : database.KeystoreDB)
    (user : utils.AndroidUserId) (key_type : super_key.SuperKeyType)
    (password : keystore2_crypto.Password) (reencrypt_with : Option SuperKeyArc)
    (e : anyhow.Error)
    (hload : database.KeystoreDB.load_super_key db key_type user = ok (.Err e, db1)) :
    ∃ e', super_key.SuperKeyManager.get_or_create_super_key self db user key_type password
      reencrypt_with = ok (.Err e', self, db1) ∧ root e' = root e

recall SuperKeyManager_get_or_create_super_key_extract_error (root : anyhow.Error → ErrRoot)
    (self : super_key.SuperKeyManager) (db db1 : database.KeystoreDB)
    (user : utils.AndroidUserId) (key_type : super_key.SuperKeyType)
    (password : keystore2_crypto.Password) (reencrypt_with : Option SuperKeyArc)
    (g : database.KeyIdGuard) (ke : database.KeyEntry) (e : anyhow.Error)
    (hload : database.KeystoreDB.load_super_key db key_type user = ok (.Ok (some (g, ke)), db1))
    (hext : super_key.SuperKeyManager.extract_super_key_from_key_entry key_type.algorithm ke
      password reencrypt_with = ok (.Err e)) :
    ∃ e', super_key.SuperKeyManager.get_or_create_super_key self db user key_type password
      reencrypt_with = ok (.Err e', self, db1) ∧ root e' = root e

end GetOrCreateSuperKey

section LogStatusOfUnlockedDeviceRequiredKeys
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

recall SuperKeyManager_log_status_of_unlocked_device_required_keys
    (hcmp : LogLevelPartialCmpSpec) (hmax : LogMaxLevelSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) (user : utils.AndroidUserId)
    (entry : super_key.UserSuperKeys) :
    super_key.SuperKeyManager.log_status_of_unlocked_device_required_keys user entry =
      ok ()

end LogStatusOfUnlockedDeviceRequiredKeys

end Keystore2Verify.SuperKey
