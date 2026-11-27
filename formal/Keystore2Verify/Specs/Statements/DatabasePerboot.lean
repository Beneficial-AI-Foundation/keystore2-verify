import Keystore2Verify.Proofs.DatabasePerboot.AuthTokenId
import Keystore2Verify.Proofs.DatabasePerboot.AuthTokenEntryWrap
import Keystore2Verify.Proofs.DatabasePerboot.PerbootDB

namespace Keystore2Verify.DatabasePerboot

section AuthTokenId
open Aeneas Aeneas.Std Result keystore2
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open database.perboot
open AuthTokenId.Insts
open CoreCmpPartialEqAuthTokenId renaming eq → idEq
open CoreCmpOrd renaming cmp → idCmp
open CoreCmpPartialOrdAuthTokenId renaming partial_cmp → idPartialCmp
open HardwareAuthenticatorType.HardwareAuthenticatorType.Insts
open CoreCmpPartialEqHardwareAuthenticatorType renaming eq → hatyEq
open HardwareAuthenticatorType.HardwareAuthenticatorType.Insts.CoreCmpOrd renaming cmp → hatyCmp

recall auth_token_id_eq_user_id_differs (a b : AuthTokenId) (h : a.user_id ≠ b.user_id) :
    idEq a b = ok false

recall auth_token_id_eq_auth_id_differs (a b : AuthTokenId) (h1 : a.user_id = b.user_id)
    (h2 : a.auth_id ≠ b.auth_id) :
    idEq a b = ok false

recall auth_token_id_eq_same_ids (a b : AuthTokenId) (h1 : a.user_id = b.user_id)
    (h2 : a.auth_id = b.auth_id) :
    idEq a b
      = hatyEq a.authenticator_type b.authenticator_type

recall auth_token_id_eq (hEq : HardwareAuthenticatorTypeEqSpec) (a b : AuthTokenId) :
    ∃ r, idEq a b = ok r ∧
      (r = true ↔ a = b)

recall auth_token_id_cmp_user_id_differs (a b : AuthTokenId) (h : a.user_id ≠ b.user_id) :
    idCmp a b = ok (compare (idNum a.user_id) (idNum b.user_id))

recall auth_token_id_cmp_auth_id_differs (a b : AuthTokenId) (h1 : a.user_id = b.user_id)
    (h2 : a.auth_id ≠ b.auth_id) :
    idCmp a b = ok (compare (idNum a.auth_id) (idNum b.auth_id))

recall auth_token_id_cmp_same_ids (a b : AuthTokenId) (h1 : a.user_id = b.user_id)
    (h2 : a.auth_id = b.auth_id) :
    idCmp a b = hatyCmp a.authenticator_type b.authenticator_type

recall auth_token_id_partial_cmp_ok (a b : AuthTokenId) (o : Ordering)
    (h : idCmp a b = ok o) :
    idPartialCmp a b = ok (some o)

recall auth_token_id_partial_cmp_fail (a b : AuthTokenId) (e : Error)
    (h : idCmp a b = fail e) :
    idPartialCmp a b = fail e

recall auth_token_id_from_auth_token (tok : HardwareAuthToken.HardwareAuthToken) :
    AuthTokenId.from_auth_token tok = ok
      { user_id := tok.userId, auth_id := tok.authenticatorId,
        authenticator_type := tok.authenticatorType }

end AuthTokenId

section AuthTokenEntryWrap
open Aeneas Aeneas.Std Result keystore2
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open database.perboot
open AuthTokenEntryWrap.Insts
open CoreCloneClone renaming clone → wrapClone
open CoreHashHash renaming hash → wrapHash
open CoreCmpPartialEqAuthTokenEntryWrap renaming eq → wrapEq
open AuthTokenId.Insts.CoreHashHash renaming hash → idHash
open HardwareAuthToken.HardwareAuthToken.Insts.CoreCloneClone renaming clone → hatClone
open HardwareAuthenticatorType.HardwareAuthenticatorType.Insts
open CoreCmpPartialEqHardwareAuthenticatorType renaming eq → hatyEq

recall auth_token_entry_wrap_clone_ok (self : AuthTokenEntryWrap)
    (hat : HardwareAuthToken.HardwareAuthToken)
    (h : hatClone self.auth_token
      = ok hat) :
    wrapClone self
      = ok { auth_token := hat, time_received := self.time_received }

recall auth_token_entry_wrap_clone_fail (self : AuthTokenEntryWrap) (e : Error)
    (h : hatClone self.auth_token
      = fail e) :
    wrapClone self = fail e

recall auth_token_entry_wrap_clone (hC : HardwareAuthTokenCloneSpec)
    (self : AuthTokenEntryWrap) :
    wrapClone self = ok self

recall auth_token_entry_wrap_hash {H : Type} (inst : core.hash.Hasher H)
    (self : AuthTokenEntryWrap) (state : H) :
    wrapHash inst self state
      = idHash inst (idOf self.auth_token) state

recall auth_token_entry_wrap_eq_ids_differ (a b : AuthTokenEntryWrap)
    (h : a.auth_token.userId ≠ b.auth_token.userId ∨
      a.auth_token.authenticatorId ≠ b.auth_token.authenticatorId) :
    wrapEq a b = ok false

recall auth_token_entry_wrap_eq_same_ids (a b : AuthTokenEntryWrap)
    (h1 : a.auth_token.userId = b.auth_token.userId)
    (h2 : a.auth_token.authenticatorId = b.auth_token.authenticatorId) :
    wrapEq a b
      = hatyEq a.auth_token.authenticatorType b.auth_token.authenticatorType

recall auth_token_entry_wrap_eq (hEq : HardwareAuthenticatorTypeEqSpec)
    (a b : AuthTokenEntryWrap) :
    ∃ r, wrapEq a b = ok r ∧
      (r = true ↔ idOf a.auth_token = idOf b.auth_token)

end AuthTokenEntryWrap

section PerbootDB
open Aeneas Aeneas.Std Result keystore2
open keystore2.std.sync.poison.rwlock
open keystore2.std.collections.hash.set
open database.perboot
open PerbootDB.Insts.CoreDefaultDefault renaming «default» → perbootDefault
open RwLock.Insts.CoreDefaultDefault renaming «default» → rwLockDefault
open RwLockWriteGuard.Insts.CoreOpsDerefDerefMut renaming deref_mut → guardDerefMut
open RwLockReadGuard.Insts.CoreOpsDerefDeref renaming deref → guardDeref
open keystore2.std.hash.random.RandomState.Insts
open keystore2.std.sync.poison
open std.hash.random
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr

recall perboot_db_default_ok (rl : RwLock TokenSet)
    (h : rwLockDefault (HashSetTSGlobal.Insts.CoreDefaultDefault AuthTokenEntryWrap
      CoreDefaultDefault) = ok rl) :
    perbootDefault = ok { auth_tokens := rl }

recall perboot_db_default_fail (e : Error)
    (h : rwLockDefault (HashSetTSGlobal.Insts.CoreDefaultDefault AuthTokenEntryWrap
      CoreDefaultDefault) = fail e) :
    perbootDefault = fail e

recall perboot_db_new : PerbootDB.new = perbootDefault

recall perboot_db_insert_auth_token_entry_ok (self : PerbootDB) (entry : database.AuthTokenEntry)
    (g : RwLockWriteGuard TokenSet) (hs : TokenSet) (back : TokenSet → RwLockWriteGuard TokenSet)
    (r : Option AuthTokenEntryWrap × TokenSet)
    (hw : RwLock.write self.auth_tokens = ok (ROk g))
    (hd : guardDerefMut g = ok (hs, back))
    (hr : HashSet.replace AuthTokenEntryWrap.Insts.CoreCmpEq AuthTokenEntryWrap.Insts.CoreHashHash
      CoreHashBuildHasherDefaultHasher hs entry = ok r) :
    PerbootDB.insert_auth_token_entry self entry = ok ()

recall perboot_db_insert_auth_token_entry_poisoned (self : PerbootDB)
    (entry : database.AuthTokenEntry) (p : PoisonError (RwLockWriteGuard TokenSet))
    (hw : RwLock.write self.auth_tokens = ok (RErr p)) :
    PerbootDB.insert_auth_token_entry self entry = fail Error.panic

recall perboot_db_insert_auth_token_entry_write_fails (self : PerbootDB)
    (entry : database.AuthTokenEntry) (e : Error)
    (hw : RwLock.write self.auth_tokens = fail e) :
    PerbootDB.insert_auth_token_entry self entry = fail e

recall perboot_db_insert_auth_token_entry_deref_fails (self : PerbootDB)
    (entry : database.AuthTokenEntry) (g : RwLockWriteGuard TokenSet) (e : Error)
    (hw : RwLock.write self.auth_tokens = ok (ROk g))
    (hd : guardDerefMut g = fail e) :
    PerbootDB.insert_auth_token_entry self entry = fail e

recall perboot_db_insert_auth_token_entry_replace_fails (self : PerbootDB)
    (entry : database.AuthTokenEntry) (g : RwLockWriteGuard TokenSet) (hs : TokenSet)
    (back : TokenSet → RwLockWriteGuard TokenSet) (e : Error)
    (hw : RwLock.write self.auth_tokens = ok (ROk g))
    (hd : guardDerefMut g = ok (hs, back))
    (hr : HashSet.replace AuthTokenEntryWrap.Insts.CoreCmpEq AuthTokenEntryWrap.Insts.CoreHashHash
      CoreHashBuildHasherDefaultHasher hs entry = fail e) :
    PerbootDB.insert_auth_token_entry self entry = fail e

recall perboot_db_auth_tokens_len_ok (self : PerbootDB) (g : RwLockReadGuard TokenSet)
    (hs : TokenSet) (n : Std.Usize)
    (hr : RwLock.read self.auth_tokens = ok (ROk g))
    (hd : guardDeref g = ok hs) (hl : HashSet.len hs = ok n) :
    PerbootDB.auth_tokens_len self = ok n

recall perboot_db_auth_tokens_len_poisoned (self : PerbootDB)
    (p : PoisonError (RwLockReadGuard TokenSet))
    (hr : RwLock.read self.auth_tokens = ok (RErr p)) :
    PerbootDB.auth_tokens_len self = fail Error.panic

recall perboot_db_auth_tokens_len_read_fails (self : PerbootDB) (e : Error)
    (hr : RwLock.read self.auth_tokens = fail e) :
    PerbootDB.auth_tokens_len self = fail e

recall perboot_db_auth_tokens_len_deref_fails (self : PerbootDB) (g : RwLockReadGuard TokenSet)
    (e : Error) (hr : RwLock.read self.auth_tokens = ok (ROk g))
    (hd : guardDeref g = fail e) :
    PerbootDB.auth_tokens_len self = fail e

recall perboot_db_auth_tokens_len_len_fails (self : PerbootDB) (g : RwLockReadGuard TokenSet)
    (hs : TokenSet) (e : Error)
    (hr : RwLock.read self.auth_tokens = ok (ROk g))
    (hd : guardDeref g = ok hs) (hl : HashSet.len hs = fail e) :
    PerbootDB.auth_tokens_len self = fail e

end PerbootDB

end Keystore2Verify.DatabasePerboot
