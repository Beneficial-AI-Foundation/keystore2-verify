import Keystore2Verify.Proofs.Permission.KeyPerm
import Keystore2Verify.Proofs.Permission.KeystorePerm
import Keystore2Verify.Proofs.Permission.KeyPermSet
import Keystore2Verify.Proofs.Permission.Includes
import Keystore2Verify.Proofs.Permission.IntoIter
import Keystore2Verify.Proofs.Permission.CheckKeystorePermission
import Keystore2Verify.Proofs.Permission.CheckGrantPermission
import Keystore2Verify.Proofs.Permission.CheckKeyPermission

namespace Keystore2Verify.Permission
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

section KeyPerm
open I32.Insts.CoreConvertFromKeyPerm renaming «from» → i32FromKeyPerm
open permission.KeyPerm.Insts
open CoreConvertFromI32 renaming «from» → keyPermFromI32
open Keystore2_selinuxClassPermission renaming «name» → keyPermName
open Keystore2_selinuxClassPermission renaming class_name → keyPermClassName
open CoreCmpPartialEqKeyPerm renaming eq → keyPermEq
open CoreCloneClone renaming clone → keyPermClone

recall key_perm_from_i32 (x : Std.I32) :
    ∃ p, keyPermFromI32 x = ok p ∧
      (x.val ∈ keyPermNumbers → keyPermValue p = x.val) ∧
      (x.val ∉ keyPermNumbers → p = permission.KeyPerm.None)

recall key_perm_into_i32 (p : permission.KeyPerm) :
    ∃ v, i32FromKeyPerm p = ok v ∧ v.val = keyPermValue p

recall key_perm_round_trip (p : permission.KeyPerm) (v : Std.I32)
    (h : i32FromKeyPerm p = ok v) :
    keyPermFromI32 v = ok p

recall key_perm_into_i32_injective (p q : permission.KeyPerm) (v : Std.I32)
    (hp : i32FromKeyPerm p = ok v)
    (hq : i32FromKeyPerm q = ok v) : p = q

recall key_perm_name :
    keyPermName .None = ok (toStr "none") ∧
    keyPermName .Delete = ok (toStr "delete") ∧
    keyPermName .GenUniqueId = ok (toStr "gen_unique_id") ∧
    keyPermName .GetInfo = ok (toStr "get_info") ∧
    keyPermName .Grant = ok (toStr "grant") ∧
    keyPermName .ManageBlob = ok (toStr "manage_blob") ∧
    keyPermName .Rebind = ok (toStr "rebind") ∧
    keyPermName .ReqForcedOp = ok (toStr "req_forced_op") ∧
    keyPermName .Update = ok (toStr "update") ∧
    keyPermName .Use = ok (toStr "use") ∧
    keyPermName .UseDevId = ok (toStr "use_dev_id") ∧
    keyPermName .ConvertStorageKeyToEphemeral = ok (toStr "convert_storage_key_to_ephemeral")

recall key_perm_name_injective (p q : permission.KeyPerm) (s : Str)
    (hp : keyPermName p = ok s) (hq : keyPermName q = ok s) : p = q

recall key_perm_class_name (p : permission.KeyPerm) :
    keyPermClassName p = ok (toStr "keystore2_key")

recall key_perm_clone (p : permission.KeyPerm) : keyPermClone p = ok p

recall key_perm_eq (p q : permission.KeyPerm) :
    ∃ b, keyPermEq p q = ok b ∧ (b = true ↔ p = q)

end KeyPerm

section KeystorePerm
open I32.Insts.CoreConvertFromKeystorePerm renaming «from» → i32FromKeystorePerm
open permission.KeystorePerm.Insts
open CoreConvertFromI32 renaming «from» → keystorePermFromI32
open Keystore2_selinuxClassPermission renaming «name» → keystorePermName
open Keystore2_selinuxClassPermission renaming class_name → keystorePermClassName
open CoreCmpPartialEqKeystorePerm renaming eq → keystorePermEq
open CoreCloneClone renaming clone → keystorePermClone

recall keystore_perm_from_i32 (x : Std.I32) :
    ∃ p, keystorePermFromI32 x = ok p ∧
      (x.val ∈ keystorePermNumbers → keystorePermValue p = x.val) ∧
      (x.val ∉ keystorePermNumbers → p = permission.KeystorePerm.None)

recall keystore_perm_into_i32 (p : permission.KeystorePerm) :
    ∃ v, i32FromKeystorePerm p = ok v ∧ v.val = keystorePermValue p

recall keystore_perm_round_trip (p : permission.KeystorePerm) (v : Std.I32)
    (h : i32FromKeystorePerm p = ok v) :
    keystorePermFromI32 v = ok p

recall keystore_perm_into_i32_injective (p q : permission.KeystorePerm) (v : Std.I32)
    (hp : i32FromKeystorePerm p = ok v)
    (hq : i32FromKeystorePerm q = ok v) : p = q

recall keystore_perm_name :
    keystorePermName .None = ok (toStr "none") ∧
    keystorePermName .AddAuth = ok (toStr "add_auth") ∧
    keystorePermName .ClearNs = ok (toStr "clear_ns") ∧
    keystorePermName .List = ok (toStr "list") ∧
    keystorePermName .Lock = ok (toStr "lock") ∧
    keystorePermName .Reset = ok (toStr "reset") ∧
    keystorePermName .Unlock = ok (toStr "unlock") ∧
    keystorePermName .ChangeUser = ok (toStr "change_user") ∧
    keystorePermName .ChangePassword = ok (toStr "change_password") ∧
    keystorePermName .ClearUID = ok (toStr "clear_uid") ∧
    keystorePermName .GetAuthToken = ok (toStr "get_auth_token") ∧
    keystorePermName .EarlyBootEnded = ok (toStr "early_boot_ended") ∧
    keystorePermName .PullMetrics = ok (toStr "pull_metrics") ∧
    keystorePermName .DeleteAllKeys = ok (toStr "delete_all_keys") ∧
    keystorePermName .GetAttestationKey = ok (toStr "get_attestation_key") ∧
    keystorePermName .GetLastAuthTime = ok (toStr "get_last_auth_time")

recall keystore_perm_name_injective (p q : permission.KeystorePerm) (s : Str)
    (hp : keystorePermName p = ok s) (hq : keystorePermName q = ok s) : p = q

recall keystore_perm_class_name (p : permission.KeystorePerm) :
    keystorePermClassName p = ok (toStr "keystore2")

recall keystore_perm_clone (p : permission.KeystorePerm) : keystorePermClone p = ok p

recall keystore_perm_eq (p q : permission.KeystorePerm) :
    ∃ b, keystorePermEq p q = ok b ∧ (b = true ↔ p = q)

end KeystorePerm

section KeyPermSet
open I32.Insts.CoreConvertFromKeyPermSet renaming «from» → i32FromKeyPermSet
open permission.KeyPermSet.Insts
open CoreConvertFromKeyPerm renaming «from» → setFromKeyPerm
open CoreConvertFromI32 renaming «from» → setFromI32
open CoreCloneClone renaming clone → setClone
open CoreCmpPartialEqKeyPermSet renaming eq → setEq
open CoreCmpOrd renaming cmp → setCmp
open CoreCmpPartialOrdKeyPermSet renaming partial_cmp → setPartialCmp

recall key_perm_set_from_key_perm (p : permission.KeyPerm) :
    ∃ s, setFromKeyPerm p = ok s ∧ s.val = keyPermValue p

recall key_perm_set_from_i32 (x : Std.I32) : setFromI32 x = ok x

recall i32_from_key_perm_set (s : permission.KeyPermSet) :
    i32FromKeyPermSet s = ok s

recall key_perm_set_clone (s : permission.KeyPermSet) : setClone s = ok s

recall key_perm_set_eq (a b : permission.KeyPermSet) :
    ∃ r, setEq a b = ok r ∧ (r = true ↔ a = b)

recall key_perm_set_cmp (a b : permission.KeyPermSet) :
    setCmp a b = ok (compare a.val b.val)

recall key_perm_set_partial_cmp (a b : permission.KeyPermSet) :
    setPartialCmp a b = ok (some (compare a.val b.val))

end KeyPermSet

section Includes
open permission.KeyPermSet.Insts

recall includes_ok {T : Type} (inst : core.convert.Into T permission.KeyPermSet)
    (self : permission.KeyPermSet) (other : T) (o : permission.KeyPermSet)
    (h : inst.into other = ok o) :
    ∃ b, permission.KeyPermSet.includes inst self other = ok b ∧
      (b = true ↔ Includes self o)

recall includes_fail {T : Type} (inst : core.convert.Into T permission.KeyPermSet)
    (self : permission.KeyPermSet) (other : T) (x : Error)
    (h : inst.into other = fail x) :
    permission.KeyPermSet.includes inst self other = fail x

recall includes_key_perm (self : permission.KeyPermSet) (p : permission.KeyPerm) :
    ∃ o b, CoreConvertFromKeyPerm.from p = ok o ∧
      permission.KeyPermSet.includes
        (core.convert.IntoFrom CoreConvertFromKeyPerm) self p = ok b ∧
      (b = true ↔ Includes self o)

recall includes_i32 (self : permission.KeyPermSet) (x : Std.I32) :
    ∃ b, permission.KeyPermSet.includes
        (core.convert.IntoFrom CoreConvertFromI32) self x = ok b ∧
      (b = true ↔ Includes self x)

recall includes_key_perm_set (self other : permission.KeyPermSet) :
    ∃ b, permission.KeyPermSet.includes
        (core.convert.IntoFrom (core.convert.FromSame permission.KeyPermSet)) self other = ok b ∧
      (b = true ↔ Includes self other)

recall includes_div {T : Type} (inst : core.convert.Into T permission.KeyPermSet)
    (self : permission.KeyPermSet) (other : T) (h : inst.into other = .div) :
    permission.KeyPermSet.includes inst self other = .div

end Includes

section IntoIter
open permission.perm
open permission.KeyPermSet.Insts
open permission.perm.IntoIter.Insts
open CoreIterTraitsIteratorIteratorKeyPerm renaming next → iterNext
open permission.KeyPerm.Insts.CoreConvertFromI32 renaming «from» → keyPermFromI32

recall into_iter_new (v : permission.KeyPermSet) :
    IntoIter.new v = ok { vec := v, pos := 0#u8 }

recall key_perm_set_into_iter (v : permission.KeyPermSet) :
    CoreIterTraitsCollectIntoIteratorKeyPermIntoIter.into_iter v =
      ok { vec := v, pos := 0#u8 }

recall into_iter_next_some (it : permission.perm.IntoIter) (i : Nat)
    (hi : NextBit it.vec it.pos.val i) :
    ∃ kp it', keyPermFromI32 (bitVal i) = ok kp ∧ iterNext it = ok (some kp, it') ∧
      it'.vec = it.vec ∧ it'.pos.val = i + 1

recall into_iter_next_none (it : permission.perm.IntoIter) (hpos : it.pos.val ≤ 32)
    (hnone : ∀ j, it.pos.val ≤ j → j < 32 → ¬ HasBit it.vec j) :
    ∃ it', iterNext it = ok (none, it') ∧ it'.vec = it.vec ∧ it'.pos.val = 32

recall into_iter_next_pos_too_large (it : permission.perm.IntoIter) (hpos : 32 < it.pos.val) :
    ∃ x, iterNext it = fail x

end IntoIter

section CheckKeystorePermission
open core.ffi.c_str
open permission.KeystorePerm.Insts

recall check_keystore_permission_ok (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_ctx : CStr) (perm : permission.KeystorePerm)
    (ctx : keystore2_selinux.Context) (c : CStr)
    (hget : keystore2_selinux.getcon = ok (.Ok ctx)) (hc : contextCStr ctx = ok c)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = ok (.Ok ())) :
    permission.check_keystore_permission caller_ctx perm = ok (.Ok ())

recall check_keystore_permission_getcon_err (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_ctx : CStr) (perm : permission.KeystorePerm)
    (e : anyhow.Error) (hget : keystore2_selinux.getcon = ok (.Err e)) :
    ∃ e', permission.check_keystore_permission caller_ctx perm = ok (.Err e') ∧
      root e' = root e

recall check_keystore_permission_check_err (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_ctx : CStr) (perm : permission.KeystorePerm)
    (ctx : keystore2_selinux.Context) (c : CStr) (e : anyhow.Error)
    (hget : keystore2_selinux.getcon = ok (.Ok ctx)) (hc : contextCStr ctx = ok c)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = ok (.Err e)) :
    permission.check_keystore_permission caller_ctx perm = ok (.Err e)

recall check_keystore_permission_getcon_fail (caller_ctx : CStr)
    (perm : permission.KeystorePerm) (x : Error)
    (hget : keystore2_selinux.getcon = fail x) :
    permission.check_keystore_permission caller_ctx perm = fail x

recall check_keystore_permission_check_fail (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_ctx : CStr) (perm : permission.KeystorePerm)
    (ctx : keystore2_selinux.Context) (c : CStr) (x : Error)
    (hget : keystore2_selinux.getcon = ok (.Ok ctx)) (hc : contextCStr ctx = ok c)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = fail x) :
    permission.check_keystore_permission caller_ctx perm = fail x

recall check_keystore_permission_deref_fail (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_ctx : CStr) (perm : permission.KeystorePerm)
    (ctx : keystore2_selinux.Context) (x : Error)
    (hget : keystore2_selinux.getcon = ok (.Ok ctx)) (hc : contextCStr ctx = fail x) :
    permission.check_keystore_permission caller_ctx perm = fail x

recall check_keystore_permission_ok_of_result (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_ctx : CStr) (perm : permission.KeystorePerm)
    (h : permission.check_keystore_permission caller_ctx perm = ok (.Ok ())) :
    ∃ ctx c, keystore2_selinux.getcon = ok (.Ok ctx) ∧ contextCStr ctx = ok c ∧
      keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c perm =
        ok (.Ok ())

end CheckKeystorePermission

section CheckGrantPermission
open core.ffi.c_str
open permission.KeyPerm.Insts
open CoreConvertFromI32 renaming «from» → keyPermFromI32

recall check_grant_permission_foreign_app (root : anyhow.Error → ErrRoot)
    (hctx : SelinuxStrCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc)
    (hdom : key.domain = domainApp) (hne : caller_uid ≠ key.nspace) :
    ∃ e, permission.check_grant_permission caller_uid caller_ctx access_vec key = ok (.Err e) ∧
      root e = deniedRoot

recall check_grant_permission_app_getcon_err (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc)
    (hdom : key.domain = domainApp) (heq : caller_uid = key.nspace)
    (e : anyhow.Error) (hget : keystore2_selinux.getcon = ok (.Err e)) :
    ∃ e', permission.check_grant_permission caller_uid caller_ctx access_vec key =
        ok (.Err e') ∧ root e' = root e

recall check_grant_permission_selinux_lookup_err (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc)
    (hdom : key.domain = domainSelinux)
    (e : anyhow.Error) (hlook : permission.lookup_keystore2_key_context key.nspace = ok (.Err e)) :
    ∃ e', permission.check_grant_permission caller_uid caller_ctx access_vec key =
        ok (.Err e') ∧ root e' = root e

recall check_grant_permission_app_getcon_fail
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc)
    (hdom : key.domain = domainApp) (heq : caller_uid = key.nspace)
    (x : Error) (hget : keystore2_selinux.getcon = fail x) :
    permission.check_grant_permission caller_uid caller_ctx access_vec key = fail x

recall check_grant_permission_selinux_lookup_fail
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc)
    (hdom : key.domain = domainSelinux)
    (x : Error) (hlook : permission.lookup_keystore2_key_context key.nspace = fail x) :
    permission.check_grant_permission caller_uid caller_ctx access_vec key = fail x

recall check_grant_permission_other_domain (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hctx : KsStringCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc)
    (happ : key.domain ≠ domainApp) (hsel : key.domain ≠ domainSelinux) :
    ∃ e, permission.check_grant_permission caller_uid caller_ctx access_vec key = ok (.Err e) ∧
      root e = .ks sysError

recall check_grant_permission_grant_check_err (root : anyhow.Error → ErrRoot)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hctxU : AnyhowStrCtxLaw root Unit)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx))) (e : anyhow.Error)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Err e)) :
    ∃ e', permission.check_grant_permission caller_uid caller_ctx access_vec key =
        ok (.Err e') ∧ root e' = root e

recall check_grant_permission_deref_fail (root : anyhow.Error → ErrRoot)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc)
    (ctx : keystore2_selinux.Context)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (x : Error) (hc : contextCStr ctx = fail x) :
    permission.check_grant_permission caller_uid caller_ctx access_vec key = fail x

recall check_grant_permission_grant_check_fail (root : anyhow.Error → ErrRoot)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (x : Error)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = fail x) :
    permission.check_grant_permission caller_uid caller_ctx access_vec key = fail x

recall check_grant_permission_grant_in_set (root : anyhow.Error → ErrRoot)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hctxU : AnyhowStrCtxLaw root Unit) (hsel : SelinuxStrCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Ok ()))
    (hbit : HasBit access_vec 3) :
    ∃ e, permission.check_grant_permission caller_uid caller_ctx access_vec key = ok (.Err e) ∧
      root e = deniedRoot

recall check_grant_permission_ok_empty (root : anyhow.Error → ErrRoot)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hctxU : AnyhowStrCtxLaw root Unit)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Ok ()))
    (hempty : ∀ i, i < 32 → ¬ HasBit access_vec i) :
    permission.check_grant_permission caller_uid caller_ctx access_vec key = ok (.Ok ())

recall check_grant_permission_ok (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hctxU : AnyhowStrCtxLaw root Unit) (hctxS : AnyhowStringCtxLaw root Unit)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Ok ()))
    (hbit : ¬ HasBit access_vec 3)
    (hloop : ∀ i, i < 32 → HasBit access_vec i → ∃ kp, keyPermFromI32 (bitVal i) = ok kp ∧
      keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp =
        ok (.Ok ())) :
    permission.check_grant_permission caller_uid caller_ctx access_vec key = ok (.Ok ())

recall check_grant_permission_loop_err (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hctxU : AnyhowStrCtxLaw root Unit) (hctxS : AnyhowStringCtxLaw root Unit)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Ok ()))
    (hbit : ¬ HasBit access_vec 3)
    (i : Nat) (hi : i < 32) (hset : HasBit access_vec i)
    (hlow : ∀ j, j < i → HasBit access_vec j → ∃ kp, keyPermFromI32 (bitVal j) = ok kp ∧
      keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp =
        ok (.Ok ()))
    (kp : permission.KeyPerm) (hkp : keyPermFromI32 (bitVal i) = ok kp)
    (e : anyhow.Error)
    (hbad : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp =
      ok (.Err e)) :
    ∃ e', permission.check_grant_permission caller_uid caller_ctx access_vec key =
        ok (.Err e') ∧ root e' = root e

recall check_grant_permission_loop_fail (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hctxU : AnyhowStrCtxLaw root Unit) (hctxS : AnyhowStringCtxLaw root Unit)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Ok ()))
    (hbit : ¬ HasBit access_vec 3)
    (i : Nat) (hi : i < 32) (hset : HasBit access_vec i)
    (hlow : ∀ j, j < i → HasBit access_vec j → ∃ kp, keyPermFromI32 (bitVal j) = ok kp ∧
      keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp =
        ok (.Ok ()))
    (kp : permission.KeyPerm) (hkp : keyPermFromI32 (bitVal i) = ok kp)
    (x : Error)
    (hbad : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp =
      fail x) :
    permission.check_grant_permission caller_uid caller_ctx access_vec key = fail x

recall check_grant_permission_of_ok (root : anyhow.Error → ErrRoot)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hctxU : AnyhowStrCtxLaw root Unit) (hctxS : AnyhowStringCtxLaw root Unit)
    (hsel : SelinuxStrCtxLaw root) (hks : KsStringCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc)
    (hok : permission.check_grant_permission caller_uid caller_ctx access_vec key =
      ok (.Ok ())) :
    ¬ HasBit access_vec 3 ∧
      ∃ ctx c, contextCStr ctx = ok c ∧
        ((key.domain = domainApp ∧ caller_uid = key.nspace ∧
            keystore2_selinux.getcon = ok (.Ok ctx)) ∨
          (key.domain = domainSelinux ∧
            permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx))) ∧
        keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
          permission.KeyPerm.Grant = ok (.Ok ()) ∧
        ∀ i, i < 32 → HasBit access_vec i → ∃ kp, keyPermFromI32 (bitVal i) = ok kp ∧
          keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp =
            ok (.Ok ())

end CheckGrantPermission

section CheckKeyPermission
open core.ffi.c_str
open permission.KeyPerm.Insts

recall check_key_permission_covered
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hcov : Covers perm access_vector) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector = ok (.Ok ())

recall check_key_permission_none_perm
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (key : KeyDesc)
    (av : permission.KeyPermSet) :
    permission.check_key_permission caller_uid caller_ctx permission.KeyPerm.None key (some av) =
      ok (.Ok ())

recall check_key_permission_foreign_app (root : anyhow.Error → ErrRoot)
    (hctx : SelinuxStrCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector)
    (hdom : key.domain = domainApp) (hne : caller_uid ≠ key.nspace) :
    ∃ e, permission.check_key_permission caller_uid caller_ctx perm key access_vector =
        ok (.Err e) ∧ root e = deniedRoot

recall check_key_permission_app_getcon_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector)
    (hdom : key.domain = domainApp) (heq : caller_uid = key.nspace)
    (e : anyhow.Error) (hget : keystore2_selinux.getcon = ok (.Err e)) :
    ∃ e', permission.check_key_permission caller_uid caller_ctx perm key access_vector =
        ok (.Err e') ∧ root e' = root e

recall check_key_permission_lookup_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector)
    (hdom : key.domain = domainSelinux ∨ key.domain = domainBlob)
    (e : anyhow.Error) (hlook : permission.lookup_keystore2_key_context key.nspace = ok (.Err e)) :
    ∃ e', permission.check_key_permission caller_uid caller_ctx perm key access_vector =
        ok (.Err e') ∧ root e' = root e

recall check_key_permission_app_getcon_fail
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector)
    (hdom : key.domain = domainApp) (heq : caller_uid = key.nspace)
    (x : Error) (hget : keystore2_selinux.getcon = fail x) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector = fail x

recall check_key_permission_lookup_fail
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector)
    (hdom : key.domain = domainSelinux ∨ key.domain = domainBlob)
    (x : Error) (hlook : permission.lookup_keystore2_key_context key.nspace = fail x) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector = fail x

recall check_key_permission_grant_not_granted (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hctx : SelinuxStringCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (av : permission.KeyPermSet)
    (hnc : ¬ Covers perm (some av)) (hdom : key.domain = domainGrant) :
    ∃ e, permission.check_key_permission caller_uid caller_ctx perm key (some av) =
        ok (.Err e) ∧ root e = deniedRoot

recall check_key_permission_grant_no_vector (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (hdom : key.domain = domainGrant) :
    ∃ e, permission.check_key_permission caller_uid caller_ctx perm key none = ok (.Err e) ∧
      root e = .ks sysError

recall check_key_permission_key_id (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (hdom : key.domain = domainKeyId) :
    ∃ e, permission.check_key_permission caller_uid caller_ctx perm key access_vector =
        ok (.Err e) ∧ root e = .ks sysError

recall check_key_permission_unknown_domain (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hctx : KsStringCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector)
    (h0 : key.domain ≠ domainApp) (h1 : key.domain ≠ domainGrant)
    (h2 : key.domain ≠ domainSelinux) (h3 : key.domain ≠ domainBlob)
    (h4 : key.domain ≠ domainKeyId) :
    ∃ e, permission.check_key_permission caller_uid caller_ctx perm key access_vector =
        ok (.Err e) ∧ root e = .ks invalidArgumentError

recall check_key_permission_blob_manage_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (hdom : key.domain = domainBlob)
    (ctx : keystore2_selinux.Context) (c : CStr) (e : anyhow.Error)
    (hlook : permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx))
    (hc : contextCStr ctx = ok c)
    (hmanage : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.ManageBlob = ok (.Err e)) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector =
      ok (.Err e)

recall check_key_permission_app_selinux_check_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = ok (.Ok ())) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector =
      ok (.Ok ())

recall check_key_permission_app_selinux_check_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (e : anyhow.Error)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = ok (.Err e)) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector =
      ok (.Err e)

recall check_key_permission_blob_check_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (hdom : key.domain = domainBlob)
    (ctx : keystore2_selinux.Context) (c : CStr)
    (hlook : permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx))
    (hc : contextCStr ctx = ok c)
    (hmanage : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.ManageBlob = ok (.Ok ()))
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = ok (.Ok ())) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector =
      ok (.Ok ())

recall check_key_permission_blob_check_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (hdom : key.domain = domainBlob)
    (ctx : keystore2_selinux.Context) (c : CStr)
    (hlook : permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx))
    (hc : contextCStr ctx = ok c)
    (hmanage : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.ManageBlob = ok (.Ok ()))
    (e : anyhow.Error)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = ok (.Err e)) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector =
      ok (.Err e)

recall check_key_permission_app_selinux_deref_fail (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector)
    (ctx : keystore2_selinux.Context)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (x : Error) (hc : contextCStr ctx = fail x) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector = fail x

recall check_key_permission_app_selinux_check_fail (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (x : Error)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = fail x) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector = fail x

recall check_key_permission_blob_deref_fail (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (hdom : key.domain = domainBlob)
    (ctx : keystore2_selinux.Context)
    (hlook : permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx))
    (x : Error) (hc : contextCStr ctx = fail x) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector = fail x

recall check_key_permission_blob_manage_fail (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (hdom : key.domain = domainBlob)
    (ctx : keystore2_selinux.Context) (c : CStr) (x : Error)
    (hlook : permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx))
    (hc : contextCStr ctx = ok c)
    (hmanage : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.ManageBlob = fail x) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector = fail x

recall check_key_permission_blob_check_fail (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (hdom : key.domain = domainBlob)
    (ctx : keystore2_selinux.Context) (c : CStr)
    (hlook : permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx))
    (hc : contextCStr ctx = ok c)
    (hmanage : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.ManageBlob = ok (.Ok ()))
    (x : Error)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = fail x) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector = fail x

recall check_key_permission_of_ok (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (hselStr : SelinuxStrCtxLaw root) (hselString : SelinuxStringCtxLaw root)
    (hks : KsStringCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hok : permission.check_key_permission caller_uid caller_ctx perm key access_vector =
      ok (.Ok ())) :
    Covers perm access_vector ∨
      ∃ ctx c, contextCStr ctx = ok c ∧
        keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c perm =
          ok (.Ok ()) ∧
        ((key.domain = domainApp ∧ caller_uid = key.nspace ∧
            keystore2_selinux.getcon = ok (.Ok ctx)) ∨
          (key.domain = domainSelinux ∧
            permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)) ∨
          (key.domain = domainBlob ∧
            permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx) ∧
            keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
              permission.KeyPerm.ManageBlob = ok (.Ok ())))

end CheckKeyPermission

end Keystore2Verify.Permission
