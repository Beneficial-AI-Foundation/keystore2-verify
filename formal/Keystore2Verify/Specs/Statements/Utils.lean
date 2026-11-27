import Keystore2Verify.Proofs.Utils.AndroidUserId
import Keystore2Verify.Proofs.Utils.AppUid
import Keystore2Verify.Proofs.Utils.SecureUserId
import Keystore2Verify.Proofs.Utils.Challenge
import Keystore2Verify.Proofs.Utils.IsImeiAttestationTag
import Keystore2Verify.Proofs.Utils.CheckDeviceAttestationPermissions
import Keystore2Verify.Proofs.Utils.CheckUniqueIdAttestationPermissions
import Keystore2Verify.Proofs.Utils.CheckGetAppUidsAffectedBySidPermissions
import Keystore2Verify.Proofs.Utils.CheckDumpPermission
import Keystore2Verify.Proofs.Utils.KeyCharacteristicsToInternal
import Keystore2Verify.Proofs.Utils.KeyParametersToAuthorizations
import Keystore2Verify.Proofs.Utils.Compat2ResponseCode
import Keystore2Verify.Proofs.Utils.UiOpts2Compat
import Keystore2Verify.Proofs.Utils.AesGcm
import Keystore2Verify.Proofs.Utils.AppInfo
import Keystore2Verify.Proofs.Utils.Getpriority
import Keystore2Verify.Proofs.Utils.Setpriority

namespace Keystore2Verify.Utils
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

section AndroidUserId
open utils.AndroidUserId.Insts
open CoreCmpPartialEqAndroidUserId renaming eq → androidUserIdEq
open CoreCloneClone renaming clone → androidUserIdClone
open CoreCmpOrd renaming cmp → androidUserIdCmp
open CoreCmpPartialOrdAndroidUserId renaming partial_cmp → androidUserIdPartialCmp

recall androidUserId_eq (x y : utils.AndroidUserId) :
    androidUserIdEq x y = ok (decide (x = y))

recall androidUserId_clone (x : utils.AndroidUserId) : androidUserIdClone x = ok x

recall androidUserId_cmp (x y : utils.AndroidUserId) :
    androidUserIdCmp x y = ok (compare x.val y.val)

recall androidUserId_partial_cmp (x y : utils.AndroidUserId) :
    androidUserIdPartialCmp x y = ok (some (compare x.val y.val))
end AndroidUserId

section AppUid
open rustutils.android.users renaming multiuser_get_user_id → multiuserGetUserId
open utils.AppUid.Insts
open CoreCmpPartialEqAppUid renaming eq → appUidEq
open CoreCloneClone renaming clone → appUidClone
open CoreCmpOrd renaming cmp → appUidCmp
open CoreCmpPartialOrdAppUid renaming partial_cmp → appUidPartialCmp

recall appUid_eq (x y : utils.AppUid) :
    appUidEq x y = ok (decide (x = y))

recall appUid_clone (x : utils.AppUid) : appUidClone x = ok x

recall appUid_cmp (x y : utils.AppUid) :
    appUidCmp x y = ok (compare x.val y.val)

recall appUid_partial_cmp (x y : utils.AppUid) :
    appUidPartialCmp x y = ok (some (compare x.val y.val))

recall AppUid_owning_user (self : utils.AppUid) (i u : Std.U32)
    (hi : (i.val : Int) = self.val % 2 ^ 32)
    (hcall : multiuserGetUserId i = ok u) :
    ∃ r, utils.AppUid.owning_user self = ok r ∧
      r.val = if u.val < 2 ^ 31 then (u.val : Int) else (u.val : Int) - 2 ^ 32

recall AppUid_calling (u : Std.U32) (hcall : binder.ThreadState.get_calling_uid = ok u) :
    ∃ r, utils.AppUid.calling = ok r ∧ r.val = u.val
end AppUid

section SecureUserId
open utils.SecureUserId.Insts
open CoreCmpPartialEqSecureUserId renaming eq → secureUserIdEq
open CoreCloneClone renaming clone → secureUserIdClone
open CoreCmpOrd renaming cmp → secureUserIdCmp
open CoreCmpPartialOrdSecureUserId renaming partial_cmp → secureUserIdPartialCmp

recall secureUserId_eq (x y : utils.SecureUserId) :
    secureUserIdEq x y = ok (decide (x = y))

recall secureUserId_clone (x : utils.SecureUserId) : secureUserIdClone x = ok x

recall secureUserId_cmp (x y : utils.SecureUserId) :
    secureUserIdCmp x y = ok (compare x.val y.val)

recall secureUserId_partial_cmp (x y : utils.SecureUserId) :
    secureUserIdPartialCmp x y = ok (some (compare x.val y.val))
end SecureUserId

section Challenge
open utils.Challenge.Insts
open CoreCmpPartialEqChallenge renaming eq → challengeEq
open CoreCloneClone renaming clone → challengeClone
open CoreCmpOrd renaming cmp → challengeCmp
open CoreCmpPartialOrdChallenge renaming partial_cmp → challengePartialCmp

recall challenge_eq (x y : utils.Challenge) :
    challengeEq x y = ok (decide (x = y))

recall challenge_clone (x : utils.Challenge) : challengeClone x = ok x

recall challenge_cmp (x y : utils.Challenge) :
    challengeCmp x y = ok (compare x.val y.val)

recall challenge_partial_cmp (x y : utils.Challenge) :
    challengePartialCmp x y = ok (some (compare x.val y.val))
end Challenge

section IsImeiAttestationTag
open android_hardware_security_keymint.aidl.android.hardware.security.keymint

recall is_imei_attestation_tag_iff
    (tag : Tag.Tag) :
    utils.is_imei_attestation_tag tag =
      ok (decide (tag.val = -1879047478 ∨ tag.val = -1879047469))
end IsImeiAttestationTag

section CheckDeviceAttestationPermissions
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open ErrorCode.ErrorCode renaming CANNOT_ATTEST_IDS → cannotAttestIds

recall check_device_attestation_permissions_ok (c : ErrorCode.ErrorCode)
    (hc : cannotAttestIds = ok c)
    (hcall : utils.check_android_permission
      (toStr "android.permission.READ_PRIVILEGED_PHONE_STATE") (error.Error.Km c) = ok (ROk ())) :
    utils.check_device_attestation_permissions = ok (ROk ())

recall check_device_attestation_permissions_err
    (root : anyhow.Error → ErrRoot) (c : ErrorCode.ErrorCode) (e : anyhow.Error)
    (hc : cannotAttestIds = ok c)
    (hcall : utils.check_android_permission
      (toStr "android.permission.READ_PRIVILEGED_PHONE_STATE")
      (error.Error.Km c) = ok (RErr e)) :
    ∃ e', utils.check_device_attestation_permissions = ok (RErr e') ∧
      root e' = root e
end CheckDeviceAttestationPermissions

section CheckUniqueIdAttestationPermissions
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open ErrorCode.ErrorCode renaming CANNOT_ATTEST_IDS → cannotAttestIds

recall check_unique_id_attestation_permissions_ok (c : ErrorCode.ErrorCode)
    (hc : cannotAttestIds = ok c)
    (hcall : utils.check_android_permission
      (toStr "android.permission.REQUEST_UNIQUE_ID_ATTESTATION") (error.Error.Km c) = ok (ROk ())) :
    utils.check_unique_id_attestation_permissions = ok (ROk ())

recall check_unique_id_attestation_permissions_err
    (root : anyhow.Error → ErrRoot) (c : ErrorCode.ErrorCode) (e : anyhow.Error)
    (hc : cannotAttestIds = ok c)
    (hcall : utils.check_android_permission
      (toStr "android.permission.REQUEST_UNIQUE_ID_ATTESTATION")
      (error.Error.Km c) = ok (RErr e)) :
    ∃ e', utils.check_unique_id_attestation_permissions = ok (RErr e') ∧
      root e' = root e
end CheckUniqueIdAttestationPermissions

section CheckGetAppUidsAffectedBySidPermissions
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open ErrorCode.ErrorCode renaming CANNOT_ATTEST_IDS → cannotAttestIds

recall check_get_app_uids_affected_by_sid_permissions_ok (c : ErrorCode.ErrorCode)
    (hc : cannotAttestIds = ok c)
    (hcall : utils.check_android_permission
      (toStr "android.permission.MANAGE_USERS") (error.Error.Km c) = ok (ROk ())) :
    utils.check_get_app_uids_affected_by_sid_permissions = ok (ROk ())

recall check_get_app_uids_affected_by_sid_permissions_err
    (root : anyhow.Error → ErrRoot) (c : ErrorCode.ErrorCode) (e : anyhow.Error)
    (hc : cannotAttestIds = ok c)
    (hcall : utils.check_android_permission
      (toStr "android.permission.MANAGE_USERS")
      (error.Error.Km c) = ok (RErr e)) :
    ∃ e', utils.check_get_app_uids_affected_by_sid_permissions = ok (RErr e') ∧
      root e' = root e
end CheckGetAppUidsAffectedBySidPermissions

section CheckDumpPermission
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open android_system_keystore2.aidl.android.system.keystore2
open ResponseCode.ResponseCode renaming PERMISSION_DENIED → permissionDenied

recall check_dump_permission_ok (c : ResponseCode.ResponseCode)
    (hc : permissionDenied = ok c)
    (hcall : utils.check_android_permission
      (toStr "android.permission.DUMP") (error.Error.Rc c) = ok (ROk ())) :
    utils.check_dump_permission = ok (ROk ())

recall check_dump_permission_err
    (root : anyhow.Error → ErrRoot) (c : ResponseCode.ResponseCode) (e : anyhow.Error)
    (hc : permissionDenied = ok c)
    (hcall : utils.check_android_permission
      (toStr "android.permission.DUMP")
      (error.Error.Rc c) = ok (RErr e)) :
    ∃ e', utils.check_dump_permission = ok (RErr e') ∧
      root e' = root e
end CheckDumpPermission

section KeyCharacteristicsToInternal
open utils.key_characteristics_to_internal
open Aeneas.Std.core.iter.traits.iterator renaming IteratorVecIntoIter → vecIntoIter
open keystore2.core.iter.adapters.map.Map.Insts renaming
  CoreIterTraitsIteratorIterator → mapIterator
open core.iter.adapters
open alloc.vec
open core.convert renaming IntoFrom.into → intoFrom
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open closure.closure.Insts renaming CoreOpsFunctionFnMutTupleKeyParameterKeyParameter → innerFnMut
open closure.Insts renaming
  CoreOpsFunctionFnMutTupleKeyCharacteristicsMapIntoIterKeyParameterGlobalclosure → outerFnMut
open key_parameter.KeyParameterValue.Insts renaming CoreConvertFromKeyParameter → valueFromKp

recall key_characteristics_to_internal_flat
    (srcI : map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure →
      into_iter.IntoIter KeyParameter.KeyParameter)
    (fnI : map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure →
      closure.closure)
    (src : flatten.FlatMap (into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) closure
      key_parameter.KeyParameter
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) →
      into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
    (fn : flatten.FlatMap (into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) closure
      key_parameter.KeyParameter
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) → closure)
    (front : flatten.FlatMap (into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) closure
      key_parameter.KeyParameter
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) →
      Option (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure))
    (valid : flatten.FlatMap (into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) closure
      key_parameter.KeyParameter
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) → Prop)
    (hmapDef : MapDefaultSpec innerFnMut srcI fnI) (hmapNext : MapNextSpec innerFnMut srcI fnI)
    (hflatDef : FlatMapDefaultSpec outerFnMut (mapIterator (vecIntoIter _) innerFnMut)
      src fn front valid)
    (hflatNext : FlatMapNextSpec outerFnMut (mapIterator (vecIntoIter _) innerFnMut)
      src fn front valid)
    (key_characteristics : Vec KeyCharacteristics.KeyCharacteristics)
    (hconv : ∀ kc ∈ key_characteristics.val, ∀ kp ∈ kc.authorizations.val,
      ∃ v, intoFrom valueFromKp kp = ok v)
    (hbound : (key_characteristics.val.flatMap (fun kc => kc.authorizations.val)).length ≤
      Std.Usize.max) :
    ∃ out, utils.key_characteristics_to_internal key_characteristics = ok out ∧
      List.Forall₂ (fun (ckp : KeyCharacteristics.KeyCharacteristics × KeyParameter.KeyParameter)
          (r : key_parameter.KeyParameter) =>
        intoFrom valueFromKp ckp.2 = ok r.value ∧ r.security_level = ckp.1.securityLevel)
        (key_characteristics.val.flatMap
          (fun kc => (kc.authorizations).val.map (fun kp => (kc, kp)))) out.val

recall key_characteristics_to_internal_overflow
    (srcI : map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure →
      into_iter.IntoIter KeyParameter.KeyParameter)
    (fnI : map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure →
      closure.closure)
    (src : flatten.FlatMap (into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) closure
      key_parameter.KeyParameter
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) →
      into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
    (fn : flatten.FlatMap (into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) closure
      key_parameter.KeyParameter
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) → closure)
    (front : flatten.FlatMap (into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) closure
      key_parameter.KeyParameter
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) →
      Option (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure))
    (valid : flatten.FlatMap (into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) closure
      key_parameter.KeyParameter
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) → Prop)
    (hmapDef : MapDefaultSpec innerFnMut srcI fnI) (hmapNext : MapNextSpec innerFnMut srcI fnI)
    (hflatDef : FlatMapDefaultSpec outerFnMut (mapIterator (vecIntoIter _) innerFnMut)
      src fn front valid)
    (hflatNext : FlatMapNextSpec outerFnMut (mapIterator (vecIntoIter _) innerFnMut)
      src fn front valid)
    (key_characteristics : Vec KeyCharacteristics.KeyCharacteristics)
    (hconv : ∀ kc ∈ key_characteristics.val, ∀ kp ∈ kc.authorizations.val,
      ∃ v, intoFrom valueFromKp kp = ok v)
    (hbig : Std.Usize.max <
      (key_characteristics.val.flatMap (fun kc => kc.authorizations.val)).length) :
    utils.key_characteristics_to_internal key_characteristics = fail Error.panic
end KeyCharacteristicsToInternal

section KeyParametersToAuthorizations
open utils.key_parameters_to_authorizations
open closure.Insts renaming CoreOpsFunctionFnMutTupleKeyParameterAuthorization → authFnMut
open core.convert renaming IntoFrom.into → intoFrom
open core.iter.adapters
open alloc.vec
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open KeyParameter.KeyParameter.Insts renaming CoreConvertFromKeyParameterValue → kpFromValue

recall key_parameters_to_authorizations_map
    (src : map.Map (into_iter.IntoIter key_parameter.KeyParameter) closure →
      into_iter.IntoIter key_parameter.KeyParameter)
    (fn : map.Map (into_iter.IntoIter key_parameter.KeyParameter) closure → closure)
    (hdef : MapDefaultSpec authFnMut src fn) (hnext : MapNextSpec authFnMut src fn)
    (parameters : Vec key_parameter.KeyParameter)
    (hconv : ∀ p ∈ parameters.val, ∃ kp, intoFrom kpFromValue p.value = ok kp) :
    ∃ out, utils.key_parameters_to_authorizations parameters = ok out ∧
      List.Forall₂ (fun p a =>
        intoFrom kpFromValue p.value = ok a.keyParameter ∧
          a.securityLevel = p.security_level) parameters.val out.val
end KeyParametersToAuthorizations

section Compat2ResponseCode
open android_security_apc.aidl.android.security.apc
open ResponseCode.ResponseCode renaming OK → apcOk, CANCELLED → apcCancelled,
  ABORTED → apcAborted, OPERATION_PENDING → apcOperationPending, IGNORED → apcIgnored,
  SYSTEM_ERROR → apcSystemError

recall compat_2_response_code_ok (c : ResponseCode.ResponseCode)
    (hc : apcOk = ok c) : utils.compat_2_response_code 0#u32 = ok c

recall compat_2_response_code_cancelled (c : ResponseCode.ResponseCode)
    (hc : apcCancelled = ok c) : utils.compat_2_response_code 1#u32 = ok c

recall compat_2_response_code_aborted (c : ResponseCode.ResponseCode)
    (hc : apcAborted = ok c) : utils.compat_2_response_code 2#u32 = ok c

recall compat_2_response_code_operation_pending (c : ResponseCode.ResponseCode)
    (hc : apcOperationPending = ok c) : utils.compat_2_response_code 3#u32 = ok c

recall compat_2_response_code_ignored (c : ResponseCode.ResponseCode)
    (hc : apcIgnored = ok c) : utils.compat_2_response_code 4#u32 = ok c

recall compat_2_response_code_system_error (c : ResponseCode.ResponseCode)
    (hc : apcSystemError = ok c) : utils.compat_2_response_code 5#u32 = ok c

recall compat_2_response_code_other (c : ResponseCode.ResponseCode) (rc : Std.U32)
    (hrc : 6 ≤ rc.val) (hc : apcSystemError = ok c) :
    utils.compat_2_response_code rc = ok c
end Compat2ResponseCode

section UiOpts2Compat
open android_security_apc.aidl.android.security.apc
open IProtectedConfirmation renaming FLAG_UI_OPTION_INVERTED → flagInverted,
  FLAG_UI_OPTION_MAGNIFIED → flagMagnified

recall ui_opts_2_compat_flags (opt i m : Std.I32)
    (hi : flagInverted = ok i) (hm : flagMagnified = ok m) :
    ∃ r, utils.ui_opts_2_compat opt = ok r ∧
      (r.inverted = true ↔ (opt &&& i) ≠ 0#i32) ∧
      (r.magnified = true ↔ (opt &&& m) ≠ 0#i32)
end UiOpts2Compat

section AesGcm
open utils.AesGcm renaming Blanket.decrypt → aesGcmDecrypt, Blanket.encrypt → aesGcmEncrypt
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr

recall AesGcm_decrypt_ok {T : Type} (inst : utils.AesGcmKey T) (self : T)
    (data iv tag k : Slice Std.U8) (z : keystore2_crypto.zvec.ZVec)
    (root : anyhow.Error → ErrRoot) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hk : inst.key self = ok k)
    (hdec : keystore2_crypto.aes_gcm_decrypt data iv tag k = ok (ROk z)) :
    aesGcmDecrypt inst self data iv tag = ok (ROk z)

recall AesGcm_decrypt_err {T : Type} (inst : utils.AesGcmKey T) (self : T)
    (data iv tag k : Slice Std.U8) (x : keystore2_crypto.error.Error)
    (root : anyhow.Error → ErrRoot) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hk : inst.key self = ok k)
    (hdec : keystore2_crypto.aes_gcm_decrypt data iv tag k = ok (RErr x)) :
    ∃ e, aesGcmDecrypt inst self data iv tag = ok (RErr e) ∧ root e = ErrRoot.crypto x

recall AesGcm_encrypt_ok {T : Type} (inst : utils.AesGcmKey T) (self : T)
    (plaintext k : Slice Std.U8)
    (r : alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8)
    (root : anyhow.Error → ErrRoot) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : CryptoCtxLaw root
      (alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8))
    (hk : inst.key self = ok k)
    (henc : keystore2_crypto.aes_gcm_encrypt plaintext k = ok (ROk r)) :
    aesGcmEncrypt inst self plaintext = ok (ROk r)

recall AesGcm_encrypt_err {T : Type} (inst : utils.AesGcmKey T) (self : T)
    (plaintext k : Slice Std.U8) (x : keystore2_crypto.error.Error)
    (root : anyhow.Error → ErrRoot) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : CryptoCtxLaw root
      (alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8))
    (hk : inst.key self = ok k)
    (henc : keystore2_crypto.aes_gcm_encrypt plaintext k = ok (RErr x)) :
    ∃ e, aesGcmEncrypt inst self plaintext = ok (RErr e) ∧ root e = ErrRoot.crypto x
end AesGcm

section AppInfo
open utils.AppInfo.Insts
open CoreDefaultDefault renaming default → appInfoDefault
open CoreCloneClone renaming clone → appInfoClone
open CoreCmpPartialEqAppInfo renaming eq → appInfoEq

recall AppInfo_default (hdef : OptionDefaultI32Spec) :
    appInfoDefault = ok { target_sdk := none, is_system_app := false }

recall AppInfo_clone (x : utils.AppInfo) : appInfoClone x = ok x

recall AppInfo_eq_ne_system (x y : utils.AppInfo) (h : x.is_system_app ≠ y.is_system_app) :
    appInfoEq x y = ok false

recall AppInfo_eq_same_system (heq : OptionEqI32Spec) (x y : utils.AppInfo)
    (h : x.is_system_app = y.is_system_app) :
    appInfoEq x y = ok (decide (x.target_sdk = y.target_sdk))
end AppInfo

section Getpriority
open libc.unix.linux_like.linux.gnu renaming PRIO_PROCESS → prioProcess,
  getpriority → libcGetpriority

recall getpriority_ok (p : Std.U32) (r : Std.I32)
    (hcl : utils.errno_clear = ok ()) (hp : prioProcess = ok p)
    (hr : libcGetpriority p 0#u32 = ok r) (he : utils.errno_read = ok 0#i32) :
    utils.getpriority = ok (some r)

recall getpriority_errno (p : Std.U32) (r e : Std.I32)
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec)
    (hcl : utils.errno_clear = ok ()) (hp : prioProcess = ok p)
    (hr : libcGetpriority p 0#u32 = ok r) (he : utils.errno_read = ok e) (hne : e ≠ 0#i32) :
    utils.getpriority = ok none

recall getpriority_fail_clear (e : Error) (hcl : utils.errno_clear = fail e) :
    utils.getpriority = fail e

recall getpriority_fail_prio (e : Error) (hcl : utils.errno_clear = ok ())
    (hp : prioProcess = fail e) : utils.getpriority = fail e

recall getpriority_fail_libc (p : Std.U32) (e : Error) (hcl : utils.errno_clear = ok ())
    (hp : prioProcess = ok p) (hr : libcGetpriority p 0#u32 = fail e) :
    utils.getpriority = fail e

recall getpriority_fail_errno (p : Std.U32) (r : Std.I32) (e : Error)
    (hcl : utils.errno_clear = ok ()) (hp : prioProcess = ok p)
    (hr : libcGetpriority p 0#u32 = ok r) (he : utils.errno_read = fail e) :
    utils.getpriority = fail e
end Getpriority

section Setpriority
open libc.unix.linux_like.linux.gnu renaming PRIO_PROCESS → prioProcess,
  setpriority → libcSetpriority

recall setpriority_ok (prio : Std.I32) (p : Std.U32)
    (hcl : utils.errno_clear = ok ()) (hp : prioProcess = ok p)
    (hr : libcSetpriority p 0#u32 prio = ok 0#i32) :
    utils.setpriority prio = ok ()

recall setpriority_failed (prio : Std.I32) (p : Std.U32) (r e : Std.I32)
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec)
    (hcl : utils.errno_clear = ok ()) (hp : prioProcess = ok p)
    (hr : libcSetpriority p 0#u32 prio = ok r) (hne : r ≠ 0#i32)
    (he : utils.errno_read = ok e) :
    utils.setpriority prio = ok ()

recall setpriority_fail_clear (prio : Std.I32) (e : Error) (hcl : utils.errno_clear = fail e) :
    utils.setpriority prio = fail e

recall setpriority_fail_prio (prio : Std.I32) (e : Error) (hcl : utils.errno_clear = ok ())
    (hp : prioProcess = fail e) : utils.setpriority prio = fail e

recall setpriority_fail_libc (prio : Std.I32) (p : Std.U32) (e : Error)
    (hcl : utils.errno_clear = ok ()) (hp : prioProcess = ok p)
    (hr : libcSetpriority p 0#u32 prio = fail e) : utils.setpriority prio = fail e

recall setpriority_fail_errno (prio : Std.I32) (p : Std.U32) (r : Std.I32) (e : Error)
    (hcl : utils.errno_clear = ok ()) (hp : prioProcess = ok p)
    (hr : libcSetpriority p 0#u32 prio = ok r) (hne : r ≠ 0#i32)
    (he : utils.errno_read = fail e) : utils.setpriority prio = fail e
end Setpriority

end Keystore2Verify.Utils
