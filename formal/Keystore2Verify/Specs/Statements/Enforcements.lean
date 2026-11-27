import Keystore2Verify.Proofs.Enforcements.AuthRequestOpAuth
import Keystore2Verify.Proofs.Enforcements.AuthRequestTimestamp
import Keystore2Verify.Proofs.Enforcements.AuthRequestGetAuthTokens
import Keystore2Verify.Proofs.Enforcements.TokenReceiverMapDefault
import Keystore2Verify.Proofs.Enforcements.TokenReceiverIsObsolete
import Keystore2Verify.Proofs.Enforcements.TimestampTokenRequest
import Keystore2Verify.Proofs.Enforcements.AuthInfoBeforeUpdate
import Keystore2Verify.Proofs.Enforcements.AuthInfoAfterFinish
import Keystore2Verify.Proofs.Enforcements.AuthInfoGetAuthTokens
import Keystore2Verify.Proofs.Enforcements.EnforcementsDefault
import Keystore2Verify.Proofs.Enforcements.InstallConfirmationTokenReceiver
import Keystore2Verify.Proofs.Enforcements.FindAuthToken
import Keystore2Verify.Proofs.Enforcements.IsGivenTimePassed
import Keystore2Verify.Proofs.Enforcements.SetDeviceLocked
import Keystore2Verify.Proofs.Enforcements.RegisterOpAuthReceiver
import Keystore2Verify.Proofs.Enforcements.SuperEncryptionRequired
import Keystore2Verify.Proofs.Enforcements.EnforcementsGetAuthTokens
import Keystore2Verify.Proofs.Enforcements.GetLastAuthTime

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2

section AuthRequestOpAuth
open alloc.sync
open std.sync.poison.mutex

recall auth_request_op_auth (m : Mutex (Option AuthToken))
    (a : alloc.sync.Arc enforcements.AuthRequest)
    (hm : Mutex.new (none : Option AuthToken) = ok m)
    (ha : Arc.new
      ({ state := enforcements.AuthRequestState.OpAuth, hat := m } : enforcements.AuthRequest)
      = ok a) :
    enforcements.AuthRequest.op_auth = ok a

end AuthRequestOpAuth

section AuthRequestTimestamp
open alloc.sync
open std.sync.poison.mutex

recall auth_request_timestamp (hat : AuthToken)
    (receiver : TsReceiver)
    (m : Mutex (TsReceiver))
    (m1 : Mutex (Option AuthToken)) (a : alloc.sync.Arc enforcements.AuthRequest)
    (hm : Mutex.new receiver = ok m) (hm1 : Mutex.new (some hat) = ok m1)
    (ha : Arc.new
      ({ state := enforcements.AuthRequestState.TimeStamp m, hat := m1 }
        : enforcements.AuthRequest) = ok a) :
    enforcements.AuthRequest.timestamp hat receiver = ok a

end AuthRequestTimestamp

section AuthRequestGetAuthTokens
open std.sync.poison
open std.sync.mpsc
open Keystore2Verify.Externals
open std.sync.poison.mutex
open MutexGuard.Insts
open CoreOpsDerefDerefMut renaming deref_mut → guardDerefMut
open CoreOpsDerefDeref renaming deref → guardDeref
open android_hardware_security_keymint.aidl.android.hardware.security.keymint.ErrorCode.ErrorCode
  renaming KEY_USER_NOT_AUTHENTICATED → keyUserNotAuthenticated

recall auth_request_get_auth_tokens_slot_poisoned (self : enforcements.AuthRequest)
    (pe : PoisonError (MutexGuard (Option AuthToken)))
    (hlock : Mutex.lock self.hat = ok (.Err pe)) :
    enforcements.AuthRequest.get_auth_tokens self = fail Error.panic

recall auth_request_get_auth_tokens_no_token (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root AuthToken)
    (self : enforcements.AuthRequest) (g : MutexGuard (Option AuthToken))
    (f : Option AuthToken → MutexGuard (Option AuthToken))
    (ec : KmErrorCode)
    (hlock : Mutex.lock self.hat = ok (.Ok g)) (hmut : guardDerefMut g = ok (none, f))
    (hec : keyUserNotAuthenticated = ok ec) :
    ∃ e, enforcements.AuthRequest.get_auth_tokens self = ok (.Err e) ∧
      root e = ErrRoot.ks (error.Error.Km ec)

recall auth_request_get_auth_tokens_op_auth (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root AuthToken)
    (self : enforcements.AuthRequest) (hat : AuthToken) (g : MutexGuard (Option AuthToken))
    (f : Option AuthToken → MutexGuard (Option AuthToken))
    (ec : KmErrorCode)
    (hstate : self.state = enforcements.AuthRequestState.OpAuth)
    (hlock : Mutex.lock self.hat = ok (.Ok g)) (hmut : guardDerefMut g = ok (some hat, f))
    (hec : keyUserNotAuthenticated = ok ec) :
    enforcements.AuthRequest.get_auth_tokens self = ok (.Ok (hat, none))

recall auth_request_get_auth_tokens_timestamp_poisoned (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root AuthToken)
    (self : enforcements.AuthRequest) (hat : AuthToken) (g : MutexGuard (Option AuthToken))
    (f : Option AuthToken → MutexGuard (Option AuthToken))
    (ec : KmErrorCode)
    (recv : Mutex (TsReceiver))
    (pe : PoisonError
      (MutexGuard (TsReceiver)))
    (hstate : self.state = enforcements.AuthRequestState.TimeStamp recv)
    (hlock : Mutex.lock self.hat = ok (.Ok g)) (hmut : guardDerefMut g = ok (some hat, f))
    (hec : keyUserNotAuthenticated = ok ec) (hlock1 : Mutex.lock recv = ok (.Err pe)) :
    enforcements.AuthRequest.get_auth_tokens self = fail Error.panic

recall auth_request_get_auth_tokens_timestamp_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root AuthToken) (hctx1 : RecvStrCtxAssumption root)
    (hctx2 : KsStringCtxAssumption root TimeStamp)
    (self : enforcements.AuthRequest) (hat : AuthToken) (g : MutexGuard (Option AuthToken))
    (f : Option AuthToken → MutexGuard (Option AuthToken))
    (ec : KmErrorCode)
    (recv : Mutex (TsReceiver))
    (g1 : MutexGuard (TsReceiver))
    (r : TsReceiver) (tst : TimeStamp)
    (hstate : self.state = enforcements.AuthRequestState.TimeStamp recv)
    (hlock : Mutex.lock self.hat = ok (.Ok g)) (hmut : guardDerefMut g = ok (some hat, f))
    (hec : keyUserNotAuthenticated = ok ec)
    (hlock1 : Mutex.lock recv = ok (.Ok g1)) (hderef : guardDeref g1 = ok r)
    (hrecv : Receiver.recv r = ok (.Ok (.Ok tst))) :
    enforcements.AuthRequest.get_auth_tokens self = ok (.Ok (hat, some tst))

recall auth_request_get_auth_tokens_timestamp_worker_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root AuthToken) (hctx1 : RecvStrCtxAssumption root)
    (hctx2 : KsStringCtxAssumption root TimeStamp)
    (self : enforcements.AuthRequest) (hat : AuthToken) (g : MutexGuard (Option AuthToken))
    (f : Option AuthToken → MutexGuard (Option AuthToken))
    (ec : KmErrorCode)
    (recv : Mutex (TsReceiver))
    (g1 : MutexGuard (TsReceiver))
    (r : TsReceiver) (e : error.Error)
    (hstate : self.state = enforcements.AuthRequestState.TimeStamp recv)
    (hlock : Mutex.lock self.hat = ok (.Ok g)) (hmut : guardDerefMut g = ok (some hat, f))
    (hec : keyUserNotAuthenticated = ok ec)
    (hlock1 : Mutex.lock recv = ok (.Ok g1)) (hderef : guardDeref g1 = ok r)
    (hrecv : Receiver.recv r = ok (.Ok (.Err e))) :
    ∃ e', enforcements.AuthRequest.get_auth_tokens self = ok (.Err e') ∧
      root e' = ErrRoot.ks e

recall auth_request_get_auth_tokens_timestamp_disconnected (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root AuthToken) (hctx1 : RecvStrCtxAssumption root)
    (self : enforcements.AuthRequest) (hat : AuthToken) (g : MutexGuard (Option AuthToken))
    (f : Option AuthToken → MutexGuard (Option AuthToken))
    (ec : KmErrorCode)
    (recv : Mutex (TsReceiver))
    (g1 : MutexGuard (TsReceiver))
    (r : TsReceiver)
    (re : RecvError)
    (hstate : self.state = enforcements.AuthRequestState.TimeStamp recv)
    (hlock : Mutex.lock self.hat = ok (.Ok g)) (hmut : guardDerefMut g = ok (some hat, f))
    (hec : keyUserNotAuthenticated = ok ec)
    (hlock1 : Mutex.lock recv = ok (.Ok g1)) (hderef : guardDeref g1 = ok r)
    (hrecv : Receiver.recv r = ok (.Err re)) :
    ∃ e', enforcements.AuthRequest.get_auth_tokens self = ok (.Err e') ∧
      root e' = ErrRoot.other

end AuthRequestGetAuthTokens

section TokenReceiverMapDefault
open std.collections.hash.map
open std.hash.random
open std.sync.poison.mutex
open enforcements.TokenReceiverMap.Insts.CoreDefaultDefault renaming
  default → tokenReceiverMapDefault

recall token_receiver_map_default
    (hm : HashMap utils.Challenge enforcements.TokenReceiver
      RandomState alloc.alloc.Global)
    (m : Mutex ((HashMap utils.Challenge enforcements.TokenReceiver
      RandomState alloc.alloc.Global) × Std.U8))
    (hnew : HashMapKVRandomStateGlobal.new utils.Challenge
      enforcements.TokenReceiver = ok hm)
    (hmutex : Mutex.new (hm, 26#u8) = ok m) :
    tokenReceiverMapDefault
      = ok { map_and_cleanup_counter := m }

end TokenReceiverMapDefault

section TokenReceiverIsObsolete
open alloc.sync
open alloc.alloc.Global.Insts renaming CoreAllocAllocatorClone → globalAllocClone

recall token_receiver_is_obsolete_gone (self : enforcements.TokenReceiver)
    (hup : Weak.upgrade globalAllocClone self.req
      = ok none) :
    enforcements.TokenReceiver.is_obsolete self = ok true

recall token_receiver_is_obsolete_alive (self : enforcements.TokenReceiver)
    (a : alloc.sync.Arc enforcements.AuthRequest)
    (hup : Weak.upgrade globalAllocClone self.req
      = ok (some a)) :
    enforcements.TokenReceiver.is_obsolete self = ok false

end TokenReceiverIsObsolete

section TimestampTokenRequest
open std.sync.mpsc
open Keystore2Verify.Externals

recall timestamp_token_request_sent (challenge : utils.Challenge)
    (sender : Sender (TsResult))
    (r : TsResult)
    (hget : enforcements.get_timestamp_token challenge = ok r)
    (hsend : Sender.send sender r = ok (.Ok ())) :
    enforcements.timestamp_token_request challenge sender = ok ()

recall timestamp_token_request_hung_up (challenge : utils.Challenge)
    (hcmp : LogLevelPartialCmpSpec) (hmax : LogMaxLevelSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec)
    (sender : Sender (TsResult))
    (r : TsResult)
    (e : SendError (TsResult))
    (hget : enforcements.get_timestamp_token challenge = ok r)
    (hsend : Sender.send sender r = ok (.Err e)) :
    enforcements.timestamp_token_request challenge sender = ok ()

end TimestampTokenRequest

section AuthInfoBeforeUpdate

recall auth_info_before_update (self : enforcements.AuthInfo) :
    enforcements.AuthInfo.before_update self = enforcements.AuthInfo.get_auth_tokens self

end AuthInfoBeforeUpdate

section AuthInfoAfterFinish
open std.thread.local
open Keystore2Verify.Externals
open enforcements.AuthInfo.after_finish.closure.Insts renaming
  CoreOpsFunctionFnOnceTupleShared1RefCellKeystoreDBResultTupleError → afterFinishOnce

recall auth_info_after_finish_unlimited (self : enforcements.AuthInfo)
    (h : self.key_usage_limited = none) :
    enforcements.AuthInfo.after_finish self = ok (.Ok ())

recall auth_info_after_finish_updated (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyCtxLaw root Unit)
    (self : enforcements.AuthInfo) (key_id : Std.I64)
    (lk : LocalKey (core.cell.RefCell database.KeystoreDB))
    (h : self.key_usage_limited = some key_id) (hdb : globals.DB = ok lk)
    (hwith : LocalKey.with afterFinishOnce lk key_id = ok (.Ok ())) :
    enforcements.AuthInfo.after_finish self = ok (.Ok ())

recall auth_info_after_finish_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyCtxLaw root Unit)
    (self : enforcements.AuthInfo) (key_id : Std.I64)
    (lk : LocalKey (core.cell.RefCell database.KeystoreDB))
    (e : anyhow.Error)
    (h : self.key_usage_limited = some key_id) (hdb : globals.DB = ok lk)
    (hwith : LocalKey.with afterFinishOnce lk key_id = ok (.Err e)) :
    ∃ e', enforcements.AuthInfo.after_finish self = ok (.Err e') ∧ root e' = root e

end AuthInfoAfterFinish

section AuthInfoGetAuthTokens
open alloc.sync.Arc.Insts.CoreOpsDerefDeref renaming deref → arcDeref
open Keystore2Verify.Externals
open android_hardware_security_keymint.aidl.android.hardware.security.keymint.ErrorCode.ErrorCode
  renaming KEY_USER_NOT_AUTHENTICATED → keyUserNotAuthenticated
open enforcements.DeferredAuthState

recall auth_info_get_auth_tokens_no_auth (self : enforcements.AuthInfo)
    (h : self.state = NoAuthRequired) :
    enforcements.AuthInfo.get_auth_tokens self = ok (.Ok (none, none), self)

recall auth_info_get_auth_tokens_token (hc : AuthTokenCloneSpec)
    (hc1 : OptionTimeStampCloneSpec)
    (self : enforcements.AuthInfo) (hat : AuthToken) (tst : Option TimeStamp)
    (h : self.state = Token hat tst) :
    enforcements.AuthInfo.get_auth_tokens self = ok (.Ok (some hat, tst), self)

recall auth_info_get_auth_tokens_waiting_ok (root : anyhow.Error → ErrRoot)
    (hctx : Permission.AnyhowStrCtxLaw root (AuthToken × Option TimeStamp))
    (hc : AuthTokenCloneSpec) (hc1 : OptionTimeStampCloneSpec)
    (self : enforcements.AuthInfo) (req : alloc.sync.Arc enforcements.AuthRequest)
    (ar : enforcements.AuthRequest) (hat : AuthToken) (tst : Option TimeStamp)
    (h : self.state = Waiting req)
    (hderef : arcDeref alloc.alloc.Global req = ok ar)
    (hget : enforcements.AuthRequest.get_auth_tokens ar = ok (.Ok (hat, tst))) :
    enforcements.AuthInfo.get_auth_tokens self
      = ok (.Ok (some hat, tst), { self with state := Token hat tst })

recall auth_info_get_auth_tokens_waiting_err (root : anyhow.Error → ErrRoot)
    (hctx : Permission.AnyhowStrCtxLaw root (AuthToken × Option TimeStamp))
    (self : enforcements.AuthInfo) (req : alloc.sync.Arc enforcements.AuthRequest)
    (ar : enforcements.AuthRequest) (e : anyhow.Error)
    (h : self.state = Waiting req)
    (hderef : arcDeref alloc.alloc.Global req = ok ar)
    (hget : enforcements.AuthRequest.get_auth_tokens ar = ok (.Err e)) :
    ∃ e', enforcements.AuthInfo.get_auth_tokens self = ok (.Err e', self) ∧
      root e' = root e

recall auth_info_get_auth_tokens_op_auth_required (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root (Option AuthToken × Option TimeStamp))
    (self : enforcements.AuthInfo) (sids : alloc.vec.Vec utils.SecureUserId)
    (ty : AuthType)
    (ec : KmErrorCode)
    (h : self.state = OpAuthRequired sids ty) (hec : keyUserNotAuthenticated = ok ec) :
    ∃ e, enforcements.AuthInfo.get_auth_tokens self = ok (.Err e, self) ∧
      root e = ErrRoot.ks (error.Error.Km ec)

recall auth_info_get_auth_tokens_timestamp_required (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root (Option AuthToken × Option TimeStamp))
    (self : enforcements.AuthInfo) (hat : AuthToken)
    (ec : KmErrorCode)
    (h : self.state = TimeStampRequired hat) (hec : keyUserNotAuthenticated = ok ec) :
    ∃ e, enforcements.AuthInfo.get_auth_tokens self = ok (.Err e, self) ∧
      root e = ErrRoot.ks (error.Error.Km ec)

end AuthInfoGetAuthTokens

section EnforcementsDefault
open std.hash.random
open std.collections.hash.map
open std.sync.poison
open std.collections.hash.set
open mutex.Mutex.Insts renaming CoreDefaultDefault → mutexDefaultInst
open mutex.Mutex.Insts.CoreDefaultDefault renaming default → mutexDefault
open rwlock.RwLock.Insts.CoreDefaultDefault renaming default → rwLockDefault
open core.option.Option.Insts renaming CoreDefaultDefault → optionDefaultInst
open alloc.sync.Arc.Insts.CoreDefaultDefault renaming default → arcDefault
open HashSetTSGlobal.Insts renaming CoreDefaultDefault → hashSetDefaultInst
open RandomState.Insts renaming CoreDefaultDefault → randomStateDefaultInst
open enforcements.TokenReceiverMap.Insts.CoreDefaultDefault renaming
  default → tokenReceiverMapDefault
open enforcements.Enforcements.Insts.CoreDefaultDefault renaming default → enforcementsDefault

recall enforcements_default
    (m : mutex.Mutex (HashSet utils.AndroidUserId RandomState alloc.alloc.Global))
    (rl : rwlock.RwLock (Option (alloc.sync.Arc async_task.AsyncTask)))
    (hm : HashMap utils.Challenge enforcements.TokenReceiver RandomState alloc.alloc.Global)
    (m2 : mutex.Mutex ((HashMap utils.Challenge enforcements.TokenReceiver
      RandomState alloc.alloc.Global) × Std.U8))
    (a : alloc.sync.Arc (mutex.Mutex (Option ByteReceiver)))
    (hmd : mutexDefault (hashSetDefaultInst utils.AndroidUserId randomStateDefaultInst) = ok m)
    (hrl : rwLockDefault (optionDefaultInst (alloc.sync.Arc async_task.AsyncTask)) = ok rl)
    (hnew : HashMapKVRandomStateGlobal.new utils.Challenge enforcements.TokenReceiver = ok hm)
    (hmutex : mutex.Mutex.new (hm, 26#u8) = ok m2)
    (ha : arcDefault (mutexDefaultInst (optionDefaultInst ByteReceiver)) = ok a) :
    enforcementsDefault
      = ok { device_unlocked_set := m, lock_state_task := rl,
             op_auth_map := { map_and_cleanup_counter := m2 },
             confirmation_token_receiver := a }

end EnforcementsDefault

section InstallConfirmationTokenReceiver
open alloc.sync.Arc.Insts.CoreOpsDerefDeref renaming deref → arcDeref
open std.sync.poison
open std.sync.poison.mutex
open MutexGuard.Insts
open CoreOpsDerefDerefMut renaming deref_mut → guardDerefMut

recall install_confirmation_token_receiver_ok (self : enforcements.Enforcements)
    (receiver : ByteReceiver)
    (m : Mutex (Option (ByteReceiver)))
    (g : MutexGuard (Option (ByteReceiver)))
    (x : Option (ByteReceiver) ×
      (Option (ByteReceiver) →
        MutexGuard (Option (ByteReceiver))))
    (hderef : arcDeref alloc.alloc.Global
      self.confirmation_token_receiver = ok m)
    (hlock : Mutex.lock m = ok (.Ok g)) (hmut : guardDerefMut g = ok x) :
    enforcements.Enforcements.install_confirmation_token_receiver self receiver = ok ()

recall install_confirmation_token_receiver_poisoned (self : enforcements.Enforcements)
    (receiver : ByteReceiver)
    (m : Mutex (Option (ByteReceiver)))
    (pe : PoisonError
      (MutexGuard (Option (ByteReceiver))))
    (hderef : arcDeref alloc.alloc.Global
      self.confirmation_token_receiver = ok m)
    (hlock : Mutex.lock m = ok (.Err pe)) :
    enforcements.Enforcements.install_confirmation_token_receiver self receiver
      = fail Error.panic

end InstallConfirmationTokenReceiver

section FindAuthToken
open core.ops.function
open std.thread.local
open enforcements.Enforcements.find_auth_token.closure.Insts renaming
  CoreOpsFunctionFnOnceTupleShared0RefCellKeystoreDBOptionAuthTokenEntry → findOnce

recall find_auth_token_with {F : Type}
    (hfn : Fn F database.AuthTokenEntry Bool) (p : F)
    (lk : LocalKey (core.cell.RefCell database.KeystoreDB))
    (r : Option database.AuthTokenEntry)
    (hdb : globals.DB = ok lk)
    (hwith : LocalKey.with (findOnce hfn) lk p = ok r) :
    enforcements.Enforcements.find_auth_token hfn p = ok r

end FindAuthToken

section IsGivenTimePassed
open std.time
open core.time

recall is_given_time_passed_inclusive (given_time : Std.I64)
    (st ep : SystemTime) (d : Duration) (ms : Std.U128)
    (hnow : SystemTime.now = ok st) (hep : SystemTime.UNIX_EPOCH = ok ep)
    (hdur : SystemTime.duration_since st ep = ok (.Ok d))
    (hms : Duration.as_millis d = ok ms) :
    enforcements.Enforcements.is_given_time_passed given_time true
      = ok (decide (ms ≥ IScalar.hcast .U128 given_time))

recall is_given_time_passed_exclusive (given_time : Std.I64)
    (st ep : SystemTime) (d : Duration) (ms : Std.U128)
    (hnow : SystemTime.now = ok st) (hep : SystemTime.UNIX_EPOCH = ok ep)
    (hdur : SystemTime.duration_since st ep = ok (.Ok d))
    (hms : Duration.as_millis d = ok ms) :
    enforcements.Enforcements.is_given_time_passed given_time false
      = ok (decide (ms > IScalar.hcast .U128 given_time))

recall is_given_time_passed_before_epoch (given_time : Std.I64) (inclusive : Bool)
    (st ep : SystemTime) (e : SystemTimeError)
    (hnow : SystemTime.now = ok st) (hep : SystemTime.UNIX_EPOCH = ok ep)
    (hdur : SystemTime.duration_since st ep = ok (.Err e)) :
    enforcements.Enforcements.is_given_time_passed given_time inclusive = ok false

end IsGivenTimePassed

section SetDeviceLocked
open std.sync.poison
open std.sync.poison.mutex
open MutexGuard.Insts
open CoreOpsDerefDerefMut renaming deref_mut → guardDerefMut

recall set_device_locked_poisoned (self : enforcements.Enforcements)
    (user : utils.AndroidUserId) (status : Bool)
    (pe : PoisonError (MutexGuard UserSet))
    (hlock : Mutex.lock self.device_unlocked_set = ok (.Err pe)) :
    enforcements.Enforcements.set_device_locked self user status = fail Error.panic

recall set_device_locked_locked (self : enforcements.Enforcements) (user : utils.AndroidUserId)
    (g : MutexGuard UserSet) (f : UserSet → MutexGuard UserSet) (hs : UserSet)
    (r : Bool × UserSet)
    (hlock : Mutex.lock self.device_unlocked_set = ok (.Ok g))
    (hmut : guardDerefMut g = ok (hs, f)) (hrem : userSetRemove hs user = ok r) :
    enforcements.Enforcements.set_device_locked self user true = ok ()

recall set_device_locked_unlocked (self : enforcements.Enforcements) (user : utils.AndroidUserId)
    (g : MutexGuard UserSet) (f : UserSet → MutexGuard UserSet) (hs : UserSet)
    (r : Bool × UserSet)
    (hlock : Mutex.lock self.device_unlocked_set = ok (.Ok g))
    (hmut : guardDerefMut g = ok (hs, f)) (hins : userSetInsert hs user = ok r) :
    enforcements.Enforcements.set_device_locked self user false = ok ()

end SetDeviceLocked

section RegisterOpAuthReceiver

recall register_op_auth_receiver_forwards (self : enforcements.Enforcements)
    (challenge : utils.Challenge) (recv : enforcements.TokenReceiver) (r : Unit)
    (hadd : enforcements.TokenReceiverMap.add_receiver self.op_auth_map challenge recv = ok r) :
    enforcements.Enforcements.register_op_auth_receiver self challenge recv = ok r

end RegisterOpAuthReceiver

section SuperEncryptionRequired
open android_system_keystore2.aidl.android.system.keystore2
open IKeystoreSecurityLevel renaming
  KEY_FLAG_AUTH_BOUND_WITHOUT_CRYPTOGRAPHIC_LSKF_BINDING → lskfFlag
open Domain.Domain renaming APP → domainApp
open Domain.Domain.Insts.CoreCmpPartialEqDomain renaming eq → domainEq

recall super_encryption_required_flag_set (domain : Domain.Domain)
    (key_parameters : Slice key_parameter.KeyParameter) (f k : Std.I32)
    (hk : lskfFlag = ok k) (hbit : (f &&& k) ≠ 0#i32) :
    enforcements.Enforcements.super_encryption_required domain key_parameters (some f)
      = ok super_key.SuperEncryptionType.None

recall super_encryption_required_no_flags_domain_free (domain : Domain.Domain)
    (key_parameters : Slice key_parameter.KeyParameter)
    (hfree : ∀ kp ∈ key_parameters.val, ¬ DomainDependent kp.value) :
    enforcements.Enforcements.super_encryption_required domain key_parameters none
      = ok (superEncChoose false key_parameters.val (0, super_key.SuperEncryptionType.None))

recall super_encryption_required_no_flags (domain : Domain.Domain)
    (key_parameters : Slice key_parameter.KeyParameter) (a : Domain.Domain) (isApp : Bool)
    (hdom : (∃ kp ∈ key_parameters.val, DomainDependent kp.value) →
      domainApp = ok a ∧ domainEq domain a = ok isApp) :
    enforcements.Enforcements.super_encryption_required domain key_parameters none
      = ok (superEncChoose isApp key_parameters.val (0, super_key.SuperEncryptionType.None))

recall super_encryption_required_flag_clear (domain : Domain.Domain)
    (key_parameters : Slice key_parameter.KeyParameter) (f k : Std.I32)
    (a : Domain.Domain) (isApp : Bool)
    (hk : lskfFlag = ok k) (hbit : (f &&& k) = 0#i32)
    (hdom : (∃ kp ∈ key_parameters.val, DomainDependent kp.value) →
      domainApp = ok a ∧ domainEq domain a = ok isApp) :
    enforcements.Enforcements.super_encryption_required domain key_parameters (some f)
      = ok (superEncChoose isApp key_parameters.val (0, super_key.SuperEncryptionType.None))

end SuperEncryptionRequired

section EnforcementsGetAuthTokens
open Keystore2Verify.Externals
open enforcements.Enforcements.get_auth_tokens
open closure.Insts renaming CoreOpsFunctionFnTupleShared3AuthTokenEntryBool → byChallenge
open closure_1.Insts renaming CoreOpsFunctionFnTupleShared4AuthTokenEntryBool → byAge
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open HardwareAuthenticatorType.HardwareAuthenticatorType renaming ANY → authTypeAny
open android_security_authorization.aidl.android.security.authorization.ResponseCode.ResponseCode
  renaming NO_AUTH_TOKEN_FOUND → noAuthTokenFound

recall enforcements_get_auth_tokens_by_challenge (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root TimeStamp)
    (self : enforcements.Enforcements) (challenge : utils.Challenge) (sid : utils.SecureUserId)
    (max_age : Std.I64) (any : HardwareAuthenticatorType.HardwareAuthenticatorType)
    (e : database.AuthTokenEntry) (tst : TimeStamp)
    (hany : authTypeAny = ok any)
    (hfind : enforcements.Enforcements.find_auth_token byChallenge (challenge, sidVec sid, any)
      = ok (some e))
    (hts : enforcements.get_timestamp_token challenge = ok (.Ok tst)) :
    enforcements.Enforcements.get_auth_tokens self challenge sid max_age
      = ok (.Ok (e.auth_token, tst))

recall enforcements_get_auth_tokens_by_challenge_clock_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root TimeStamp)
    (self : enforcements.Enforcements) (challenge : utils.Challenge) (sid : utils.SecureUserId)
    (max_age : Std.I64) (any : HardwareAuthenticatorType.HardwareAuthenticatorType)
    (e : database.AuthTokenEntry) (te : error.Error)
    (hany : authTypeAny = ok any)
    (hfind : enforcements.Enforcements.find_auth_token byChallenge (challenge, sidVec sid, any)
      = ok (some e))
    (hts : enforcements.get_timestamp_token challenge = ok (.Err te)) :
    ∃ e', enforcements.Enforcements.get_auth_tokens self challenge sid max_age = ok (.Err e') ∧
      root e' = ErrRoot.ks te

recall enforcements_get_auth_tokens_age_zero (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AuthzStringCtxAssumption root (AuthToken × TimeStamp))
    (self : enforcements.Enforcements) (challenge : utils.Challenge) (sid : utils.SecureUserId)
    (any : HardwareAuthenticatorType.HardwareAuthenticatorType)
    (rc : AuthzResponseCode)
    (hany : authTypeAny = ok any)
    (hfind : enforcements.Enforcements.find_auth_token byChallenge (challenge, sidVec sid, any)
      = ok none)
    (hrc : noAuthTokenFound = ok rc) :
    ∃ e, enforcements.Enforcements.get_auth_tokens self challenge sid 0#i64 = ok (.Err e) ∧
      root e = ErrRoot.other

recall enforcements_get_auth_tokens_not_found (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AuthzStringCtxAssumption root (AuthToken × TimeStamp))
    (self : enforcements.Enforcements) (challenge : utils.Challenge) (sid : utils.SecureUserId)
    (max_age : Std.I64) (any : HardwareAuthenticatorType.HardwareAuthenticatorType)
    (now : database.BootTime)
    (rc : AuthzResponseCode)
    (hmax : max_age ≠ 0#i64) (hany : authTypeAny = ok any)
    (hfind : enforcements.Enforcements.find_auth_token byChallenge (challenge, sidVec sid, any)
      = ok none)
    (hnow : database.BootTime.now = ok now)
    (hfind1 : enforcements.Enforcements.find_auth_token byAge (now, max_age, sidVec sid, any)
      = ok none)
    (hrc : noAuthTokenFound = ok rc) :
    ∃ e, enforcements.Enforcements.get_auth_tokens self challenge sid max_age = ok (.Err e) ∧
      root e = ErrRoot.other

recall enforcements_get_auth_tokens_by_age (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root TimeStamp)
    (self : enforcements.Enforcements) (challenge : utils.Challenge) (sid : utils.SecureUserId)
    (max_age : Std.I64) (any : HardwareAuthenticatorType.HardwareAuthenticatorType)
    (now : database.BootTime) (e : database.AuthTokenEntry) (tst : TimeStamp)
    (hmax : max_age ≠ 0#i64) (hany : authTypeAny = ok any)
    (hfind : enforcements.Enforcements.find_auth_token byChallenge (challenge, sidVec sid, any)
      = ok none)
    (hnow : database.BootTime.now = ok now)
    (hfind1 : enforcements.Enforcements.find_auth_token byAge (now, max_age, sidVec sid, any)
      = ok (some e))
    (hts : enforcements.get_timestamp_token challenge = ok (.Ok tst)) :
    enforcements.Enforcements.get_auth_tokens self challenge sid max_age
      = ok (.Ok (e.auth_token, tst))

recall enforcements_get_auth_tokens_by_age_clock_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root TimeStamp)
    (self : enforcements.Enforcements) (challenge : utils.Challenge) (sid : utils.SecureUserId)
    (max_age : Std.I64) (any : HardwareAuthenticatorType.HardwareAuthenticatorType)
    (now : database.BootTime) (e : database.AuthTokenEntry) (te : error.Error)
    (hmax : max_age ≠ 0#i64) (hany : authTypeAny = ok any)
    (hfind : enforcements.Enforcements.find_auth_token byChallenge (challenge, sidVec sid, any)
      = ok none)
    (hnow : database.BootTime.now = ok now)
    (hfind1 : enforcements.Enforcements.find_auth_token byAge (now, max_age, sidVec sid, any)
      = ok (some e))
    (hts : enforcements.get_timestamp_token challenge = ok (.Err te)) :
    ∃ e', enforcements.Enforcements.get_auth_tokens self challenge sid max_age = ok (.Err e') ∧
      root e' = ErrRoot.ks te

end EnforcementsGetAuthTokens

section GetLastAuthTime
open enforcements.Enforcements.get_last_auth_time.closure.Insts renaming
  CoreOpsFunctionFnTupleShared2AuthTokenEntryBool → lastAuthPredicate

recall get_last_auth_time_none (self : enforcements.Enforcements) (sid : utils.SecureUserId)
    (auth_type : AuthType)
    (hfind : enforcements.Enforcements.find_auth_token lastAuthPredicate (sid, auth_type)
      = ok none) :
    enforcements.Enforcements.get_last_auth_time self sid auth_type = ok none

recall get_last_auth_time_some (self : enforcements.Enforcements) (sid : utils.SecureUserId)
    (auth_type : AuthType)
    (e : database.AuthTokenEntry)
    (hfind : enforcements.Enforcements.find_auth_token lastAuthPredicate (sid, auth_type)
      = ok (some e)) :
    enforcements.Enforcements.get_last_auth_time self sid auth_type
      = ok (some e.time_received)

end GetLastAuthTime

end Keystore2Verify.Enforcements
