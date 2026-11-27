import Keystore2Verify.Proofs.Apc.Error
import Keystore2Verify.Proofs.Apc.GetRemainingBackOff
import Keystore2Verify.Proofs.Apc.ApcStateNew
import Keystore2Verify.Proofs.Apc.IsSupported

namespace Keystore2Verify.Apc
open Aeneas Aeneas.Std Result keystore2
open keystore2.android_security_apc.aidl.android.security.apc
open keystore2.std.collections.hash.map.HashMapKVSGlobal.Insts.CoreDefaultDefault
  renaming default → hashMapDefault
open keystore2.core.time.Duration
  renaming from_secs → durationFromSecs, checked_sub → durationCheckedSub,
    checked_mul → durationCheckedMul
open keystore2.std.time.Instant renaming elapsed → instantElapsed
open Aeneas.Std.core.option.Option renaming unwrap_or → optionUnwrapOr
open keystore2.std.sync.mpsc (Sender)
open keystore2.std.collections.hash.map (HashMap)
open keystore2.std.hash.random (RandomState)
open keystore2.std.hash.random.RandomState.Insts renaming CoreDefaultDefault → randomStateDefault

recall apc_error_sys_ok (c : ResponseCode.ResponseCode)
    (h :
      ResponseCode.ResponseCode.SYSTEM_ERROR = ok c) :
    apc.Error.sys = ok (apc.Error.Rc c)

recall apc_error_sys_fail (x : Error)
    (h :
      ResponseCode.ResponseCode.SYSTEM_ERROR = fail x) :
    apc.Error.sys = fail x

recall apc_error_pending_ok (c : ResponseCode.ResponseCode)
    (h :
      ResponseCode.ResponseCode.OPERATION_PENDING = ok c) :
    apc.Error.pending = ok (apc.Error.Rc c)

recall apc_error_pending_fail (x : Error)
    (h :
      ResponseCode.ResponseCode.OPERATION_PENDING = fail x) :
    apc.Error.pending = fail x

recall apc_error_ignored_ok (c : ResponseCode.ResponseCode)
    (h :
      ResponseCode.ResponseCode.IGNORED = ok c) :
    apc.Error.ignored = ok (apc.Error.Rc c)

recall apc_error_ignored_fail (x : Error)
    (h :
      ResponseCode.ResponseCode.IGNORED = fail x) :
    apc.Error.ignored = fail x

recall apc_error_unimplemented_ok (c : ResponseCode.ResponseCode)
    (h :
      ResponseCode.ResponseCode.UNIMPLEMENTED = ok c) :
    apc.Error.unimplemented = ok (apc.Error.Rc c)

recall apc_error_unimplemented_fail (x : Error)
    (h :
      ResponseCode.ResponseCode.UNIMPLEMENTED = fail x) :
    apc.Error.unimplemented = fail x

recall rate_info_one_day_eq :
    apc.RateInfo.ONE_DAY = durationFromSecs 86400#u64

recall rate_info_get_remaining_back_off_none (self : apc.RateInfo)
    (h : self.counter.val ≤ 2) :
    apc.RateInfo.get_remaining_back_off self = ok none

recall rate_info_get_remaining_back_off_3_to_5 (self : apc.RateInfo)
    (hlo : 3 ≤ self.counter.val) (hhi : self.counter.val ≤ 5)
    (back_off elapsed : core.time.Duration) (r : Option core.time.Duration)
    (hb : durationFromSecs 30#u64 = ok back_off)
    (he : instantElapsed self.timestamp = ok elapsed)
    (hs : durationCheckedSub back_off elapsed = ok r) :
    apc.RateInfo.get_remaining_back_off self = ok r

recall rate_info_get_remaining_back_off_6_to_16 (self : apc.RateInfo)
    (hlo : 6 ≤ self.counter.val) (hhi : self.counter.val ≤ 16)
    (base one_day elapsed : core.time.Duration) (r : Option core.time.Duration)
    (m : Std.U32)
    (o : Option core.time.Duration)
    (hm : m.val = 2 ^ (self.counter.val - 6))
    (hb : durationFromSecs 60#u64 = ok base)
    (hmul : durationCheckedMul base m = ok o)
    (hd : apc.RateInfo.ONE_DAY = ok one_day)
    (he : instantElapsed self.timestamp = ok elapsed)
    (hs : durationCheckedSub (optionUnwrapOr o one_day) elapsed
      = ok r) :
    apc.RateInfo.get_remaining_back_off self = ok r

recall rate_info_get_remaining_back_off_17_up (self : apc.RateInfo)
    (hlo : 17 ≤ self.counter.val)
    (one_day elapsed : core.time.Duration) (r : Option core.time.Duration)
    (hd : apc.RateInfo.ONE_DAY = ok one_day)
    (he : instantElapsed self.timestamp = ok elapsed)
    (hs : durationCheckedSub one_day elapsed = ok r) :
    apc.RateInfo.get_remaining_back_off self = ok r

recall apc_state_new_ok
    (sender : Sender (alloc.vec.Vec Std.U8))
    (hm : HashMap utils.AppUid apc.RateInfo
      RandomState alloc.alloc.Global)
    (h : hashMapDefault utils.AppUid apc.RateInfo
      randomStateDefault = ok hm) :
    apc.ApcState.new sender =
      ok { session := none, rate_limiting := hm, confirmation_token_sender := sender }

recall apc_state_new_fail
    (sender : Sender (alloc.vec.Vec Std.U8)) (x : Error)
    (h : hashMapDefault utils.AppUid apc.RateInfo
      randomStateDefault = fail x) :
    apc.ApcState.new sender = fail x

recall apc_manager_is_supported_ok (o : Option keystore2_apc_compat.ApcHal)
    (h : keystore2_apc_compat.ApcHal.try_get_service = ok o) :
    ∃ b, apc.ApcManager.is_supported = ok (.Ok b) ∧ (b = true ↔ o ≠ none)

recall apc_manager_is_supported_fail (x : Error)
    (h : keystore2_apc_compat.ApcHal.try_get_service = fail x) :
    apc.ApcManager.is_supported = fail x

end Keystore2Verify.Apc
