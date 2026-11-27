import Keystore2Verify.Specs.Defs.Externals

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

/-- conditional: if `HashMap::default` returns the map `hm`, then `ApcState::new` returns a state
with no session, the rate-limiting map `hm`, and the given sender unchanged. Hypothesis: the
outcome of `HashMap::default` with the default `RandomState`. Nothing is said about the contents
of `hm`. -/
theorem apc_state_new_ok
    (sender : Sender (alloc.vec.Vec Std.U8))
    (hm : HashMap utils.AppUid apc.RateInfo
      RandomState alloc.alloc.Global)
    (h : hashMapDefault utils.AppUid apc.RateInfo
      randomStateDefault = ok hm) :
    apc.ApcState.new sender =
      ok { session := none, rate_limiting := hm, confirmation_token_sender := sender } := by
  sorry

/-- conditional: if `HashMap::default` fails with `x`, `ApcState::new` fails with `x`. Hypothesis:
the outcome of `HashMap::default`. -/
theorem apc_state_new_fail
    (sender : Sender (alloc.vec.Vec Std.U8)) (x : Error)
    (h : hashMapDefault utils.AppUid apc.RateInfo
      randomStateDefault = fail x) :
    apc.ApcState.new sender = fail x := by
  sorry

end Keystore2Verify.Apc
