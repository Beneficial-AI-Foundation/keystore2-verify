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

/-- exact: `ONE_DAY` is the duration of `60 * 60 * 24 = 86400` seconds: the products do not
overflow, and the value is `Duration::from_secs 86400`. -/
theorem rate_info_one_day_eq :
    apc.RateInfo.ONE_DAY = durationFromSecs 86400#u64 := by
  sorry

/-- exact: with at most 2 failed attempts there is no back-off: the result is `None`. In the Rust
source this path returns before the clock is read. -/
theorem rate_info_get_remaining_back_off_none (self : apc.RateInfo)
    (h : self.counter.val ≤ 2) :
    apc.RateInfo.get_remaining_back_off self = ok none := by
  sorry

/-- conditional: with 3 to 5 failed attempts the back-off is 30 seconds, and the result is what
`checked_sub` returns for it and the time elapsed since `self.timestamp`: `Some` of the remaining
time, or `None` once the back-off has elapsed (`r` is any `Option`, so both are covered).
Hypotheses: the counter range, and the outcomes of `from_secs 30`, `elapsed` and `checked_sub`. -/
theorem rate_info_get_remaining_back_off_3_to_5 (self : apc.RateInfo)
    (hlo : 3 ≤ self.counter.val) (hhi : self.counter.val ≤ 5)
    (back_off elapsed : core.time.Duration) (r : Option core.time.Duration)
    (hb : durationFromSecs 30#u64 = ok back_off)
    (he : instantElapsed self.timestamp = ok elapsed)
    (hs : durationCheckedSub back_off elapsed = ok r) :
    apc.RateInfo.get_remaining_back_off self = ok r := by
  sorry

/-- conditional: with 6 to 16 failed attempts the back-off is 60 seconds times `2 ^ (counter - 6)`,
or `ONE_DAY` if that product is `None`. The result is what `checked_sub` returns for it and the
time elapsed since `self.timestamp`, `Some` or `None`.
Hypotheses: the counter range; the outcomes of `from_secs
60` and of `checked_mul` with the multiplier `m = 2 ^ (counter - 6)`; the value of `ONE_DAY`,
which the generated code reads on this path whether or not it is used; and the outcomes of
`elapsed` and `checked_sub`. -/
theorem rate_info_get_remaining_back_off_6_to_16 (self : apc.RateInfo)
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
    apc.RateInfo.get_remaining_back_off self = ok r := by
  sorry

/-- conditional: with 17 or more failed attempts the back-off is `ONE_DAY`, and the result is what
`checked_sub` returns for it and the time elapsed since `self.timestamp`: `Some` of the remaining
time, or `None` once the back-off has elapsed (`r` is any `Option`, so both are covered).
Hypotheses: the counter range, and the outcomes of `ONE_DAY`, `elapsed` and `checked_sub`. -/
theorem rate_info_get_remaining_back_off_17_up (self : apc.RateInfo)
    (hlo : 17 ≤ self.counter.val)
    (one_day elapsed : core.time.Duration) (r : Option core.time.Duration)
    (hd : apc.RateInfo.ONE_DAY = ok one_day)
    (he : instantElapsed self.timestamp = ok elapsed)
    (hs : durationCheckedSub one_day elapsed = ok r) :
    apc.RateInfo.get_remaining_back_off self = ok r := by
  sorry

end Keystore2Verify.Apc
