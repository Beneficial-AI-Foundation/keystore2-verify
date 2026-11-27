import Keystore2Verify.Specs.Defs.Enforcements

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2
open std.time
open core.time

/-! The cast `IScalar.hcast .U128 given_time` is Rust's `given_time as u128`: a negative time
becomes `2^128` plus the time, so it is larger than every clock reading. -/

/-- conditional: if the clock is at or after the epoch and the flag is set, `is_given_time_passed`
returns whether the milliseconds since the epoch are at least the given time. Hypotheses: the
outcomes of `SystemTime::now` (it returns `st`), of `SystemTime::UNIX_EPOCH` (it returns `ep`), of
`duration_since` on them (it returns `Ok d`) and of `Duration::as_millis` on `d` (it returns
`ms`). -/
theorem is_given_time_passed_inclusive (given_time : Std.I64)
    (st ep : SystemTime) (d : Duration) (ms : Std.U128)
    (hnow : SystemTime.now = ok st) (hep : SystemTime.UNIX_EPOCH = ok ep)
    (hdur : SystemTime.duration_since st ep = ok (.Ok d))
    (hms : Duration.as_millis d = ok ms) :
    enforcements.Enforcements.is_given_time_passed given_time true
      = ok (decide (ms ≥ IScalar.hcast .U128 given_time)) := by
  sorry

/-- conditional: if the clock is at or after the epoch and the flag is clear,
`is_given_time_passed` returns whether the milliseconds since the epoch are greater than the given
time. Hypotheses: those of `is_given_time_passed_inclusive`. -/
theorem is_given_time_passed_exclusive (given_time : Std.I64)
    (st ep : SystemTime) (d : Duration) (ms : Std.U128)
    (hnow : SystemTime.now = ok st) (hep : SystemTime.UNIX_EPOCH = ok ep)
    (hdur : SystemTime.duration_since st ep = ok (.Ok d))
    (hms : Duration.as_millis d = ok ms) :
    enforcements.Enforcements.is_given_time_passed given_time false
      = ok (decide (ms > IScalar.hcast .U128 given_time)) := by
  sorry

/-- conditional: if the clock is before the epoch, `is_given_time_passed` returns `false`, for both
values of the flag. In the Rust source this path returns before `as_millis` is called. Hypotheses:
the outcomes of `SystemTime::now` (it returns `st`), of `SystemTime::UNIX_EPOCH` (it returns `ep`)
and of `duration_since` on them (it returns `Err e`). -/
theorem is_given_time_passed_before_epoch (given_time : Std.I64) (inclusive : Bool)
    (st ep : SystemTime) (e : SystemTimeError)
    (hnow : SystemTime.now = ok st) (hep : SystemTime.UNIX_EPOCH = ok ep)
    (hdur : SystemTime.duration_since st ep = ok (.Err e)) :
    enforcements.Enforcements.is_given_time_passed given_time inclusive = ok false := by
  sorry
