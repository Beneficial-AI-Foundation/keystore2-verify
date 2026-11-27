import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open std.time
open core.time.Duration renaming checked_sub → durationCheckedSub
open database.TryIntoDateTimeSystemTimeDateTimeError.try_into.closure.Insts
  renaming CoreOpsFunctionFnOnceTupleDurationOptionSystemTime → fnOnceSub
open database.TryIntoDateTimeSystemTimeDateTimeError.try_into.closure_1.Insts
  renaming CoreOpsFunctionFnOnceTupleDurationOptionSystemTime → fnOnceAdd
open database.DateTime.Insts
open CoreCloneClone renaming clone → dateTimeClone
open CoreCmpPartialEqDateTime renaming eq → dateTimeEq
open CoreCmpOrd renaming cmp → dateTimeCmp
open CoreCmpPartialOrdDateTime renaming partial_cmp → dateTimePartialCmp
open CoreDefaultDefault renaming default → dateTimeDefault
open CoreConvertTryFromSystemTimeDateTimeError renaming try_from → dateTimeTryFrom
open CoreConvertTryIntoSystemTimeDateTimeError renaming try_into → dateTimeTryInto
open database.DateTime renaming now → dateTimeNow
open database.DateTime renaming from_millis_epoch → dateTimeFromMillis
open database.DateTime renaming to_millis_epoch → dateTimeToMillis

/-- exact: `clone` never fails and returns its argument. -/
theorem date_time_clone (x : database.DateTime) : dateTimeClone x = ok x := by
  sorry

/-- exact: `default` never fails and returns the time 0 (the Unix epoch). -/
theorem date_time_default : dateTimeDefault = ok 0#i64 := by
  sorry

/-- exact: `eq` never fails. It returns `true` exactly when the two millisecond counts are
equal. -/
theorem date_time_eq (a b : database.DateTime) :
    ∃ r, dateTimeEq a b = ok r ∧ (r = true ↔ a = b) := by
  sorry

/-- exact: `cmp` never fails. It compares the two millisecond counts as signed numbers. -/
theorem date_time_cmp (a b : database.DateTime) :
    dateTimeCmp a b = ok (compare a.val b.val) := by
  sorry

/-- exact: `partial_cmp` never fails and returns `Some` of the result of `cmp`. -/
theorem date_time_partial_cmp (a b : database.DateTime) :
    dateTimePartialCmp a b = ok (some (compare a.val b.val)) := by
  sorry

/-- exact: `from_millis_epoch` never fails and stores the number as it is. -/
theorem date_time_from_millis_epoch (m : Std.I64) : dateTimeFromMillis m = ok m := by
  sorry

/-- exact: `to_millis_epoch` never fails and returns the stored number. -/
theorem date_time_to_millis_epoch (d : database.DateTime) : dateTimeToMillis d = ok d := by
  sorry

/-- conditional: `DateTime::try_from(SystemTime)` for a time `t` before the Unix epoch returns the
error `SystemTimeError`. Observations: `nanos` and `dnanos` (see the assumptions).
Hypotheses: `UnixEpochSpec`, `DurationSinceSpec`. -/
theorem date_time_try_from_before_epoch (nanos : SystemTime → Int)
    (dnanos : core.time.Duration → Nat) (hep : UnixEpochSpec nanos)
    (hds : DurationSinceSpec nanos dnanos) (t : SystemTime)
    (hneg : nanos t < 0) :
    ∃ e, dateTimeTryFrom t = ok (.Err (.SystemTimeError e)) := by
  sorry

/-- conditional: `DateTime::try_from(SystemTime)` for a time `t` at or after the Unix epoch whose
millisecond count fits in an `i64` returns that count, rounded down. Hypotheses:
`UnixEpochSpec`, `DurationSinceSpec`, `DurationAsMillisSpec`,
`I64TryFromU128Spec`. -/
theorem date_time_try_from_ok (nanos : SystemTime → Int)
    (dnanos : core.time.Duration → Nat) (hep : UnixEpochSpec nanos)
    (hds : DurationSinceSpec nanos dnanos) (hms : DurationAsMillisSpec dnanos)
    (hc : I64TryFromU128Spec) (t : SystemTime)
    (h0 : 0 ≤ nanos t) (hfit : nanos t / 1000000 ≤ Std.I64.max) :
    ∃ v, dateTimeTryFrom t = ok (.Ok v) ∧ v.val = nanos t / 1000000 := by
  sorry

/-- conditional: `DateTime::try_from(SystemTime)` for a time at or after the Unix epoch whose
millisecond count does not fit in an `i64` returns the error `TypeConversion`. Hypotheses: the
same as for `date_time_try_from_ok`. -/
theorem date_time_try_from_overflow (nanos : SystemTime → Int)
    (dnanos : core.time.Duration → Nat) (hep : UnixEpochSpec nanos)
    (hds : DurationSinceSpec nanos dnanos) (hms : DurationAsMillisSpec dnanos)
    (hc : I64TryFromU128Spec) (t : SystemTime)
    (h0 : 0 ≤ nanos t) (hbig : Std.I64.max < nanos t / 1000000) :
    ∃ e, dateTimeTryFrom t = ok (.Err (.TypeConversion e)) := by
  sorry

/-- conditional: `DateTime::now`, when `SystemTime::now` returned `t` before the Unix epoch,
returns the error `SystemTimeError`. Hypotheses: `SystemTime::now` returned `t`,
`UnixEpochSpec`, `DurationSinceSpec`. -/
theorem date_time_now_before_epoch (nanos : SystemTime → Int)
    (dnanos : core.time.Duration → Nat) (hep : UnixEpochSpec nanos)
    (hds : DurationSinceSpec nanos dnanos) (t : SystemTime)
    (hnow : SystemTime.now = ok t) (hneg : nanos t < 0) :
    ∃ e, dateTimeNow = ok (.Err (.SystemTimeError e)) := by
  sorry

/-- conditional: `DateTime::now`, when `SystemTime::now` returned `t` at or after the Unix epoch
with a millisecond count that fits in an `i64`, returns that count, rounded down. Hypotheses:
`SystemTime::now` returned `t`, and the four assumptions of `date_time_try_from_ok`. -/
theorem date_time_now_ok (nanos : SystemTime → Int)
    (dnanos : core.time.Duration → Nat) (hep : UnixEpochSpec nanos)
    (hds : DurationSinceSpec nanos dnanos) (hms : DurationAsMillisSpec dnanos)
    (hc : I64TryFromU128Spec) (t : SystemTime)
    (hnow : SystemTime.now = ok t) (h0 : 0 ≤ nanos t)
    (hfit : nanos t / 1000000 ≤ Std.I64.max) :
    ∃ v, dateTimeNow = ok (.Ok v) ∧ v.val = nanos t / 1000000 := by
  sorry

/-- conditional: `DateTime::now`, when `SystemTime::now` returned `t` at or after the Unix epoch
with a millisecond count that does not fit in an `i64`, returns the error `TypeConversion`.
Hypotheses: as for `date_time_now_ok`. -/
theorem date_time_now_overflow (nanos : SystemTime → Int)
    (dnanos : core.time.Duration → Nat) (hep : UnixEpochSpec nanos)
    (hds : DurationSinceSpec nanos dnanos) (hms : DurationAsMillisSpec dnanos)
    (hc : I64TryFromU128Spec) (t : SystemTime)
    (hnow : SystemTime.now = ok t) (h0 : 0 ≤ nanos t)
    (hbig : Std.I64.max < nanos t / 1000000) :
    ∃ e, dateTimeNow = ok (.Err (.TypeConversion e)) := by
  sorry

/-- conditional: `TryInto<SystemTime> for DateTime`, when `SystemTime::now` returned `t` before
the Unix epoch, returns the error `SystemTimeError` for every `DateTime`. Hypotheses:
`SystemTime::now` returned `t`, `UnixEpochSpec`, `DurationSinceSpec`. -/
theorem date_time_try_into_before_epoch (nanos : SystemTime → Int)
    (dnanos : core.time.Duration → Nat) (hep : UnixEpochSpec nanos)
    (hds : DurationSinceSpec nanos dnanos) (t : SystemTime)
    (hnow : SystemTime.now = ok t) (hneg : nanos t < 0) (d : database.DateTime) :
    ∃ e, dateTimeTryInto d = ok (.Err (.SystemTimeError e)) := by
  sorry

/-- conditional: `TryInto<SystemTime> for DateTime` of a negative time, when `SystemTime::now`
returned `t` at or after the Unix epoch, returns the error `TypeConversion`. Hypotheses:
`SystemTime::now` returned `t`, `UnixEpochSpec`, `DurationSinceSpec`,
`U64TryFromI64Spec`. -/
theorem date_time_try_into_negative (nanos : SystemTime → Int)
    (dnanos : core.time.Duration → Nat) (hep : UnixEpochSpec nanos)
    (hds : DurationSinceSpec nanos dnanos) (hu : U64TryFromI64Spec)
    (t : SystemTime) (hnow : SystemTime.now = ok t) (h0 : 0 ≤ nanos t)
    (d : database.DateTime) (hd : d.val < 0) :
    ∃ e, dateTimeTryInto d = ok (.Err (.TypeConversion e)) := by
  sorry

/-- conditional: `TryInto<SystemTime> for DateTime`, when the stored time `d` is not negative,
the clock `t` is at or after the Unix epoch and `d` is earlier than `t` (the branch `now_epoch >
then_epoch`), returns the time `now - (now_epoch - then_epoch)`, that is the time of `d` itself,
`d` milliseconds after the epoch. Hypotheses: `SystemTime::now` returned `t`; the assumptions
`UnixEpochSpec`, `DurationSinceSpec`, `U64TryFromI64Spec`, `DurationFromMillisSpec`,
`DurationPartialCmpSpec`, `DurationCheckedSubSpec`, `OptionAndThenSpec` for the closure,
`SystemTimeCheckedSubSpec`; and that `SystemTime::checked_sub` of `t` by the duration
`now_epoch - then_epoch` (the one computed difference, `nanos t - d * 10^6` nanoseconds) returns a
time (the subtraction does not overflow). -/
theorem date_time_try_into_earlier
    (nanos : SystemTime → Int) (dnanos : core.time.Duration → Nat)
    (hep : UnixEpochSpec nanos) (hds : DurationSinceSpec nanos dnanos)
    (hu : U64TryFromI64Spec) (hfm : DurationFromMillisSpec dnanos)
    (hpc : DurationPartialCmpSpec dnanos)
    (hcs : DurationCheckedSubSpec dnanos) (hand : OptionAndThenSpec fnOnceSub)
    (hsub : SystemTimeCheckedSubSpec nanos dnanos)
    (t : SystemTime) (hnow : SystemTime.now = ok t) (h0 : 0 ≤ nanos t)
    (d : database.DateTime) (hd : 0 ≤ d.val) (hlt : d.val * 1000000 < nanos t)
    (hok : ∀ dd, (dnanos dd : Int) = nanos t - d.val * 1000000 →
      ∃ t', SystemTime.checked_sub t dd = ok (some t')) :
    ∃ t', dateTimeTryInto d = ok (.Ok t') ∧ nanos t' = d.val * 1000000 := by
  sorry

/-- conditional: as `date_time_try_into_earlier`, but the stored time `d` is not earlier than the
clock (`then_epoch >= now_epoch`, including equality, which takes this branch). The result is
`now + (then_epoch - now_epoch)`, that is the time of `d` itself. Hypotheses: as for
`date_time_try_into_earlier`, with `DurationCheckedSubSpec`, `OptionAndThenSpec` for the second
closure and `SystemTimeCheckedAddSpec`; and that `SystemTime::checked_add` of `t` by the duration
`then_epoch - now_epoch` (the one computed difference, `d * 10^6 - nanos t` nanoseconds) returns
a time. -/
theorem date_time_try_into_not_earlier
    (nanos : SystemTime → Int) (dnanos : core.time.Duration → Nat)
    (hep : UnixEpochSpec nanos) (hds : DurationSinceSpec nanos dnanos)
    (hu : U64TryFromI64Spec) (hfm : DurationFromMillisSpec dnanos)
    (hpc : DurationPartialCmpSpec dnanos)
    (hcs : DurationCheckedSubSpec dnanos) (hand : OptionAndThenSpec fnOnceAdd)
    (hadd : SystemTimeCheckedAddSpec nanos dnanos)
    (t : SystemTime) (hnow : SystemTime.now = ok t) (h0 : 0 ≤ nanos t)
    (d : database.DateTime) (hd : 0 ≤ d.val) (hge : nanos t ≤ d.val * 1000000)
    (hok : ∀ dd, (dnanos dd : Int) = d.val * 1000000 - nanos t →
      ∃ t', SystemTime.checked_add t dd = ok (some t')) :
    ∃ t', dateTimeTryInto d = ok (.Ok t') ∧ nanos t' = d.val * 1000000 := by
  sorry

/-- conditional: in the branch `now_epoch > then_epoch` (the stored time is earlier than the
clock), `TryInto<SystemTime> for DateTime` returns the error `TimeArithmetic` when
`SystemTime::checked_sub` returns `None`. Hypotheses: as for `date_time_try_into_earlier`, without
`SystemTimeCheckedSubSpec`, and with the outcome that `SystemTime::checked_sub` of `t` by the
computed difference returns `None`. -/
theorem date_time_try_into_earlier_overflow
    (nanos : SystemTime → Int) (dnanos : core.time.Duration → Nat)
    (hep : UnixEpochSpec nanos) (hds : DurationSinceSpec nanos dnanos)
    (hu : U64TryFromI64Spec) (hfm : DurationFromMillisSpec dnanos)
    (hpc : DurationPartialCmpSpec dnanos)
    (hcs : DurationCheckedSubSpec dnanos) (hand : OptionAndThenSpec fnOnceSub)
    (t : SystemTime) (hnow : SystemTime.now = ok t) (h0 : 0 ≤ nanos t)
    (d : database.DateTime) (hd : 0 ≤ d.val) (hlt : d.val * 1000000 < nanos t)
    (hnone : ∀ dd, (dnanos dd : Int) = nanos t - d.val * 1000000 →
      SystemTime.checked_sub t dd = ok none) :
    dateTimeTryInto d = ok (.Err .TimeArithmetic) := by
  sorry

/-- conditional: in the branch `now_epoch <= then_epoch` (equality included),
`TryInto<SystemTime> for DateTime` returns the error `TimeArithmetic` when
`SystemTime::checked_add` returns `None`. Hypotheses: as for `date_time_try_into_not_earlier`,
without `SystemTimeCheckedAddSpec`, and with the outcome that `SystemTime::checked_add` of `t` by
the computed difference returns `None`. -/
theorem date_time_try_into_not_earlier_overflow
    (nanos : SystemTime → Int) (dnanos : core.time.Duration → Nat)
    (hep : UnixEpochSpec nanos) (hds : DurationSinceSpec nanos dnanos)
    (hu : U64TryFromI64Spec) (hfm : DurationFromMillisSpec dnanos)
    (hpc : DurationPartialCmpSpec dnanos)
    (hcs : DurationCheckedSubSpec dnanos) (hand : OptionAndThenSpec fnOnceAdd)
    (t : SystemTime) (hnow : SystemTime.now = ok t) (h0 : 0 ≤ nanos t)
    (d : database.DateTime) (hd : 0 ≤ d.val) (hge : nanos t ≤ d.val * 1000000)
    (hnone : ∀ dd, (dnanos dd : Int) = d.val * 1000000 - nanos t →
      SystemTime.checked_add t dd = ok none) :
    dateTimeTryInto d = ok (.Err .TimeArithmetic) := by
  sorry

/-- conditional: in the branch `now_epoch > then_epoch`, `TryInto<SystemTime> for DateTime`
returns the error `TimeArithmetic` when `Duration::checked_sub` of the two durations returns
`None`. In the Rust source, the closure is not run when duration subtraction returns `None`.
Hypotheses: `SystemTime::now` returned `t`; `UnixEpochSpec`, `DurationSinceSpec`,
`U64TryFromI64Spec`, `DurationFromMillisSpec`, `DurationPartialCmpSpec` and `OptionAndThenSpec`
for the first closure; `t` is at or after the epoch; `d` is not negative and earlier than `t`;
and `Duration::checked_sub` of `now_epoch` and `then_epoch` (given by their nanoseconds) returns
`None`. Neither `DurationCheckedSubSpec` nor a `SystemTime` arithmetic assumption is used. In the
real library this return is not possible in this branch, since `now_epoch` is the larger
duration. -/
theorem date_time_try_into_earlier_duration_none
    (nanos : SystemTime → Int) (dnanos : core.time.Duration → Nat)
    (hep : UnixEpochSpec nanos) (hds : DurationSinceSpec nanos dnanos)
    (hu : U64TryFromI64Spec) (hfm : DurationFromMillisSpec dnanos)
    (hpc : DurationPartialCmpSpec dnanos)
    (hand : OptionAndThenSpec fnOnceSub)
    (t : SystemTime) (hnow : SystemTime.now = ok t) (h0 : 0 ≤ nanos t)
    (d : database.DateTime) (hd : 0 ≤ d.val) (hlt : d.val * 1000000 < nanos t)
    (hnone : ∀ a b, dnanos a = nanos t → dnanos b = d.val * 1000000 →
      durationCheckedSub a b = ok none) :
    dateTimeTryInto d = ok (.Err .TimeArithmetic) := by
  sorry

/-- conditional: in the branch `now_epoch <= then_epoch` (equality included),
`TryInto<SystemTime> for DateTime` returns the error `TimeArithmetic` when `Duration::checked_sub`
of `then_epoch` and `now_epoch` returns `None`. This theorem uses the second closure and the
reversed duration difference. In the Rust source, the closure is not run when duration subtraction
returns `None`. Hypotheses: `SystemTime::now` returned `t`; `UnixEpochSpec`, `DurationSinceSpec`,
`U64TryFromI64Spec`, `DurationFromMillisSpec`, `DurationPartialCmpSpec` and `OptionAndThenSpec`
for the second closure; `t` is at or after the epoch; `d` is not negative and not earlier than
`t`; and `Duration::checked_sub` of `then_epoch` and `now_epoch` returns `None`. Neither
`DurationCheckedSubSpec` nor a `SystemTime` arithmetic assumption is used. In the real library
this return is not possible in this branch. -/
theorem date_time_try_into_not_earlier_duration_none
    (nanos : SystemTime → Int) (dnanos : core.time.Duration → Nat)
    (hep : UnixEpochSpec nanos) (hds : DurationSinceSpec nanos dnanos)
    (hu : U64TryFromI64Spec) (hfm : DurationFromMillisSpec dnanos)
    (hpc : DurationPartialCmpSpec dnanos)
    (hand : OptionAndThenSpec fnOnceAdd)
    (t : SystemTime) (hnow : SystemTime.now = ok t) (h0 : 0 ≤ nanos t)
    (d : database.DateTime) (hd : 0 ≤ d.val) (hge : nanos t ≤ d.val * 1000000)
    (hnone : ∀ a b, dnanos a = d.val * 1000000 → dnanos b = nanos t →
      durationCheckedSub a b = ok none) :
    dateTimeTryInto d = ok (.Err .TimeArithmetic) := by
  sorry
