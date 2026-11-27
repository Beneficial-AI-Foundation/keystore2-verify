import Keystore2Verify.Specs.Defs.MetricsStore

namespace Keystore2Verify.MetricsStore
open Aeneas Aeneas.Std Result keystore2

/-- exact: if `val ≤ no_round_threshold`, `round_logarithmic` returns `val` unchanged, read as an
`i64`. It does not fail. The cast is a wrapping cast: a `val` above `i64::MAX` gives the negative
number `val - 2^64`. -/
theorem round_logarithmic_below (val : Std.U64) (buckets_per_decade : Std.U32)
    (min_step no_round_threshold : Std.U64) (h : val.val ≤ no_round_threshold.val) :
    ∃ r, metrics_store.round_logarithmic val buckets_per_decade min_step no_round_threshold =
        ok r ∧
      r.val = if val.val ≤ 2 ^ 63 - 1 then (val.val : Int) else (val.val : Int) - 2 ^ 64 := by
  sorry

/-- conditional: if `val > no_round_threshold`, `val < 10^19`, the step is not 0 and `val` plus
half the step fits in a `u64`, then `round_logarithmic` returns `val` rounded to the nearest
multiple of the step (halves round up), capped at `i64::MAX` (`roundLogRounded`). Hypotheses:
the assumptions about `u64::ilog10` and `u64::pow`, `buckets_per_decade ≠ 0`, and the three
numeric conditions. -/
theorem round_logarithmic_rounded (hil : U64Ilog10Spec) (hpow : U64PowSpec)
    (val : Std.U64) (buckets_per_decade : Std.U32) (min_step no_round_threshold : Std.U64)
    (hgt : no_round_threshold.val < val.val) (hval : val.val < 10 ^ 19)
    (hb : 0 < buckets_per_decade.val)
    (hstep : 0 < roundLogStep val.val buckets_per_decade.val min_step.val)
    (hsum : val.val + roundLogStep val.val buckets_per_decade.val min_step.val / 2 < 2 ^ 64) :
    ∃ r, metrics_store.round_logarithmic val buckets_per_decade min_step no_round_threshold =
        ok r ∧
      r.val = (min (roundLogRounded val.val buckets_per_decade.val min_step.val)
        (2 ^ 63 - 1) : Nat) := by
  sorry

/-- conditional: if `val > no_round_threshold`, `val < 10^19` and `buckets_per_decade = 0`,
`round_logarithmic` fails with a division by zero. Hypotheses: the assumptions about
`u64::ilog10` and `u64::pow`. -/
theorem round_logarithmic_zero_buckets (hil : U64Ilog10Spec) (hpow : U64PowSpec)
    (val : Std.U64) (buckets_per_decade : Std.U32) (min_step no_round_threshold : Std.U64)
    (hgt : no_round_threshold.val < val.val) (hval : val.val < 10 ^ 19)
    (hb : buckets_per_decade.val = 0) :
    metrics_store.round_logarithmic val buckets_per_decade min_step no_round_threshold =
      fail Error.divisionByZero := by
  sorry

/-- conditional: if `val > no_round_threshold`, `val < 10^19`, `buckets_per_decade ≠ 0` and the step
is 0 (`min_step = 0` and `10^(e+1) < buckets_per_decade`), `round_logarithmic` fails with a
division by zero. Hypotheses: the assumptions about `u64::ilog10` and `u64::pow`. -/
theorem round_logarithmic_zero_step (hil : U64Ilog10Spec) (hpow : U64PowSpec)
    (val : Std.U64) (buckets_per_decade : Std.U32) (min_step no_round_threshold : Std.U64)
    (hgt : no_round_threshold.val < val.val) (hval : val.val < 10 ^ 19)
    (hb : 0 < buckets_per_decade.val)
    (hstep : roundLogStep val.val buckets_per_decade.val min_step.val = 0) :
    metrics_store.round_logarithmic val buckets_per_decade min_step no_round_threshold =
      fail Error.divisionByZero := by
  sorry

/-- conditional: if `val > no_round_threshold`, `val < 10^19`, the step is not 0 and `val` plus half
the step does not fit in a `u64`, `round_logarithmic` fails with an integer overflow.
Hypotheses: the assumptions about `u64::ilog10` and `u64::pow`, and `buckets_per_decade ≠ 0`. -/
theorem round_logarithmic_sum_overflow (hil : U64Ilog10Spec) (hpow : U64PowSpec)
    (val : Std.U64) (buckets_per_decade : Std.U32) (min_step no_round_threshold : Std.U64)
    (hgt : no_round_threshold.val < val.val) (hval : val.val < 10 ^ 19)
    (hb : 0 < buckets_per_decade.val)
    (hstep : 0 < roundLogStep val.val buckets_per_decade.val min_step.val)
    (hsum : 2 ^ 64 ≤ val.val + roundLogStep val.val buckets_per_decade.val min_step.val / 2) :
    metrics_store.round_logarithmic val buckets_per_decade min_step no_round_threshold =
      fail Error.integerOverflow := by
  sorry

/-- conditional: if `val > no_round_threshold` and `val ≥ 10^19`, then `10^(e+1)` with `e = 19`
does not fit in a `u64`, and `round_logarithmic` fails. Hypotheses: the assumptions about
`u64::ilog10` and `u64::pow` (the second one is a target assumption for the overflow). -/
theorem round_logarithmic_pow_overflow (hil : U64Ilog10Spec) (hpow : U64PowSpec)
    (val : Std.U64) (buckets_per_decade : Std.U32) (min_step no_round_threshold : Std.U64)
    (hgt : no_round_threshold.val < val.val) (hval : 10 ^ 19 ≤ val.val) :
    ∃ x, metrics_store.round_logarithmic val buckets_per_decade min_step no_round_threshold =
      fail x := by
  sorry

end Keystore2Verify.MetricsStore
