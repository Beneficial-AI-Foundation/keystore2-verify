import Keystore2Verify.Specs.Defs.MetricsStore

namespace Keystore2Verify.MetricsStore
open Aeneas Aeneas.Std Result keystore2

/-- conditional: `round_latency` never fails and returns `roundLatencyNat n`, where `n` is the
number of whole milliseconds of the duration (`millis`): `n` is capped at `i32::MAX`, then rounded
to the nearest multiple of 5 (up to 10 ms), 10 (up to 100 ms) or half the largest power of ten at
most the capped value (above that), halves rounding up. The result fits in an `i32`. Hypotheses: the
assumptions about `Duration::as_millis` (for the observation `millis`), `u32::ilog10` and
`u32::pow`. -/
theorem round_latency_value (millis : core.time.Duration → Nat)
    (hms : DurationAsMillisSpec millis) (hil : U32Ilog10Spec) (hpow : U32PowSpec)
    (latency : core.time.Duration) :
    ∃ r, metrics_store.round_latency latency = ok r ∧
      r.val = (roundLatencyNat (millis latency) : Int) := by
  sorry

end Keystore2Verify.MetricsStore
