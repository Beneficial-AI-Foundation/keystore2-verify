import Keystore2Verify.Specs.Defs.MetricsStore

namespace Keystore2Verify.MetricsStore
open Aeneas Aeneas.Std Result keystore2
open android_security_metrics.aidl.android.security.metrics.SecurityLevel.SecurityLevel

/-- exact: `process_security_level` maps the KeyMint level 0 (SOFTWARE), 1 (TRUSTED_ENVIRONMENT),
2 (STRONGBOX) and 100 (KEYSTORE) to the metrics constants `SECURITY_LEVEL_SOFTWARE`,
`SECURITY_LEVEL_TRUSTED_ENVIRONMENT`, `SECURITY_LEVEL_STRONGBOX` and `SECURITY_LEVEL_KEYSTORE`,
and every other `i32` to `SECURITY_LEVEL_UNSPECIFIED`. The result is the constant itself, which
is a `Result` in the translation: the function fails exactly when the constant does. -/
theorem process_security_level_cases (sec_level : Std.I32) :
    metrics_store.process_security_level sec_level =
      if sec_level.val = 0 then SECURITY_LEVEL_SOFTWARE
      else if sec_level.val = 1 then SECURITY_LEVEL_TRUSTED_ENVIRONMENT
      else if sec_level.val = 2 then SECURITY_LEVEL_STRONGBOX
      else if sec_level.val = 100 then SECURITY_LEVEL_KEYSTORE
      else SECURITY_LEVEL_UNSPECIFIED := by
  sorry

end Keystore2Verify.MetricsStore
