import Keystore2Verify.Specs.Defs.Externals

namespace Keystore2Verify.WatchdogHelper
open Aeneas Aeneas.Std Result keystore2

/-- exact: for every message and timeout, `watch_millis` returns `ok none`: no watch point is set.
This is the module of the build without the `watchdog` feature. The module of the build with the
feature is not modelled. -/
theorem watch_millis_none (s : Str) (i : Std.U64) :
    watchdog_helper.watchdog.watch_millis s i = ok none := by
  sorry
