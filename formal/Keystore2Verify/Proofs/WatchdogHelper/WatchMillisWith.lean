import Keystore2Verify.Specs.Defs.Externals

namespace Keystore2Verify.WatchdogHelper
open Aeneas Aeneas.Std Result keystore2

/-- exact: for every message, timeout, value of type `T0` and `Debug` instance,
`watch_millis_with` returns `ok none`: no watch point is set. The value and the instance are not
used. This is the module of the build without the `watchdog` feature. The module of the build with
the feature is not modelled. -/
theorem watch_millis_with_none {T0 : Type} (inst : core.fmt.Debug T0) (s : Str) (i : Std.U64)
    (t : T0) :
    watchdog_helper.watchdog.watch_millis_with inst s i t = ok none := by
  sorry
