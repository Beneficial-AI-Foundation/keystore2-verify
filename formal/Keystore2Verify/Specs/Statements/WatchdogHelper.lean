import Keystore2Verify.Proofs.WatchdogHelper.WatchMillis
import Keystore2Verify.Proofs.WatchdogHelper.WatchMillisWith

namespace Keystore2Verify.WatchdogHelper

section WatchMillis
open Aeneas Aeneas.Std Result keystore2

recall watch_millis_none (s : Str) (i : Std.U64) :
    watchdog_helper.watchdog.watch_millis s i = ok none

end WatchMillis

section WatchMillisWith
open Aeneas Aeneas.Std Result keystore2

recall watch_millis_with_none {T0 : Type} (inst : core.fmt.Debug T0) (s : Str) (i : Std.U64)
    (t : T0) :
    watchdog_helper.watchdog.watch_millis_with inst s i t = ok none

end WatchMillisWith

end Keystore2Verify.WatchdogHelper
