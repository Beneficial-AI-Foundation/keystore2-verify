import Keystore2Verify.Specs.Defs.Globals

namespace Keystore2Verify.Globals
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals
open core.sync.atomic
open core.sync.atomic.private
open android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- conditional: `boot_completed` returns the value that `load` with `Acquire` order gives on the
static `BOOT_COMPLETED`. Hypotheses: the outcome of the constructor of the static (`a`) and of
`load` on it (`b`). The translation builds the static again at each call and has no `store`, so it
cannot show that the value is `true` after boot: the statement does not claim any value. -/
theorem boot_completed_load (a : Atomic Bool
      (Align1 Std.U8))
    (b : Bool) (hstatic : globals.BOOT_COMPLETED = ok a)
    (hload : AtomicBoolAlign1U8.load a Ordering.Acquire = ok b) :
    globals.boot_completed = ok b := by
  sorry

end Keystore2Verify.Globals
