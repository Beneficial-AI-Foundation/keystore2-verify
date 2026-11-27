import Keystore2Verify.Specs.Defs.Utils

namespace Keystore2Verify.Utils
open Aeneas Aeneas.Std Result keystore2
open android_security_apc.aidl.android.security.apc
open IProtectedConfirmation renaming FLAG_UI_OPTION_INVERTED → flagInverted,
  FLAG_UI_OPTION_MAGNIFIED → flagMagnified

/-- conditional: `ui_opts_2_compat` returns the struct whose field `inverted` is `true` exactly when
`opt` has a bit of `FLAG_UI_OPTION_INVERTED` set, and whose field `magnified` is `true`
exactly when `opt` has a bit of `FLAG_UI_OPTION_MAGNIFIED` set. Negative `opt` count as bit
patterns. Hypotheses: the two constants are `ok i` and `ok m` (`hi`, `hm`). -/
theorem ui_opts_2_compat_flags (opt i m : Std.I32)
    (hi : flagInverted = ok i) (hm : flagMagnified = ok m) :
    ∃ r, utils.ui_opts_2_compat opt = ok r ∧
      (r.inverted = true ↔ (opt &&& i) ≠ 0#i32) ∧
      (r.magnified = true ↔ (opt &&& m) ≠ 0#i32) := by
  sorry

end Keystore2Verify.Utils
