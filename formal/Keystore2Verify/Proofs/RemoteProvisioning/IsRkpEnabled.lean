import Keystore2Verify.Specs.Defs.RemoteProvisioning

namespace Keystore2Verify.RemoteProvisioning
open Aeneas Aeneas.Std Result keystore2
open remote_provisioning.RemProvState renaming is_rkp_enabled → isRkpEnabled
open rustutils.android.system_properties

/-- conditional: if the property `remote_provisioning.hostname` is set to the string `value`,
`is_rkp_enabled` returns the negation of the outcome `b` of `String::is_empty` on `value`.
Hypotheses: the outcomes of `read` (the system property) and of `String::is_empty` on `value`. The
real `is_empty` returns `true` exactly for the empty string; no assumption says so here. -/
theorem is_rkp_enabled_some (self : remote_provisioning.RemProvState)
    (value : String) (b : Bool)
    (hread : read (toStr "remote_provisioning.hostname") =
      ok (core.result.Result.Ok (some value) : core.result.Result _ PropertyWatcherError))
    (hempty : alloc.string.String.is_empty value = ok b) :
    isRkpEnabled self = ok (!b) := by
  sorry

/-- conditional: if the property `remote_provisioning.hostname` is not set, or cannot be read,
`is_rkp_enabled` returns `false`. Hypothesis: the outcome of `read`. -/
theorem is_rkp_enabled_none (self : remote_provisioning.RemProvState)
    (r : core.result.Result (Option String) PropertyWatcherError)
    (hread : read (toStr "remote_provisioning.hostname") = ok r)
    (hnone : r = .Ok none ∨ ∃ e, r = .Err e) :
    isRkpEnabled self = ok false := by
  sorry
