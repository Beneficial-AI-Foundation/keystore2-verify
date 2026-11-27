import Keystore2Verify.Specs.Defs.RemoteProvisioning

namespace Keystore2Verify.RemoteProvisioning
open Aeneas Aeneas.Std Result keystore2
open remote_provisioning.RemProvState renaming is_rkp_only → isRkpOnly
open rustutils.android.system_properties

/-- conditional: for `STRONGBOX` (2), `is_rkp_only` returns the value of the boolean system
property `remote_provisioning.strongbox.rkp_only`, with the default `false` if the property
cannot be read (`unwrap_or(false)`). Hypothesis: the outcome `r` of `read_bool` (the system
property). -/
theorem is_rkp_only_strongbox (self : remote_provisioning.RemProvState)
    (hl : self.security_level = 2#i32)
    (r : core.result.Result Bool PropertyWatcherError)
    (h : read_bool (toStr "remote_provisioning.strongbox.rkp_only") false = ok r) :
    isRkpOnly self = ok (propBool r) := by
  sorry

/-- conditional: for `TRUSTED_ENVIRONMENT` (1), `is_rkp_only` returns the value of the boolean
system property `remote_provisioning.tee.rkp_only`, with the default `false` if the property
cannot be read. Hypothesis: the outcome `r` of `read_bool`. -/
theorem is_rkp_only_tee (self : remote_provisioning.RemProvState)
    (hl : self.security_level = 1#i32)
    (r : core.result.Result Bool PropertyWatcherError)
    (h : read_bool (toStr "remote_provisioning.tee.rkp_only") false = ok r) :
    isRkpOnly self = ok (propBool r) := by
  sorry

/-- exact: for every other security level (`SOFTWARE` 0, `KEYSTORE` 100 and any other number),
`is_rkp_only` returns `false`. In the Rust source it reads no property. -/
theorem is_rkp_only_other (self : remote_provisioning.RemProvState)
    (h1 : self.security_level ≠ 1#i32) (h2 : self.security_level ≠ 2#i32) :
    isRkpOnly self = ok false := by
  sorry
