import Keystore2Verify.Specs.Defs.RemoteProvisioning

namespace Keystore2Verify.RemoteProvisioning
open Aeneas Aeneas.Std Result keystore2
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open remote_provisioning.RemProvState.Insts.CoreDefaultDefault renaming default → provDefault
open remote_provisioning.RemProvState renaming new → provNew
open SecurityLevel.SecurityLevel.Insts.CoreDefaultDefault renaming default → levelDefault

/-- conditional: if the default `SecurityLevel` is `sl`, the default `RemProvState` is
`{ security_level := sl }`. Hypothesis: the outcome of `SecurityLevel::default` (an external
function). -/
theorem rem_prov_state_default (sl : SecurityLevel.SecurityLevel) (h : levelDefault = ok sl) :
    provDefault = ok { security_level := sl } := by
  sorry

/-- exact: `RemProvState::new` never fails and keeps the security level. -/
theorem rem_prov_state_new (security_level : SecurityLevel.SecurityLevel) :
    provNew security_level = ok { security_level := security_level } := by
  sorry
