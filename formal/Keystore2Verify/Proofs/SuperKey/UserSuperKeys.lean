import Keystore2Verify.Specs.Defs.SuperKey

namespace Keystore2Verify.SuperKey
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals
open super_key.UserSuperKeys.Insts

/-- conditional: the default `UserSuperKeys` has no key in any of its four fields. Hypotheses: the
assumption about `Option::default` at `Option<Arc<SuperKey>>` (used for the first three fields) and
at `Option<BiometricUnlock>`. -/
theorem UserSuperKeys_default (harc : OptionDefaultSpec SuperKeyArc)
    (hbio : OptionDefaultSpec super_key.BiometricUnlock) :
    CoreDefaultDefault.default =
      ok { credential_encrypted := none, unlocked_device_required_symmetric := none,
           unlocked_device_required_private := none, biometric_unlock := none } := by
  sorry

end Keystore2Verify.SuperKey
