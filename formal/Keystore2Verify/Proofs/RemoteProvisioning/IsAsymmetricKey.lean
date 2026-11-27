import Keystore2Verify.Specs.Defs.RemoteProvisioning

namespace Keystore2Verify.RemoteProvisioning
open Aeneas Aeneas.Std Result keystore2
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open remote_provisioning.RemProvState renaming is_asymmetric_key → isAsymmetricKey
open remote_provisioning.RemProvState.is_asymmetric_key.closure.Insts
  renaming CoreOpsFunctionFnMutTupleShared0KeyParameterBool → asymClosure

/-- conditional: `is_asymmetric_key` returns `true` exactly when some parameter is
`Tag::ALGORITHM` with an algorithm value of RSA, EC or ML_DSA (`IsAsymParam`). For the empty
slice, an `ALGORITHM` tag with another value type, another algorithm (such as AES), or such a
value under another tag, it returns `false`. Hypothesis: the assumption about `Iter::any`
(`CoreSliceIterAnySpec`) for the closure of this function. -/
theorem is_asymmetric_key_iff (hany : CoreSliceIterAnySpec asymClosure)
    (self : remote_provisioning.RemProvState) (params : Slice KeyParameter.KeyParameter) :
    ∃ b, isAsymmetricKey self params = ok b ∧
      (b = true ↔ ∃ p ∈ params.val, IsAsymParam p) := by
  sorry
