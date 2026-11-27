import Keystore2Verify.Specs.Defs.Utils

namespace Keystore2Verify.Utils
open Aeneas Aeneas.Std Result keystore2
open utils.key_parameters_to_authorizations
open closure.Insts renaming CoreOpsFunctionFnMutTupleKeyParameterAuthorization → authFnMut
open core.convert renaming IntoFrom.into → intoFrom
open core.iter.adapters
open alloc.vec
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open KeyParameter.KeyParameter.Insts renaming CoreConvertFromKeyParameterValue → kpFromValue

/-- conditional: `key_parameters_to_authorizations` returns one authorization for each parameter,
in the order of the parameters. The authorization of a parameter `p` has the security level of `p`
and the key parameter that `into` makes from the value of `p`. The result has as many elements as
the input vector, so it needs no bound of its own. Hypotheses: the assumptions about external
functions `MapDefaultSpec` and `MapNextSpec` for the closure, with the observations `src` and
`fn` of the adapter `Map`; and, for every parameter, that the conversion of its value returns
normally (`hconv`: the extraction leaves `From<KeyParameterValue>` for the KeyMint `KeyParameter`
opaque). -/
theorem key_parameters_to_authorizations_map
    (src : map.Map (into_iter.IntoIter key_parameter.KeyParameter) closure →
      into_iter.IntoIter key_parameter.KeyParameter)
    (fn : map.Map (into_iter.IntoIter key_parameter.KeyParameter) closure → closure)
    (hdef : MapDefaultSpec authFnMut src fn) (hnext : MapNextSpec authFnMut src fn)
    (parameters : Vec key_parameter.KeyParameter)
    (hconv : ∀ p ∈ parameters.val, ∃ kp, intoFrom kpFromValue p.value = ok kp) :
    ∃ out, utils.key_parameters_to_authorizations parameters = ok out ∧
      List.Forall₂ (fun p a =>
        intoFrom kpFromValue p.value = ok a.keyParameter ∧
          a.securityLevel = p.security_level) parameters.val out.val := by
  sorry

end Keystore2Verify.Utils
