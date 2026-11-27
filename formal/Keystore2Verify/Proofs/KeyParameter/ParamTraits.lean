import Keystore2Verify.Specs.Defs.KeyParameter

namespace Keystore2Verify.KeyParameter
open Aeneas Aeneas.Std Result keystore2
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open key_parameter (KeyParameterValue)
open key_parameter.KeyParameterValue.Insts.CoreCmpPartialEqKeyParameterValue
  renaming eq → valueEq
open key_parameter.KeyParameterValue.Insts.CoreCloneClone renaming clone → valueClone
open key_parameter.KeyParameterValue.Insts.CoreCmpOrd renaming cmp → valueCmp
open key_parameter.KeyParameterValue renaming get_tag → valueGetTag
open key_parameter.KeyParameter.Insts.CoreCmpPartialEqKeyParameter renaming eq → paramEq
open key_parameter.KeyParameter.Insts.CoreCloneClone renaming clone → paramClone
open key_parameter.KeyParameter.Insts.CoreCmpOrd renaming cmp → paramCmp
open key_parameter.KeyParameter.Insts.CoreCmpPartialOrdKeyParameter 
  renaming partial_cmp → paramPartialCmp
open key_parameter.KeyParameter renaming get_tag → paramGetTag
open key_parameter.KeyParameter.impl renaming security_level → paramSecurityLevel
open keystore2.alloc.vec.Vec.Insts.CoreCmpOrd renaming cmp → vecCmp
open KeyParameter.KeyParameter.Insts.CoreConvertFromKeyParameterValue renaming «from» → kmParamFrom
open Algorithm.Algorithm.Insts.CoreCmpPartialEqAlgorithm renaming eq → algorithmEq
open Algorithm.Algorithm.Insts.CoreCloneClone renaming clone → algorithmClone
open Algorithm.Algorithm.Insts.CoreCmpOrd renaming cmp → algorithmCmp
open BlockMode.BlockMode.Insts.CoreCmpPartialEqBlockMode renaming eq → blockModeEq
open BlockMode.BlockMode.Insts.CoreCloneClone renaming clone → blockModeClone
open BlockMode.BlockMode.Insts.CoreCmpOrd renaming cmp → blockModeCmp
open Digest.Digest.Insts.CoreCmpPartialEqDigest renaming eq → digestEq
open Digest.Digest.Insts.CoreCloneClone renaming clone → digestClone
open Digest.Digest.Insts.CoreCmpOrd renaming cmp → digestCmp
open EcCurve.EcCurve.Insts.CoreCmpPartialEqEcCurve renaming eq → ecCurveEq
open EcCurve.EcCurve.Insts.CoreCloneClone renaming clone → ecCurveClone
open EcCurve.EcCurve.Insts.CoreCmpOrd renaming cmp → ecCurveCmp
open HardwareAuthenticatorType.HardwareAuthenticatorType.Insts.CoreCloneClone
  renaming clone → hardwareAuthenticatorTypeClone
open HardwareAuthenticatorType.HardwareAuthenticatorType.Insts.CoreCmpOrd
  renaming cmp → hardwareAuthenticatorTypeCmp
open KeyOrigin.KeyOrigin.Insts.CoreCmpPartialEqKeyOrigin renaming eq → keyOriginEq
open KeyOrigin.KeyOrigin.Insts.CoreCloneClone renaming clone → keyOriginClone
open KeyOrigin.KeyOrigin.Insts.CoreCmpOrd renaming cmp → keyOriginCmp
open KeyPurpose.KeyPurpose.Insts.CoreCmpPartialEqKeyPurpose renaming eq → keyPurposeEq
open KeyPurpose.KeyPurpose.Insts.CoreCloneClone renaming clone → keyPurposeClone
open KeyPurpose.KeyPurpose.Insts.CoreCmpOrd renaming cmp → keyPurposeCmp
open MlDsaVariant.MlDsaVariant.Insts.CoreCmpPartialEqMlDsaVariant renaming eq → mlDsaVariantEq
open MlDsaVariant.MlDsaVariant.Insts.CoreCloneClone renaming clone → mlDsaVariantClone
open MlDsaVariant.MlDsaVariant.Insts.CoreCmpOrd renaming cmp → mlDsaVariantCmp
open PaddingMode.PaddingMode.Insts.CoreCmpPartialEqPaddingMode renaming eq → paddingModeEq
open PaddingMode.PaddingMode.Insts.CoreCloneClone renaming clone → paddingModeClone
open PaddingMode.PaddingMode.Insts.CoreCmpOrd renaming cmp → paddingModeCmp
open SecurityLevel.SecurityLevel.Insts.CoreCmpPartialEqSecurityLevel renaming eq → securityLevelEq
open SecurityLevel.SecurityLevel.Insts.CoreCloneClone renaming clone → securityLevelClone
open SecurityLevel.SecurityLevel.Insts.CoreCmpOrd renaming cmp → securityLevelCmp

/-- conditional: if the values of two parameters are not equal, the parameters are not equal. In the
Rust source this path returns before the security levels are compared. Hypothesis: the outcome
of the equality of the values. -/
theorem key_parameter_eq_value_ne (a b : key_parameter.KeyParameter)
    (h : valueEq a.value b.value = ok false) :
    paramEq a b = ok false := by
  sorry

/-- conditional: if the values of two parameters are equal, the parameters are equal as the equality
of the security levels says. If that equality returns `r`, the result is `r`. Hypotheses: the
values are equal, and the outcome of the equality of the security levels. -/
theorem key_parameter_eq_value_eq (a b : key_parameter.KeyParameter) (r : Bool)
    (hv : valueEq a.value b.value = ok true)
    (hs : securityLevelEq a.security_level b.security_level = ok r) :
    paramEq a b = ok r := by
  sorry

/-- conditional: cloning a parameter clones its value and its security level. If the two clones
return `v` and `s`, the result is the parameter with value `v` and security level `s`.
Hypotheses: the outcomes of the two clones. -/
theorem key_parameter_clone_ok (a : key_parameter.KeyParameter)
    (v : KeyParameterValue) (s : SecurityLevel.SecurityLevel)
    (hv : valueClone a.value = ok v)
    (hs : securityLevelClone a.security_level = ok s) :
    paramClone a = ok { value := v, security_level := s } := by
  sorry

/-- conditional: if the values of two parameters are ordered `lt`, so are the parameters. In the
Rust source this path returns before the security levels are compared. Hypothesis: the outcome
of the comparison of the values. -/
theorem key_parameter_cmp_value_lt (a b : key_parameter.KeyParameter)
    (h : valueCmp a.value b.value = ok Ordering.lt) :
    paramCmp a b = ok Ordering.lt := by
  sorry

/-- conditional: if the values of two parameters are ordered `gt`, so are the parameters.
Hypothesis: the outcome of the comparison of the values. -/
theorem key_parameter_cmp_value_gt (a b : key_parameter.KeyParameter)
    (h : valueCmp a.value b.value = ok Ordering.gt) :
    paramCmp a b = ok Ordering.gt := by
  sorry

/-- conditional: if the values of two parameters compare equal, the parameters are ordered as their
security levels are. If that comparison returns `o`, the result is `o`. Hypotheses: the values
compare equal, and the outcome of the comparison of the security levels. -/
theorem key_parameter_cmp_value_eq (a b : key_parameter.KeyParameter) (o : Ordering)
    (hv : valueCmp a.value b.value = ok Ordering.eq)
    (hs : securityLevelCmp a.security_level b.security_level = ok o) :
    paramCmp a b = ok o := by
  sorry

/-- conditional: `partial_cmp` of two parameters is always `Some`, and it holds the result of `cmp`.
Hypothesis: the outcome of `cmp`. -/
theorem key_parameter_partial_cmp_ok (a b : key_parameter.KeyParameter) (o : Ordering)
    (h : paramCmp a b = ok o) :
    paramPartialCmp a b = ok (some o) := by
  sorry

/-- conditional: if `cmp` of two parameters fails with `x`, so does `partial_cmp`. Hypothesis: the
outcome of `cmp`. -/
theorem key_parameter_partial_cmp_fail (a b : key_parameter.KeyParameter) (x : Error)
    (h : paramCmp a b = fail x) :
    paramPartialCmp a b = fail x := by
  sorry

end Keystore2Verify.KeyParameter
