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

/-- exact: `KeyParameter::new` returns the parameter with the given value and security level. -/
theorem key_parameter_new (v : KeyParameterValue) (s : SecurityLevel.SecurityLevel) :
    key_parameter.KeyParameter.new v s = ok { value := v, security_level := s } := by
  sorry

/-- exact: the tag of a parameter is the tag of its value. -/
theorem key_parameter_get_tag (p : key_parameter.KeyParameter) :
    paramGetTag p = valueGetTag p.value := by
  sorry

/-- exact: `key_parameter_value` returns the value of the parameter. -/
theorem key_parameter_key_parameter_value (p : key_parameter.KeyParameter) :
    key_parameter.KeyParameter.key_parameter_value p = ok p.value := by
  sorry

/-- exact: `security_level` returns the security level of the parameter. -/
theorem key_parameter_security_level (p : key_parameter.KeyParameter) :
    paramSecurityLevel p = ok p.security_level := by
  sorry

/-- conditional: `into_key_parameter` converts the value of the parameter and drops the security
level. If the conversion returns `k`, the result is `k`. Hypothesis: the outcome of the
conversion of `p.value`. -/
theorem key_parameter_into_key_parameter (p : key_parameter.KeyParameter)
    (k : KeyParameter.KeyParameter) (h : kmParamFrom p.value = ok k) :
    key_parameter.KeyParameter.into_key_parameter p = ok k := by
  sorry

/-- conditional: `into_authorization` returns the authorization with the security level of the
parameter and the converted value. If the conversion of `p.value` returns `k`, the result has
the key parameter `k`. Hypothesis: the outcome of the conversion. -/
theorem key_parameter_into_authorization (p : key_parameter.KeyParameter)
    (k : KeyParameter.KeyParameter) (h : kmParamFrom p.value = ok k) :
    key_parameter.KeyParameter.into_authorization p =
      ok { securityLevel := p.security_level, keyParameter := k } := by
  sorry

/-- conditional: if the conversion of `p.value` fails with `x`, `into_key_parameter` and
`into_authorization` fail with `x`. Hypothesis: the outcome of the conversion. -/
theorem key_parameter_into_fail (p : key_parameter.KeyParameter) (x : Error)
    (h : kmParamFrom p.value = fail x) :
    key_parameter.KeyParameter.into_key_parameter p = fail x ∧
      key_parameter.KeyParameter.into_authorization p = fail x := by
  sorry

end Keystore2Verify.KeyParameter
