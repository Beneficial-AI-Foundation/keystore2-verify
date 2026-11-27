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

/-- exact: cloning a value of a variant without payload returns it. -/
theorem key_parameter_value_clone_unit (v : KeyParameterValue) (hv : IsUnitValue v) :
    valueClone v = ok v := by
  sorry

/-- exact: cloning a value of a variant with a `i32` payload returns it. -/
theorem key_parameter_value_clone_i32 (c : Std.I32 → KeyParameterValue) (hc : IsI32Ctor c)
    (x : Std.I32) :
    valueClone (c x) = ok (c x) := by
  sorry

/-- exact: cloning a value of a variant with a `i64` payload returns it. -/
theorem key_parameter_value_clone_i64 (c : Std.I64 → KeyParameterValue) (hc : IsI64Ctor c)
    (x : Std.I64) :
    valueClone (c x) = ok (c x) := by
  sorry

/-- exact: cloning a value of a variant with a `Vec<u8>` payload returns a value of the same variant
with a payload that has the same bytes. -/
theorem key_parameter_value_clone_vec (c : alloc.vec.Vec Std.U8 → KeyParameterValue)
    (hc : IsVecCtor c) (x : alloc.vec.Vec Std.U8) :
    ∃ y, valueClone (c x) = ok (c y) ∧ y.val = x.val := by
  sorry

/-- conditional: cloning a `KeyPurpose` value clones its payload. If the clone of `KeyPurpose`
returns `a'`, the result is `KeyPurpose a'`. Hypothesis: the outcome of the clone of
`KeyPurpose`. -/
theorem key_parameter_value_clone_key_purpose (a a' : KeyPurpose.KeyPurpose)
    (h : keyPurposeClone a = ok a') :
    valueClone (KeyParameterValue.KeyPurpose a) = ok (KeyParameterValue.KeyPurpose a') := by
  sorry

/-- conditional: cloning a `Algorithm` value clones its payload. If the clone of `Algorithm` returns
`a'`, the result is `Algorithm a'`. Hypothesis: the outcome of the clone of `Algorithm`. -/
theorem key_parameter_value_clone_algorithm (a a' : Algorithm.Algorithm)
    (h : algorithmClone a = ok a') :
    valueClone (KeyParameterValue.Algorithm a) = ok (KeyParameterValue.Algorithm a') := by
  sorry

/-- conditional: cloning a `BlockMode` value clones its payload. If the clone of `BlockMode` returns
`a'`, the result is `BlockMode a'`. Hypothesis: the outcome of the clone of `BlockMode`. -/
theorem key_parameter_value_clone_block_mode (a a' : BlockMode.BlockMode)
    (h : blockModeClone a = ok a') :
    valueClone (KeyParameterValue.BlockMode a) = ok (KeyParameterValue.BlockMode a') := by
  sorry

/-- conditional: cloning a `Digest` value clones its payload. If the clone of `Digest` returns `a'`,
the result is `Digest a'`. Hypothesis: the outcome of the clone of `Digest`. -/
theorem key_parameter_value_clone_digest (a a' : Digest.Digest)
    (h : digestClone a = ok a') :
    valueClone (KeyParameterValue.Digest a) = ok (KeyParameterValue.Digest a') := by
  sorry

/-- conditional: cloning a `RsaOaepMgfDigest` value clones its payload. If the clone of `Digest`
returns `a'`, the result is `RsaOaepMgfDigest a'`. Hypothesis: the outcome of the clone of
`Digest`. -/
theorem key_parameter_value_clone_rsa_oaep_mgf_digest (a a' : Digest.Digest)
    (h : digestClone a = ok a') :
    valueClone (KeyParameterValue.RsaOaepMgfDigest a) = ok (KeyParameterValue.RsaOaepMgfDigest a')
        := by
  sorry

/-- conditional: cloning a `PaddingMode` value clones its payload. If the clone of `PaddingMode`
returns `a'`, the result is `PaddingMode a'`. Hypothesis: the outcome of the clone of
`PaddingMode`. -/
theorem key_parameter_value_clone_padding_mode (a a' : PaddingMode.PaddingMode)
    (h : paddingModeClone a = ok a') :
    valueClone (KeyParameterValue.PaddingMode a) = ok (KeyParameterValue.PaddingMode a') := by
  sorry

/-- conditional: cloning a `EcCurve` value clones its payload. If the clone of `EcCurve` returns
`a'`, the result is `EcCurve a'`. Hypothesis: the outcome of the clone of `EcCurve`. -/
theorem key_parameter_value_clone_ec_curve (a a' : EcCurve.EcCurve)
    (h : ecCurveClone a = ok a') :
    valueClone (KeyParameterValue.EcCurve a) = ok (KeyParameterValue.EcCurve a') := by
  sorry

/-- conditional: cloning a `MlDsaVariant` value clones its payload. If the clone of `MlDsaVariant`
returns `a'`, the result is `MlDsaVariant a'`. Hypothesis: the outcome of the clone of
`MlDsaVariant`. -/
theorem key_parameter_value_clone_ml_dsa_variant (a a' : MlDsaVariant.MlDsaVariant)
    (h : mlDsaVariantClone a = ok a') :
    valueClone (KeyParameterValue.MlDsaVariant a) = ok (KeyParameterValue.MlDsaVariant a') := by
  sorry

/-- conditional: cloning a `HardwareAuthenticatorType` value clones its payload. If the clone of
`HardwareAuthenticatorType` returns `a'`, the result is `HardwareAuthenticatorType a'`.
Hypothesis: the outcome of the clone of `HardwareAuthenticatorType`. -/
theorem key_parameter_value_clone_hardware_authenticator_type (a a' :
    HardwareAuthenticatorType.HardwareAuthenticatorType)
    (h : hardwareAuthenticatorTypeClone a = ok a') :
    valueClone (KeyParameterValue.HardwareAuthenticatorType a) = ok
        (KeyParameterValue.HardwareAuthenticatorType a') := by
  sorry

/-- conditional: cloning a `KeyOrigin` value clones its payload. If the clone of `KeyOrigin` returns
`a'`, the result is `KeyOrigin a'`. Hypothesis: the outcome of the clone of `KeyOrigin`. -/
theorem key_parameter_value_clone_key_origin (a a' : KeyOrigin.KeyOrigin)
    (h : keyOriginClone a = ok a') :
    valueClone (KeyParameterValue.KeyOrigin a) = ok (KeyParameterValue.KeyOrigin a') := by
  sorry

end Keystore2Verify.KeyParameter
