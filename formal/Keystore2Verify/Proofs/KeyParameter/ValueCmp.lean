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

/-- exact: a value of an earlier variant is less than a value of a later one. The order of the
variants is the order of the Rust enum. -/
theorem key_parameter_value_cmp_lt (a b : KeyParameterValue) (h : a.ctorIdx < b.ctorIdx) :
    valueCmp a b = ok Ordering.lt := by
  sorry

/-- exact: a value of a later variant is greater than a value of an earlier one. -/
theorem key_parameter_value_cmp_gt (a b : KeyParameterValue) (h : b.ctorIdx < a.ctorIdx) :
    valueCmp a b = ok Ordering.gt := by
  sorry

/-- exact: two values of the same variant without payload are equal in the order. -/
theorem key_parameter_value_cmp_unit (a b : KeyParameterValue) (ha : IsUnitValue a)
    (h : a.ctorIdx = b.ctorIdx) :
    valueCmp a b = ok Ordering.eq := by
  sorry

/-- exact: two values of the same variant with a `i32` payload are ordered as the numbers are. -/
theorem key_parameter_value_cmp_i32 (c : Std.I32 → KeyParameterValue) (hc : IsI32Ctor c)
    (x y : Std.I32) :
    valueCmp (c x) (c y) = ok (compare x.val y.val) := by
  sorry

/-- exact: two values of the same variant with a `i64` payload are ordered as the numbers are. -/
theorem key_parameter_value_cmp_i64 (c : Std.I64 → KeyParameterValue) (hc : IsI64Ctor c)
    (x y : Std.I64) :
    valueCmp (c x) (c y) = ok (compare x.val y.val) := by
  sorry

/-- conditional: two values of the same variant with a `Vec<u8>` payload are ordered as the `Ord` of
`Vec<u8>` says. If that comparison returns `o`, the result is `o`. Hypothesis: the outcome of
the comparison of the two payloads. -/
theorem key_parameter_value_cmp_vec (c : alloc.vec.Vec Std.U8 → KeyParameterValue)
    (hc : IsVecCtor c) (x y : alloc.vec.Vec Std.U8) (o : Ordering)
    (h : vecCmp alloc.alloc.Global core.cmp.OrdU8 x y = ok o) :
    valueCmp (c x) (c y) = ok o := by
  sorry

/-- conditional: two `KeyPurpose` values are ordered as the `Ord` of `KeyPurpose` says. If that
comparison returns `o`, the result is `o`. Hypothesis: the outcome of the comparison. -/
theorem key_parameter_value_cmp_key_purpose (a b : KeyPurpose.KeyPurpose) (o : Ordering)
    (h : keyPurposeCmp a b = ok o) :
    valueCmp (KeyParameterValue.KeyPurpose a) (KeyParameterValue.KeyPurpose b) = ok o := by
  sorry

/-- conditional: two `Algorithm` values are ordered as the `Ord` of `Algorithm` says. If that
comparison returns `o`, the result is `o`. Hypothesis: the outcome of the comparison. -/
theorem key_parameter_value_cmp_algorithm (a b : Algorithm.Algorithm) (o : Ordering)
    (h : algorithmCmp a b = ok o) :
    valueCmp (KeyParameterValue.Algorithm a) (KeyParameterValue.Algorithm b) = ok o := by
  sorry

/-- conditional: two `BlockMode` values are ordered as the `Ord` of `BlockMode` says. If that
comparison returns `o`, the result is `o`. Hypothesis: the outcome of the comparison. -/
theorem key_parameter_value_cmp_block_mode (a b : BlockMode.BlockMode) (o : Ordering)
    (h : blockModeCmp a b = ok o) :
    valueCmp (KeyParameterValue.BlockMode a) (KeyParameterValue.BlockMode b) = ok o := by
  sorry

/-- conditional: two `Digest` values are ordered as the `Ord` of `Digest` says. If that comparison
returns `o`, the result is `o`. Hypothesis: the outcome of the comparison. -/
theorem key_parameter_value_cmp_digest (a b : Digest.Digest) (o : Ordering)
    (h : digestCmp a b = ok o) :
    valueCmp (KeyParameterValue.Digest a) (KeyParameterValue.Digest b) = ok o := by
  sorry

/-- conditional: two `RsaOaepMgfDigest` values are ordered as the `Ord` of `Digest` says. If that
comparison returns `o`, the result is `o`. Hypothesis: the outcome of the comparison. -/
theorem key_parameter_value_cmp_rsa_oaep_mgf_digest (a b : Digest.Digest) (o : Ordering)
    (h : digestCmp a b = ok o) :
    valueCmp (KeyParameterValue.RsaOaepMgfDigest a) (KeyParameterValue.RsaOaepMgfDigest b) = ok o
        := by
  sorry

/-- conditional: two `PaddingMode` values are ordered as the `Ord` of `PaddingMode` says. If that
comparison returns `o`, the result is `o`. Hypothesis: the outcome of the comparison. -/
theorem key_parameter_value_cmp_padding_mode (a b : PaddingMode.PaddingMode) (o : Ordering)
    (h : paddingModeCmp a b = ok o) :
    valueCmp (KeyParameterValue.PaddingMode a) (KeyParameterValue.PaddingMode b) = ok o := by
  sorry

/-- conditional: two `EcCurve` values are ordered as the `Ord` of `EcCurve` says. If that comparison
returns `o`, the result is `o`. Hypothesis: the outcome of the comparison. -/
theorem key_parameter_value_cmp_ec_curve (a b : EcCurve.EcCurve) (o : Ordering)
    (h : ecCurveCmp a b = ok o) :
    valueCmp (KeyParameterValue.EcCurve a) (KeyParameterValue.EcCurve b) = ok o := by
  sorry

/-- conditional: two `MlDsaVariant` values are ordered as the `Ord` of `MlDsaVariant` says. If that
comparison returns `o`, the result is `o`. Hypothesis: the outcome of the comparison. -/
theorem key_parameter_value_cmp_ml_dsa_variant (a b : MlDsaVariant.MlDsaVariant) (o : Ordering)
    (h : mlDsaVariantCmp a b = ok o) :
    valueCmp (KeyParameterValue.MlDsaVariant a) (KeyParameterValue.MlDsaVariant b) = ok o := by
  sorry

/-- conditional: two `HardwareAuthenticatorType` values are ordered as the `Ord` of
`HardwareAuthenticatorType` says. If that comparison returns `o`, the result is `o`. Hypothesis:
the outcome of the comparison. -/
theorem key_parameter_value_cmp_hardware_authenticator_type (a b :
    HardwareAuthenticatorType.HardwareAuthenticatorType) (o : Ordering)
    (h : hardwareAuthenticatorTypeCmp a b = ok o) :
    valueCmp (KeyParameterValue.HardwareAuthenticatorType a)
        (KeyParameterValue.HardwareAuthenticatorType b) = ok o := by
  sorry

/-- conditional: two `KeyOrigin` values are ordered as the `Ord` of `KeyOrigin` says. If that
comparison returns `o`, the result is `o`. Hypothesis: the outcome of the comparison. -/
theorem key_parameter_value_cmp_key_origin (a b : KeyOrigin.KeyOrigin) (o : Ordering)
    (h : keyOriginCmp a b = ok o) :
    valueCmp (KeyParameterValue.KeyOrigin a) (KeyParameterValue.KeyOrigin b) = ok o := by
  sorry

end Keystore2Verify.KeyParameter
