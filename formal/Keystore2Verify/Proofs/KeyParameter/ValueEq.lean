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

/-- exact: two values with different variants are not equal. -/
theorem key_parameter_value_eq_ne_variant (a b : KeyParameterValue)
    (h : a.ctorIdx ≠ b.ctorIdx) :
    valueEq a b = ok false := by
  sorry

/-- exact: two values of the same variant without payload are equal. -/
theorem key_parameter_value_eq_unit (a b : KeyParameterValue) (ha : IsUnitValue a)
    (h : a.ctorIdx = b.ctorIdx) :
    valueEq a b = ok true := by
  sorry

/-- exact: two values of the same variant with a `i32` payload are equal exactly when the payloads
are equal. `IsI32Ctor` lists those variants. -/
theorem key_parameter_value_eq_i32 (c : Std.I32 → KeyParameterValue) (hc : IsI32Ctor c)
    (x y : Std.I32) :
    ∃ b, valueEq (c x) (c y) = ok b ∧ (b = true ↔ x = y) := by
  sorry

/-- exact: two values of the same variant with a `i64` payload are equal exactly when the payloads
are equal. `IsI64Ctor` lists those variants. -/
theorem key_parameter_value_eq_i64 (c : Std.I64 → KeyParameterValue) (hc : IsI64Ctor c)
    (x y : Std.I64) :
    ∃ b, valueEq (c x) (c y) = ok b ∧ (b = true ↔ x = y) := by
  sorry

/-- exact: two values of the same variant with a `Vec<u8>` payload are equal exactly when the
payloads are equal. `IsVecCtor` lists those variants. -/
theorem key_parameter_value_eq_vec (c : alloc.vec.Vec Std.U8 → KeyParameterValue) (hc : IsVecCtor c)
    (x y : alloc.vec.Vec Std.U8) :
    ∃ b, valueEq (c x) (c y) = ok b ∧ (b = true ↔ x.val = y.val) := by
  sorry

/-- conditional: two `KeyPurpose` values are equal as the equality of `KeyPurpose` says. If that
equality returns `r` on the payloads, the result is `r`. Hypothesis: the outcome of the equality
of `KeyPurpose`. -/
theorem key_parameter_value_eq_key_purpose (a b : KeyPurpose.KeyPurpose) (r : Bool)
    (h : keyPurposeEq a b = ok r) :
    valueEq (KeyParameterValue.KeyPurpose a) (KeyParameterValue.KeyPurpose b) = ok r := by
  sorry

/-- conditional: two `Algorithm` values are equal as the equality of `Algorithm` says. If that
equality returns `r` on the payloads, the result is `r`. Hypothesis: the outcome of the equality
of `Algorithm`. -/
theorem key_parameter_value_eq_algorithm (a b : Algorithm.Algorithm) (r : Bool)
    (h : algorithmEq a b = ok r) :
    valueEq (KeyParameterValue.Algorithm a) (KeyParameterValue.Algorithm b) = ok r := by
  sorry

/-- conditional: two `BlockMode` values are equal as the equality of `BlockMode` says. If that
equality returns `r` on the payloads, the result is `r`. Hypothesis: the outcome of the equality
of `BlockMode`. -/
theorem key_parameter_value_eq_block_mode (a b : BlockMode.BlockMode) (r : Bool)
    (h : blockModeEq a b = ok r) :
    valueEq (KeyParameterValue.BlockMode a) (KeyParameterValue.BlockMode b) = ok r := by
  sorry

/-- conditional: two `Digest` values are equal as the equality of `Digest` says. If that equality
returns `r` on the payloads, the result is `r`. Hypothesis: the outcome of the equality of
`Digest`. -/
theorem key_parameter_value_eq_digest (a b : Digest.Digest) (r : Bool)
    (h : digestEq a b = ok r) :
    valueEq (KeyParameterValue.Digest a) (KeyParameterValue.Digest b) = ok r := by
  sorry

/-- conditional: two `RsaOaepMgfDigest` values are equal as the equality of `Digest` says. If that
equality returns `r` on the payloads, the result is `r`. Hypothesis: the outcome of the equality
of `Digest`. -/
theorem key_parameter_value_eq_rsa_oaep_mgf_digest (a b : Digest.Digest) (r : Bool)
    (h : digestEq a b = ok r) :
    valueEq (KeyParameterValue.RsaOaepMgfDigest a) (KeyParameterValue.RsaOaepMgfDigest b) = ok r
        := by
  sorry

/-- conditional: two `PaddingMode` values are equal as the equality of `PaddingMode` says. If that
equality returns `r` on the payloads, the result is `r`. Hypothesis: the outcome of the equality
of `PaddingMode`. -/
theorem key_parameter_value_eq_padding_mode (a b : PaddingMode.PaddingMode) (r : Bool)
    (h : paddingModeEq a b = ok r) :
    valueEq (KeyParameterValue.PaddingMode a) (KeyParameterValue.PaddingMode b) = ok r := by
  sorry

/-- conditional: two `EcCurve` values are equal as the equality of `EcCurve` says. If that equality
returns `r` on the payloads, the result is `r`. Hypothesis: the outcome of the equality of
`EcCurve`. -/
theorem key_parameter_value_eq_ec_curve (a b : EcCurve.EcCurve) (r : Bool)
    (h : ecCurveEq a b = ok r) :
    valueEq (KeyParameterValue.EcCurve a) (KeyParameterValue.EcCurve b) = ok r := by
  sorry

/-- conditional: two `MlDsaVariant` values are equal as the equality of `MlDsaVariant` says. If that
equality returns `r` on the payloads, the result is `r`. Hypothesis: the outcome of the equality
of `MlDsaVariant`. -/
theorem key_parameter_value_eq_ml_dsa_variant (a b : MlDsaVariant.MlDsaVariant) (r : Bool)
    (h : mlDsaVariantEq a b = ok r) :
    valueEq (KeyParameterValue.MlDsaVariant a) (KeyParameterValue.MlDsaVariant b) = ok r := by
  sorry

/-- conditional: two `HardwareAuthenticatorType` values are equal as the equality of
`HardwareAuthenticatorType` says. If that equality returns `r` on the payloads, the result is
`r`. Hypothesis: the outcome of the equality of `HardwareAuthenticatorType`. -/
theorem key_parameter_value_eq_hardware_authenticator_type (a b :
    HardwareAuthenticatorType.HardwareAuthenticatorType) (r : Bool)
    (h : hardwareAuthenticatorTypeEq a b = ok r) :
    valueEq (KeyParameterValue.HardwareAuthenticatorType a)
        (KeyParameterValue.HardwareAuthenticatorType b) = ok r := by
  sorry

/-- conditional: two `KeyOrigin` values are equal as the equality of `KeyOrigin` says. If that
equality returns `r` on the payloads, the result is `r`. Hypothesis: the outcome of the equality
of `KeyOrigin`. -/
theorem key_parameter_value_eq_key_origin (a b : KeyOrigin.KeyOrigin) (r : Bool)
    (h : keyOriginEq a b = ok r) :
    valueEq (KeyParameterValue.KeyOrigin a) (KeyParameterValue.KeyOrigin b) = ok r := by
  sorry

end Keystore2Verify.KeyParameter
