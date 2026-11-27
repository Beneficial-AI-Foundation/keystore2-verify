import Keystore2Verify.Proofs.KeyParameter.GetTag
import Keystore2Verify.Proofs.KeyParameter.ValueEq
import Keystore2Verify.Proofs.KeyParameter.ValueClone
import Keystore2Verify.Proofs.KeyParameter.ValueCmp
import Keystore2Verify.Proofs.KeyParameter.ParamTraits
import Keystore2Verify.Proofs.KeyParameter.Param

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

recall key_parameter_value_get_tag (v : KeyParameterValue) :
    valueGetTag v = tagOf v

recall key_parameter_value_get_tag_algorithm (a : Algorithm.Algorithm) :
    valueGetTag (KeyParameterValue.Algorithm a) = ok 268435458#i32

recall key_parameter_value_get_tag_ec_curve (c : EcCurve.EcCurve) :
    valueGetTag (KeyParameterValue.EcCurve c) = ok 268435466#i32

recall key_parameter_value_eq_ne_variant (a b : KeyParameterValue)
    (h : a.ctorIdx ≠ b.ctorIdx) :
    valueEq a b = ok false

recall key_parameter_value_eq_unit (a b : KeyParameterValue) (ha : IsUnitValue a)
    (h : a.ctorIdx = b.ctorIdx) :
    valueEq a b = ok true

recall key_parameter_value_eq_i32 (c : Std.I32 → KeyParameterValue) (hc : IsI32Ctor c)
    (x y : Std.I32) :
    ∃ b, valueEq (c x) (c y) = ok b ∧ (b = true ↔ x = y)

recall key_parameter_value_eq_i64 (c : Std.I64 → KeyParameterValue) (hc : IsI64Ctor c)
    (x y : Std.I64) :
    ∃ b, valueEq (c x) (c y) = ok b ∧ (b = true ↔ x = y)

recall key_parameter_value_eq_vec (c : alloc.vec.Vec Std.U8 → KeyParameterValue) (hc : IsVecCtor c)
    (x y : alloc.vec.Vec Std.U8) :
    ∃ b, valueEq (c x) (c y) = ok b ∧ (b = true ↔ x.val = y.val)

recall key_parameter_value_eq_key_purpose (a b : KeyPurpose.KeyPurpose) (r : Bool)
    (h : keyPurposeEq a b = ok r) :
    valueEq (KeyParameterValue.KeyPurpose a) (KeyParameterValue.KeyPurpose b) = ok r

recall key_parameter_value_eq_algorithm (a b : Algorithm.Algorithm) (r : Bool)
    (h : algorithmEq a b = ok r) :
    valueEq (KeyParameterValue.Algorithm a) (KeyParameterValue.Algorithm b) = ok r

recall key_parameter_value_eq_block_mode (a b : BlockMode.BlockMode) (r : Bool)
    (h : blockModeEq a b = ok r) :
    valueEq (KeyParameterValue.BlockMode a) (KeyParameterValue.BlockMode b) = ok r

recall key_parameter_value_eq_digest (a b : Digest.Digest) (r : Bool)
    (h : digestEq a b = ok r) :
    valueEq (KeyParameterValue.Digest a) (KeyParameterValue.Digest b) = ok r

recall key_parameter_value_eq_rsa_oaep_mgf_digest (a b : Digest.Digest) (r : Bool)
    (h : digestEq a b = ok r) :
    valueEq (KeyParameterValue.RsaOaepMgfDigest a) (KeyParameterValue.RsaOaepMgfDigest b) = ok r

recall key_parameter_value_eq_padding_mode (a b : PaddingMode.PaddingMode) (r : Bool)
    (h : paddingModeEq a b = ok r) :
    valueEq (KeyParameterValue.PaddingMode a) (KeyParameterValue.PaddingMode b) = ok r

recall key_parameter_value_eq_ec_curve (a b : EcCurve.EcCurve) (r : Bool)
    (h : ecCurveEq a b = ok r) :
    valueEq (KeyParameterValue.EcCurve a) (KeyParameterValue.EcCurve b) = ok r

recall key_parameter_value_eq_ml_dsa_variant (a b : MlDsaVariant.MlDsaVariant) (r : Bool)
    (h : mlDsaVariantEq a b = ok r) :
    valueEq (KeyParameterValue.MlDsaVariant a) (KeyParameterValue.MlDsaVariant b) = ok r

recall key_parameter_value_eq_hardware_authenticator_type (a b :
    HardwareAuthenticatorType.HardwareAuthenticatorType) (r : Bool)
    (h : hardwareAuthenticatorTypeEq a b = ok r) :
    valueEq (KeyParameterValue.HardwareAuthenticatorType a)
        (KeyParameterValue.HardwareAuthenticatorType b) = ok r

recall key_parameter_value_eq_key_origin (a b : KeyOrigin.KeyOrigin) (r : Bool)
    (h : keyOriginEq a b = ok r) :
    valueEq (KeyParameterValue.KeyOrigin a) (KeyParameterValue.KeyOrigin b) = ok r

recall key_parameter_value_clone_unit (v : KeyParameterValue) (hv : IsUnitValue v) :
    valueClone v = ok v

recall key_parameter_value_clone_i32 (c : Std.I32 → KeyParameterValue) (hc : IsI32Ctor c)
    (x : Std.I32) :
    valueClone (c x) = ok (c x)

recall key_parameter_value_clone_i64 (c : Std.I64 → KeyParameterValue) (hc : IsI64Ctor c)
    (x : Std.I64) :
    valueClone (c x) = ok (c x)

recall key_parameter_value_clone_vec (c : alloc.vec.Vec Std.U8 → KeyParameterValue)
    (hc : IsVecCtor c) (x : alloc.vec.Vec Std.U8) :
    ∃ y, valueClone (c x) = ok (c y) ∧ y.val = x.val

recall key_parameter_value_clone_key_purpose (a a' : KeyPurpose.KeyPurpose)
    (h : keyPurposeClone a = ok a') :
    valueClone (KeyParameterValue.KeyPurpose a) = ok (KeyParameterValue.KeyPurpose a')

recall key_parameter_value_clone_algorithm (a a' : Algorithm.Algorithm)
    (h : algorithmClone a = ok a') :
    valueClone (KeyParameterValue.Algorithm a) = ok (KeyParameterValue.Algorithm a')

recall key_parameter_value_clone_block_mode (a a' : BlockMode.BlockMode)
    (h : blockModeClone a = ok a') :
    valueClone (KeyParameterValue.BlockMode a) = ok (KeyParameterValue.BlockMode a')

recall key_parameter_value_clone_digest (a a' : Digest.Digest)
    (h : digestClone a = ok a') :
    valueClone (KeyParameterValue.Digest a) = ok (KeyParameterValue.Digest a')

recall key_parameter_value_clone_rsa_oaep_mgf_digest (a a' : Digest.Digest)
    (h : digestClone a = ok a') :
    valueClone (KeyParameterValue.RsaOaepMgfDigest a) = ok (KeyParameterValue.RsaOaepMgfDigest a')

recall key_parameter_value_clone_padding_mode (a a' : PaddingMode.PaddingMode)
    (h : paddingModeClone a = ok a') :
    valueClone (KeyParameterValue.PaddingMode a) = ok (KeyParameterValue.PaddingMode a')

recall key_parameter_value_clone_ec_curve (a a' : EcCurve.EcCurve)
    (h : ecCurveClone a = ok a') :
    valueClone (KeyParameterValue.EcCurve a) = ok (KeyParameterValue.EcCurve a')

recall key_parameter_value_clone_ml_dsa_variant (a a' : MlDsaVariant.MlDsaVariant)
    (h : mlDsaVariantClone a = ok a') :
    valueClone (KeyParameterValue.MlDsaVariant a) = ok (KeyParameterValue.MlDsaVariant a')

recall key_parameter_value_clone_hardware_authenticator_type (a a' :
    HardwareAuthenticatorType.HardwareAuthenticatorType)
    (h : hardwareAuthenticatorTypeClone a = ok a') :
    valueClone (KeyParameterValue.HardwareAuthenticatorType a) = ok
        (KeyParameterValue.HardwareAuthenticatorType a')

recall key_parameter_value_clone_key_origin (a a' : KeyOrigin.KeyOrigin)
    (h : keyOriginClone a = ok a') :
    valueClone (KeyParameterValue.KeyOrigin a) = ok (KeyParameterValue.KeyOrigin a')

recall key_parameter_value_cmp_lt (a b : KeyParameterValue) (h : a.ctorIdx < b.ctorIdx) :
    valueCmp a b = ok Ordering.lt

recall key_parameter_value_cmp_gt (a b : KeyParameterValue) (h : b.ctorIdx < a.ctorIdx) :
    valueCmp a b = ok Ordering.gt

recall key_parameter_value_cmp_unit (a b : KeyParameterValue) (ha : IsUnitValue a)
    (h : a.ctorIdx = b.ctorIdx) :
    valueCmp a b = ok Ordering.eq

recall key_parameter_value_cmp_i32 (c : Std.I32 → KeyParameterValue) (hc : IsI32Ctor c)
    (x y : Std.I32) :
    valueCmp (c x) (c y) = ok (compare x.val y.val)

recall key_parameter_value_cmp_i64 (c : Std.I64 → KeyParameterValue) (hc : IsI64Ctor c)
    (x y : Std.I64) :
    valueCmp (c x) (c y) = ok (compare x.val y.val)

recall key_parameter_value_cmp_vec (c : alloc.vec.Vec Std.U8 → KeyParameterValue)
    (hc : IsVecCtor c) (x y : alloc.vec.Vec Std.U8) (o : Ordering)
    (h : vecCmp alloc.alloc.Global core.cmp.OrdU8 x y = ok o) :
    valueCmp (c x) (c y) = ok o

recall key_parameter_value_cmp_key_purpose (a b : KeyPurpose.KeyPurpose) (o : Ordering)
    (h : keyPurposeCmp a b = ok o) :
    valueCmp (KeyParameterValue.KeyPurpose a) (KeyParameterValue.KeyPurpose b) = ok o

recall key_parameter_value_cmp_algorithm (a b : Algorithm.Algorithm) (o : Ordering)
    (h : algorithmCmp a b = ok o) :
    valueCmp (KeyParameterValue.Algorithm a) (KeyParameterValue.Algorithm b) = ok o

recall key_parameter_value_cmp_block_mode (a b : BlockMode.BlockMode) (o : Ordering)
    (h : blockModeCmp a b = ok o) :
    valueCmp (KeyParameterValue.BlockMode a) (KeyParameterValue.BlockMode b) = ok o

recall key_parameter_value_cmp_digest (a b : Digest.Digest) (o : Ordering)
    (h : digestCmp a b = ok o) :
    valueCmp (KeyParameterValue.Digest a) (KeyParameterValue.Digest b) = ok o

recall key_parameter_value_cmp_rsa_oaep_mgf_digest (a b : Digest.Digest) (o : Ordering)
    (h : digestCmp a b = ok o) :
    valueCmp (KeyParameterValue.RsaOaepMgfDigest a) (KeyParameterValue.RsaOaepMgfDigest b) = ok o

recall key_parameter_value_cmp_padding_mode (a b : PaddingMode.PaddingMode) (o : Ordering)
    (h : paddingModeCmp a b = ok o) :
    valueCmp (KeyParameterValue.PaddingMode a) (KeyParameterValue.PaddingMode b) = ok o

recall key_parameter_value_cmp_ec_curve (a b : EcCurve.EcCurve) (o : Ordering)
    (h : ecCurveCmp a b = ok o) :
    valueCmp (KeyParameterValue.EcCurve a) (KeyParameterValue.EcCurve b) = ok o

recall key_parameter_value_cmp_ml_dsa_variant (a b : MlDsaVariant.MlDsaVariant) (o : Ordering)
    (h : mlDsaVariantCmp a b = ok o) :
    valueCmp (KeyParameterValue.MlDsaVariant a) (KeyParameterValue.MlDsaVariant b) = ok o

recall key_parameter_value_cmp_hardware_authenticator_type (a b :
    HardwareAuthenticatorType.HardwareAuthenticatorType) (o : Ordering)
    (h : hardwareAuthenticatorTypeCmp a b = ok o) :
    valueCmp (KeyParameterValue.HardwareAuthenticatorType a)
        (KeyParameterValue.HardwareAuthenticatorType b) = ok o

recall key_parameter_value_cmp_key_origin (a b : KeyOrigin.KeyOrigin) (o : Ordering)
    (h : keyOriginCmp a b = ok o) :
    valueCmp (KeyParameterValue.KeyOrigin a) (KeyParameterValue.KeyOrigin b) = ok o

recall key_parameter_eq_value_ne (a b : key_parameter.KeyParameter)
    (h : valueEq a.value b.value = ok false) :
    paramEq a b = ok false

recall key_parameter_eq_value_eq (a b : key_parameter.KeyParameter) (r : Bool)
    (hv : valueEq a.value b.value = ok true)
    (hs : securityLevelEq a.security_level b.security_level = ok r) :
    paramEq a b = ok r

recall key_parameter_clone_ok (a : key_parameter.KeyParameter)
    (v : KeyParameterValue) (s : SecurityLevel.SecurityLevel)
    (hv : valueClone a.value = ok v)
    (hs : securityLevelClone a.security_level = ok s) :
    paramClone a = ok { value := v, security_level := s }

recall key_parameter_cmp_value_lt (a b : key_parameter.KeyParameter)
    (h : valueCmp a.value b.value = ok Ordering.lt) :
    paramCmp a b = ok Ordering.lt

recall key_parameter_cmp_value_gt (a b : key_parameter.KeyParameter)
    (h : valueCmp a.value b.value = ok Ordering.gt) :
    paramCmp a b = ok Ordering.gt

recall key_parameter_cmp_value_eq (a b : key_parameter.KeyParameter) (o : Ordering)
    (hv : valueCmp a.value b.value = ok Ordering.eq)
    (hs : securityLevelCmp a.security_level b.security_level = ok o) :
    paramCmp a b = ok o

recall key_parameter_partial_cmp_ok (a b : key_parameter.KeyParameter) (o : Ordering)
    (h : paramCmp a b = ok o) :
    paramPartialCmp a b = ok (some o)

recall key_parameter_partial_cmp_fail (a b : key_parameter.KeyParameter) (x : Error)
    (h : paramCmp a b = fail x) :
    paramPartialCmp a b = fail x

recall key_parameter_new (v : KeyParameterValue) (s : SecurityLevel.SecurityLevel) :
    key_parameter.KeyParameter.new v s = ok { value := v, security_level := s }

recall key_parameter_get_tag (p : key_parameter.KeyParameter) :
    paramGetTag p = valueGetTag p.value

recall key_parameter_key_parameter_value (p : key_parameter.KeyParameter) :
    key_parameter.KeyParameter.key_parameter_value p = ok p.value

recall key_parameter_security_level (p : key_parameter.KeyParameter) :
    paramSecurityLevel p = ok p.security_level

recall key_parameter_into_key_parameter (p : key_parameter.KeyParameter)
    (k : KeyParameter.KeyParameter) (h : kmParamFrom p.value = ok k) :
    key_parameter.KeyParameter.into_key_parameter p = ok k

recall key_parameter_into_authorization (p : key_parameter.KeyParameter)
    (k : KeyParameter.KeyParameter) (h : kmParamFrom p.value = ok k) :
    key_parameter.KeyParameter.into_authorization p =
      ok { securityLevel := p.security_level, keyParameter := k }

recall key_parameter_into_fail (p : key_parameter.KeyParameter) (x : Error)
    (h : kmParamFrom p.value = fail x) :
    key_parameter.KeyParameter.into_key_parameter p = fail x ∧
      key_parameter.KeyParameter.into_authorization p = fail x

end Keystore2Verify.KeyParameter
