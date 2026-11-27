import Keystore2Verify.Specs.Defs.Externals

/-!
# Definitions for the statements about `key_parameter.rs`

`tagOf` is the table that pairs each variant of `KeyParameterValue` with its KeyMint tag. It is
read off the `#[key_param(tag = ...)]` attributes of the Rust enum. The four predicates sort
the variants by the shape of their payload (none, `i32`, `i64`, `Vec<u8>`); the other ten
variants hold an AIDL enum. Nothing here is an axiom.
-/

namespace Keystore2Verify.KeyParameter
open Aeneas Aeneas.Std Result keystore2
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open key_parameter (KeyParameterValue)

/-- The tag of a variant of `KeyParameterValue`, as the `tag = ...` attribute of the Rust enum
gives it. The payload is not looked at. Of the 63 tags, `ALGORITHM` and `EC_CURVE` are known
numbers and the other 61 are constants of the translation that can themselves fail. -/
noncomputable def tagOf : KeyParameterValue → Result Tag.Tag
  | .Invalid => Tag.Tag.INVALID
  | .KeyPurpose _ => Tag.Tag.PURPOSE
  | .Algorithm _ => ok Tag.Tag.ALGORITHM
  | .KeySize _ => Tag.Tag.KEY_SIZE
  | .BlockMode _ => Tag.Tag.BLOCK_MODE
  | .Digest _ => Tag.Tag.DIGEST
  | .RsaOaepMgfDigest _ => Tag.Tag.RSA_OAEP_MGF_DIGEST
  | .PaddingMode _ => Tag.Tag.PADDING
  | .CallerNonce => Tag.Tag.CALLER_NONCE
  | .MinMacLength _ => Tag.Tag.MIN_MAC_LENGTH
  | .EcCurve _ => ok Tag.Tag.EC_CURVE
  | .MlDsaVariant _ => Tag.Tag.ML_DSA_VARIANT
  | .RSAPublicExponent _ => Tag.Tag.RSA_PUBLIC_EXPONENT
  | .IncludeUniqueID => Tag.Tag.INCLUDE_UNIQUE_ID
  | .BootLoaderOnly => Tag.Tag.BOOTLOADER_ONLY
  | .RollbackResistance => Tag.Tag.ROLLBACK_RESISTANCE
  | .EarlyBootOnly => Tag.Tag.EARLY_BOOT_ONLY
  | .ActiveDateTime _ => Tag.Tag.ACTIVE_DATETIME
  | .OriginationExpireDateTime _ => Tag.Tag.ORIGINATION_EXPIRE_DATETIME
  | .UsageExpireDateTime _ => Tag.Tag.USAGE_EXPIRE_DATETIME
  | .MinSecondsBetweenOps _ => Tag.Tag.MIN_SECONDS_BETWEEN_OPS
  | .MaxUsesPerBoot _ => Tag.Tag.MAX_USES_PER_BOOT
  | .UsageCountLimit _ => Tag.Tag.USAGE_COUNT_LIMIT
  | .UserID _ => Tag.Tag.USER_ID
  | .UserSecureID _ => Tag.Tag.USER_SECURE_ID
  | .NoAuthRequired => Tag.Tag.NO_AUTH_REQUIRED
  | .HardwareAuthenticatorType _ => Tag.Tag.USER_AUTH_TYPE
  | .AuthTimeout _ => Tag.Tag.AUTH_TIMEOUT
  | .AllowWhileOnBody => Tag.Tag.ALLOW_WHILE_ON_BODY
  | .TrustedUserPresenceRequired => Tag.Tag.TRUSTED_USER_PRESENCE_REQUIRED
  | .TrustedConfirmationRequired => Tag.Tag.TRUSTED_CONFIRMATION_REQUIRED
  | .UnlockedDeviceRequired => Tag.Tag.UNLOCKED_DEVICE_REQUIRED
  | .ApplicationID _ => Tag.Tag.APPLICATION_ID
  | .ApplicationData _ => Tag.Tag.APPLICATION_DATA
  | .CreationDateTime _ => Tag.Tag.CREATION_DATETIME
  | .KeyOrigin _ => Tag.Tag.ORIGIN
  | .RootOfTrust _ => Tag.Tag.ROOT_OF_TRUST
  | .OSVersion _ => Tag.Tag.OS_VERSION
  | .OSPatchLevel _ => Tag.Tag.OS_PATCHLEVEL
  | .UniqueID _ => Tag.Tag.UNIQUE_ID
  | .AttestationChallenge _ => Tag.Tag.ATTESTATION_CHALLENGE
  | .AttestationApplicationID _ => Tag.Tag.ATTESTATION_APPLICATION_ID
  | .AttestationIdBrand _ => Tag.Tag.ATTESTATION_ID_BRAND
  | .AttestationIdDevice _ => Tag.Tag.ATTESTATION_ID_DEVICE
  | .AttestationIdProduct _ => Tag.Tag.ATTESTATION_ID_PRODUCT
  | .AttestationIdSerial _ => Tag.Tag.ATTESTATION_ID_SERIAL
  | .AttestationIdIMEI _ => Tag.Tag.ATTESTATION_ID_IMEI
  | .AttestationIdSecondIMEI _ => Tag.Tag.ATTESTATION_ID_SECOND_IMEI
  | .AttestationIdMEID _ => Tag.Tag.ATTESTATION_ID_MEID
  | .AttestationIdManufacturer _ => Tag.Tag.ATTESTATION_ID_MANUFACTURER
  | .AttestationIdModel _ => Tag.Tag.ATTESTATION_ID_MODEL
  | .VendorPatchLevel _ => Tag.Tag.VENDOR_PATCHLEVEL
  | .BootPatchLevel _ => Tag.Tag.BOOT_PATCHLEVEL
  | .AssociatedData _ => Tag.Tag.ASSOCIATED_DATA
  | .Nonce _ => Tag.Tag.NONCE
  | .MacLength _ => Tag.Tag.MAC_LENGTH
  | .ResetSinceIdRotation => Tag.Tag.RESET_SINCE_ID_ROTATION
  | .ConfirmationToken _ => Tag.Tag.CONFIRMATION_TOKEN
  | .CertificateSerial _ => Tag.Tag.CERTIFICATE_SERIAL
  | .CertificateSubject _ => Tag.Tag.CERTIFICATE_SUBJECT
  | .CertificateNotBefore _ => Tag.Tag.CERTIFICATE_NOT_BEFORE
  | .CertificateNotAfter _ => Tag.Tag.CERTIFICATE_NOT_AFTER
  | .MaxBootLevel _ => Tag.Tag.MAX_BOOT_LEVEL

/-- The variants of `KeyParameterValue` that carry no payload. -/
def IsUnitValue (v : KeyParameterValue) : Prop :=
  v = KeyParameterValue.Invalid ∨ v = KeyParameterValue.CallerNonce ∨
  v = KeyParameterValue.IncludeUniqueID ∨ v = KeyParameterValue.BootLoaderOnly ∨
  v = KeyParameterValue.RollbackResistance ∨
  v = KeyParameterValue.EarlyBootOnly ∨ v = KeyParameterValue.NoAuthRequired ∨
  v = KeyParameterValue.AllowWhileOnBody ∨
  v = KeyParameterValue.TrustedUserPresenceRequired ∨
  v = KeyParameterValue.TrustedConfirmationRequired ∨
  v = KeyParameterValue.UnlockedDeviceRequired ∨
  v = KeyParameterValue.ResetSinceIdRotation

/-- The variants of `KeyParameterValue` whose payload is an `i32`. -/
def IsI32Ctor (c : Std.I32 → KeyParameterValue) : Prop :=
  c = KeyParameterValue.KeySize ∨ c = KeyParameterValue.MinMacLength ∨
  c = KeyParameterValue.MinSecondsBetweenOps ∨
  c = KeyParameterValue.MaxUsesPerBoot ∨ c = KeyParameterValue.UsageCountLimit ∨
  c = KeyParameterValue.UserID ∨ c = KeyParameterValue.AuthTimeout ∨
  c = KeyParameterValue.OSVersion ∨ c = KeyParameterValue.OSPatchLevel ∨
  c = KeyParameterValue.VendorPatchLevel ∨
  c = KeyParameterValue.BootPatchLevel ∨ c = KeyParameterValue.MacLength ∨
  c = KeyParameterValue.MaxBootLevel

/-- The variants of `KeyParameterValue` whose payload is an `i64`. -/
def IsI64Ctor (c : Std.I64 → KeyParameterValue) : Prop :=
  c = KeyParameterValue.RSAPublicExponent ∨
  c = KeyParameterValue.ActiveDateTime ∨
  c = KeyParameterValue.OriginationExpireDateTime ∨
  c = KeyParameterValue.UsageExpireDateTime ∨
  c = KeyParameterValue.UserSecureID ∨ c = KeyParameterValue.CreationDateTime ∨
  c = KeyParameterValue.CertificateNotBefore ∨
  c = KeyParameterValue.CertificateNotAfter

/-- The variants of `KeyParameterValue` whose payload is a `Vec<u8>`. -/
def IsVecCtor (c : alloc.vec.Vec Std.U8 → KeyParameterValue) : Prop :=
  c = KeyParameterValue.ApplicationID ∨ c = KeyParameterValue.ApplicationData ∨
  c = KeyParameterValue.RootOfTrust ∨ c = KeyParameterValue.UniqueID ∨
  c = KeyParameterValue.AttestationChallenge ∨
  c = KeyParameterValue.AttestationApplicationID ∨
  c = KeyParameterValue.AttestationIdBrand ∨
  c = KeyParameterValue.AttestationIdDevice ∨
  c = KeyParameterValue.AttestationIdProduct ∨
  c = KeyParameterValue.AttestationIdSerial ∨
  c = KeyParameterValue.AttestationIdIMEI ∨
  c = KeyParameterValue.AttestationIdSecondIMEI ∨
  c = KeyParameterValue.AttestationIdMEID ∨
  c = KeyParameterValue.AttestationIdManufacturer ∨
  c = KeyParameterValue.AttestationIdModel ∨
  c = KeyParameterValue.AssociatedData ∨ c = KeyParameterValue.Nonce ∨
  c = KeyParameterValue.ConfirmationToken ∨
  c = KeyParameterValue.CertificateSerial ∨
  c = KeyParameterValue.CertificateSubject

open HardwareAuthenticatorType.HardwareAuthenticatorType.Insts in
/-- The equality of `HardwareAuthenticatorType` under a short name, because the name that the
translation gives it does not fit on one line. -/
noncomputable abbrev hardwareAuthenticatorTypeEq :=
  CoreCmpPartialEqHardwareAuthenticatorType.eq

end Keystore2Verify.KeyParameter
