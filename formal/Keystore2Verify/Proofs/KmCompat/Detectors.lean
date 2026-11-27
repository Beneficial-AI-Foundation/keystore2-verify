import Keystore2Verify.Specs.Defs.KmCompat

namespace Keystore2Verify.KmCompat
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open keystore2.core.slice.Slice renaming starts_with → sliceStartsWith
open keystore2.Shared0Slice.Insts.CoreCmpPartialEqVec renaming eq → sliceVecEq
open km_compat renaming wrap_keyblob → wrapKeyblob, unwrap_keyblob → unwrapKeyblob

/-- exact: `KeyMintV1::new` stores the security level. -/
theorem key_mint_v1_new (sec_level : SecurityLevel.SecurityLevel) :
    km_compat.KeyMintV1.new sec_level = ok { sec_level := sec_level } := by
  sorry

/-- exact: `Keymaster::new` holds a `KeyMintV1` with the given security level. -/
theorem keymaster_new (sec_level : SecurityLevel.SecurityLevel) :
    km_compat.Keymaster.new sec_level = ok { v1 := { sec_level := sec_level } } := by
  sorry

end Keystore2Verify.KmCompat
