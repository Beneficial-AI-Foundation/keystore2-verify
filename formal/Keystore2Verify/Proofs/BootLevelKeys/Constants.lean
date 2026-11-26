import Keystore2Verify.Specs.Defs.BootLevelKeys

namespace Keystore2Verify.BootLevelKeys
open Aeneas Aeneas.Std Result keystore2 keystore2.boot_level_keys
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open keystore2.boot_level_keys.BootLevel.Insts
open CoreCloneClone renaming clone → bootLevelClone
open CoreCmpPartialEqBootLevel renaming eq → bootLevelEq
open CoreCmpOrd renaming cmp → bootLevelCmp
open CoreCmpPartialOrdBootLevel renaming partial_cmp → bootLevelPartialCmp

/-- exact: the info string `HKDF_ADVANCE` is the 20 ASCII bytes `Advance KDF one step`. -/
theorem hkdf_advance_bytes :
    BytesAre BootLevelKeyCache.HKDF_ADVANCE.val "Advance KDF one step" := by
  unfold BytesAre BootLevelKeyCache.HKDF_ADVANCE
  simp [Array.to_slice, Array.make]

/-- exact: the info string `HKDF_AES` is the 24 ASCII bytes `Generate AES-256-GCM key`. -/
theorem hkdf_aes_bytes : BytesAre BootLevelKeyCache.HKDF_AES.val "Generate AES-256-GCM key" := by
  unfold BytesAre BootLevelKeyCache.HKDF_AES
  simp [Array.to_slice, Array.make]

/-- exact: the key size `HKDF_KEY_SIZE` is 32. -/
theorem hkdf_key_size_val : BootLevelKeyCache.HKDF_KEY_SIZE.val = 32 := by
  unfold BootLevelKeyCache.HKDF_KEY_SIZE
  rfl

end Keystore2Verify.BootLevelKeys
