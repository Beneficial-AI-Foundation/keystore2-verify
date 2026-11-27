import Keystore2Verify.Specs.Defs.Externals

/-!
# Definitions for the statements about `get_level_zero_key_km_and_strategy`
-/

namespace Keystore2Verify.BootLevelKeysMore
open Aeneas Aeneas.Std Result keystore2

/-- The KeyMint device that the boot level code picks. The translation leaves it opaque. -/
abbrev KM : Type := raw_device.KeyMintDevice

end Keystore2Verify.BootLevelKeysMore
