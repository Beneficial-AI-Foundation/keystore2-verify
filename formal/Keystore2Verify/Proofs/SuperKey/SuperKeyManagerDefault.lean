import Keystore2Verify.Specs.Defs.SuperKey

namespace Keystore2Verify.SuperKey
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals
open std.sync.poison.mutex
open super_key.SuperKeyManager.Insts

/-- conditional: the default `SuperKeyManager` holds the default `SkmState`: no user keys, an
empty key index and no boot level cache. Hypotheses: the same as for `SkmState_default`. -/
theorem SuperKeyManager_default (entsU : UserKeyEntries)
    (entsK : Entries Std.I64 (alloc.sync.Weak super_key.SuperKey alloc.alloc.Global))
    (hu : UserKeysEmptySpec entsU) (hk : KeyIndexEmptySpec entsK)
    (hm : OptionDefaultSpec (Mutex boot_level_keys.BootLevelKeyCache)) :
    ∃ m, CoreDefaultDefault.default = ok m ∧
      entsU m.data.user_keys = [] ∧ entsK m.data.key_index = [] ∧
      m.data.boot_level_key_cache = none := by
  sorry

end Keystore2Verify.SuperKey
