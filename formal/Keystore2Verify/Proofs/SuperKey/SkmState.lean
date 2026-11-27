import Keystore2Verify.Specs.Defs.SuperKey

namespace Keystore2Verify.SuperKey
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals
open std.sync.poison.mutex
open super_key.SkmState.Insts

/-- conditional: the default `SkmState` has no user keys, an empty key index and no boot level
cache. Hypotheses: the assumptions for `Default::default` of the two maps (read through `entsU` and
`entsK`) and for `Option::default` at `Option<Mutex<BootLevelKeyCache>>`. -/
theorem SkmState_default (entsU : UserKeyEntries)
    (entsK : Entries Std.I64 (alloc.sync.Weak super_key.SuperKey alloc.alloc.Global))
    (hu : UserKeysEmptySpec entsU) (hk : KeyIndexEmptySpec entsK)
    (hm : OptionDefaultSpec (Mutex boot_level_keys.BootLevelKeyCache)) :
    ∃ s, CoreDefaultDefault.default = ok s ∧
      entsU s.user_keys = [] ∧ entsK s.key_index = [] ∧ s.boot_level_key_cache = none := by
  sorry

end Keystore2Verify.SuperKey
