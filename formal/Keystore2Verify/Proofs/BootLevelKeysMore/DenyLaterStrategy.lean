import Keystore2Verify.Specs.Defs.BootLevelKeysMore

namespace Keystore2Verify.BootLevelKeysMore
open Aeneas Aeneas.Std Result keystore2
open boot_level_keys.DenyLaterStrategy.Insts
open CoreCmpPartialEqDenyLaterStrategy renaming eq → strategyEq
open CoreCloneClone renaming clone → strategyClone

/-- exact: `eq` never fails and is `true` exactly when the two strategies are the same variant. -/
theorem deny_later_strategy_eq (a b : boot_level_keys.DenyLaterStrategy) :
    ∃ r, strategyEq a b = ok r ∧ (r = true ↔ a = b) := by
  sorry

/-- exact: `clone` never fails and returns the same strategy. -/
theorem deny_later_strategy_clone (s : boot_level_keys.DenyLaterStrategy) :
    strategyClone s = ok s := by
  sorry

end Keystore2Verify.BootLevelKeysMore
