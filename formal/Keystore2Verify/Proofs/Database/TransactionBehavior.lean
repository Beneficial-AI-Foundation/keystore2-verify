import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open database.TransactionBehavior.Insts.CoreCloneClone renaming clone → txBehaviorClone
open rusqlite.transaction.TransactionBehavior.Insts.CoreConvertFromTransactionBehavior
  renaming «from» → rusqliteFromTxBehavior

/-- exact: `clone` (a copy, since the type is `Copy`) never fails and returns its argument,
for `Deferred` and for `Immediate s`. -/
theorem transaction_behavior_clone (x : database.TransactionBehavior) :
    txBehaviorClone x = ok x := by
  sorry

/-- exact: `From<TransactionBehavior> for rusqlite::TransactionBehavior` never fails.
`Deferred` gives `Deferred`. -/
theorem transaction_behavior_from_deferred :
    rusqliteFromTxBehavior .Deferred = ok .Deferred := by
  sorry

/-- exact: `Immediate s` gives `Immediate` for every `s`: the name is dropped, and the result is
never `Exclusive`. -/
theorem transaction_behavior_from_immediate (s : Str) :
    rusqliteFromTxBehavior (.Immediate s) = ok .Immediate := by
  sorry
