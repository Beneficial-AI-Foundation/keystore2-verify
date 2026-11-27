import Keystore2Verify.Specs.Defs.Operation

namespace Keystore2Verify.Operation
open Aeneas Aeneas.Std Result keystore2
open operation.OperationDb renaming get → operationDbGet
open std.sync.poison.mutex

/-- conditional: if the slot `index` of the operation table holds the weak reference `w`,
`get` returns what `Weak::upgrade` returns for `w`: the operation, if it is still alive, and
`None` otherwise. Hypotheses: the lock succeeds and gives the guard `mg` (the outcome of
`Mutex::lock`), the guard dereferences to the vector `v` (the outcome of `deref`), and the
assumption about `Option::and_then` (`OptionAndThenSpec`). -/
theorem operation_db_get_slot (hand : OptionAndThenSpec)
    (self : operation.OperationDb) (index : Std.Usize)
    (mg : MutexGuard (alloc.vec.Vec (alloc.sync.Weak operation.Operation alloc.alloc.Global)))
    (hlock : Mutex.lock self.operations = ok (.Ok mg))
    (v : alloc.vec.Vec (alloc.sync.Weak operation.Operation alloc.alloc.Global))
    (hderef : MutexGuard.Insts.CoreOpsDerefDeref.deref mg = ok v)
    (w : alloc.sync.Weak operation.Operation alloc.alloc.Global)
    (hw : v.val[index.val]? = some w) :
    operationDbGet self index =
      alloc.sync.Weak.upgrade alloc.alloc.Global.Insts.CoreAllocAllocatorClone w := by
  sorry

/-- conditional: if the index is not less than the length of the operation table, `get` returns
`None`. Hypotheses: the lock succeeds and gives the guard `mg` (the outcome of `Mutex::lock`), the
guard dereferences to the vector `v` (the outcome of `deref`), and the assumption about
`Option::and_then` (`OptionAndThenSpec`). -/
theorem operation_db_get_out_of_range (hand : OptionAndThenSpec)
    (self : operation.OperationDb) (index : Std.Usize)
    (mg : MutexGuard (alloc.vec.Vec (alloc.sync.Weak operation.Operation alloc.alloc.Global)))
    (hlock : Mutex.lock self.operations = ok (.Ok mg))
    (v : alloc.vec.Vec (alloc.sync.Weak operation.Operation alloc.alloc.Global))
    (hderef : MutexGuard.Insts.CoreOpsDerefDeref.deref mg = ok v)
    (hw : v.val.length ≤ index.val) :
    operationDbGet self index = ok none := by
  sorry

/-- conditional: if the lock is poisoned (`Mutex::lock` returns an error `pe`), `get` panics
(`expect`): it returns `fail`. Hypothesis: the outcome of `Mutex::lock`. -/
theorem operation_db_get_poisoned (self : operation.OperationDb) (index : Std.Usize)
    (pe : std.sync.poison.PoisonError (MutexGuard (alloc.vec.Vec (alloc.sync.Weak
      operation.Operation alloc.alloc.Global))))
    (hlock : Mutex.lock self.operations = ok (.Err pe)) :
    operationDbGet self index = fail Error.panic := by
  sorry
