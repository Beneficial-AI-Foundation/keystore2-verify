import Keystore2Verify.Specs.Defs.AsyncTask

namespace Keystore2Verify.AsyncTask
open Aeneas Aeneas.Std Result keystore2
open async_task.AsyncTask

/-- exact: `queue_lo f` is `queue f false`, that is, it asks for the low priority queue. It has no
other effect and returns what `queue` returns. -/
theorem queue_lo_eq_queue {F : Type} (inst : core.ops.function.FnOnce F async_task.Shelf Unit)
    (self : async_task.AsyncTask) (f : F) :
    queue_lo inst self f = queue inst self f false := by
  sorry

/-- conditional: if `queue_if` returns `ok b` for the always-true condition, `queue_lo` returns
`ok ()`. Hypothesis: the outcome of `queue_if` (an item of keystore2 that the extraction could not
translate). In the Rust source `queue_if` also pushes the job and starts or wakes the thread, and
the result of `queue_lo` does not say which queue was chosen. -/
theorem queue_lo_ok {F : Type} (inst : core.ops.function.FnOnce F async_task.Shelf Unit)
    (self : async_task.AsyncTask) (f : F) (b : Bool)
    (h : queue_if (alwaysTrueCond inst) inst self () f false = ok b) :
    queue_lo inst self f = ok () := by
  sorry

/-- conditional: if `queue_if` fails with `e` for the always-true condition, `queue_lo` fails with
`e`. Hypothesis: the outcome of `queue_if`. -/
theorem queue_lo_fail {F : Type} (inst : core.ops.function.FnOnce F async_task.Shelf Unit)
    (self : async_task.AsyncTask) (f : F) (e : Error)
    (h : queue_if (alwaysTrueCond inst) inst self () f false = fail e) :
    queue_lo inst self f = fail e := by
  sorry
