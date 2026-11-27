import Keystore2Verify.Specs.Defs.AsyncTask

namespace Keystore2Verify.AsyncTask
open Aeneas Aeneas.Std Result keystore2
open async_task.AsyncTask

/-- exact: `queue_hi f` is `queue f true`, that is, it asks for the high priority queue. It has no
other effect and returns what `queue` returns. -/
theorem queue_hi_eq_queue {F : Type} (inst : core.ops.function.FnOnce F async_task.Shelf Unit)
    (self : async_task.AsyncTask) (f : F) :
    queue_hi inst self f = queue inst self f true := by
  sorry

/-- conditional: if `queue_if` returns `ok b` for the always-true condition, `queue_hi` returns
`ok ()`. Hypothesis: the outcome of `queue_if` (an item of keystore2 that the extraction could not
translate). In the Rust source `queue_if` also pushes the job and starts or wakes the thread, and
the result of `queue_hi` does not say which queue was chosen. -/
theorem queue_hi_ok {F : Type} (inst : core.ops.function.FnOnce F async_task.Shelf Unit)
    (self : async_task.AsyncTask) (f : F) (b : Bool)
    (h : queue_if (alwaysTrueCond inst) inst self () f true = ok b) :
    queue_hi inst self f = ok () := by
  sorry

/-- conditional: if `queue_if` fails with `e` for the always-true condition, `queue_hi` fails with
`e`. Hypothesis: the outcome of `queue_if`. -/
theorem queue_hi_fail {F : Type} (inst : core.ops.function.FnOnce F async_task.Shelf Unit)
    (self : async_task.AsyncTask) (f : F) (e : Error)
    (h : queue_if (alwaysTrueCond inst) inst self () f true = fail e) :
    queue_hi inst self f = fail e := by
  sorry
