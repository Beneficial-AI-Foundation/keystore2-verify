import Keystore2Verify.Specs.Defs.AsyncTask

namespace Keystore2Verify.AsyncTask
open Aeneas Aeneas.Std Result keystore2
open async_task.AsyncTask

/-- conditional: if `queue_if` returns `ok b` for the always-true condition and the priority
`hi_prio`, `queue` returns `ok ()`: it drops `b`, also when `b` is `false`. Hypothesis: the outcome
of `queue_if` for that priority (an item of keystore2 that the extraction could not translate). -/
theorem queue_ok {F : Type} (inst : core.ops.function.FnOnce F async_task.Shelf Unit)
    (self : async_task.AsyncTask) (f : F) (hi_prio b : Bool)
    (h : queue_if (alwaysTrueCond inst) inst self () f hi_prio = ok b) :
    queue inst self f hi_prio = ok () := by
  sorry

/-- conditional: if `queue_if` fails with `e` for the always-true condition, `queue` fails with
`e`. Hypothesis: the outcome of `queue_if`. -/
theorem queue_fail {F : Type} (inst : core.ops.function.FnOnce F async_task.Shelf Unit)
    (self : async_task.AsyncTask) (f : F) (hi_prio : Bool) (e : Error)
    (h : queue_if (alwaysTrueCond inst) inst self () f hi_prio = fail e) :
    queue inst self f hi_prio = fail e := by
  sorry
