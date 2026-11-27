import Keystore2Verify.Specs.Defs.Externals

/-!
# Definitions for the statements about `async_task.rs`

A short name for the `FnOnce` instance of the condition closure that `AsyncTask::queue` passes to
`queue_if`. Nothing here is an axiom.
-/

namespace Keystore2Verify.AsyncTask
open Aeneas Aeneas.Std Result keystore2

/-- The condition `|_state| true` that `AsyncTask::queue` passes to `queue_if`, as an instance of
`FnOnce`. It is built from the instance of the job type. -/
abbrev alwaysTrueCond {F : Type} (inst : core.ops.function.FnOnce F async_task.Shelf Unit) :=
  async_task.AsyncTask.queue.closure.Insts.CoreOpsFunctionFnOnceTupleShared0AsyncTaskStateBool
    inst

end Keystore2Verify.AsyncTask
