import Keystore2Verify.Proofs.AsyncTask.State
import Keystore2Verify.Proofs.AsyncTask.QueueHi
import Keystore2Verify.Proofs.AsyncTask.QueueLo
import Keystore2Verify.Proofs.AsyncTask.Queue

namespace Keystore2Verify.AsyncTask

section State
open Aeneas Aeneas.Std Result keystore2
open async_task.State.Insts.CoreCmpPartialEqState renaming eq → stateEq

recall state_eq :
    stateEq .Exiting .Exiting = ok true ∧ stateEq .Running .Running = ok true ∧
    stateEq .Exiting .Running = ok false ∧ stateEq .Running .Exiting = ok false

end State

section QueueHi
open Aeneas Aeneas.Std Result keystore2
open async_task.AsyncTask

recall queue_hi_eq_queue {F : Type} (inst : core.ops.function.FnOnce F async_task.Shelf Unit)
    (self : async_task.AsyncTask) (f : F) :
    queue_hi inst self f = queue inst self f true

recall queue_hi_ok {F : Type} (inst : core.ops.function.FnOnce F async_task.Shelf Unit)
    (self : async_task.AsyncTask) (f : F) (b : Bool)
    (h : queue_if (alwaysTrueCond inst) inst self () f true = ok b) :
    queue_hi inst self f = ok ()

recall queue_hi_fail {F : Type} (inst : core.ops.function.FnOnce F async_task.Shelf Unit)
    (self : async_task.AsyncTask) (f : F) (e : Error)
    (h : queue_if (alwaysTrueCond inst) inst self () f true = fail e) :
    queue_hi inst self f = fail e

end QueueHi

section QueueLo
open Aeneas Aeneas.Std Result keystore2
open async_task.AsyncTask

recall queue_lo_eq_queue {F : Type} (inst : core.ops.function.FnOnce F async_task.Shelf Unit)
    (self : async_task.AsyncTask) (f : F) :
    queue_lo inst self f = queue inst self f false

recall queue_lo_ok {F : Type} (inst : core.ops.function.FnOnce F async_task.Shelf Unit)
    (self : async_task.AsyncTask) (f : F) (b : Bool)
    (h : queue_if (alwaysTrueCond inst) inst self () f false = ok b) :
    queue_lo inst self f = ok ()

recall queue_lo_fail {F : Type} (inst : core.ops.function.FnOnce F async_task.Shelf Unit)
    (self : async_task.AsyncTask) (f : F) (e : Error)
    (h : queue_if (alwaysTrueCond inst) inst self () f false = fail e) :
    queue_lo inst self f = fail e

end QueueLo

section Queue
open Aeneas Aeneas.Std Result keystore2
open async_task.AsyncTask

recall queue_ok {F : Type} (inst : core.ops.function.FnOnce F async_task.Shelf Unit)
    (self : async_task.AsyncTask) (f : F) (hi_prio b : Bool)
    (h : queue_if (alwaysTrueCond inst) inst self () f hi_prio = ok b) :
    queue inst self f hi_prio = ok ()

recall queue_fail {F : Type} (inst : core.ops.function.FnOnce F async_task.Shelf Unit)
    (self : async_task.AsyncTask) (f : F) (hi_prio : Bool) (e : Error)
    (h : queue_if (alwaysTrueCond inst) inst self () f hi_prio = fail e) :
    queue inst self f hi_prio = fail e

end Queue

end Keystore2Verify.AsyncTask
