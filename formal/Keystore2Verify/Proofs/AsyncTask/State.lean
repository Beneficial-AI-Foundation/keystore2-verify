import Keystore2Verify.Specs.Defs.Externals

namespace Keystore2Verify.AsyncTask
open Aeneas Aeneas.Std Result keystore2
open async_task.State.Insts.CoreCmpPartialEqState renaming eq → stateEq

/-- exact: the derived `PartialEq` of `State` never fails. Two states are equal exactly when they
are the same variant: `true` for `(Exiting, Exiting)` and `(Running, Running)`, `false` for the
two mixed pairs. -/
theorem state_eq :
    stateEq .Exiting .Exiting = ok true ∧ stateEq .Running .Running = ok true ∧
    stateEq .Exiting .Running = ok false ∧ stateEq .Running .Exiting = ok false := by
  sorry
