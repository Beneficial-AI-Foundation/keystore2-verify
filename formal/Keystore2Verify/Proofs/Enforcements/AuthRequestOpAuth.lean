import Keystore2Verify.Specs.Defs.Enforcements

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2
open alloc.sync
open std.sync.poison.mutex

/-- conditional: forwarding result. `op_auth` returns the `Arc` that `Arc::new` gives for a request
with the state `OpAuth` and the slot `m`, where `m` is what `Mutex::new(None)` gives. The theorem
states which values the generated body passes on. It does not state the contents of the opaque
`Mutex` and `Arc` wrappers: that the request is in the state `OpAuth` and that its slot is empty
is not observable here. Hypotheses: the outcomes of `Mutex::new(None)` (it returns `m`) and of
`Arc::new` on that request (it returns `a`). The result is then `Ok a`. -/
theorem auth_request_op_auth (m : Mutex (Option AuthToken))
    (a : alloc.sync.Arc enforcements.AuthRequest)
    (hm : Mutex.new (none : Option AuthToken) = ok m)
    (ha : Arc.new
      ({ state := enforcements.AuthRequestState.OpAuth, hat := m } : enforcements.AuthRequest)
      = ok a) :
    enforcements.AuthRequest.op_auth = ok a := by
  sorry
