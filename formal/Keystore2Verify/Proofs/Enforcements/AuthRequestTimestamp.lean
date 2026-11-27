import Keystore2Verify.Specs.Defs.Enforcements

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2
open alloc.sync
open std.sync.poison.mutex

/-- conditional: forwarding result. `timestamp` returns the `Arc` that `Arc::new` gives for a
request with the state `TimeStamp m` and the slot `m1`, where `m` is what `Mutex::new(receiver)`
gives and `m1` is what `Mutex::new(Some(hat))` gives. The theorem states which values the generated
body passes on. It does not state the contents of the opaque `Mutex`, `Arc` and channel wrappers:
that the receiver and the token are the ones stored is not observable here. Hypotheses: the outcomes
of `Mutex::new(receiver)` (it returns `m`), of `Mutex::new(Some(hat))` (it returns `m1`) and of
`Arc::new` on that request (it returns `a`). The result is then `Ok a`. -/
theorem auth_request_timestamp (hat : AuthToken)
    (receiver : TsReceiver)
    (m : Mutex (TsReceiver))
    (m1 : Mutex (Option AuthToken)) (a : alloc.sync.Arc enforcements.AuthRequest)
    (hm : Mutex.new receiver = ok m) (hm1 : Mutex.new (some hat) = ok m1)
    (ha : Arc.new
      ({ state := enforcements.AuthRequestState.TimeStamp m, hat := m1 }
        : enforcements.AuthRequest) = ok a) :
    enforcements.AuthRequest.timestamp hat receiver = ok a := by
  sorry
