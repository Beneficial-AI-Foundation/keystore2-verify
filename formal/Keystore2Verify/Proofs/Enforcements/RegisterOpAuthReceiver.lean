import Keystore2Verify.Specs.Defs.Enforcements

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2

/-- conditional: if `TokenReceiverMap::add_receiver` returns `()` for the map `self.op_auth_map`,
the challenge and the receiver, `register_op_auth_receiver` returns `()`. A panic inside
`add_receiver` is not stated. What `add_receiver` does to the map lies in an item that the
translation leaves opaque (blocked by extraction). Hypothesis: the outcome `r` of `add_receiver`. -/
theorem register_op_auth_receiver_forwards (self : enforcements.Enforcements)
    (challenge : utils.Challenge) (recv : enforcements.TokenReceiver) (r : Unit)
    (hadd : enforcements.TokenReceiverMap.add_receiver self.op_auth_map challenge recv = ok r) :
    enforcements.Enforcements.register_op_auth_receiver self challenge recv = ok r := by
  sorry
