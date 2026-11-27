import Keystore2Verify.Specs.Defs.Enforcements

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2
open alloc.sync
open alloc.alloc.Global.Insts renaming CoreAllocAllocatorClone → globalAllocClone

/-- conditional: if the weak reference of the receiver cannot be upgraded, `is_obsolete` returns
`true`. Hypothesis: the outcome of `Weak::upgrade` on `self.req` is `none`. -/
theorem token_receiver_is_obsolete_gone (self : enforcements.TokenReceiver)
    (hup : Weak.upgrade globalAllocClone self.req
      = ok none) :
    enforcements.TokenReceiver.is_obsolete self = ok true := by
  sorry

/-- conditional: if the weak reference of the receiver can be upgraded to the request `a`,
`is_obsolete` returns `false`. Hypothesis: the outcome of `Weak::upgrade` on `self.req` is
`some a`. -/
theorem token_receiver_is_obsolete_alive (self : enforcements.TokenReceiver)
    (a : alloc.sync.Arc enforcements.AuthRequest)
    (hup : Weak.upgrade globalAllocClone self.req
      = ok (some a)) :
    enforcements.TokenReceiver.is_obsolete self = ok false := by
  sorry
