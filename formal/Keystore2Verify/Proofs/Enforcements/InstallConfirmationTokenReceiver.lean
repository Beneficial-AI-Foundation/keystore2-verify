import Keystore2Verify.Specs.Defs.Enforcements

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2
open alloc.sync.Arc.Insts.CoreOpsDerefDeref renaming deref → arcDeref
open std.sync.poison
open std.sync.poison.mutex
open MutexGuard.Insts
open CoreOpsDerefDerefMut renaming deref_mut → guardDerefMut

/-- conditional: if the confirmation token slot can be locked, `install_confirmation_token_receiver`
returns `()`. In the Rust source the call also stores `Some(receiver)` in the slot. The translation
drops that store: `deref_mut` is called, its result is discarded and the receiver argument is not
used, so no statement can say that the slot is set (blocked by extraction). Hypotheses: the
outcomes of `deref` on the `Arc` of the slot (it returns `m`), of `Mutex::lock` on `m` (it returns
the guard `g`) and of `deref_mut` on `g` (it returns `x`). -/
theorem install_confirmation_token_receiver_ok (self : enforcements.Enforcements)
    (receiver : ByteReceiver)
    (m : Mutex (Option (ByteReceiver)))
    (g : MutexGuard (Option (ByteReceiver)))
    (x : Option (ByteReceiver) ×
      (Option (ByteReceiver) →
        MutexGuard (Option (ByteReceiver))))
    (hderef : arcDeref alloc.alloc.Global
      self.confirmation_token_receiver = ok m)
    (hlock : Mutex.lock m = ok (.Ok g)) (hmut : guardDerefMut g = ok x) :
    enforcements.Enforcements.install_confirmation_token_receiver self receiver = ok () := by
  sorry

/-- conditional: if locking the confirmation token slot returns a poison error,
`install_confirmation_token_receiver` panics (`fail`). Hypotheses: the outcomes of `deref` on the
`Arc` of the slot (it returns `m`) and of `Mutex::lock` on `m`. -/
theorem install_confirmation_token_receiver_poisoned (self : enforcements.Enforcements)
    (receiver : ByteReceiver)
    (m : Mutex (Option (ByteReceiver)))
    (pe : PoisonError
      (MutexGuard (Option (ByteReceiver))))
    (hderef : arcDeref alloc.alloc.Global
      self.confirmation_token_receiver = ok m)
    (hlock : Mutex.lock m = ok (.Err pe)) :
    enforcements.Enforcements.install_confirmation_token_receiver self receiver
      = fail Error.panic := by
  sorry
