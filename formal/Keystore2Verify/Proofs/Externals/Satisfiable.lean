import Keystore2Verify.Specs.Defs.Externals

open Aeneas Aeneas.Std Result keystore2

namespace Keystore2Verify.Externals

/-!
# The laws about external functions can hold together

These are abstract model obligations for the queue, error and byte-reading laws. The queue
statement covers each element type; the error statement chooses one classifier across result
and context types. The crypto length laws are tested together by `ec_crypto_laws_satisfiable`.
Neither module supplies a joint model for all closed contracts on concrete extracted symbols.
The statements here, like the wrapper theorems, have `sorry` bodies.
-/

theorem vecdeque_laws_satisfiable (T : Type) :
    ∃ (Q : Type) (view : Q → List T) (new : Result Q) (len : Q → Result Std.Usize)
      (is_empty : Q → Result Bool) (clear : Q → Result Q) (push_back : Q → T → Result Q)
      (split_off : Q → Std.Usize → Result (Q × Q)),
      VecDequeNewLaw view new ∧ VecDequeLenLaw view len ∧ VecDequeIsEmptyLaw view is_empty ∧
      VecDequeClearLaw view clear ∧ VecDequePushBackLaw view push_back ∧
      VecDequeSplitOffLaw view split_off := by
  sorry

theorem anyhow_laws_satisfiable :
    ∃ (Err : Type) (root : Err → ErrRoot), ∀ (T C : Type),
    ∃ (newKs : error.Error → Result Err) (newSel : keystore2_selinux.Error → Result Err)
      (newCrypto : keystore2_crypto.error.Error → Result Err)
      (fromKs : error.Error → Result Err) (fromSel : keystore2_selinux.Error → Result Err)
      (fromCrypto : keystore2_crypto.error.Error → Result Err)
      (context : Err → C → Result Err) (extError : Err → C → Result Err)
      (extKs : error.Error → C → Result Err) (extSel : keystore2_selinux.Error → C → Result Err)
      (extCrypto : keystore2_crypto.error.Error → C → Result Err)
      (resAny : core.result.Result T Err → C → Result (core.result.Result T Err))
      (resKs : core.result.Result T error.Error → C → Result (core.result.Result T Err))
      (resSel : core.result.Result T keystore2_selinux.Error → C →
        Result (core.result.Result T Err))
      (resCrypto : core.result.Result T keystore2_crypto.error.Error → C →
        Result (core.result.Result T Err)),
      ErrorNewLaw root ErrRoot.ks newKs ∧ ErrorNewLaw root ErrRoot.selinux newSel ∧
      ErrorNewLaw root ErrRoot.crypto newCrypto ∧
      ErrorFromLaw root ErrRoot.ks fromKs ∧ ErrorFromLaw root ErrRoot.selinux fromSel ∧
      ErrorFromLaw root ErrRoot.crypto fromCrypto ∧
      ErrorContextLaw root context ∧ ExtContextErrorLaw root extError ∧
      ExtContextBlanketLaw root ErrRoot.ks extKs ∧
      ExtContextBlanketLaw root ErrRoot.selinux extSel ∧
      ExtContextBlanketLaw root ErrRoot.crypto extCrypto ∧
      ResultContextLaw root root resAny ∧ ResultContextLaw ErrRoot.ks root resKs ∧
      ResultContextLaw ErrRoot.selinux root resSel ∧
      ResultContextLaw ErrRoot.crypto root resCrypto := by
  sorry

theorem std_laws_satisfiable :
    ∃ (u32 : Array Std.U8 4#usize → Result Std.U32) (i32 : Array Std.U8 4#usize → Result Std.I32)
      (i64 : Array Std.U8 8#usize → Result Std.I64),
      FromNeBytesLaw 4#usize (fun x => x.bv) u32 ∧ FromNeBytesLaw 4#usize (fun x => x.bv) i32 ∧
      FromNeBytesLaw 8#usize (fun x => x.bv) i64 := by
  sorry

end Keystore2Verify.Externals
