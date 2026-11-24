import Keystore2Verify.Specs.Defs.Externals

open Aeneas Aeneas.Std Result keystore2

namespace Keystore2Verify.Externals

/-!
# The laws about external functions can hold together

A set of laws that cannot hold together would make every theorem that assumes them empty. For
each family of laws that share a carrier, these statements give some carrier and some functions
for which all the laws hold. The proofs are `sorry`: the models are a list for the queue, and
`ErrRoot × List String` for an error.
-/

theorem vecdeque_laws_satisfiable :
    ∃ (Q : Type) (view : Q → List Nat) (new : Result Q) (len : Q → Result Std.Usize)
      (is_empty : Q → Result Bool) (clear : Q → Result Q) (push_back : Q → Nat → Result Q)
      (split_off : Q → Std.Usize → Result (Q × Q)),
      VecDequeNewLaw view new ∧ VecDequeLenLaw view len ∧ VecDequeIsEmptyLaw view is_empty ∧
      VecDequeClearLaw view clear ∧ VecDequePushBackLaw view push_back ∧
      VecDequeSplitOffLaw view split_off := by
  sorry

theorem anyhow_laws_satisfiable :
    ∃ (Err : Type) (root : Err → ErrRoot)
      (newKs : error.Error → Result Err) (newSel : keystore2_selinux.Error → Result Err)
      (newCrypto : keystore2_crypto.error.Error → Result Err)
      (fromKs : error.Error → Result Err) (fromSel : keystore2_selinux.Error → Result Err)
      (fromCrypto : keystore2_crypto.error.Error → Result Err)
      (context : Err → String → Result Err) (extError : Err → String → Result Err)
      (extStd : keystore2_crypto.error.Error → String → Result Err)
      (resAny : core.result.Result Unit Err → String → Result (core.result.Result Unit Err))
      (resStd : core.result.Result Unit keystore2_crypto.error.Error → String →
        Result (core.result.Result Unit Err)),
      ErrorNewLaw root ErrRoot.ks newKs ∧ ErrorNewLaw root ErrRoot.selinux newSel ∧
      ErrorNewLaw root ErrRoot.crypto newCrypto ∧
      ErrorFromLaw root ErrRoot.ks fromKs ∧ ErrorFromLaw root ErrRoot.selinux fromSel ∧
      ErrorFromLaw root ErrRoot.crypto fromCrypto ∧
      ErrorContextLaw root context ∧ ExtContextErrorLaw root extError ∧
      ExtContextBlanketLaw root ErrRoot.crypto extStd ∧
      ResultContextLaw root root resAny ∧ ResultContextLaw ErrRoot.crypto root resStd := by
  sorry

theorem std_laws_satisfiable :
    ∃ (u32 : Array Std.U8 4#usize → Result Std.U32) (i32 : Array Std.U8 4#usize → Result Std.I32)
      (i64 : Array Std.U8 8#usize → Result Std.I64),
      FromNeBytes4Law (fun x => x.bv) u32 ∧ FromNeBytes4Law (fun x => x.bv) i32 ∧
      FromNeBytes8Law (fun x => x.bv) i64 := by
  sorry

theorem crypto_laws_satisfiable :
    ∃ (Z : Type) (deref : Z → Result (Slice Std.U8))
      (expand : Std.Usize → Slice Std.U8 → Slice Std.U8 →
        Result (core.result.Result Z keystore2_crypto.error.Error))
      (extract : Slice Std.U8 → Slice Std.U8 →
        Result (core.result.Result Z keystore2_crypto.error.Error))
      (salt : Result (core.result.Result (alloc.vec.Vec Std.U8) keystore2_crypto.error.Error)),
      HkdfExpandLenLaw deref expand ∧ HkdfExtractLenLaw deref extract ∧ SaltLenLaw salt := by
  sorry

end Keystore2Verify.Externals
