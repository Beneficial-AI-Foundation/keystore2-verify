import Keystore2Verify.Proofs.Externals.Satisfiable

open Aeneas Aeneas.Std Result keystore2

namespace Keystore2Verify.Externals

/-! The statements of `Proofs/Externals/Satisfiable.lean`, restated with `recall`. -/

recall vecdeque_laws_satisfiable (T : Type) :
    ∃ (Q : Type) (view : Q → List T) (new : Result Q) (len : Q → Result Std.Usize)
      (is_empty : Q → Result Bool) (clear : Q → Result Q) (push_back : Q → T → Result Q)
      (split_off : Q → Std.Usize → Result (Q × Q)),
      VecDequeNewLaw view new ∧ VecDequeLenLaw view len ∧ VecDequeIsEmptyLaw view is_empty ∧
      VecDequeClearLaw view clear ∧ VecDequePushBackLaw view push_back ∧
      VecDequeSplitOffLaw view split_off

recall anyhow_laws_satisfiable (T C : Type) :
    ∃ (Err : Type) (root : Err → ErrRoot)
      (newKs : error.Error → Result Err) (newSel : keystore2_selinux.Error → Result Err)
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
      ResultContextLaw ErrRoot.crypto root resCrypto

recall std_laws_satisfiable :
    ∃ (u32 : Array Std.U8 4#usize → Result Std.U32) (i32 : Array Std.U8 4#usize → Result Std.I32)
      (i64 : Array Std.U8 8#usize → Result Std.I64),
      FromNeBytes4Law (fun x => x.bv) u32 ∧ FromNeBytes4Law (fun x => x.bv) i32 ∧
      FromNeBytes8Law (fun x => x.bv) i64

recall crypto_laws_satisfiable :
    ∃ (Z : Type) (deref : Z → Result (Slice Std.U8))
      (expand : Std.Usize → Slice Std.U8 → Slice Std.U8 →
        Result (core.result.Result Z keystore2_crypto.error.Error))
      (extract : Slice Std.U8 → Slice Std.U8 →
        Result (core.result.Result Z keystore2_crypto.error.Error))
      (salt : Result (core.result.Result (alloc.vec.Vec Std.U8) keystore2_crypto.error.Error)),
      TotalLaw deref ∧ HkdfExpandLenLaw deref expand ∧ HkdfExtractLenLaw deref extract ∧
      SaltLenLaw salt

end Keystore2Verify.Externals
