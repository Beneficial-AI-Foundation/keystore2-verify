import Keystore2Verify.Specs.Defs.Externals

open Aeneas Aeneas.Std Result keystore2

namespace Keystore2Verify.Externals

/-!
# The laws about external functions can hold together

A set of laws that cannot hold together would make every theorem that assumes them empty. For
each family of laws that share a carrier, these statements give some carrier and some functions
for which all the laws hold. The proofs are `sorry`. The statements are for every element type
of the queue and for every result type and context type of the error family. The models are a
list of at most `Std.Usize.max` elements for the queue (`push_back` fails past `queueBound`),
`ErrRoot × List String` for an error, and, for the secret vector, `Z := Slice U8` with `deref` the
identity, so that `expand n _ _` returns `Ok` of `n` bytes, `extract` returns `Ok` of 32 bytes and
the salt is `Ok` of 16 bytes.

The laws of the queue and error families, and the byte-reading laws, already force
successful calls on the inputs they are stated for (their valid-input domains), so a model in
which every call fails cannot satisfy them. The length laws of the crypto family only say what a
successful result looks like, so a model in which every call fails would satisfy them. The
statement for them also asks for one successful call of each function, so that two length laws
that contradict each other on a successful result would be exposed.
-/

theorem vecdeque_laws_satisfiable (T : Type) :
    ∃ (Q : Type) (view : Q → List T) (new : Result Q) (len : Q → Result Std.Usize)
      (is_empty : Q → Result Bool) (clear : Q → Result Q) (push_back : Q → T → Result Q)
      (split_off : Q → Std.Usize → Result (Q × Q)),
      VecDequeNewLaw view new ∧ VecDequeLenLaw view len ∧ VecDequeIsEmptyLaw view is_empty ∧
      VecDequeClearLaw view clear ∧ VecDequePushBackLaw view push_back ∧
      VecDequeSplitOffLaw view split_off := by
  sorry

theorem anyhow_laws_satisfiable (T C : Type) :
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
      ResultContextLaw ErrRoot.crypto root resCrypto := by
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
      TotalLaw deref ∧ HkdfExpandLenLaw deref expand ∧ HkdfExtractLenLaw deref extract ∧
      SaltLenLaw salt ∧
      (∃ n a b z, expand n a b = ok (.Ok z)) ∧ (∃ a b z, extract a b = ok (.Ok z)) ∧
      (∃ s, salt = ok (.Ok s)) := by
  sorry

end Keystore2Verify.Externals
