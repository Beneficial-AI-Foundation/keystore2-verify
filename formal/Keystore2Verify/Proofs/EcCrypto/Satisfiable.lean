import Keystore2Verify.Specs.Defs.EcCrypto

namespace Keystore2Verify.EcCrypto
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

/-!
# The crypto laws of `ec_crypto.rs` can hold together

The laws about the secret vector are stated over one view `deref` of the vector as a slice. A set
of laws that cannot hold together, or that hold only when no crypto call succeeds, would make
every statement that assumes them empty. The statement below gives one carrier and one set of
functions for which the shared length laws and the four laws of `Specs/Defs/EcCrypto.lean` hold
together, and in which five of the seven functions have a call that returns `Ok` and the other two
(`marshal` and `to_oct`) return `Ok` on every input.
-/

/-- exact: there are a carrier `Z` for the secret vector, a view `deref` of it as a slice and one
function for each of the seven external calls, such that `TotalLaw deref`, `HkdfExpandLenLaw`,
`HkdfExtractLenLaw`, `SaltLenLaw` and the four laws `EcKeyMarshalLenLaw`, `PointToOctLenLaw`,
`AesGcmEncryptLenLaw` and `AesGcmDecryptLenLaw` hold together. The functions `expand`, `extract`,
`salt`, `enc` and `dec` have a call that returns `Ok`. `marshal` and `to_oct` return `Ok` on every
input of their inhabited abstract carrier `Unit`. This does not assume an inhabitant or a
reachable successful call for either extracted input type. The model is `Z := Slice U8` with `deref` the identity: every
function always returns `Ok`, with a vector of zeros of the length that its law asks for (the
ciphertext of the encryption is the message, and the plaintext of the decryption is the ciphertext).
-/
theorem ec_crypto_laws_satisfiable :
    ∃ (Z : Type) (deref : Z → Result (Slice Std.U8))
      (expand : Std.Usize → Slice Std.U8 → Slice Std.U8 →
        Result (core.result.Result Z keystore2_crypto.error.Error))
      (extract : Slice Std.U8 → Slice Std.U8 →
        Result (core.result.Result Z keystore2_crypto.error.Error))
      (salt : Result (core.result.Result (alloc.vec.Vec Std.U8) keystore2_crypto.error.Error))
      (marshal : Unit →
        Result (core.result.Result Z keystore2_crypto.error.Error))
      (to_oct : Unit →
        Result (core.result.Result (alloc.vec.Vec Std.U8) keystore2_crypto.error.Error))
      (enc : Slice Std.U8 → Slice Std.U8 → Result (core.result.Result
        (alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8)
        keystore2_crypto.error.Error))
      (dec : Slice Std.U8 → Slice Std.U8 → Slice Std.U8 → Slice Std.U8 →
        Result (core.result.Result Z keystore2_crypto.error.Error)),
      TotalLaw deref ∧ HkdfExpandLenLaw deref expand ∧ HkdfExtractLenLaw deref extract ∧
      SaltLenLaw salt ∧ EcKeyMarshalLenLaw deref marshal ∧ PointToOctLenLaw to_oct ∧
      AesGcmEncryptLenLaw enc ∧ AesGcmDecryptLenLaw deref dec ∧
      (∃ n prk info z, expand n prk info = ok (.Ok z)) ∧
      (∃ secret salt' z, extract secret salt' = ok (.Ok z)) ∧
      (∃ s, salt = ok (.Ok s)) ∧
      (∀ key, ∃ z, marshal key = ok (.Ok z)) ∧
      (∀ pt, ∃ v, to_oct pt = ok (.Ok v)) ∧
      (∃ m k ct iv tag, enc m k = ok (.Ok (ct, iv, tag))) ∧
      (∃ data iv tag key p, dec data iv tag key = ok (.Ok p)) := by
  have h32 : 32 ≤ Std.Usize.max := by scalar_tac
  have h16 : 16 ≤ Std.Usize.max := by scalar_tac
  have h12 : 12 ≤ Std.Usize.max := by scalar_tac
  have h73 : 73 ≤ Std.Usize.max := by scalar_tac
  have h1 : 1 ≤ Std.Usize.max := by scalar_tac
  have hs : ∀ s : Slice Std.U8, s.length ≤ Std.Usize.max := fun s => s.property
  let s0 : Slice Std.U8 := Slice.from [] (by simp)
  let zs : ∀ n, n ≤ Std.Usize.max → Slice Std.U8 := fun n h =>
    Slice.from (List.replicate n 0#u8) (by simpa using h)
  let zv : ∀ n, n ≤ Std.Usize.max → alloc.vec.Vec Std.U8 := fun n h =>
    ⟨zs n h⟩
  have hzs : ∀ n h, (zs n h).val = List.replicate n 0#u8 := fun _ _ => Slice.from_val _ _
  have hzv : ∀ n h, (zv n h).val = List.replicate n 0#u8 := fun n h => hzs n h
  refine ⟨Slice Std.U8, ok, fun n _ _ => ok (.Ok (zs n.val (by scalar_tac))),
    fun _ _ => ok (.Ok (zs 32 h32)), ok (.Ok (zv 16 h16)), fun _ => ok (.Ok (zs 73 h73)),
    fun _ => ok (.Ok (zv 1 h1)), fun m _ => ok (.Ok (zv m.length (hs m), zv 12 h12, zv 16 h16)),
    fun d _ _ _ => ok (.Ok (zs d.length (hs d))), ?_⟩
  refine ⟨fun a => ⟨_, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n prk info z h
    cases Result.ok_injective h
    exact ⟨_, rfl, by simp [hzs, Slice.length]⟩
  · intro secret salt z h
    cases Result.ok_injective h
    exact ⟨_, rfl, by simp [hzs, Slice.length]⟩
  · intro s h
    cases Result.ok_injective h
    simp [hzv]
  · intro key z h
    cases Result.ok_injective h
    exact ⟨_, rfl, by simp [hzs, Slice.length]⟩
  · intro p v h
    cases Result.ok_injective h
    simp [hzv]
  · intro m k ct iv tag h
    cases Result.ok_injective h
    simp [hzv, Slice.length]
  · intro data iv tag key p h
    cases Result.ok_injective h
    exact ⟨_, rfl, by simp [hzs, Slice.length]⟩
  · exact ⟨0#usize, s0, s0, _, rfl⟩
  · exact ⟨s0, s0, _, rfl⟩
  · exact ⟨_, rfl⟩
  · exact fun _ => ⟨_, rfl⟩
  · exact fun _ => ⟨_, rfl⟩
  · exact ⟨s0, s0, _, _, _, rfl⟩
  · exact ⟨s0, s0, s0, s0, _, rfl⟩

end Keystore2Verify.EcCrypto
