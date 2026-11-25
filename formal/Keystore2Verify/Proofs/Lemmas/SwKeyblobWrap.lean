import Keystore2Verify.Proofs.SwKeyblob.AddDerLen

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- Appending a slice of bytes that fits in the vector model concatenates the bytes. -/
theorem extend_ok_aux (v : alloc.vec.Vec Std.U8) (s : Slice Std.U8)
    (h : v.val.length + s.val.length ≤ Std.Usize.max) :
    ∃ v', alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s = ok v' ∧
      v'.val = v.val ++ s.val := by
  unfold alloc.vec.Vec.extend_from_slice
  have h' : v.length + s.length ≤ Std.Usize.max := h
  obtain ⟨l, hl, hlv⟩ :
      ∃ l, List.clone core.clone.CloneU8.clone s.val = ok l ∧ l.val = s.val := by
    have hs := List.clone_spec (clone := core.clone.CloneU8.clone) (l := s.val) (fun _ _ => rfl)
    cases hx : List.clone core.clone.CloneU8.clone s.val <;> rw [hx] at hs <;> simp_all
  simp [h', hl, hlv]

/-- The generic body of `pkcs8_wrap_nist_key` for the algorithm identifier `alg`. -/
noncomputable def wrapBody (alg nist_key : Slice Std.U8) :
    Result (core.result.Result (alloc.vec.Vec Std.U8) anyhow.Error) := do
  let nos ← alloc.vec.Vec.push (alloc.vec.Vec.new Std.U8) 4#u8
  let i := Slice.len nist_key
  let (r, nos1) ← sw_keyblob.add_der_len nos i
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let nos2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 nos1 nist_key
    let buf ← alloc.vec.Vec.push (alloc.vec.Vec.new Std.U8) 48#u8
    let i1 := Slice.len sw_keyblob.DER_VERSION_0
    let i2 := Slice.len alg
    let i3 ← i1 + i2
    let i4 := alloc.vec.Vec.len nos2
    let i5 ← i3 + i4
    let (r1, buf1) ← sw_keyblob.add_der_len buf i5
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let buf2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 buf1 sw_keyblob.DER_VERSION_0
      let buf3 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 buf2 alg
      let s := alloc.vec.Vec.deref nos2
      let buf4 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 buf3 s
      ok (core.result.Result.Ok buf4)
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame anyhow.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame anyhow.Error) residual

/-- The curve arms of `pkcs8_wrap_nist_key` are `wrapBody` for the curve's identifier. -/
theorem wrap_eq_body (nist_key : Slice Std.U8) (curve : EcCurve.EcCurve) (alg : Slice Std.U8)
    (hc : NistAlgId curve alg) :
    sw_keyblob.pkcs8_wrap_nist_key nist_key curve = wrapBody alg nist_key := by
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (unfold sw_keyblob.pkcs8_wrap_nist_key wrapBody
     simp only [EcCurve.EcCurve.P_224, EcCurve.EcCurve.P_256, EcCurve.EcCurve.P_384,
       EcCurve.EcCurve.P_521]
     rfl)

/-- `nums` commutes with append. -/
theorem nums_append (a b : List Std.U8) : nums (a ++ b) = nums a ++ nums b := by
  simp [nums]

/-- The bytes of the constant `DER_VERSION_0`. -/
theorem der_version_val : sw_keyblob.DER_VERSION_0.val = [2#u8, 1#u8, 0#u8] := by
  unfold sw_keyblob.DER_VERSION_0; rfl

/-- The encoding of a length is at most three bytes. -/
theorem derLen_length_le (n : Nat) : (derLen n).length ≤ 3 := by
  unfold derLen; split_ifs <;> simp

/-- The body of `pkcs8_wrap_nist_key` wraps the key when the content fits a DER length. -/
theorem wrap_body_ok (alg key : Slice Std.U8)
    (hbody : (pkcs8Body (nums alg.val) (nums key.val)).length ≤ 0xffff) :
    ∃ out, wrapBody alg key = ok (.Ok out) ∧
      nums out.val = pkcs8Wrap (nums alg.val) (nums key.val) := by
  have hmax : 4294967295 ≤ Std.Usize.max := by scalar_tac
  have hd3 := derLen_length_le key.val.length
  have hbl : (pkcs8Body (nums alg.val) (nums key.val)).length =
      3 + alg.val.length + (1 + (derLen key.val.length).length + key.val.length) := by
    simp [pkcs8Body, nums]; omega
  have hK : key.val.length ≤ 0xffff := by omega
  obtain ⟨n0, h0, hv0⟩ := push_ok_aux (alloc.vec.Vec.new Std.U8) 4#u8
    (by simp [alloc.vec.Vec.new]; omega)
  obtain ⟨n1, h1, hv1⟩ := add_der_len_ok n0 (Slice.len key) (by simpa using hK)
    (by rw [hv0]; simp [alloc.vec.Vec.new]; omega)
  obtain ⟨n2, h2, hv2⟩ := extend_ok_aux n1 key (by
    have := congrArg List.length hv1
    simp [nums, hv0, alloc.vec.Vec.new] at this ⊢; omega)
  obtain ⟨b0, hb0, hbv0⟩ := push_ok_aux (alloc.vec.Vec.new Std.U8) 48#u8
    (by simp [alloc.vec.Vec.new]; omega)
  have hl2 : n2.val.length = 1 + (derLen key.val.length).length + key.val.length := by
    have := congrArg List.length hv1
    simp [nums, hv0, alloc.vec.Vec.new] at this
    rw [hv2]; simp [this]; omega
  obtain ⟨i3, hi3, hi3v⟩ := usize_add_ok (Slice.len sw_keyblob.DER_VERSION_0) (Slice.len alg)
    (by simp [der_version_val]; have := Slice.length_ineq alg; omega)
  obtain ⟨i5, hi5, hi5v⟩ := usize_add_ok i3 (alloc.vec.Vec.len n2) (by
    simp [hi3v, der_version_val]; omega)
  have hi5n : i5.val = (pkcs8Body (nums alg.val) (nums key.val)).length := by
    simp [hi5v, hi3v, der_version_val, hl2, hbl]
  have hd5 := derLen_length_le i5.val
  obtain ⟨b1, hb1, hbv1⟩ := add_der_len_ok b0 i5 (by omega)
    (by rw [hbv0]; simp [alloc.vec.Vec.new]; omega)
  have hla : alg.len.val = alg.val.length := Slice.len_val alg
  have hln : n2.len.val = 1 + (derLen key.val.length).length + key.val.length := by
    rw [← hl2]; simp
  have hdv : (alloc.vec.Vec.deref n2).val.length = n2.val.length := by simp [alloc.vec.Vec.deref]
  have hlb1 : b1.val.length = 1 + (derLen i5.val).length := by
    have := congrArg List.length hbv1
    simp [nums, hbv0, alloc.vec.Vec.new] at this
    omega
  obtain ⟨b2, hb2, hbv2⟩ := extend_ok_aux b1 sw_keyblob.DER_VERSION_0 (by
    simp [der_version_val]; omega)
  obtain ⟨b3, hb3, hbv3⟩ := extend_ok_aux b2 alg (by
    simp [hbv2, der_version_val]; omega)
  obtain ⟨b4, hb4, hbv4⟩ := extend_ok_aux b3 (alloc.vec.Vec.deref n2) (by
    simp only [hbv3, hbv2, List.length_append, hdv, der_version_val]; simp; omega)
  refine ⟨b4, ?_, ?_⟩
  · unfold wrapBody
    simp [h0, h1, h2, hb0, hi3, hi5, hb1, hb2, hb3, hb4, core.result.Result.Insts.CoreOpsTry.branch,
      alloc.vec.Vec.new]
  · simp only [pkcs8Wrap, ← hi5n]
    have hb1n : nums b1.val = [48] ++ derLen i5.val := by
      rw [hbv1, hbv0]; simp [nums, alloc.vec.Vec.new]
    have hn2 : nums n2.val = [4] ++ derLen key.val.length ++ nums key.val := by
      rw [hv2, nums_append, hv1, hv0]; simp [nums, alloc.vec.Vec.new]
    have hdv2 : (alloc.vec.Vec.deref n2).val = n2.val := by simp [alloc.vec.Vec.deref]
    rw [hbv4, hbv3, hbv2]
    simp only [nums_append, hb1n, hdv2, hn2, der_version_val]
    simp [pkcs8Body, nums]

/-- `Argument::new_debug` always returns the erased value. -/
@[simp] theorem arg_new_debug_eq {T : Type} (i : core.fmt.Debug T) (x : T) :
    core.fmt.rt.Argument.new_debug i x = ok noArg := rfl

/-- A key longer than `0xffff` bytes gives a blob error in the body of the wrapper. -/
theorem wrap_body_err_key (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (alg key : Slice Std.U8) (hkey : 0xffff < key.val.length) :
    ∃ e, wrapBody alg key = ok (.Err e) ∧ IsBlobErr root e := by
  obtain ⟨n0, h0, hv0⟩ := push_ok_aux (alloc.vec.Vec.new Std.U8) 4#u8
    (by simp [alloc.vec.Vec.new]; scalar_tac)
  obtain ⟨e, he, hr⟩ := add_der_len_err root hlaw n0 key.len (by simpa using hkey)
  refine ⟨e, ?_, hr⟩
  unfold wrapBody
  simp [h0, he, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]

/-- A content longer than `0xffff` bytes gives a blob error in the body of the wrapper. -/
theorem wrap_body_err_body (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (alg key : Slice Std.U8) (halg : alg.val.length ≤ 0xffff) (hkey : key.val.length ≤ 0xffff)
    (hbody : 0xffff < (pkcs8Body (nums alg.val) (nums key.val)).length) :
    ∃ e, wrapBody alg key = ok (.Err e) ∧ IsBlobErr root e := by
  have hmax : 4294967295 ≤ Std.Usize.max := by scalar_tac
  have hd3 := derLen_length_le key.val.length
  have hbl : (pkcs8Body (nums alg.val) (nums key.val)).length =
      3 + alg.val.length + (1 + (derLen key.val.length).length + key.val.length) := by
    simp [pkcs8Body, nums]; omega
  obtain ⟨n0, h0, hv0⟩ := push_ok_aux (alloc.vec.Vec.new Std.U8) 4#u8
    (by simp [alloc.vec.Vec.new]; omega)
  obtain ⟨n1, h1, hv1⟩ := add_der_len_ok n0 (Slice.len key) (by simpa using hkey)
    (by rw [hv0]; simp [alloc.vec.Vec.new]; omega)
  obtain ⟨n2, h2, hv2⟩ := extend_ok_aux n1 key (by
    have := congrArg List.length hv1
    simp [nums, hv0, alloc.vec.Vec.new] at this ⊢; omega)
  obtain ⟨b0, hb0, hbv0⟩ := push_ok_aux (alloc.vec.Vec.new Std.U8) 48#u8
    (by simp [alloc.vec.Vec.new]; omega)
  have hl2 : n2.val.length = 1 + (derLen key.val.length).length + key.val.length := by
    have := congrArg List.length hv1
    simp [nums, hv0, alloc.vec.Vec.new] at this
    rw [hv2]; simp [this]; omega
  obtain ⟨i3, hi3, hi3v⟩ := usize_add_ok (Slice.len sw_keyblob.DER_VERSION_0) (Slice.len alg)
    (by simp [der_version_val]; omega)
  obtain ⟨i5, hi5, hi5v⟩ := usize_add_ok i3 (alloc.vec.Vec.len n2) (by
    simp [hi3v, der_version_val]; omega)
  have hi5n : i5.val = (pkcs8Body (nums alg.val) (nums key.val)).length := by
    simp [hi5v, hi3v, der_version_val, hl2, hbl]
  obtain ⟨e, he, hr⟩ := add_der_len_err root hlaw b0 i5 (by omega)
  refine ⟨e, ?_, hr⟩
  unfold wrapBody
  simp [h0, h1, h2, hb0, hi3, hi5, he, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, alloc.vec.Vec.new]

/-- The identifiers of the NIST curves are short. -/
theorem nist_alg_len (curve : EcCurve.EcCurve) (alg : Slice Std.U8) (hc : NistAlgId curve alg) :
    alg.val.length ≤ 0xffff := by
  rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
    first
    | (unfold sw_keyblob.DER_ALGORITHM_ID_P224; simp)
    | (unfold sw_keyblob.DER_ALGORITHM_ID_P256; simp)
    | (unfold sw_keyblob.DER_ALGORITHM_ID_P384; simp)
    | (unfold sw_keyblob.DER_ALGORITHM_ID_P521; simp)

/-- A curve that is not a NIST curve gives a blob error. -/
theorem wrap_err_curve (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (key : Slice Std.U8) (curve : EcCurve.EcCurve) (hc : ¬ NistCurve curve) :
    ∃ e, sw_keyblob.pkcs8_wrap_nist_key key curve = ok (.Err e) ∧ IsBlobErr root e := by
  obtain ⟨hnew, hctx, hfmt⟩ := hlaw
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨s, hs⟩ := hfmt noArgs
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s
  refine ⟨e1, ?_, by unfold IsBlobErr; rw [hr1, hr0]⟩
  have n0 : curve ≠ 0#i32 :=
    fun h => hc ⟨_, Or.inl ⟨by simp [h, EcCurve.EcCurve.P_224], rfl⟩⟩
  have n1 : curve ≠ 1#i32 :=
    fun h => hc ⟨_, Or.inr (Or.inl ⟨by simp [h, EcCurve.EcCurve.P_256], rfl⟩)⟩
  have n2 : curve ≠ 2#i32 :=
    fun h => hc ⟨_, Or.inr (Or.inr (Or.inl ⟨by simp [h, EcCurve.EcCurve.P_384], rfl⟩))⟩
  have n3 : curve ≠ 3#i32 :=
    fun h => hc ⟨_, Or.inr (Or.inr (Or.inr ⟨by simp [h, EcCurve.EcCurve.P_521], rfl⟩))⟩
  unfold sw_keyblob.pkcs8_wrap_nist_key
  split <;> first
    | (simp [he0, hs, core.hint.must_use, he1]; done)
    | exact absurd rfl n0
    | exact absurd rfl n1
    | exact absurd rfl n2
    | exact absurd rfl n3

end Keystore2Verify.SwKeyblob
