import Keystore2Verify.Proofs.Lemmas.SwKeyblobWrap
import Keystore2Verify.Proofs.SwKeyblob.ConsumeU8
import Keystore2Verify.Proofs.SwKeyblob.ConsumeVec

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- The constant `MAC_LEN` is 8. -/
theorem mac_len_eq : sw_keyblob.KeyBlob.MAC_LEN = 8#usize := by
  unfold sw_keyblob.KeyBlob.MAC_LEN; rfl

/-- The version constant is 0. -/
theorem blob_version_eq : sw_keyblob.KeyBlob.KEY_BLOB_VERSION = 0#u8 := by
  unfold sw_keyblob.KeyBlob.KEY_BLOB_VERSION; rfl

/-- A `usize` product that stays in range returns the product. -/
theorem usize_mul_ok (x y : Std.Usize) (h : x.val * y.val ≤ Std.Usize.max) :
    ∃ z, x * y = ok z ∧ z.val = x.val * y.val := by
  have hs := UScalar.mul_spec (x := x) (y := y) (by scalar_tac)
  cases hx : x * y <;> rw [hx] at hs <;> simp_all

/-- A `usize` difference that stays in range returns the difference. -/
theorem usize_sub_ok (x y : Std.Usize) (h : y.val ≤ x.val) :
    ∃ z, x - y = ok z ∧ z.val = x.val - y.val := by
  have hs := UScalar.sub_spec (x := x) (y := y) h
  cases hx : x - y <;> rw [hx] at hs <;> simp_all

/-- The arithmetic of the length guard. -/
theorem guard_arith : (3#usize * 4#usize : Result Std.Usize) = ok 12#usize ∧
    (1#usize + 12#usize : Result Std.Usize) = ok 13#usize ∧
    (13#usize + 8#usize : Result Std.Usize) = ok 21#usize := by
  have hmax : 21 ≤ Std.Usize.max := by scalar_tac
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨z, hz, hv⟩ := usize_mul_ok 3#usize 4#usize (by simp; omega)
    have : z = 12#usize := by apply UScalar.eq_of_val_eq; simpa using hv
    rw [hz, this]
  · obtain ⟨z, hz, hv⟩ := usize_add_ok 1#usize 12#usize (by simp; omega)
    have : z = 13#usize := by apply UScalar.eq_of_val_eq; simpa using hv
    rw [hz, this]
  · obtain ⟨z, hz, hv⟩ := usize_add_ok 13#usize 8#usize (by simp; omega)
    have : z = 21#usize := by apply UScalar.eq_of_val_eq; simpa using hv
    rw [hz, this]

/-- A blob error of `new_from_serialized` for a short blob. -/
theorem nfs_err_short (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8) (hidden : Slice KeyParam)
    (h : data.val.length < minBlobLen) :
    ∃ e, sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Err e) ∧
      IsBlobErr root e := by
  obtain ⟨hnew, hctx, hfmt⟩ := hlaw
  obtain ⟨n, hn, hn4⟩ := hsize
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨s, hs⟩ := hfmt noArgs
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s
  refine ⟨e1, ?_, by unfold IsBlobErr; rw [hr1, hr0]⟩
  have hn' : n = 4#usize := by apply UScalar.eq_of_val_eq; simpa using hn4
  subst hn'
  unfold sw_keyblob.KeyBlob.new_from_serialized
  have hlt : data.len < 21#usize := by
    have : data.len.val = data.val.length := Slice.len_val data
    unfold minBlobLen at h
    scalar_tac
  obtain ⟨h1, h2, h3⟩ := guard_arith
  have h21 : data.val.length < 21 := h
  simp [hn, mac_len_eq, h1, h2, h3, h21, he0, hs, core.hint.must_use, he1]

/-- The part of `new_from_serialized` after the call of `compute_hmac`, as a function of the
outcome `r` of that call, the blob and the last 8 bytes of the blob `mac`. -/
noncomputable def nfsAfter (data mac : Slice Std.U8)
    (r : core.result.Result (alloc.vec.Vec Std.U8) anyhow.Error) :
    Result (core.result.Result sw_keyblob.KeyBlob anyhow.Error) := do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let b ←
      Shared0Slice.Insts.CoreCmpPartialEqVec.ne alloc.alloc.Global
        core.cmp.PartialEqU8 mac val
    if b
    then
      let e ←
        anyhow.error.Error.new error.Error.Insts.CoreErrorError
          (error.Error.Km
          ErrorCode.ErrorCode.INVALID_KEY_BLOB)
      let a ←
        core.fmt.Arguments.from_str_nonconst (toStr
          "keystore2/src/sw_keyblob.rs:243: invalid key blob")
      let s1 ← alloc.fmt.format a
      let s2 ← core.hint.must_use s1
      let e1 ←
        anyhow.error.Error.context alloc.string.String.Insts.CoreFmtDisplay e
          s2
      ok (core.result.Result.Err e1)
    else
      let (r1, data1) ← sw_keyblob.consume_u8 data
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        if val1 != sw_keyblob.KeyBlob.KEY_BLOB_VERSION
        then
          let e ←
            anyhow.error.Error.new error.Error.Insts.CoreErrorError
              (error.Error.Km
              ErrorCode.ErrorCode.INVALID_KEY_BLOB)
          let a ←
            core.fmt.rt.Argument.new_display U8.Insts.CoreFmtDisplay val1
          let a1 ←
            core.fmt.Arguments.new
              (Array.make 60#usize [
                57#u8, 107#u8, 101#u8, 121#u8, 115#u8, 116#u8, 111#u8,
                114#u8, 101#u8, 50#u8, 47#u8, 115#u8, 114#u8, 99#u8, 47#u8,
                115#u8, 119#u8, 95#u8, 107#u8, 101#u8, 121#u8, 98#u8, 108#u8,
                111#u8, 98#u8, 46#u8, 114#u8, 115#u8, 58#u8, 50#u8, 52#u8,
                56#u8, 58#u8, 32#u8, 117#u8, 110#u8, 101#u8, 120#u8, 112#u8,
                101#u8, 99#u8, 116#u8, 101#u8, 100#u8, 32#u8, 98#u8, 108#u8,
                111#u8, 98#u8, 32#u8, 118#u8, 101#u8, 114#u8, 115#u8, 105#u8,
                111#u8, 110#u8, 32#u8, 192#u8, 0#u8
                ]) (Array.make 1#usize [ a ])
          let s1 ← alloc.fmt.format a1
          let s2 ← core.hint.must_use s1
          let e1 ←
            anyhow.error.Error.context
              alloc.string.String.Insts.CoreFmtDisplay e s2
          ok (core.result.Result.Err e1)
        else
          let (r2, data2) ← sw_keyblob.consume_vec data1
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let (r3, data3) ← sw_keyblob.deserialize_params data2
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              let (r4, data4) ← sw_keyblob.deserialize_params data3
              let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue val4 =>
                let rest ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)
                    data4 { start := sw_keyblob.KeyBlob.MAC_LEN }
                let b1 ← core.slice.Slice.is_empty rest
                if b1
                then
                  ok (core.result.Result.Ok
                    {
                      key_material := val2,
                      hw_enforced := val3,
                      sw_enforced := val4
                    })
                else
                  let e ←
                    anyhow.error.Error.new error.Error.Insts.CoreErrorError
                      (error.Error.Km
                      ErrorCode.ErrorCode.INVALID_KEY_BLOB)
                  let args := Slice.len rest
                  let a ←
                    core.fmt.rt.Argument.new_display
                      Usize.Insts.CoreFmtDisplay args
                  let a1 ←
                    core.fmt.Arguments.new
                      (Array.make 54#usize [
                        49#u8, 107#u8, 101#u8, 121#u8, 115#u8, 116#u8,
                        111#u8, 114#u8, 101#u8, 50#u8, 47#u8, 115#u8, 114#u8,
                        99#u8, 47#u8, 115#u8, 119#u8, 95#u8, 107#u8, 101#u8,
                        121#u8, 98#u8, 108#u8, 111#u8, 98#u8, 46#u8, 114#u8,
                        115#u8, 58#u8, 50#u8, 53#u8, 55#u8, 58#u8, 32#u8,
                        101#u8, 120#u8, 116#u8, 114#u8, 97#u8, 32#u8, 100#u8,
                        97#u8, 116#u8, 97#u8, 32#u8, 40#u8, 108#u8, 101#u8,
                        110#u8, 32#u8, 192#u8, 1#u8, 41#u8, 0#u8
                        ]) (Array.make 1#usize [ a ])
                  let s1 ← alloc.fmt.format a1
                  let s2 ← core.hint.must_use s1
                  let e1 ←
                    anyhow.error.Error.context
                      alloc.string.String.Insts.CoreFmtDisplay e s2
                  ok (core.result.Result.Err e1)
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  sw_keyblob.KeyBlob (core.convert.FromSame anyhow.Error)
                  residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                sw_keyblob.KeyBlob (core.convert.FromSame anyhow.Error)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              sw_keyblob.KeyBlob (core.convert.FromSame anyhow.Error)
              residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          sw_keyblob.KeyBlob (core.convert.FromSame anyhow.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      sw_keyblob.KeyBlob (core.convert.FromSame anyhow.Error) residual

/-- For a blob of at least 21 bytes, `new_from_serialized` computes the MAC of all bytes but the
last 8 and continues with `nfsAfter`. -/
theorem nfs_eq (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8) (hidden : Slice KeyParam)
    (h : minBlobLen ≤ data.val.length) (s : Slice Std.U8)
    (hs : s.val = data.val.take (data.val.length - 8)) :
    ∃ mac : Slice Std.U8, mac.val = data.val.drop (data.val.length - 8) ∧
      sw_keyblob.KeyBlob.new_from_serialized data hidden =
        (do let r ← sw_keyblob.KeyBlob.compute_hmac s hidden; nfsAfter data mac r) := by
  obtain ⟨n, hn, hn4⟩ := hsize
  have hn' : n = 4#usize := by apply UScalar.eq_of_val_eq; simpa using hn4
  subst hn'
  obtain ⟨h1, h2, h3⟩ := guard_arith
  have hlen : data.len.val = data.val.length := Slice.len_val data
  unfold minBlobLen at h
  obtain ⟨i6, hi6, hv6⟩ := usize_sub_ok data.len 8#usize (by simp; omega)
  have hv6' : i6.val = data.val.length - 8 := by simpa [hlen] using hv6
  refine ⟨data.drop i6, by simp [hv6'], ?_⟩
  have hile : i6.val ≤ data.val.length := by omega
  have hss : (Slice.from (List.take i6.val data.val) (by scalar_tac) : Slice Std.U8) = s := by
    apply Slice.ext
    simp [hs, hv6']
  have hidx1 : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) data { start := i6 } =
      ok (data.drop i6) := by
    simp [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeFromUsizeSlice.index, hile]
  have hidx2 : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) data { «end» := i6 } = ok s := by
    simp [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeToUsizeSlice.index, hile,
      ← hss]
  have hnl : ¬ data.len < 21#usize := by
    have : (21#usize : Std.Usize).val = 21 := by simp
    rw [Std.UScalar.lt_equiv]; omega
  unfold sw_keyblob.KeyBlob.new_from_serialized nfsAfter
  simp only [hn, h1, h2, h3, mac_len_eq, hnl, hi6, hidx1, hidx2, Std.bind_ok, ite_false]
  rfl

/-- A bind whose continuation never returns `r` never returns `r`. -/
theorem bind_ne_ok {A B : Type} (x : Result A) (k : A → Result B) (r : B)
    (hk : ∀ a, k a ≠ ok r) : (x >>= k) ≠ ok r := by
  cases x <;> simp [hk]

/-- A blob that is too short does not parse. -/
theorem nfs_short_not_ok (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (kb : sw_keyblob.KeyBlob) (h : data.val.length < minBlobLen) :
    sw_keyblob.KeyBlob.new_from_serialized data hidden ≠ ok (.Ok kb) := by
  obtain ⟨n, hn, hn4⟩ := hsize
  have hn' : n = 4#usize := by apply UScalar.eq_of_val_eq; simpa using hn4
  subst hn'
  obtain ⟨h1, h2, h3⟩ := guard_arith
  have h21 : data.val.length < 21 := h
  unfold sw_keyblob.KeyBlob.new_from_serialized
  simp only [hn, h1, h2, h3, mac_len_eq, Std.bind_ok]
  have hlt : data.len < 21#usize := by
    have : data.len.val = data.val.length := Slice.len_val data
    scalar_tac
  simp only [hlt, ite_true]
  repeat (apply bind_ne_ok; intro _)
  simp

/-- A blob of at least 21 bytes with a wrong MAC is an error of the blob class. -/
theorem nfs_err_mac (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (h : minBlobLen ≤ data.val.length) (s : Slice Std.U8)
    (hs : s.val = data.val.take (data.val.length - 8)) (m : alloc.vec.Vec Std.U8)
    (hmac : sw_keyblob.KeyBlob.compute_hmac s hidden = ok (.Ok m))
    (hbad : data.val.drop (data.val.length - 8) ≠ m.val) :
    ∃ e, sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Err e) ∧
      IsBlobErr root e := by
  obtain ⟨⟨hnew, hctx, hfmt⟩, hstr⟩ := hlaw
  obtain ⟨mac, hmv, heq⟩ := nfs_eq hsize data hidden h s hs
  obtain ⟨b, hb, hbt⟩ := hne mac m
  have hbtrue : b = true := hbt.mpr (by rw [hmv]; exact hbad)
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨a, ha⟩ := hstr (toStr "keystore2/src/sw_keyblob.rs:243: invalid key blob")
  obtain ⟨s0, hs0⟩ := hfmt a
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s0
  refine ⟨e1, ?_, by unfold IsBlobErr; rw [hr1, hr0]⟩
  rw [heq]
  simp [hmac, nfsAfter, core.result.Result.Insts.CoreOpsTry.branch, hb, hbtrue, he0, ha, hs0,
    core.hint.must_use, he1]

/-- If `new_from_serialized` returns `Ok`, the length guard and the MAC check passed. -/
theorem nfs_ok_mac (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (data : Slice Std.U8) (hidden : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (h : sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Ok kb)) :
    MacOk data hidden := by
  have hlen : minBlobLen ≤ data.val.length := by
    by_contra hlt
    exact nfs_short_not_ok hsize data hidden kb (by omega) h
  have hmaxl : (data.val.take (data.val.length - 8)).length ≤ Std.Usize.max :=
    (List.length_take_le' _ _).trans (Slice.length_ineq data)
  obtain ⟨mac, hmv, heq⟩ := nfs_eq hsize data hidden hlen
    (Slice.from (data.val.take (data.val.length - 8)) hmaxl) (by simp)
  rw [heq] at h
  cases hc : sw_keyblob.KeyBlob.compute_hmac
      (Slice.from (data.val.take (data.val.length - 8)) hmaxl) hidden with
  | ret r =>
    cases r with
    | Ok m =>
      obtain ⟨b, hb, hbt⟩ := hne mac m
      cases hbb : b with
      | true =>
        simp [hc, nfsAfter, core.result.Result.Insts.CoreOpsTry.branch, hb, hbb] at h
        exact absurd h (by repeat (apply bind_ne_ok; intro _); simp)
      | false =>
        have hne' : ¬ mac.val ≠ m.val := fun hh => by simpa [hbb] using hbt.mpr hh
        refine ⟨hlen, _, m, by simp, hc, ?_⟩
        rw [← hmv]; exact not_not.mp hne'
    | Err e =>
      simp [hc, nfsAfter, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from] at h
  | vis i k => simp [hc] at h
  | div => simp [hc] at h

/-- If the checks before the parameter lists pass, both lists parse and fewer than 8 bytes
remain, `new_from_serialized` fails. -/
theorem nfs_fail_rest (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (hpast : PastKey data hidden) (d2 : Slice Std.U8)
    (hd2 : d2.val = data.val.drop (5 + u32At data.val 1))
    (hw : alloc.vec.Vec KeyParam) (d3 : Slice Std.U8)
    (hdes1 : sw_keyblob.deserialize_params d2 = ok (.Ok hw, d3))
    (sw : alloc.vec.Vec KeyParam) (d4 : Slice Std.U8)
    (hdes2 : sw_keyblob.deserialize_params d3 = ok (.Ok sw, d4))
    (hrest : d4.val.length < 8) :
    ∃ x, sw_keyblob.KeyBlob.new_from_serialized data hidden = fail x := by
  obtain ⟨⟨hlen, s0, m, hs0, hmac, hdrop⟩, hhead, hkey⟩ := hpast
  obtain ⟨mac, hmv, heq⟩ := nfs_eq hsize data hidden hlen s0 hs0
  obtain ⟨b, hb, hbt⟩ := hne mac m
  have hbf : b = false := by
    cases hbb : b
    · rfl
    · exact absurd (by rw [hmv]; exact hdrop) (hbt.mp hbb)
  obtain ⟨rest, hdv⟩ : ∃ rest, data.val = 0#u8 :: rest := by
    cases hd : data.val with
    | nil => simp [hd] at hhead
    | cons a r => simp [hd] at hhead; exact ⟨r, by rw [hhead]⟩
  obtain ⟨data1, hc1, hd1⟩ := consume_u8_ok hfirst data 0#u8 rest hdv
  unfold minBlobLen at hlen
  have hlen1 : data1.val.length = data.val.length - 1 := by
    rw [hd1, hdv]; simp
  have h4 : 4 ≤ data1.val.length := by omega
  have hu : u32At data1.val 0 = u32At data.val 1 := by
    rw [hd1, hdv]; simp [u32At]
  obtain ⟨v, data2, hc2, -, hd2'⟩ := consume_vec_ok hsize hfrom data1 h4 (by omega)
  have hdd : data2 = d2 := by
    apply Slice.ext
    rw [hd2', hd2, hd1, hdv]
    simp [u32At, Nat.add_comm 5, Nat.add_comm 4]
  subst hdd
  refine ⟨Error.undef, ?_⟩
  have hr8 : ¬ 8 ≤ d4.val.length := by omega
  rw [heq]
  simp [hmac, nfsAfter, core.result.Result.Insts.CoreOpsTry.branch, hb, hbf, hc1, hc2, hdes1,
    hdes2, blob_version_eq, mac_len_eq, core.slice.index.SliceIndexRangeFromUsizeSlice.index, hr8]

end Keystore2Verify.SwKeyblob
