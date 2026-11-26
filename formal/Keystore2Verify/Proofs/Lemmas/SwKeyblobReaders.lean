import Keystore2Verify.Specs.Defs.SwKeyblob

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- The only value of `core.fmt.Arguments`, which the Aeneas model erases to `Unit`. -/
def noArgs : core.fmt.Arguments := ()

/-- The only value of `core.fmt.rt.Argument`, which the Aeneas model erases to `Unit`. -/
def noArg : core.fmt.rt.Argument := ()

/-- `Arguments::new` always returns the erased value. -/
@[simp] theorem args_new_eq {N M : Std.Usize} (a : Std.Array Std.U8 N)
    (b : Std.Array core.fmt.rt.Argument M) : core.fmt.Arguments.new a b = ok noArgs := rfl

/-- `Argument::new_display` always returns the erased value. -/
@[simp] theorem arg_new_display_eq {T : Type} (i : core.fmt.Display T) (x : T) :
    core.fmt.rt.Argument.new_display i x = ok noArg := rfl

/-- A `usize` addition that stays in range returns the sum. -/
theorem usize_add_ok (x y : Std.Usize) (h : x.val + y.val ≤ Std.Usize.max) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
  have hs := UScalar.add_spec (x := x) (y := y) (by scalar_tac)
  cases hx : x + y <;> rw [hx] at hs <;> simp_all

/-- A `usize` addition that leaves the range fails with `integerOverflow`. -/
theorem usize_add_fail (x y : Std.Usize) (h : Std.Usize.max < x.val + y.val) :
    x + y = fail .integerOverflow := by
  have h' : ¬ (x.val + y.val < 2 ^ System.Platform.numBits) := by scalar_tac
  show UScalar.tryMk .Usize (x.val + y.val) = _
  simp [UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, h', Result.ofOption]

/-- The first word of the list after 4 bytes is the word at index 4. -/
theorem u32At_drop_four (l : List Std.U8) : u32At (l.drop 4) 0 = u32At l 4 := by
  simp [u32At]

/-- A push that fits in the vector model appends the element. -/
theorem push_ok_aux (v : alloc.vec.Vec Std.U8) (x : Std.U8)
    (h : v.val.length + 1 ≤ Std.Usize.max) :
    ∃ v', alloc.vec.Vec.push v x = ok v' ∧ v'.val = v.val ++ [x] := by
  have hs := alloc.vec.Vec.push_spec v x (by omega)
  cases hx : alloc.vec.Vec.push v x <;> rw [hx] at hs <;> simp_all

/-- A push that does not fit in the vector model fails. -/
theorem push_fail_aux (v : alloc.vec.Vec Std.U8) (x : Std.U8)
    (h : Std.Usize.max < v.val.length + 1) :
    alloc.vec.Vec.push v x = fail .maximumSizeExceeded := by
  unfold alloc.vec.Vec.push
  simp
  exact ⟨by scalar_tac, by omega⟩

/-- Shifting a `usize` right by 8 divides by 256. -/
theorem usize_shr8 (x : Std.Usize) :
    ∃ z, x >>> 8#i32 = ok z ∧ z.val = x.val / 256 := by
  have hs := Usize.ShiftRight_IScalar_spec x 8#i32 (by decide)
    (by have := System.Platform.numBits_eq; simp; omega)
  cases hx : x >>> 8#i32 <;> rw [hx] at hs <;> simp_all [Nat.shiftRight_eq_div_pow]

/-- `to_vec` on a slice of bytes returns a vector with the same bytes. -/
theorem to_vec_u8 (s : Slice Std.U8) :
    ∃ v, alloc.slice.Slice.to_vec core.clone.CloneU8 s = ok v ∧ v.val = s.val := by
  have hs := alloc.slice.Slice.to_vec_spec core.clone.CloneU8 s (fun _ _ => rfl)
  cases hx : alloc.slice.Slice.to_vec core.clone.CloneU8 s <;> rw [hx] at hs <;>
    simp_all [alloc.vec.Vec.val]

/-- `consume_u32` on fewer than 4 bytes. -/
theorem consume_u32_err_aux (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8) (h : data.val.length < 4) :
    ∃ e, sw_keyblob.consume_u32 data = ok (.Err e, data) ∧ IsBlobErr root e := by
  obtain ⟨hnew, hctx, hfmt⟩ := hlaw
  obtain ⟨n, hn, hn4⟩ := hsize
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨s, hs⟩ := hfmt noArgs
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s
  refine ⟨e1, ?_, by unfold IsBlobErr; rw [hr1, hr0]⟩
  unfold sw_keyblob.consume_u32
  rw [show sw_keyblob.consume_u32.LEN = ok n from by
    unfold sw_keyblob.consume_u32.LEN; exact hn]
  have hlt : data.val.length < n.val := by omega
  simp [hlt, he0, hs, core.hint.must_use, he1]

/-- `consume_u32` on at least 4 bytes. -/
theorem consume_u32_ok_aux (hsize : SizeOfLaw Std.U32 4) (hfrom : CoreNumU32FromNeBytesSpec)
    (data : Slice Std.U8) (h : 4 ≤ data.val.length) :
    ∃ x data', sw_keyblob.consume_u32 data = ok (.Ok x, data') ∧
      x.val = u32At data.val 0 ∧ data'.val = data.val.drop 4 := by
  obtain ⟨n, hn, hn4⟩ := hsize
  unfold sw_keyblob.consume_u32
  rw [show sw_keyblob.consume_u32.LEN = ok n from by
    unfold sw_keyblob.consume_u32.LEN; exact hn]
  have hlt : ¬ data.val.length < 4 := by omega
  simp [hlt, h, core.slice.index.SliceIndexRangeToUsizeSlice.index,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index, hn4,
    core.array.TryFromArrayCopySlice.try_from]
  have hl4 : (data.val.take 4).length = 4 := by simp; omega
  simp [core.result.Result.unwrap]
  obtain ⟨x, hx, hbv⟩ := hfrom (Array.from (List.take 4 data.val) (by simpa using hl4))
  refine ⟨x, data.drop n, by simp [hx], ?_, by simp [hn4]⟩
  have hlt : leNat (List.take 4 data.val) < 2 ^ 32 := by
    have := Nat.ofDigits_lt_base_pow_length (b := 256)
      (l := (List.take 4 data.val).map (·.val)) (by omega)
      (by simp only [List.mem_map]; rintro _ ⟨a, -, rfl⟩; exact a.hmax)
    simpa [leNat, Nat.min_eq_left h] using this
  have h1 := congrArg BitVec.toNat hbv
  simp only [UScalar.bv_toNat] at h1
  have h2 := h1.trans (BitVec.toNat_ofNat _ _)
  rw [Nat.mod_eq_of_lt (by simpa using hlt)] at h2
  simp [h2, u32At]

end Keystore2Verify.SwKeyblob
