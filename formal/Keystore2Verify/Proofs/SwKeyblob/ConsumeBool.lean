import Keystore2Verify.Proofs.SwKeyblob.ConsumeU8

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- conditional: on an empty slice, `consume_bool` returns an error whose root cause is
`INVALID_KEY_BLOB`, and the slice is returned unchanged. Hypotheses: `BlobErrLaws` and the law
`CoreSliceFirstSpec`. -/
theorem consume_bool_err_empty (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hfirst : CoreSliceFirstSpec) (data : Slice Std.U8) (h : data.val = []) :
    ∃ e, sw_keyblob.consume_bool data = ok (.Err e, data) ∧ IsBlobErr root e := by
  obtain ⟨e, he, hr⟩ := consume_u8_err root hlaw hfirst data h
  refine ⟨e, ?_, hr⟩
  unfold sw_keyblob.consume_bool
  simp [he, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]

/-- conditional: on a slice that starts with the byte 1, `consume_bool` returns `Ok true`, and
the slice moves forward by one byte. Hypothesis: the law `CoreSliceFirstSpec`. -/
theorem consume_bool_true (hfirst : CoreSliceFirstSpec) (data : Slice Std.U8)
    (rest : List Std.U8) (h : data.val = 1#u8 :: rest) :
    ∃ data', sw_keyblob.consume_bool data = ok (.Ok true, data') ∧ data'.val = rest := by
  obtain ⟨data1, hd, hv⟩ := consume_u8_ok hfirst data 1#u8 rest h
  refine ⟨data1, ?_, hv⟩
  unfold sw_keyblob.consume_bool
  simp [hd, core.result.Result.Insts.CoreOpsTry.branch]

/-- conditional: on a slice that starts with a byte other than 1 (0 included), `consume_bool`
returns an error whose root cause is `INVALID_KEY_BLOB`, and the slice has moved forward by one
byte. It never returns `Ok false`. Hypotheses: `BlobErrLaws` and the law `CoreSliceFirstSpec`. -/
theorem consume_bool_err_value (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hfirst : CoreSliceFirstSpec) (data : Slice Std.U8) (b : Std.U8) (rest : List Std.U8)
    (h : data.val = b :: rest) (hb : b.val ≠ 1) :
    ∃ e data', sw_keyblob.consume_bool data = ok (.Err e, data') ∧ IsBlobErr root e ∧
      data'.val = rest := by
  obtain ⟨⟨hnew, hctx, hfmt⟩, hstr⟩ := hlaw
  obtain ⟨data1, hd, hv⟩ := consume_u8_ok hfirst data b rest h
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨a, ha⟩ :=
    hstr (toStr "keystore2/src/sw_keyblob.rs:315: bool value other than 1 encountered")
  obtain ⟨s, hs⟩ := hfmt a
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s
  refine ⟨e1, data1, ?_, by unfold IsBlobErr; rw [hr1, hr0], hv⟩
  have hb1 : b ≠ 1#u8 := fun hh => hb (by rw [hh]; rfl)
  unfold sw_keyblob.consume_bool
  simp [hd, core.result.Result.Insts.CoreOpsTry.branch, hb1, he0, ha, hs,
    core.hint.must_use, he1]
end Keystore2Verify.SwKeyblob
