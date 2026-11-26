import Keystore2Verify.Specs.Defs.SwKeyblob
import Keystore2Verify.Proofs.Lemmas.SwKeyblobExportBody
import Keystore2Verify.Proofs.SwKeyblob.Pkcs8WrapNistKey
import Keystore2Verify.Proofs.Lemmas.SwKeyblobExportWrap

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open alloc.vec

/-! The forward statements fix outcomes of the calls that `export_key` makes and say what it
returns. The success inverses instead start from the returned value. `ParsesTo` is the call of `new_from_serialized`, `comb` is the hardware
enforced parameters followed by the software enforced ones, and the tag lookups are
`get_tag_value` on `comb`. Its existence witnesses model capacity, not Rust byte capacity or
allocation success. Outcomes of opaque calls are explicit hypotheses in the forward statements
and recovered witnesses in the inverses. -/

/-- conditional: if `hidden_params` fails, `export_key` returns the same `fail x`. The translated
`hidden_params` returns a vector, never `Err`, so there is no error case to state. It is the
first call of `export_key`. Hypothesis: the failure `x` as the outcome of `hidden_params` on
`params` and the software root of trust. -/
theorem export_key_fail_hidden (data : Slice Std.U8) (params : Slice KeyParam) (x : Error)
    (hh : sw_keyblob.hidden_params params
      (Array.to_slice (Array.make 1#usize [sw_keyblob.SOFTWARE_ROOT_OF_TRUST])) = fail x) :
    sw_keyblob.export_key data params = fail x := by
  unfold sw_keyblob.export_key
  simp [lift, hh]

/-- conditional: if `export_key` returns `Ok`, the blob passed the MAC check. There is a hidden
input `hidden`, the outcome of `hidden_params` on `params` (`HiddenOf`), such that the blob has at
least 21 bytes and its last 8 bytes equal the MAC computed over the other bytes and `hidden`
(`MacOk`). The outcome of `hidden_params` is derived from the observed success, not assumed. This
is a fact about the control flow of the function; it says nothing about the strength of the MAC.
Hypotheses: the laws `SizeOfLaw Std.U32 4` and `Shared0SliceNeSpec`. -/
theorem export_key_ok_mac (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (data : Slice Std.U8) (params : Slice KeyParam)
    (out : KeyFormat.KeyFormat × alloc.vec.Vec Std.U8 × alloc.vec.Vec KeyParam)
    (h : sw_keyblob.export_key data params = ok (.Ok out)) :
    ∃ hidden, HiddenOf params hidden ∧ MacOk data hidden := by
  obtain ⟨kb, hidden, hid, hn⟩ := ek_ok_parse data params out h
  exact ⟨hidden, hid, nfs_ok_mac hsize hne data hidden kb hn⟩

/-- conditional: a blob of fewer than 21 bytes gives an error whose root cause is
`INVALID_KEY_BLOB`. Hypotheses: `HiddenOf` (the outcome of `hidden_params`), `BlobErrFmtLaws`, and
the law `SizeOfLaw Std.U32 4`. -/
theorem export_key_err_short (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8) (params hidden : Slice KeyParam)
    (hid : HiddenOf params hidden) (h : data.val.length < minBlobLen) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e := by
  obtain ⟨e, he, hr⟩ := nfs_err_short root hlaw hsize data hidden h
  exact ⟨e, ek_err_parse data params e ⟨hidden, hid, he⟩, hr⟩

/-- conditional: if the MAC of the blob does not match, `export_key` returns an error whose root
cause is `INVALID_KEY_BLOB`. Hypotheses: `HiddenOf`, the blob has at least 21 bytes, the outcome
of `compute_hmac` on all bytes but the last 8 (`s`) and the hidden input, the last 8 bytes
differ from it, `BlobErrLaws`, and the laws `SizeOfLaw Std.U32 4` and `Shared0SliceNeSpec`. -/
theorem export_key_err_mac (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec) (data : Slice Std.U8)
    (params hidden : Slice KeyParam) (hid : HiddenOf params hidden)
    (h : minBlobLen ≤ data.val.length) (s : Slice Std.U8)
    (hs : s.val = data.val.take (data.val.length - 8)) (m : alloc.vec.Vec Std.U8)
    (hmac : sw_keyblob.KeyBlob.compute_hmac s hidden = ok (.Ok m))
    (hbad : data.val.drop (data.val.length - 8) ≠ m.val) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e := by
  obtain ⟨e, he, hr⟩ := nfs_err_mac root hlaw hsize hne data hidden h s hs m hmac hbad
  exact ⟨e, ek_err_parse data params e ⟨hidden, hid, he⟩, hr⟩

/-- conditional: if the parser returns `Err e`, then `export_key` returns the same
error `e`: the error value is passed through unchanged. This covers every error of
`new_from_serialized`. Hypothesis: `ParsesTo` with the result `Err e`. -/
theorem export_key_err_parse (data : Slice Std.U8)
    (params : Slice KeyParam) (e : anyhow.Error)
    (hp : ParsesTo data params (ok (.Err e))) :
    sw_keyblob.export_key data params = ok (.Err e) := by
  exact ek_err_parse data params e hp

/-- conditional: if the parser fails, then `export_key` returns the same `fail x`. Hypothesis:
`ParsesTo` with the failure `x`. -/
theorem export_key_fail_parse (data : Slice Std.U8) (params : Slice KeyParam) (x : Error)
    (hp : ParsesTo data params (fail x)) :
    sw_keyblob.export_key data params = fail x := by
  exact ek_fail_parse data params x hp

/-- conditional: if both parameter lists parse and the remaining slice is shorter than the MAC,
the parser's outer failure propagates to `export_key`. A reading of the Rust source shows that
this panic is reachable (`data[8..]` in `sw_keyblob.rs:255`, where the parser reads from the
whole blob, the MAC bytes included). The Lean statement assumes the hidden parameters, the
parser outcomes and the length of the remainder. Hypotheses: `HiddenOf`, `PastKey` (the MAC is
good, the version is 0, and the key material fits), both calls of `deserialize_params` return
`Ok`, the slice `d4` that is left is shorter than 8 bytes, and the laws
`SizeOfLaw Std.U32 4`, `Shared0SliceNeSpec`, `CoreSliceFirstSpec` and
`CoreNumU32FromNeBytesSpec`. -/
theorem export_key_fail_rest (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (params hidden : Slice KeyParam) (hid : HiddenOf params hidden)
    (hpast : PastKey data hidden) (d2 : Slice Std.U8)
    (hd2 : d2.val = data.val.drop (5 + u32At data.val 1))
    (hw : alloc.vec.Vec KeyParam) (d3 : Slice Std.U8)
    (hdes1 : sw_keyblob.deserialize_params d2 = ok (.Ok hw, d3))
    (sw : alloc.vec.Vec KeyParam) (d4 : Slice Std.U8)
    (hdes2 : sw_keyblob.deserialize_params d3 = ok (.Ok sw, d4))
    (hrest : d4.val.length < 8) :
    ∃ x, sw_keyblob.export_key data params = fail x := by
  obtain ⟨x, hx⟩ := nfs_fail_rest hsize hne hfirst hfrom data hidden hpast d2 hd2 hw d3 hdes1 sw
    d4 hdes2 hrest
  exact ⟨x, ek_fail_parse data params x ⟨hidden, hid, hx⟩⟩

/-- conditional: if the parser returns a blob whose two parameter lists do not fit in one vector,
`export_key` panics. Hypotheses: `ParsesTo` with `Ok kb`, and the lengths of the two lists add up
to more than `Usize.max`. That is the bound of the Aeneas vector model (`CombinedFits`); in Rust
the panic comes at the lower limit of `isize::MAX` bytes, which for `KeyParameter` is a smaller
count. So this statement describes the model and is not a capacity guarantee for the Rust code. -/
theorem export_key_fail_capacity (data : Slice Std.U8) (params : Slice KeyParam)
    (kb : sw_keyblob.KeyBlob) (hp : ParsesTo data params (ok (.Ok kb)))
    (hover : ¬ CombinedFits kb) :
    sw_keyblob.export_key data params = fail .panic := by
  obtain ⟨hidden, ⟨rots, hv, hr, hh, hd⟩, hn⟩ := hp
  subst hr hd
  unfold sw_keyblob.export_key
  have hover' : ¬ ((kb.hw_enforced.val).length + (Vec.deref kb.sw_enforced).val.length ≤
      Std.Usize.max) := by
    unfold CombinedFits at hover
    simpa [Vec.deref] using hover
  simp [lift, hh, hn, core.result.Result.Insts.CoreOpsTry.branch,
    alloc.vec.Vec.extend_from_slice, hover']

/-- conditional: if the `ALGORITHM` lookup returns `none`, `export_key` returns an error whose root
cause is `INVALID_KEY_BLOB`. Hypotheses: `ParsesTo` with `Ok kb`, `comb` is the two lists joined,
`get_tag_value comb ALGORITHM` returns `none`, `BlobErrLaws`, and the law
`KeyParameterCloneLaw`. -/
theorem export_key_err_no_algorithm (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hclone : KeyParameterCloneLaw) (data : Slice Std.U8) (params : Slice KeyParam)
    (kb : sw_keyblob.KeyBlob) (hp : ParsesTo data params (ok (.Ok kb)))
    (comb : Slice KeyParam) (hcomb : CombinedOf kb comb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok none) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e := by
  obtain ⟨⟨hnew, hctx, hfmt⟩, hstr⟩ := hlaw
  obtain ⟨hidden, ⟨rots, hv, hr, hh, hd⟩, hn⟩ := hp
  subst hr hd
  obtain ⟨cs, hex, hcs⟩ := ek_comb hclone kb comb hcomb
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨a, ha⟩ := hstr (toStr "keystore2/src/sw_keyblob.rs:67: No algorithm found!")
  obtain ⟨s0, hs0⟩ := hfmt a
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s0
  refine ⟨e1, ?_, by unfold IsBlobErr; rw [hr1, hr0]⟩
  unfold sw_keyblob.export_key
  simp [lift, hh, hn, hex, hcs, hget, core.result.Result.Insts.CoreOpsTry.branch,
    core.option.Option.ok_or_else,
    sw_keyblob.export_key.closure.Insts.CoreOpsFunctionFnOnceTupleError.call_once, he0, ha, hs0,
    core.hint.must_use, he1,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]

set_option maxHeartbeats 1000000 in
/-- conditional: if the returned `ALGORITHM` value is not `Algorithm` of AES, triple DES, HMAC, RSA
or EC (ML-DSA, any other integer, or a value of another kind), `export_key` returns an error whose
root cause is `INVALID_KEY_BLOB`. Hypotheses: as for `export_key_err_no_algorithm`, with
`BlobErrFmtLaws` in place of `BlobErrLaws`, `get_tag_value` returning `some v` and `v` not a
`KnownAlgorithm`, and the law `KeyParameterCloneLaw`. -/
theorem export_key_err_algorithm (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hclone : KeyParameterCloneLaw) (data : Slice Std.U8) (params : Slice KeyParam)
    (kb : sw_keyblob.KeyBlob) (hp : ParsesTo data params (ok (.Ok kb)))
    (comb : Slice KeyParam) (hcomb : CombinedOf kb comb)
    (v : ParamValue) (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some v))
    (hv : ¬ KnownAlgorithm v) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e := by
  obtain ⟨hnew, hctx, hfmt⟩ := hlaw
  obtain ⟨hidden, ⟨rots, hvv, hr, hh, hd⟩, hn⟩ := hp
  subst hr hd
  obtain ⟨cs, hex, hcs⟩ := ek_comb hclone kb comb hcomb
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨s0, hs0⟩ := hfmt noArgs
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s0
  refine ⟨e1, ?_, by unfold IsBlobErr; rw [hr1, hr0]⟩
  unfold sw_keyblob.export_key
  cases v with
  | Algorithm a =>
    have n32 : a ≠ 32#i32 := fun h => hv ⟨a, rfl, Or.inl (Or.inl h)⟩
    have n33 : a ≠ 33#i32 := fun h => hv ⟨a, rfl, Or.inl (Or.inr (Or.inl h))⟩
    have n128 : a ≠ 128#i32 := fun h => hv ⟨a, rfl, Or.inl (Or.inr (Or.inr h))⟩
    have n1 : a ≠ 1#i32 := fun h => hv ⟨a, rfl, Or.inr (Or.inl h)⟩
    have n3 : a ≠ 3#i32 := fun h => hv ⟨a, rfl, Or.inr (Or.inr h)⟩
    simp [lift, hh, hn, hex, hcs, hget, core.result.Result.Insts.CoreOpsTry.branch,
      core.option.Option.ok_or_else]
    split <;> first
      | (simp [he0, hs0, core.hint.must_use, he1]; done)
      | exact absurd rfl n32 | exact absurd rfl n33 | exact absurd rfl n128
      | exact absurd rfl n1 | exact absurd rfl n3
  | _ =>
    simp [lift, hh, hn, hex, hcs, hget, core.result.Result.Insts.CoreOpsTry.branch,
      core.option.Option.ok_or_else, he0, hs0, core.hint.must_use, he1]

/-- conditional: for an AES, triple DES or HMAC key, `export_key` returns `Ok` of the format
`RAW`, the key material of the blob without change, and the two parameter lists joined (hardware
enforced first). In the Rust source this branch does not look up the curve. Hypotheses: as for
`export_key_err_no_algorithm` without `BlobErrLaws`, with `get_tag_value` returning `Algorithm(a)`
for a `RawAlgorithm a`, and the law `KeyParameterCloneLaw`. -/
theorem export_key_ok_raw (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb) (a : Algorithm.Algorithm)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV a)))
    (ha : RawAlgorithm a) :
    ∃ c, sw_keyblob.export_key data params
        = ok (.Ok (KeyFormat.KeyFormat.RAW, kb.key_material, c)) ∧ c.val = comb.val := by
  obtain ⟨hidden, ⟨rots, hv, hr, hh, hd⟩, hn⟩ := hp
  subst hr hd
  obtain ⟨cs, hex, hcs⟩ := ek_comb hclone kb comb hcomb
  refine ⟨cs, ?_, by rw [← hcs]; simp [Vec.deref]⟩
  unfold sw_keyblob.export_key
  simp [lift, hh, hn, hex, hcs, hget, core.result.Result.Insts.CoreOpsTry.branch,
    core.option.Option.ok_or_else]
  rcases ha with rfl | rfl | rfl <;>
    simp [algAES, algTripleDes, algHMAC, KeyFormat.KeyFormat.RAW, I32.ofInt, IScalar.ofInt,
      IScalar.ofIntCore]

/-- conditional: when the algorithm lookup returns `Algorithm(RSA)`, the branch selects `PKCS8`
and rejects the pair. Under the hypotheses below, `export_key` returns an error with root cause
`INVALID_KEY_BLOB`.
Hypotheses: as for `export_key_ok_raw`, with `Algorithm(RSA)`, and `BlobErrFmtLaws`. -/
theorem export_key_err_rsa (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hclone : KeyParameterCloneLaw) (data : Slice Std.U8) (params : Slice KeyParam)
    (kb : sw_keyblob.KeyBlob) (hp : ParsesTo data params (ok (.Ok kb)))
    (comb : Slice KeyParam) (hcomb : CombinedOf kb comb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algRSA))) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e := by
  obtain ⟨hnew, hctx, hfmt⟩ := hlaw
  obtain ⟨hidden, ⟨rots, hv, hr, hh, hd⟩, hn⟩ := hp
  subst hr hd
  obtain ⟨cs, hex, hcs⟩ := ek_comb hclone kb comb hcomb
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨s0, hs0⟩ := hfmt noArgs
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s0
  refine ⟨e1, ?_, by unfold IsBlobErr; rw [hr1, hr0]⟩
  unfold sw_keyblob.export_key
  simp [lift, hh, hn, hex, hcs, hget, core.result.Result.Insts.CoreOpsTry.branch,
    core.option.Option.ok_or_else, algRSA, KeyFormat.KeyFormat.PKCS8, I32.ofInt, IScalar.ofInt,
    IScalar.ofIntCore, he0, hs0, core.hint.must_use, he1]

/-- conditional: for an EC key with no parameter that has the tag `EC_CURVE`, `export_key` returns
an error whose root cause is `INVALID_KEY_BLOB`. Hypotheses: as for `export_key_ok_raw`, with
`Algorithm(EC)`, `get_tag_value comb EC_CURVE` returning `none`, and `BlobErrLaws`. -/
theorem export_key_err_no_curve (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hclone : KeyParameterCloneLaw) (data : Slice Std.U8) (params : Slice KeyParam)
    (kb : sw_keyblob.KeyBlob) (hp : ParsesTo data params (ok (.Ok kb)))
    (comb : Slice KeyParam) (hcomb : CombinedOf kb comb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = ok none) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e := by
  obtain ⟨⟨hnew, hctx, hfmt⟩, hstr⟩ := hlaw
  obtain ⟨hidden, ⟨rots, hv, hr, hh, hd⟩, hn⟩ := hp
  subst hr hd
  obtain ⟨cs, hex, hcs⟩ := ek_comb hclone kb comb hcomb
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨a, ha⟩ :=
    hstr (toStr "keystore2/src/sw_keyblob.rs:82: Failed to determine curve for EC key!")
  obtain ⟨s0, hs0⟩ := hfmt a
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s0
  refine ⟨e1, ?_, by unfold IsBlobErr; rw [hr1, hr0]⟩
  unfold sw_keyblob.export_key
  simp [lift, hh, hn, hex, hcs, hget, hcurve, core.result.Result.Insts.CoreOpsTry.branch,
    core.option.Option.ok_or_else, algEC, KeyFormat.KeyFormat.PKCS8, I32.ofInt, IScalar.ofInt,
    IScalar.ofIntCore,
    sw_keyblob.export_key.closure_1.Insts.CoreOpsFunctionFnOnceTupleError.call_once,
    he0, ha, hs0, core.hint.must_use, he1,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]

/-- conditional: if `get_tag_value comb ALGORITHM` fails, `export_key` returns the same `fail x`.
The translated `get_tag_value` returns an `Option`, never `Err`, so there is no error case to
state. Hypotheses: `ParsesTo` with `Ok kb`, `comb` is the two lists joined, the failure
`x` as the outcome of `get_tag_value`, and the law `KeyParameterCloneLaw`. -/
theorem export_key_fail_get_algorithm (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb) (x : Error)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = fail x) :
    sw_keyblob.export_key data params = fail x := by
  obtain ⟨hidden, ⟨rots, hv, hr, hh, hd⟩, hn⟩ := hp
  subst hr hd
  obtain ⟨cs, hex, hcs⟩ := ek_comb hclone kb comb hcomb
  unfold sw_keyblob.export_key
  simp [lift, hh, hn, hex, hcs, hget, core.result.Result.Insts.CoreOpsTry.branch]

/-- conditional: for an EC key, if `get_tag_value comb EC_CURVE` fails, `export_key` returns
the same `fail x`. Hypotheses: as for `export_key_fail_get_algorithm`, with `Algorithm(EC)` as the
outcome of the first lookup and the failure `x` as the outcome of the second. -/
theorem export_key_fail_get_curve (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb) (x : Error)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = fail x) :
    sw_keyblob.export_key data params = fail x := by
  obtain ⟨hidden, ⟨rots, hv, hr, hh, hd⟩, hn⟩ := hp
  subst hr hd
  obtain ⟨cs, hex, hcs⟩ := ek_comb hclone kb comb hcomb
  unfold sw_keyblob.export_key
  simp [lift, hh, hn, hex, hcs, hget, hcurve, core.result.Result.Insts.CoreOpsTry.branch,
    core.option.Option.ok_or_else, algEC, KeyFormat.KeyFormat.PKCS8, I32.ofInt, IScalar.ofInt,
    IScalar.ofIntCore]

/-- conditional: for an EC key whose returned `EC_CURVE` value is not `EcCurve` of P-224, P-256,
P-384, P-521 or Curve25519, `export_key` returns an error whose root cause is `INVALID_KEY_BLOB`.
Hypotheses: as for `export_key_err_no_curve`, with `BlobErrFmtLaws` in place of `BlobErrLaws`,
`get_tag_value comb EC_CURVE` returning `some cv` and `cv` not a `KnownCurve`. -/
theorem export_key_err_curve (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hclone : KeyParameterCloneLaw) (data : Slice Std.U8) (params : Slice KeyParam)
    (kb : sw_keyblob.KeyBlob) (hp : ParsesTo data params (ok (.Ok kb)))
    (comb : Slice KeyParam) (hcomb : CombinedOf kb comb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (cv : ParamValue) (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = ok (some cv))
    (hcv : ¬ KnownCurve cv) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e := by
  obtain ⟨hnew, hctx, hfmt⟩ := hlaw
  obtain ⟨hidden, ⟨rots, hvv, hr, hh, hd⟩, hn⟩ := hp
  subst hr hd
  obtain ⟨cs, hex, hcs⟩ := ek_comb hclone kb comb hcomb
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨s0, hs0⟩ := hfmt noArgs
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s0
  refine ⟨e1, ?_, by unfold IsBlobErr; rw [hr1, hr0]⟩
  unfold sw_keyblob.export_key
  cases cv with
  | EcCurve c =>
    have n4 : c ≠ 4#i32 := fun h => hcv ⟨c, rfl, Or.inl h⟩
    have n0 : c ≠ 0#i32 :=
      fun h => hcv ⟨c, rfl, Or.inr ⟨_, Or.inl ⟨by simp [h, EcCurve.EcCurve.P_224], rfl⟩⟩⟩
    have n1 : c ≠ 1#i32 :=
      fun h => hcv ⟨c, rfl, Or.inr ⟨_, Or.inr (Or.inl ⟨by simp [h, EcCurve.EcCurve.P_256], rfl⟩)⟩⟩
    have n2 : c ≠ 2#i32 := fun h =>
      hcv ⟨c, rfl, Or.inr ⟨_, Or.inr (Or.inr (Or.inl ⟨by simp [h, EcCurve.EcCurve.P_384], rfl⟩))⟩⟩
    have n3 : c ≠ 3#i32 := fun h =>
      hcv ⟨c, rfl, Or.inr ⟨_, Or.inr (Or.inr (Or.inr ⟨by simp [h, EcCurve.EcCurve.P_521], rfl⟩))⟩⟩
    simp [lift, hh, hn, hex, hcs, hget, hcurve, core.result.Result.Insts.CoreOpsTry.branch,
      core.option.Option.ok_or_else, algEC, KeyFormat.KeyFormat.PKCS8, I32.ofInt, IScalar.ofInt,
      IScalar.ofIntCore]
    split <;> first
      | (simp [he0, hs0, core.hint.must_use, he1]; done)
      | exact absurd rfl n4 | exact absurd rfl n0 | exact absurd rfl n1 | exact absurd rfl n2
      | exact absurd rfl n3
  | _ =>
    simp [lift, hh, hn, hex, hcs, hget, hcurve, core.result.Result.Insts.CoreOpsTry.branch,
      core.option.Option.ok_or_else, algEC, KeyFormat.KeyFormat.PKCS8, I32.ofInt, IScalar.ofInt,
      IScalar.ofIntCore, he0, hs0, core.hint.must_use, he1]

/-- conditional: for an EC key on Curve25519, `export_key` returns `Ok` of the format `PKCS8`, the
key material of the blob without change, and the two parameter lists joined. In the Rust source
this branch neither checks nor wraps the key material. Hypotheses: as for
`export_key_err_no_curve` without `BlobErrLaws`, with `get_tag_value comb EC_CURVE` returning
`EcCurve(CURVE_25519)` in place of `none`. -/
theorem export_key_ok_curve25519 (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = ok (some (curveV curve25519))) :
    ∃ c, sw_keyblob.export_key data params
        = ok (.Ok (KeyFormat.KeyFormat.PKCS8, kb.key_material, c)) ∧ c.val = comb.val := by
  obtain ⟨hidden, ⟨rots, hv, hr, hh, hd⟩, hn⟩ := hp
  subst hr hd
  obtain ⟨cs, hex, hcs⟩ := ek_comb hclone kb comb hcomb
  refine ⟨cs, ?_, by rw [← hcs]; simp [Vec.deref]⟩
  unfold sw_keyblob.export_key
  simp [lift, hh, hn, hex, hcs, hget, hcurve, core.result.Result.Insts.CoreOpsTry.branch,
    core.option.Option.ok_or_else, algEC, curve25519, KeyFormat.KeyFormat.PKCS8, I32.ofInt,
    IScalar.ofInt, IScalar.ofIntCore, curveV]

/-- conditional: for an EC key on a NIST curve whose wrapped content is at most `0xffff` bytes
long, `export_key` returns `Ok` of the format `PKCS8`, the PKCS#8 `PrivateKeyInfo` of the key
material (`pkcs8Wrap`, built with the algorithm identifier `alg` of the curve), and the two
parameter lists joined. `pkcs8_wrap_nist_key` is translated, so its outcome is derived, not
assumed. The success path of `pkcs8_wrap_nist_key` evaluates no opaque call, and no push on it
comes near the capacity bound. Hypotheses: as for `export_key_err_no_curve` without `BlobErrLaws`,
with `get_tag_value comb EC_CURVE` returning `EcCurve(c)` in place of `none`, `alg` the identifier
of `c`, and the length of the content `pkcs8Body alg key` at most `0xffff`. -/
theorem export_key_ok_nist (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (c : EcCurve.EcCurve)
    (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = ok (some (curveV c)))
    (alg : Slice Std.U8) (hc : NistAlgId c alg)
    (hbody : (pkcs8Body (nums alg.val) (nums (Vec.deref kb.key_material).val)).length ≤ 0xffff) :
    ∃ w cs, sw_keyblob.export_key data params = ok (.Ok (KeyFormat.KeyFormat.PKCS8, w, cs)) ∧
      nums w.val = pkcs8Wrap (nums alg.val) (nums (Vec.deref kb.key_material).val) ∧
      cs.val = comb.val := by
  obtain ⟨hidden, ⟨rots, hv, hr, hh, hd⟩, hn⟩ := hp
  subst hr hd
  obtain ⟨cs, hex, hcs⟩ := ek_comb hclone kb comb hcomb
  obtain ⟨w, hw, hwv⟩ := pkcs8_wrap_nist_key_ok (Vec.deref kb.key_material) c alg hc hbody
  refine ⟨w, cs, ?_, hwv, by rw [← hcs]; simp [Vec.deref]⟩
  unfold sw_keyblob.export_key
  rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    (simp [I32.ofInt, IScalar.ofInt, IScalar.ofIntCore, EcCurve.EcCurve.P_224,
       EcCurve.EcCurve.P_256, EcCurve.EcCurve.P_384, EcCurve.EcCurve.P_521] at hw
     simp [lift, hh, hn, hex, hcs, hget, hcurve, core.result.Result.Insts.CoreOpsTry.branch,
       core.option.Option.ok_or_else, algEC, KeyFormat.KeyFormat.PKCS8, I32.ofInt, IScalar.ofInt,
       IScalar.ofIntCore, curveV, EcCurve.EcCurve.P_224, EcCurve.EcCurve.P_256,
       EcCurve.EcCurve.P_384, EcCurve.EcCurve.P_521, hw])

/-- conditional: for an EC key on a NIST curve and a key material longer than `0xffff` bytes,
`export_key` returns an error whose root cause is `INVALID_KEY_BLOB` (`pkcs8_wrap_nist_key` cannot
encode the length). Hypotheses: as for `export_key_ok_nist`, with `c` a `NistCurve` in place of
`alg` and the bound on the content, the key material longer than `0xffff` bytes, and
`BlobErrFmtLaws`. -/
theorem export_key_err_nist_key_len (root : anyhow.Error → ErrRoot)
    (hlaw : BlobErrFmtLaws root) (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (c : EcCurve.EcCurve)
    (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = ok (some (curveV c)))
    (hc : NistCurve c) (hkey : 0xffff < (Vec.deref kb.key_material).val.length) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e := by
  obtain ⟨hidden, ⟨rots, hv, hr, hh, hd⟩, hn⟩ := hp
  subst hr hd
  obtain ⟨cs, hex, hcs⟩ := ek_comb hclone kb comb hcomb
  obtain ⟨e, hw, hre⟩ := pkcs8_wrap_nist_key_err_key_len root hlaw (Vec.deref kb.key_material) c hc
    hkey
  refine ⟨e, ?_, hre⟩
  unfold sw_keyblob.export_key
  obtain ⟨alg, hc'⟩ := hc
  rcases hc' with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    (simp [I32.ofInt, IScalar.ofInt, IScalar.ofIntCore, EcCurve.EcCurve.P_224,
       EcCurve.EcCurve.P_256, EcCurve.EcCurve.P_384, EcCurve.EcCurve.P_521] at hw
     simp [lift, hh, hn, hex, hcs, hget, hcurve, core.result.Result.Insts.CoreOpsTry.branch,
       core.option.Option.ok_or_else, algEC, KeyFormat.KeyFormat.PKCS8, I32.ofInt, IScalar.ofInt,
       IScalar.ofIntCore, curveV, EcCurve.EcCurve.P_224, EcCurve.EcCurve.P_256,
       EcCurve.EcCurve.P_384, EcCurve.EcCurve.P_521, hw,
       core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
       core.convert.FromSame.from])

/-- conditional: for an EC key on a NIST curve, a key material of at most `0xffff` bytes and a
wrapped content longer than `0xffff` bytes, `export_key` returns an error whose root cause is
`INVALID_KEY_BLOB`. Together with `export_key_ok_nist` and `export_key_err_nist_key_len` this
covers every outcome of `pkcs8_wrap_nist_key` on a NIST curve, under `BlobErrFmtLaws`. Those laws
keep the opaque calls that build the error (`Error::new`, `format`, `context`) from failing;
without them an outer failure is possible on the two error paths. The success path evaluates no opaque
call: the generated body only pushes, extends, measures lengths and adds small numbers, and no
push comes near the capacity bound. Hypotheses: as for `export_key_ok_nist`, with the key at most
`0xffff` bytes, the content longer than `0xffff` bytes in place of the bound on it, and
`BlobErrFmtLaws`. -/
theorem export_key_err_nist_body_len (root : anyhow.Error → ErrRoot)
    (hlaw : BlobErrFmtLaws root) (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (c : EcCurve.EcCurve)
    (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = ok (some (curveV c)))
    (alg : Slice Std.U8) (hc : NistAlgId c alg)
    (hkey : (Vec.deref kb.key_material).val.length ≤ 0xffff)
    (hbody : 0xffff < (pkcs8Body (nums alg.val) (nums (Vec.deref kb.key_material).val)).length) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e := by
  obtain ⟨hidden, ⟨rots, hv, hr, hh, hd⟩, hn⟩ := hp
  subst hr hd
  obtain ⟨cs, hex, hcs⟩ := ek_comb hclone kb comb hcomb
  obtain ⟨e, hw, hre⟩ := pkcs8_wrap_nist_key_err_body_len root hlaw (Vec.deref kb.key_material) c
    alg hc hkey hbody
  refine ⟨e, ?_, hre⟩
  unfold sw_keyblob.export_key
  rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    (simp [I32.ofInt, IScalar.ofInt, IScalar.ofIntCore, EcCurve.EcCurve.P_224,
       EcCurve.EcCurve.P_256, EcCurve.EcCurve.P_384, EcCurve.EcCurve.P_521] at hw
     simp [lift, hh, hn, hex, hcs, hget, hcurve, core.result.Result.Insts.CoreOpsTry.branch,
       core.option.Option.ok_or_else, algEC, KeyFormat.KeyFormat.PKCS8, I32.ofInt, IScalar.ofInt,
       IScalar.ofIntCore, curveV, EcCurve.EcCurve.P_224, EcCurve.EcCurve.P_256,
       EcCurve.EcCurve.P_384, EcCurve.EcCurve.P_521, hw,
       core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
       core.convert.FromSame.from])
/-- Recover the parse and the actual tag lookups from the returned triple. NIST wrapping
specifies bytes constructed by this function, not whether an ASN.1 decoder accepts them. -/
theorem export_key_ok_of_result (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (fmt : KeyFormat.KeyFormat) (key : Vec Std.U8) (cs : Vec KeyParam)
    (h : sw_keyblob.export_key data params = ok (.Ok (fmt, key, cs))) :
    ∃ kb, ParsesTo data params (ok (.Ok kb)) ∧ CombinedOf kb (Vec.deref cs) ∧
      ((∃ a, sw_keyblob.get_tag_value (Vec.deref cs) Tag.Tag.ALGORITHM = ok (some (algV a)) ∧
        RawAlgorithm a ∧ fmt = KeyFormat.KeyFormat.RAW ∧ key = kb.key_material) ∨
       (sw_keyblob.get_tag_value (Vec.deref cs) Tag.Tag.ALGORITHM = ok (some (algV algEC)) ∧
        fmt = KeyFormat.KeyFormat.PKCS8 ∧ ∃ c,
        sw_keyblob.get_tag_value (Vec.deref cs) Tag.Tag.EC_CURVE = ok (some (curveV c)) ∧
        ((c = curve25519 ∧ key = kb.key_material) ∨
         (∃ alg, NistAlgId c alg ∧
           sw_keyblob.pkcs8_wrap_nist_key (Vec.deref kb.key_material) c = ok (.Ok key) ∧
           nums key.val = pkcs8Wrap (nums alg.val) (nums kb.key_material.val))))) := by
  have h0 := h
  clear h
  obtain ⟨kb, hp⟩ := ek_ok_parse data params _ h0
  obtain ⟨hidden, ⟨rots, hv, hr, hh, hd⟩, hn⟩ := hp
  have hp' : ParsesTo data params (ok (.Ok kb)) := ⟨_, ⟨rots, hv, hr, hh, hd⟩, hn⟩
  have hfit : CombinedFits kb := by
    by_contra hover
    rw [export_key_fail_capacity data params kb hp' hover] at h0
    simp at h0
  have hlt : (kb.hw_enforced.val ++ kb.sw_enforced.val).length ≤ Std.Usize.max := by
    unfold CombinedFits at hfit
    simpa using hfit
  obtain ⟨cs0, hex, hcs0⟩ := ek_comb hclone kb
    (Slice.from (kb.hw_enforced.val ++ kb.sw_enforced.val) hlt)
    (by unfold CombinedOf; simp)
  refine ⟨kb, hp', ?_⟩
  have hcomb : CombinedOf kb (Vec.deref cs0) := by
    rw [hcs0]; unfold CombinedOf; simp
  subst hr hd
  have h := h0
  unfold sw_keyblob.export_key at h
  simp [lift, hh, hn, hex, core.result.Result.Insts.CoreOpsTry.branch] at h
  cases hg : sw_keyblob.get_tag_value (Vec.deref cs0) Tag.Tag.ALGORITHM with
  | vis i k => simp [hg] at h
  | div => simp [hg] at h
  | ret o =>
    cases o with
    | none =>
      simp [hg, core.option.Option.ok_or_else,
        sw_keyblob.export_key.closure.Insts.CoreOpsFunctionFnOnceTupleError.call_once,
        core.hint.must_use,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from] at h
      exact absurd h (by repeat (apply bind_ne_ok; intro _); simp)
    | some v =>
      cases v with
      | Algorithm a =>
        by_cases hRaw : RawAlgorithm a
        · obtain ⟨c, hc, hcv⟩ := export_key_ok_raw hclone data params kb hp' (Vec.deref cs0) hcomb
            a hg hRaw
          rw [hc] at h0
          simp at h0
          obtain ⟨rfl, rfl, rfl⟩ := h0
          have hd : Vec.deref c = Vec.deref cs0 := by
            apply Slice.ext; simp [Vec.deref, hcv]
          rw [hd]
          exact ⟨hcomb, Or.inl ⟨a, hg, hRaw, rfl, rfl⟩⟩
        · by_cases hEC : a = algEC
          · subst hEC
            cases hg2 : sw_keyblob.get_tag_value (Vec.deref cs0) Tag.Tag.EC_CURVE with
            | vis i k =>
              simp [hg, hg2, core.option.Option.ok_or_else, algEC, KeyFormat.KeyFormat.PKCS8,
                I32.ofInt, IScalar.ofInt, IScalar.ofIntCore] at h
            | div =>
              simp [hg, hg2, core.option.Option.ok_or_else, algEC, KeyFormat.KeyFormat.PKCS8,
                I32.ofInt, IScalar.ofInt, IScalar.ofIntCore] at h
            | ret o2 =>
              cases o2 with
              | none =>
                simp [hg, hg2, core.option.Option.ok_or_else, algEC, KeyFormat.KeyFormat.PKCS8,
                  I32.ofInt, IScalar.ofInt, IScalar.ofIntCore,
                  sw_keyblob.export_key.closure_1.Insts.CoreOpsFunctionFnOnceTupleError.call_once,
                  core.hint.must_use,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  core.convert.FromSame.from] at h
                exact absurd h (by repeat (apply bind_ne_ok; intro _); simp)
              | some cv =>
                cases cv with
                | EcCurve c =>
                  by_cases h25 : c = curve25519
                  · subst h25
                    obtain ⟨c', hc', hcv⟩ := export_key_ok_curve25519 hclone data params kb hp'
                      (Vec.deref cs0) hcomb hg hg2
                    rw [hc'] at h0
                    simp at h0
                    obtain ⟨rfl, rfl, rfl⟩ := h0
                    have hd : Vec.deref c' = Vec.deref cs0 := by
                      apply Slice.ext; simp [Vec.deref, hcv]
                    rw [hd]
                    exact ⟨hcomb, Or.inr ⟨hg, rfl, curve25519, hg2, Or.inl ⟨rfl, rfl⟩⟩⟩
                  · by_cases hN : NistCurve c
                    · obtain ⟨alg, hc⟩ := hN
                      have hc0 := hc
                      rcases hc0 with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
                      · simp [hg, hg2, core.option.Option.ok_or_else, algEC,
                          KeyFormat.KeyFormat.PKCS8, I32.ofInt, IScalar.ofInt, IScalar.ofIntCore,
                          EcCurve.EcCurve.P_224, EcCurve.EcCurve.P_256,
                          EcCurve.EcCurve.P_384, EcCurve.EcCurve.P_521] at h
                        obtain ⟨r3, hw, h'⟩ := bind_eq_ok_inv _ _ _ h
                        cases r3 with
                        | Err e =>
                          simp [from_residual_err] at h'
                        | Ok w =>
                          simp at h'
                          obtain ⟨hf, rfl, rfl⟩ := h'
                          have hwb : wrapBody alg (Vec.deref kb.key_material) = ok (.Ok w) := by
                            rw [← wrap_eq_body (Vec.deref kb.key_material) _ alg hc]
                            simpa [I32.ofInt, IScalar.ofInt, IScalar.ofIntCore,
                              EcCurve.EcCurve.P_224, EcCurve.EcCurve.P_256, EcCurve.EcCurve.P_384,
                              EcCurve.EcCurve.P_521] using hw
                          have hw' := (wrap_eq_body (Vec.deref kb.key_material) _ alg hc).trans hwb
                          have hbody := wrap_body_ok_inv alg _ (nist_alg_len _ alg hc) w hwb
                          obtain ⟨out0, hout0, hnum⟩ :=
                            pkcs8_wrap_nist_key_ok (Vec.deref kb.key_material) _ alg hc hbody
                          rw [hw'] at hout0
                          simp at hout0
                          subst hout0
                          refine ⟨hcomb, Or.inr ⟨hg, ?_, _, hg2, Or.inr ⟨alg, hc, hw', ?_⟩⟩⟩
                          · simpa [KeyFormat.KeyFormat.PKCS8, I32.ofInt, IScalar.ofInt,
                              IScalar.ofIntCore] using hf.symm
                          · simpa [Vec.deref] using hnum
                    · simp [hg, hg2, core.option.Option.ok_or_else, algEC,
                        KeyFormat.KeyFormat.PKCS8, I32.ofInt, IScalar.ofInt,
                        IScalar.ofIntCore] at h
                      have n0 : c ≠ 0#i32 :=
                        fun h => hN ⟨_, Or.inl ⟨by simp [h, EcCurve.EcCurve.P_224], rfl⟩⟩
                      have n1 : c ≠ 1#i32 :=
                        fun h => hN ⟨_, Or.inr (Or.inl ⟨by simp [h, EcCurve.EcCurve.P_256], rfl⟩)⟩
                      have n2 : c ≠ 2#i32 := fun h =>
                        hN ⟨_, Or.inr (Or.inr (Or.inl ⟨by simp [h, EcCurve.EcCurve.P_384], rfl⟩))⟩
                      have n3 : c ≠ 3#i32 := fun h =>
                        hN ⟨_, Or.inr (Or.inr (Or.inr ⟨by simp [h, EcCurve.EcCurve.P_521], rfl⟩))⟩
                      split at h <;> first
                        | exact absurd rfl h25
                        | exact absurd rfl n0 | exact absurd rfl n1 | exact absurd rfl n2
                        | exact absurd rfl n3
                        | (exfalso; revert h
                           simp [core.hint.must_use]
                           intro h
                           exact absurd h (by repeat (apply bind_ne_ok; intro _); simp))
                | _ =>
                  simp [hg, hg2, core.option.Option.ok_or_else, algEC, KeyFormat.KeyFormat.PKCS8,
                    I32.ofInt, IScalar.ofInt, IScalar.ofIntCore, core.hint.must_use] at h
                  all_goals exact absurd h (by repeat (apply bind_ne_ok; intro _); simp)
          · have n32 : a ≠ 32#i32 := fun h => hRaw (Or.inl h)
            have n33 : a ≠ 33#i32 := fun h => hRaw (Or.inr (Or.inl h))
            have n128 : a ≠ 128#i32 := fun h => hRaw (Or.inr (Or.inr h))
            have n3 : a ≠ 3#i32 := hEC
            simp [hg, core.option.Option.ok_or_else] at h
            split at h <;> first
              | exact absurd (Or.inl rfl) hRaw | exact absurd (Or.inr (Or.inl rfl)) hRaw
              | exact absurd (Or.inr (Or.inr rfl)) hRaw | exact absurd rfl hEC
              | (exfalso; revert h
                 simp [core.hint.must_use, KeyFormat.KeyFormat.PKCS8, I32.ofInt, IScalar.ofInt,
                   IScalar.ofIntCore]
                 intro h
                 exact absurd h (by repeat (apply bind_ne_ok; intro _); simp))
      | _ =>
        simp [hg, core.option.Option.ok_or_else, core.hint.must_use] at h
        all_goals exact absurd h (by repeat (apply bind_ne_ok; intro _); simp)

end Keystore2Verify.SwKeyblob
