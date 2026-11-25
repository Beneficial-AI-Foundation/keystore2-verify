import Keystore2Verify.Proofs.Lemmas.SwKeyblobParseHmac

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-! Equations involving `data ++ hd` use the Aeneas vector capacity. A slice witnessing that
concatenation need not fit Rust's `isize::MAX` byte bound or be allocatable on a device. -/

/-- The slice of a vector that holds the bytes `msg`. -/
private theorem deref_eq_of_val (c : alloc.vec.Vec Std.U8) (msg : Slice Std.U8)
    (h : msg.val = c.val) : alloc.vec.Vec.deref c = msg :=
  have hdv : (alloc.vec.Vec.deref c).val = c.val := by simp [alloc.vec.Vec.deref]
  Slice.ext _ _ (hdv.trans h.symm)

/-- The two byte lists of a slice and a vector fit in the vector model. -/
private theorem fits_of_msg (data : Slice Std.U8) (hd : alloc.vec.Vec Std.U8) (msg : Slice Std.U8)
    (hmsg : msg.val = data.val ++ hd.val) : data.val.length + hd.val.length ≤ Std.Usize.max := by
  have := Slice.length_ineq msg
  rw [hmsg, List.length_append] at this
  exact this

/-- conditional: if `serialize_params hidden` returns `Ok hd` and `hmac_sha256` returns `Ok tag`
on the key `LEGACY_HMAC_KEY` and the message `data ++ hd`, then `compute_hmac` returns `Ok` of
the first 8 bytes of `tag`. Hypotheses: the two outcomes, `msg` is the bytes `data ++ hd`, and
the law `AllocVecTruncateSpec`. -/
theorem compute_hmac_ok (htrunc : AllocVecTruncateSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (hd tag : alloc.vec.Vec Std.U8) (msg : Slice Std.U8)
    (hser : sw_keyblob.serialize_params hidden = ok (.Ok hd))
    (hmsg : msg.val = data.val ++ hd.val)
    (hhmac : keystore2_crypto.hmac_sha256 sw_keyblob.KeyBlob.LEGACY_HMAC_KEY msg
      = ok (.Ok tag)) :
    ∃ t, sw_keyblob.KeyBlob.compute_hmac data hidden = ok (.Ok t) ∧
      t.val = tag.val.take 8 := by
  obtain ⟨v, c, hv, hc, hcv⟩ := hmac_combine_ok data hd (fits_of_msg data hd msg hmsg)
  have hm := deref_eq_of_val c msg (by rw [hmsg, hcv])
  obtain ⟨w, hw, hwv⟩ := htrunc tag sw_keyblob.KeyBlob.MAC_LEN
  refine ⟨w, ?_, by rw [hwv, mac_len_eq]; rfl⟩
  unfold sw_keyblob.KeyBlob.compute_hmac
  simp [hser, hv, hc, hm, hhmac, hw, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- conditional: under the hypotheses of `compute_hmac_ok` and the law
`KeystoreCryptoHmacSha256Spec`
(an `Ok` tag has 32 bytes), the MAC that `compute_hmac` returns has exactly 8 bytes. -/
theorem compute_hmac_ok_length (htrunc : AllocVecTruncateSpec)
    (hlen : KeystoreCryptoHmacSha256Spec) (data : Slice Std.U8) (hidden : Slice KeyParam)
    (hd tag : alloc.vec.Vec Std.U8) (msg : Slice Std.U8)
    (hser : sw_keyblob.serialize_params hidden = ok (.Ok hd))
    (hmsg : msg.val = data.val ++ hd.val)
    (hhmac : keystore2_crypto.hmac_sha256 sw_keyblob.KeyBlob.LEGACY_HMAC_KEY msg
      = ok (.Ok tag)) :
    ∃ t, sw_keyblob.KeyBlob.compute_hmac data hidden = ok (.Ok t) ∧ t.val.length = 8 := by
  obtain ⟨t, ht, htv⟩ := compute_hmac_ok htrunc data hidden hd tag msg hser hmsg hhmac
  refine ⟨t, ht, ?_⟩
  rw [htv]
  simp [hlen _ _ _ hhmac]

/-- conditional: if `serialize_params hidden` returns `Err e`, then `compute_hmac` returns the
same error `e`: the error value is passed through unchanged. In the Rust source this path
returns before `hmac_sha256` is called. Hypothesis: the outcome of `serialize_params`. -/
theorem compute_hmac_err_serialize (data : Slice Std.U8)
    (hidden : Slice KeyParam) (e : anyhow.Error)
    (hser : sw_keyblob.serialize_params hidden = ok (.Err e)) :
    sw_keyblob.KeyBlob.compute_hmac data hidden = ok (.Err e) := by
  unfold sw_keyblob.KeyBlob.compute_hmac
  simp [hser, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- conditional: if `serialize_params hidden` fails, then `compute_hmac` returns the same
`fail x`. Hypothesis: the outcome of `serialize_params`. -/
theorem compute_hmac_fail_serialize (data : Slice Std.U8) (hidden : Slice KeyParam) (x : Error)
    (hser : sw_keyblob.serialize_params hidden = fail x) :
    sw_keyblob.KeyBlob.compute_hmac data hidden = fail x := by
  unfold sw_keyblob.KeyBlob.compute_hmac
  simp [hser]

/-- conditional: if `serialize_params hidden` returns `Ok hd` and `hmac_sha256` returns the
crypto error `x` on the message `data ++ hd`, then `compute_hmac` returns an error whose root
cause is `x`. Hypotheses: the two outcomes, `msg` is the bytes `data ++ hd`, and the law
`CryptoFromLaw`. -/
theorem compute_hmac_err_hmac (root : anyhow.Error → ErrRoot) (hfrom : CryptoFromLaw root)
    (data : Slice Std.U8) (hidden : Slice KeyParam) (hd : alloc.vec.Vec Std.U8)
    (msg : Slice Std.U8) (x : keystore2_crypto.error.Error)
    (hser : sw_keyblob.serialize_params hidden = ok (.Ok hd))
    (hmsg : msg.val = data.val ++ hd.val)
    (hhmac : keystore2_crypto.hmac_sha256 sw_keyblob.KeyBlob.LEGACY_HMAC_KEY msg
      = ok (.Err x)) :
    ∃ e', sw_keyblob.KeyBlob.compute_hmac data hidden = ok (.Err e') ∧
      root e' = ErrRoot.crypto x := by
  obtain ⟨v, c, hv, hc, hcv⟩ := hmac_combine_ok data hd (fits_of_msg data hd msg hmsg)
  have hm := deref_eq_of_val c msg (by rw [hmsg, hcv])
  obtain ⟨e, he, hr⟩ := hfrom x
  refine ⟨e, ?_, hr⟩
  unfold sw_keyblob.KeyBlob.compute_hmac
  simp [hser, hv, hc, hm, hhmac, he, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- conditional: if `serialize_params hidden` returns `Ok hd` and `hmac_sha256` fails on the
message `data ++ hd`, then `compute_hmac` returns the same `fail x`.
Hypotheses: the two outcomes, and `msg` is the bytes `data ++ hd`. -/
theorem compute_hmac_fail_hmac (data : Slice Std.U8) (hidden : Slice KeyParam)
    (hd : alloc.vec.Vec Std.U8) (msg : Slice Std.U8) (x : Error)
    (hser : sw_keyblob.serialize_params hidden = ok (.Ok hd))
    (hmsg : msg.val = data.val ++ hd.val)
    (hhmac : keystore2_crypto.hmac_sha256 sw_keyblob.KeyBlob.LEGACY_HMAC_KEY msg = fail x) :
    sw_keyblob.KeyBlob.compute_hmac data hidden = fail x := by
  obtain ⟨v, c, hv, hc, hcv⟩ := hmac_combine_ok data hd (fits_of_msg data hd msg hmsg)
  have hm := deref_eq_of_val c msg (by rw [hmsg, hcv])
  unfold sw_keyblob.KeyBlob.compute_hmac
  simp [hser, hv, hc, hm, hhmac, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- conditional: if `serialize_params hidden` returns `Ok hd` and `data ++ hd` is longer than the
largest vector, `compute_hmac` panics. Hypotheses: the outcome of `serialize_params`, and the
total length is above `Usize.max`. That is the bound of the Aeneas vector model; in Rust the panic
comes at the lower limit of `isize::MAX` bytes. So this statement describes the model and is not a
capacity guarantee for the Rust code. -/
theorem compute_hmac_fail_capacity (data : Slice Std.U8) (hidden : Slice KeyParam)
    (hd : alloc.vec.Vec Std.U8) (hser : sw_keyblob.serialize_params hidden = ok (.Ok hd))
    (hover : Std.Usize.max < data.val.length + hd.val.length) :
    sw_keyblob.KeyBlob.compute_hmac data hidden = fail .panic := by
  have hl : ¬ (data.val.length + hd.val.length ≤ Std.Usize.max) := by omega
  obtain ⟨v, hv, hvv⟩ := to_vec_u8 data
  have hl' : ¬ (v.length + (alloc.vec.Vec.deref hd).length ≤ Std.Usize.max) := by
    have hdv : (alloc.vec.Vec.deref hd).val = hd.val := by simp [alloc.vec.Vec.deref]
    simp only [alloc.vec.Vec.length, Slice.length, hdv, hvv]
    exact hl
  have hext : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v (alloc.vec.Vec.deref hd)
      = fail .panic := by
    unfold alloc.vec.Vec.extend_from_slice
    simp [hl']
  unfold sw_keyblob.KeyBlob.compute_hmac
  simp [hser, hv, hext, core.result.Result.Insts.CoreOpsTry.branch]

/-- The returned bytes come from truncating the primitive tag for the actual serialized input. -/
theorem compute_hmac_ok_of_result (htrunc : AllocVecTruncateSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (t : alloc.vec.Vec Std.U8)
    (h : sw_keyblob.KeyBlob.compute_hmac data hidden = ok (.Ok t)) :
    ∃ (hd : alloc.vec.Vec Std.U8) (msg : Slice Std.U8) (tag : alloc.vec.Vec Std.U8),
      sw_keyblob.serialize_params hidden = ok (.Ok hd) ∧
      msg.val = data.val ++ hd.val ∧
      keystore2_crypto.hmac_sha256 sw_keyblob.KeyBlob.LEGACY_HMAC_KEY msg = ok (.Ok tag) ∧
      t.val = tag.val.take 8 := by
  rcases result_trichotomy (sw_keyblob.serialize_params hidden) with
    ⟨r, hs⟩ | ⟨x, hs⟩ | hs
  · cases r with
    | Ok hd =>
      by_cases hfit : data.val.length + hd.val.length ≤ Std.Usize.max
      · obtain ⟨v, c, hv, hc, hcv⟩ := hmac_combine_ok data hd hfit
        refine ⟨hd, alloc.vec.Vec.deref c, ?_⟩
        rcases result_trichotomy (keystore2_crypto.hmac_sha256
            sw_keyblob.KeyBlob.LEGACY_HMAC_KEY (alloc.vec.Vec.deref c)) with
          ⟨r, hr⟩ | ⟨x, hr⟩ | hr
        · cases r with
          | Ok tag =>
            obtain ⟨t', ht', htv⟩ := compute_hmac_ok htrunc data hidden hd tag
              (alloc.vec.Vec.deref c) hs (by simp [alloc.vec.Vec.deref, hcv]) hr
            rw [ht'] at h
            simp at h
            subst h
            exact ⟨tag, hs, by simp [alloc.vec.Vec.deref, hcv], hr, htv⟩
          | Err e =>
            unfold sw_keyblob.KeyBlob.compute_hmac at h
            simp [hs, hv, hc, hr, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
            revert h
            cases anyhow.Error.Insts.CoreConvertFrom.from
              keystore2_crypto.error.Error.Insts.CoreErrorError e <;> simp
        · unfold sw_keyblob.KeyBlob.compute_hmac at h
          simp [hs, hv, hc, hr, core.result.Result.Insts.CoreOpsTry.branch] at h
        · unfold sw_keyblob.KeyBlob.compute_hmac at h
          simp [hs, hv, hc, hr, core.result.Result.Insts.CoreOpsTry.branch] at h
      · rw [compute_hmac_fail_capacity data hidden hd hs (by omega)] at h
        simp at h
    | Err e =>
      rw [compute_hmac_err_serialize data hidden e hs] at h
      simp at h
  · rw [compute_hmac_fail_serialize data hidden x hs] at h
    simp at h
  · unfold sw_keyblob.KeyBlob.compute_hmac at h
    simp [hs] at h

/-- The length laws constrain the observed MAC without assuming a successful primitive call. -/
theorem compute_hmac_ok_length_of_result (htrunc : AllocVecTruncateSpec)
    (hlen : KeystoreCryptoHmacSha256Spec) (data : Slice Std.U8) (hidden : Slice KeyParam)
    (t : alloc.vec.Vec Std.U8) (h : sw_keyblob.KeyBlob.compute_hmac data hidden = ok (.Ok t)) :
    t.val.length = 8 := by
  obtain ⟨hd, msg, tag, hs, hm, hr, ht⟩ := compute_hmac_ok_of_result htrunc data hidden t h
  rw [ht]
  simp [hlen _ _ _ hr]

end Keystore2Verify.SwKeyblob
