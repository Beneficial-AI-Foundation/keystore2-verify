import Keystore2Verify.Proofs.Lemmas.SwKeyblobExportParse

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open alloc.vec

/-- Propagating an error with `?` returns the same error. -/
theorem from_residual_err (T : Type) (e : anyhow.Error) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
      (core.convert.FromSame anyhow.Error) (core.result.Result.Err e) =
      ok (core.result.Result.Err e) := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]

/-- With the clone law, appending a list of key parameters that fits in the vector model
concatenates the two lists. -/
theorem extend_kp_ok (hclone : KeyParameterCloneLaw) (v : alloc.vec.Vec KeyParam)
    (s : Slice KeyParam) (h : v.val.length + s.val.length ≤ Std.Usize.max) :
    ∃ v', alloc.vec.Vec.extend_from_slice KeyParameter.KeyParameter.Insts.CoreCloneClone v s
        = ok v' ∧ v'.val = v.val ++ s.val := by
  unfold alloc.vec.Vec.extend_from_slice
  have h' : v.length + s.length ≤ Std.Usize.max := h
  have hs := List.clone_spec (clone := KeyParameter.KeyParameter.Insts.CoreCloneClone.clone)
    (l := s.val) (fun x _ => hclone x)
  cases hx : List.clone KeyParameter.KeyParameter.Insts.CoreCloneClone.clone s.val <;>
    rw [hx] at hs <;> simp_all

/-- The first step of `export_key` after a successful parse: the two parameter lists of the blob
are joined into a vector `cs`, which is the slice `comb`. -/
theorem ek_comb (hclone : KeyParameterCloneLaw) (kb : sw_keyblob.KeyBlob)
    (comb : Slice KeyParam) (hcomb : CombinedOf kb comb) :
    ∃ cs, alloc.vec.Vec.extend_from_slice KeyParameter.KeyParameter.Insts.CoreCloneClone
        kb.hw_enforced (Vec.deref kb.sw_enforced) = ok cs ∧ Vec.deref cs = comb := by
  have hl := Slice.length_ineq comb
  have hc : comb.val = kb.hw_enforced.val ++ kb.sw_enforced.val := hcomb
  obtain ⟨cs, hex, hv⟩ := extend_kp_ok hclone kb.hw_enforced (Vec.deref kb.sw_enforced) (by
    have : comb.val.length ≤ Std.Usize.max := hl
    rw [hc] at this; simpa [Vec.deref] using this)
  refine ⟨cs, hex, ?_⟩
  apply Slice.ext
  simp [Vec.deref, hv, hc]


/-- If the parser returns `Err e`, `export_key` returns the same error. -/
theorem ek_err_parse (data : Slice Std.U8) (params : Slice KeyParam) (e : anyhow.Error)
    (hp : ParsesTo data params (ok (.Err e))) :
    sw_keyblob.export_key data params = ok (.Err e) := by
  obtain ⟨hidden, ⟨rots, hv, hr, hh, hd⟩, hn⟩ := hp
  subst hr hd
  unfold sw_keyblob.export_key
  simp [lift, hh, hn, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]

/-- If the parser fails, `export_key` fails in the same way. -/
theorem ek_fail_parse (data : Slice Std.U8) (params : Slice KeyParam) (x : Error)
    (hp : ParsesTo data params (fail x)) :
    sw_keyblob.export_key data params = fail x := by
  obtain ⟨hidden, ⟨rots, hv, hr, hh, hd⟩, hn⟩ := hp
  subst hr hd
  unfold sw_keyblob.export_key
  simp [lift, hh, hn]

/-- If `export_key` returns `Ok`, the parser returned `Ok`. -/
theorem ek_ok_parse (data : Slice Std.U8) (params : Slice KeyParam)
    (out : KeyFormat.KeyFormat × alloc.vec.Vec Std.U8 × alloc.vec.Vec KeyParam)
    (h : sw_keyblob.export_key data params = ok (.Ok out)) :
    ∃ kb, ParsesTo data params (ok (.Ok kb)) := by
  unfold sw_keyblob.export_key at h
  simp only [lift, Std.bind_ok] at h
  cases hh : sw_keyblob.hidden_params params
      (Array.to_slice (Array.make 1#usize [sw_keyblob.SOFTWARE_ROOT_OF_TRUST])) with
  | ret hv =>
    cases hn : sw_keyblob.KeyBlob.new_from_serialized data (Vec.deref hv) with
    | ret r =>
      cases r with
      | Ok kb => exact ⟨kb, _, ⟨_, hv, rfl, hh, rfl⟩, hn⟩
      | Err e =>
        simp [hh, hn, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from] at h
    | vis i k => simp [hh, hn] at h
    | div => simp [hh, hn] at h
  | vis i k => simp [hh] at h
  | div => simp [hh] at h

end Keystore2Verify.SwKeyblob
