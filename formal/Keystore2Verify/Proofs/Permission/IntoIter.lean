import Keystore2Verify.Specs.Defs.Permission

namespace Keystore2Verify.Permission
open Aeneas Aeneas.Std Result keystore2
open permission.perm
open permission.KeyPermSet.Insts
open permission.perm.IntoIter.Insts
open CoreIterTraitsIteratorIteratorKeyPerm renaming next → iterNext
open permission.KeyPerm.Insts.CoreConvertFromI32 renaming «from» → keyPermFromI32

/-- Masking a word with the single bit `n` gives that bit if it is set, and 0 otherwise. -/
private theorem and_bit (s : BitVec 32) (n : Nat) (hn : n < 32) :
    s &&& (1#32 <<< n) = if s.getLsbD n = true then 1#32 <<< n else 0#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have e : s.getLsbD n = s[n] := BitVec.getLsbD_eq_getElem hn
  by_cases h : s[n] = true
  · simp only [e, h, ↓reduceIte]
    by_cases hj' : j = n
    · subst hj'; simp [e, h]
    · simp [hj]
      intro hnj hjn; omega
  · simp only [e, h]
    by_cases hj' : j = n
    · subst hj'; simp [e, h]
    · simp [hj]
      intro _ hnj; omega

/-- The body of the loop in `next`. -/
private abbrev nextBody := CoreIterTraitsIteratorIteratorKeyPerm.next_loop.body

/-- The single bit `n` is not zero when `n < 32`. -/
private theorem one_shl_ne_zero (n : Nat) (hn : n < 32) : (1#32 <<< n) ≠ 0#32 := by
  intro h
  have := congrArg (fun b => b.getLsbD n) h
  simp [hn] at this

/-- `KeyPerm::from(i32)` never fails. -/
private theorem from_total (x : Std.I32) : ∃ kp, keyPermFromI32 x = ok kp := by
  unfold keyPermFromI32; split <;> exact ⟨_, rfl⟩

/-- A step at a position whose bit is clear moves to the next position. -/
private theorem body_miss (it : permission.perm.IntoIter) (h : it.pos.val < 32)
    (hb : ¬ HasBit it.vec it.pos.val) :
    nextBody it ⦃ r =>
      ∃ it', r = .cont it' ∧ it'.vec = it.vec ∧ it'.pos.val = it.pos.val + 1 ⦄ := by
  unfold nextBody CoreIterTraitsIteratorIteratorKeyPerm.next_loop.body
  step*
  rename_i hne
  have hpv : p.bv = 0#32 := by
    refine p_post1.trans ?_
    have := and_bit it.vec.bv it.pos.val h
    simp only [HasBit] at hb
    simpa [hb, i1_post1] using this
  have : p = 0#i32 := I32.bv_eq_imp_eq _ _ (by simpa using hpv)
  simp [this] at hne

/-- A step at a position whose bit is set returns the permission of that bit. -/
private theorem body_hit (it : permission.perm.IntoIter) (h : it.pos.val < 32)
    (hb : HasBit it.vec it.pos.val) :
    nextBody it ⦃ r =>
      ∃ kp pos', keyPermFromI32 (bitVal it.pos.val) = ok kp ∧
        r = .done (some kp, it.vec, pos') ∧ pos'.val = it.pos.val + 1 ⦄ := by
  unfold nextBody CoreIterTraitsIteratorIteratorKeyPerm.next_loop.body
  step*
  all_goals
    have hpv : p.bv = 1#32 <<< it.pos.val := by
      refine p_post1.trans ?_
      have := and_bit it.vec.bv it.pos.val h
      simp only [HasBit] at hb
      simpa [hb, i1_post1] using this
  · have hp : p = bitVal it.pos.val := I32.bv_eq_imp_eq _ _ hpv
    obtain ⟨kp, hk⟩ := from_total p
    rw [hk]
    simp
    exact ⟨hp ▸ hk, i2_post⟩
  · exfalso
    rename_i hne
    have : p = 0#i32 := IScalar.val_eq_imp _ _ (by simpa using hne)
    exact one_shl_ne_zero _ h (hpv ▸ congrArg (·.bv) this)


/-- A specification of a computation gives its successful value. -/
private theorem spec_eq_ok {α : Type} {m : Result α} {p : α → Prop} (h : m ⦃ p ⦄) :
    ∃ v, m = ok v ∧ p v := by
  cases m <;> simp_all [WP.spec_ok]

/-- A step at position 32 finishes with `None`. -/
private theorem body_end (it : permission.perm.IntoIter) (h : it.pos.val = 32) :
    nextBody it = ok (.done (none, it.vec, it.pos)) := by
  unfold nextBody CoreIterTraitsIteratorIteratorKeyPerm.next_loop.body
  have : it.pos = 32#u8 := UScalar.val_eq_imp _ _ (by simpa using h)
  simp [this]

/-- A step at a position above 32 fails, because the shift is out of range. -/
private theorem body_fail (it : permission.perm.IntoIter) (h : 32 < it.pos.val) :
    ∃ x, nextBody it = fail x := by
  unfold nextBody CoreIterTraitsIteratorIteratorKeyPerm.next_loop.body
  have : ¬ it.pos = 32#u8 := fun e => by simp [e] at h
  have hs : (1#i32 <<< it.pos) = fail .integerOverflow := by
    have : ¬ it.pos.val < IScalarTy.I32.numBits := by simp; omega
    show IScalar.shiftLeft (1#i32) it.pos.val = _
    unfold IScalar.shiftLeft
    simp only [this, ↓reduceIte]
  simp [this, hs]

/-- A step that continues leaves the loop at the new state. -/
private theorem nextLoop_cont (it it' : permission.perm.IntoIter)
    (h : nextBody it = ok (.cont it')) :
    CoreIterTraitsIteratorIteratorKeyPerm.next_loop it =
      CoreIterTraitsIteratorIteratorKeyPerm.next_loop it' := by
  unfold CoreIterTraitsIteratorIteratorKeyPerm.next_loop
  rw [loop]
  simp only [nextBody] at h
  simp [h]

/-- A step that finishes ends the loop with its result. -/
private theorem nextLoop_done (it : permission.perm.IntoIter) r
    (h : nextBody it = ok (.done r)) :
    CoreIterTraitsIteratorIteratorKeyPerm.next_loop it = ok r := by
  unfold CoreIterTraitsIteratorIteratorKeyPerm.next_loop
  rw [loop]
  simp only [nextBody] at h
  simp [h]

/-- A step that fails makes the loop fail. -/
private theorem nextLoop_fail (it : permission.perm.IntoIter) x
    (h : nextBody it = fail x) :
    CoreIterTraitsIteratorIteratorKeyPerm.next_loop it = fail x := by
  unfold CoreIterTraitsIteratorIteratorKeyPerm.next_loop
  rw [loop]
  simp only [nextBody] at h
  simp [h]

/-- The loop returns the permission of the lowest set bit at the position or above. -/
private theorem next_loop_some : ∀ (k : Nat) (it : permission.perm.IntoIter) (i : Nat),
    i - it.pos.val = k → NextBit it.vec it.pos.val i →
    ∃ kp pos', keyPermFromI32 (bitVal i) = ok kp ∧
      CoreIterTraitsIteratorIteratorKeyPerm.next_loop it = ok (some kp, it.vec, pos') ∧
      pos'.val = i + 1 := by
  intro k
  induction k with
  | zero =>
    intro it i hk ⟨hle, hlt, hbit, _⟩
    have hpos : it.pos.val = i := by omega
    have hb : HasBit it.vec it.pos.val := hpos ▸ hbit
    obtain ⟨r, hr, kp, pos', hk', rfl, hp⟩ := spec_eq_ok (body_hit it (by omega) hb)
    exact ⟨kp, pos', hpos ▸ hk', by rw [nextLoop_done it _ hr], by omega⟩
  | succ k ih =>
    intro it i hk ⟨hle, hlt, hbit, hbefore⟩
    have hne : ¬ HasBit it.vec it.pos.val := hbefore _ le_rfl (by omega)
    obtain ⟨r, hr, it', rfl, hv, hp⟩ := spec_eq_ok (body_miss it (by omega) hne)
    obtain ⟨kp, pos', h1, h2, h3⟩ := ih it' i (by omega)
      ⟨by omega, hlt, hv ▸ hbit, fun j hj hji => hv ▸ hbefore j (by omega) hji⟩
    exact ⟨kp, pos', h1, by rw [nextLoop_cont it it' hr, h2, hv], h3⟩

/-- Without a set bit at the position or above, the loop runs to the end at position 32. -/
private theorem next_loop_none : ∀ (k : Nat) (it : permission.perm.IntoIter),
    32 - it.pos.val = k → it.pos.val ≤ 32 →
    (∀ j, it.pos.val ≤ j → j < 32 → ¬ HasBit it.vec j) →
    ∃ pos', CoreIterTraitsIteratorIteratorKeyPerm.next_loop it = ok (none, it.vec, pos') ∧
      pos'.val = 32 := by
  intro k
  induction k with
  | zero =>
    intro it hk hle _
    have hpos : it.pos.val = 32 := by omega
    exact ⟨it.pos, nextLoop_done it _ (body_end it hpos), hpos⟩
  | succ k ih =>
    intro it hk hle hnone
    obtain ⟨r, hr, it', rfl, hv, hp⟩ :=
      spec_eq_ok (body_miss it (by omega) (hnone _ le_rfl (by omega)))
    obtain ⟨pos', h2, h3⟩ := ih it' (by omega) (by omega)
      (fun j hj hj' => hv ▸ hnone j (by omega) hj')
    exact ⟨pos', by rw [nextLoop_cont it it' hr, h2, hv], h3⟩

/-- exact: `IntoIter::new` never fails. It returns the iterator over the set, at position 0. -/
theorem into_iter_new (v : permission.KeyPermSet) :
    IntoIter.new v = ok { vec := v, pos := 0#u8 } := by
  rfl

/-- exact: `KeyPermSet::into_iter` never fails. It returns the iterator over the set, at
position 0. -/
theorem key_perm_set_into_iter (v : permission.KeyPermSet) :
    CoreIterTraitsCollectIntoIteratorKeyPermIntoIter.into_iter v =
      ok { vec := v, pos := 0#u8 } := by
  rfl

/-- exact: if some bit at position `pos` or above is set, `next` returns the permission of the
lowest such bit `i`, that is `KeyPerm::from(1 << i)`, and moves the position to `i + 1`. The set
does not change. A set bit that is no `KeyPerm` (bit 10, bits 12 to 31) gives `KeyPerm::None`,
and is not skipped. -/
theorem into_iter_next_some (it : permission.perm.IntoIter) (i : Nat)
    (hi : NextBit it.vec it.pos.val i) :
    ∃ kp it', keyPermFromI32 (bitVal i) = ok kp ∧ iterNext it = ok (some kp, it') ∧
      it'.vec = it.vec ∧ it'.pos.val = i + 1 := by
  obtain ⟨kp, pos', h1, h2, h3⟩ := next_loop_some _ it i rfl hi
  refine ⟨kp, ⟨it.vec, pos'⟩, h1, ?_, rfl, h3⟩
  simp [iterNext, CoreIterTraitsIteratorIteratorKeyPerm.next, h2]

/-- exact: if the position is at most 32 and no bit at position `pos` or above is set, `next`
returns `None` and moves the position to 32. The set does not change. With position 32 this says
that the iterator stays finished. -/
theorem into_iter_next_none (it : permission.perm.IntoIter) (hpos : it.pos.val ≤ 32)
    (hnone : ∀ j, it.pos.val ≤ j → j < 32 → ¬ HasBit it.vec j) :
    ∃ it', iterNext it = ok (none, it') ∧ it'.vec = it.vec ∧ it'.pos.val = 32 := by
  obtain ⟨pos', h2, h3⟩ := next_loop_none _ it rfl hpos hnone
  refine ⟨⟨it.vec, pos'⟩, ?_, rfl, h3⟩
  simp [iterNext, CoreIterTraitsIteratorIteratorKeyPerm.next, h2]

/-- exact: a position above 32 makes `next` panic, because the shift `1 << pos` is out of range.
Rust code cannot build such an iterator: the field `pos` is private and only `next` changes it,
so this is a fact about the Lean model only. -/
theorem into_iter_next_pos_too_large (it : permission.perm.IntoIter) (hpos : 32 < it.pos.val) :
    ∃ x, iterNext it = fail x := by
  obtain ⟨x, hx⟩ := body_fail it hpos
  exact ⟨x, by simp [iterNext, CoreIterTraitsIteratorIteratorKeyPerm.next,
    nextLoop_fail it x hx]⟩

end Keystore2Verify.Permission
