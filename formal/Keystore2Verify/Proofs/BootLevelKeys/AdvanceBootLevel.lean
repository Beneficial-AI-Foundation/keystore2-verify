import Keystore2Verify.Specs.Defs.BootLevelKeys
import Keystore2Verify.Proofs.BootLevelKeys.LevelAccessible
import Keystore2Verify.Proofs.Lemmas.BootLevelKeysBind

namespace Keystore2Verify.BootLevelKeys
open Aeneas Aeneas.Std Result keystore2 keystore2.boot_level_keys Keystore2Verify.Externals
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open keystore2.boot_level_keys.BootLevel.Insts
open CoreCloneClone renaming clone → bootLevelClone
open CoreCmpPartialEqBootLevel renaming eq → bootLevelEq
open CoreCmpOrd renaming cmp → bootLevelCmp
open CoreCmpPartialOrdBootLevel renaming partial_cmp → bootLevelPartialCmp
open keystore2.alloc.collections.vec_deque
open core.cmp.PartialOrd.le renaming trait_default → leTraitDefault, «default» → leDefault
open core.cmp.PartialOrd renaming le_body → leBody
open Aeneas.Std.core.fmt.Arguments renaming new → argumentsNew
open core.fmt.rt
open core.result.Result.Insts.CoreOpsTry renaming branch → resultBranch
open core.result.Result.Insts.CoreOpsTry_traitFromResidualResult renaming
  from_residual → resultFromResidual
open log.Level.Insts renaming CoreCmpPartialOrdLevelFilter → levelFilterOrd

/-- `x - y` on `usize` succeeds with the difference when `y ≤ x`. -/
private theorem usize_sub_ok (x y : Usize) (h : y.val ≤ x.val) :
    ∃ z, x - y = ok z ∧ z.val = x.val - y.val := by
  have hb := x.hBounds
  refine ⟨⟨BitVec.ofNat _ (x.val - y.val)⟩, ?_, ?_⟩
  · show UScalar.sub x y = _
    simp [UScalar.sub, not_lt.2 h]
  · simp only [UScalar.val, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by simp only [UScalar.val] at hb ⊢; omega)

/-- `x - y` on `usize` fails with an overflow when `x < y`. -/
private theorem usize_sub_fail (x y : Usize) (h : x.val < y.val) :
    x - y = fail Error.integerOverflow := by
  show UScalar.sub x y = _
  simp [UScalar.sub, h]

/-- The value that the model of `Argument::new_debug` and `new_display` returns. -/
private def argUnit : Argument := ()

/-- The value that the model of `Arguments::new` returns. -/
private def argsUnit : core.fmt.Arguments := ()

/-- `Argument::new_debug` returns the unit value, whatever its inputs. -/
private theorem new_debug_eq {T : Type} (i : core.fmt.Debug T) (x : T) :
    Argument.new_debug i x = ok argUnit := rfl

/-- `Argument::new_display` returns the unit value, whatever its inputs. -/
private theorem new_display_eq {T : Type} (i : core.fmt.Display T) (x : T) :
    Argument.new_display i x = ok argUnit := rfl

/-- `Arguments::new` returns the unit value, whatever its inputs. -/
private theorem args_new_eq {N M : Usize} (x : Array U8 N) (y : Array Argument M) :
    argumentsNew x y = ok argsUnit := rfl

/-- `Level <= LevelFilter` never fails when the comparison of the two never fails. -/
private theorem level_le_total (hcmp : LogLevelPartialCmpSpec) (x : log.Level)
    (y : log.LevelFilter) :
    ∃ b, leTraitDefault levelFilterOrd x y
      = ok b := by
  obtain ⟨c, hc⟩ := hcmp x y
  simp only [leTraitDefault, leDefault,
    leBody, hc, bind_tc_ok]
  exact ⟨_, rfl⟩

/-- exact: if the level is not accessible and `advance_boot_level` returns normally, it returns
`Ok ()` and leaves the cache unchanged. In the Rust source this path only logs. -/
theorem BootLevelKeyCache_advance_boot_level_not_accessible
    (s s' : BootLevelKeyCache) (L : BootLevel) (r : core.result.Result Unit anyhow.Error)
    (hacc : BootLevelKeyCache.level_accessible s L = ok false)
    (h : BootLevelKeyCache.advance_boot_level s L = ok (r, s')) :
    r = ROk () ∧ s' = s := by
  unfold BootLevelKeyCache.advance_boot_level at h
  simp only [hacc, bind_ok, Bool.false_eq_true, ite_false] at h
  simp [bind_eq_ok_iff] at h
  grind

/-- conditional: if the level is not accessible, `advance_boot_level` does not fail: it returns
`Ok ()` and the same cache. Hypotheses: the shared laws for the log calls (`max_level`,
`Level` comparison, `loc`, `log`) and for `VecDeque::len`, for the view `view` of the queue. -/
theorem BootLevelKeyCache_advance_boot_level_not_accessible_ok (view : View)
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) (hlen : ZVecQueueLenLaw view)
    (s : BootLevelKeyCache) (L : BootLevel)
    (hacc : BootLevelKeyCache.level_accessible s L = ok false) :
    BootLevelKeyCache.advance_boot_level s L = ok (ROk (), s) := by
  obtain ⟨b1, hb1⟩ := level_le_total hcmp log.Level.Error log.STATIC_MAX_LEVEL
  obtain ⟨lf, hlf⟩ := hmax
  obtain ⟨b2, hb2⟩ := level_le_total hcmp log.Level.Error lf
  obtain ⟨n, hn, -⟩ := hlen s.cache
  obtain ⟨l, hl⟩ := hloc
  unfold BootLevelKeyCache.advance_boot_level
  cases b1 <;> cases b2 <;>
    simp [hacc, hb1, hlf, hb2, hn, hl, new_debug_eq, new_display_eq, args_new_eq]
  rw [hlog]
  simp

/-- conditional: a level below the current level is not advanced to. `advance_boot_level`
returns `Ok ()` and the same cache, without a change. Hypotheses: the shared laws of
`advance_boot_level_not_accessible_ok`. -/
theorem BootLevelKeyCache_advance_boot_level_below (view : View)
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) (hlen : ZVecQueueLenLaw view)
    (s : BootLevelKeyCache) (L : BootLevel) (hlt : L.val < s.current.val) :
    BootLevelKeyCache.advance_boot_level s L = ok (ROk (), s) :=
  BootLevelKeyCache_advance_boot_level_not_accessible_ok view hmax hcmp hloc hlog hlen s L
    (BootLevelKeyCache_level_accessible_lt s L hlt)

/-- conditional: if the level is accessible and `get_hkdf_key` returned the cache `s1`, then
`advance_boot_level` either returns an `Err` together with `s1`, or returns `Ok ()` together
with a cache whose current level is the requested level. Hypotheses: the call outcome
`get_hkdf_key s L = ok (r0, s1)` (`hget`), where `r0` and `s1` are otherwise arbitrary; that the
level is accessible (`hacc`); and that `advance_boot_level` returned `ok (r, s')` (`h`). -/
theorem BootLevelKeyCache_advance_boot_level_accessible_shape
    (s s1 s' : BootLevelKeyCache) (L : BootLevel)
    (r0 : core.result.Result (Option keystore2_crypto.zvec.ZVec) anyhow.Error)
    (r : core.result.Result Unit anyhow.Error)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (r0, s1))
    (h : BootLevelKeyCache.advance_boot_level s L = ok (r, s')) :
    (s' = s1 ∧ ∃ e, r = RErr e) ∨
      (r = ROk () ∧ s'.current = L) := by
  unfold BootLevelKeyCache.advance_boot_level at h
  simp [hacc, hget, bind_eq_ok_iff, core.hint.must_use,
    resultBranch] at h
  obtain ⟨a, -, str, -, r1, -, h⟩ := h
  rcases r1 with v | e
  · simp [bind_eq_ok_iff] at h
    grind
  · simp [resultFromResidual] at h
    exact Or.inl ⟨h.2.symm, e, h.1.symm⟩

/-- conditional: if the level is accessible and `get_hkdf_key` returned `Err e` with the cache
`s1`, then `advance_boot_level` returns an `Err` with the same root cause and the cache `s1`:
the wrapper returns the state supplied by the lookup, without further change. Hypotheses: the
outcome of `get_hkdf_key` (`hget`), the shared law `ResultContextLaw` for `Result::context`
(`ContextKeyLaw`), and the shared laws that the message building does not panic (`format`,
`from_str_nonconst`). -/
theorem BootLevelKeyCache_advance_boot_level_err (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (e : anyhow.Error)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (RErr e, s1)) :
    ∃ e', BootLevelKeyCache.advance_boot_level s L = ok (RErr e', s1) ∧
      root e' = root e := by
  obtain ⟨a, ha⟩ := hargs (toStr "keystore2/src/boot_level_keys.rs:253: Advancing cache")
  obtain ⟨str, hs⟩ := hfmt a
  obtain ⟨e', he', hr⟩ := hctx.2 e str
  unfold BootLevelKeyCache.advance_boot_level
  simp [hacc, hget, ha, hs, he', core.hint.must_use, resultBranch,
    resultFromResidual]
  exact hr

/-- conditional: if the level is accessible and `get_hkdf_key` returned `Ok` with the cache `s1`,
then `advance_boot_level` returns `Ok ()` and a cache whose current level is the requested level
and whose queue is the queue of `s1` without its first `L - current` entries (`current` is that
of `s1`). The bound `hlen` is not strict, which is what `split_off` accepts (an offset equal to
the length is allowed), so this statement does not exclude an empty retained queue. Excluding it
needs a fact about `get_hkdf_key`, whose Rust body the translation leaves opaque: it is blocked by
extraction. The theorem `advance_boot_level_ok_retained` below adds the outcome of the lookup as
a hypothesis and concludes that the queue is not empty. Hypotheses: the outcome of
`get_hkdf_key` (`hget`); that the cache `s1` has current level at most `L` (`hle`) and at least
`L - current` entries (`hlen`), which is what makes the subtraction and the split succeed; the
shared law for `VecDeque::split_off`; `ContextKeyLaw`; the laws `format` and
`from_str_nonconst`. -/
theorem BootLevelKeyCache_advance_boot_level_ok (view : View) (root : anyhow.Error → ErrRoot)
    (hsplit : ZVecQueueSplitOffLaw view)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (o : Option keystore2_crypto.zvec.ZVec)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk o, s1))
    (hle : s1.current.val ≤ L.val)
    (hlen : L.val - s1.current.val ≤ (view s1.cache).length) :
    ∃ s', BootLevelKeyCache.advance_boot_level s L = ok (ROk (), s') ∧
      s'.current = L ∧ view s'.cache = (view s1.cache).drop (L.val - s1.current.val) := by
  obtain ⟨a, ha⟩ := hargs (toStr "keystore2/src/boot_level_keys.rs:253: Advancing cache")
  obtain ⟨str, hs⟩ := hfmt a
  obtain ⟨i1, hi1, hv1⟩ := usize_sub_ok L s1.current hle
  obtain ⟨tl, hd, hsp, hvt, -⟩ := hsplit.2 s1.cache i1 (by omega)
  refine ⟨{ current := L, cache := tl }, ?_, rfl, by simp [hvt, hv1]⟩
  unfold BootLevelKeyCache.advance_boot_level
  simp [hacc, hget, ha, hs, hctx.1 o str, core.hint.must_use,
    resultBranch, hi1, hsp]

/-- conditional: as `advance_boot_level_ok`, with one more hypothesis about the lookup: the queue
of the cache `s1` that `get_hkdf_key` returned has more than `L - current` entries (`hlong`).
Then the queue that `advance_boot_level` keeps is not empty, and its first element is the entry
of the queue of `s1` at the offset `L - current`. In the Rust source the lookup grows the queue
until it has an element at the requested offset, and the split keeps the elements from that
offset; the translation leaves `get_hkdf_key` opaque, so `hlong` is a hypothesis here, not a
consequence (blocked by extraction). The statement does not relate the returned key `o` to the
retained entry, for the same reason. Hypotheses: the outcome of `get_hkdf_key` (`hget`); that
the cache `s1` has current level at most `L` (`hle`); `hlong`; the shared law for
`VecDeque::split_off`; `ContextKeyLaw`; the laws `format` and `from_str_nonconst`. -/
theorem BootLevelKeyCache_advance_boot_level_ok_retained (view : View)
    (root : anyhow.Error → ErrRoot)
    (hsplit : ZVecQueueSplitOffLaw view)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (o : Option keystore2_crypto.zvec.ZVec)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk o, s1))
    (hle : s1.current.val ≤ L.val)
    (hlong : L.val - s1.current.val < (view s1.cache).length) :
    ∃ s', BootLevelKeyCache.advance_boot_level s L = ok (ROk (), s') ∧
      s'.current = L ∧ view s'.cache ≠ [] ∧
      (view s'.cache).head? = (view s1.cache)[L.val - s1.current.val]? := by
  obtain ⟨s', hs', hc, hv⟩ := BootLevelKeyCache_advance_boot_level_ok view root hsplit hctx hfmt
    hargs s s1 L o hacc hget hle (by omega)
  refine ⟨s', hs', hc, ?_, ?_⟩
  · rw [hv]; simp [List.drop_eq_nil_iff]; omega
  · rw [hv]; simp

/-- conditional: if the level is accessible and `get_hkdf_key` fails (returns `fail x`), then
`advance_boot_level` fails with the same `x`. Hypotheses: the level is accessible (`hacc`) and
the outcome of `get_hkdf_key` (`hget`). No law is needed. -/
theorem BootLevelKeyCache_advance_boot_level_fail_get_hkdf_key
    (s : BootLevelKeyCache) (L : BootLevel) (x : Error)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = fail x) :
    BootLevelKeyCache.advance_boot_level s L = fail x := by
  unfold BootLevelKeyCache.advance_boot_level
  simp [hacc, hget]

/-- conditional: if the level is accessible, `get_hkdf_key` returned `Ok` with a cache `s1` whose
current level is above `L`, then `advance_boot_level` fails with an integer overflow: the
subtraction `L - current` underflows. Hypotheses: the outcome of `get_hkdf_key` (`hget`); the
bound `hlt`; `ContextKeyLaw`; the laws `format` and `from_str_nonconst`. Model limit: this is a
conditional check on an arbitrary state returned by the opaque `get_hkdf_key`. In the Rust source
a successful lookup never returns such a state (the call is made only when `L` is at least
`current`, and the lookup never changes `current`), so the Rust code cannot reach this failure. -/
theorem BootLevelKeyCache_advance_boot_level_fail_sub (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (o : Option keystore2_crypto.zvec.ZVec)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk o, s1))
    (hlt : L.val < s1.current.val) :
    BootLevelKeyCache.advance_boot_level s L = fail Error.integerOverflow := by
  obtain ⟨a, ha⟩ := hargs (toStr "keystore2/src/boot_level_keys.rs:253: Advancing cache")
  obtain ⟨str, hs⟩ := hfmt a
  unfold BootLevelKeyCache.advance_boot_level
  simp [hacc, hget, ha, hs, hctx.1 o str, core.hint.must_use,
    resultBranch, usize_sub_fail L s1.current hlt]

/-- conditional: if the level is accessible, `get_hkdf_key` returned `Ok` with a cache `s1` whose
current level is at most `L`, and the queue of `s1` has fewer than `L - current` entries, then
`advance_boot_level` panics: the shared law for `VecDeque::split_off` says the split fails when
the offset is beyond the length. Hypotheses: the outcome of `get_hkdf_key` (`hget`); `hle`;
`hover`; the law `ZVecQueueSplitOffLaw`; `ContextKeyLaw`; the laws `format` and
`from_str_nonconst`. Model limit: this is a conditional check on an arbitrary state returned by
the opaque `get_hkdf_key`. In the Rust source a successful lookup never returns such a state (it
has grown the queue to hold an element at the requested offset), so the Rust code cannot reach
this failure. -/
theorem BootLevelKeyCache_advance_boot_level_fail_split_off (view : View)
    (root : anyhow.Error → ErrRoot)
    (hsplit : ZVecQueueSplitOffLaw view)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (o : Option keystore2_crypto.zvec.ZVec)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk o, s1))
    (hle : s1.current.val ≤ L.val)
    (hover : (view s1.cache).length < L.val - s1.current.val) :
    BootLevelKeyCache.advance_boot_level s L = fail Error.panic := by
  obtain ⟨a, ha⟩ := hargs (toStr "keystore2/src/boot_level_keys.rs:253: Advancing cache")
  obtain ⟨str, hs⟩ := hfmt a
  obtain ⟨i1, hi1, hv1⟩ := usize_sub_ok L s1.current hle
  unfold BootLevelKeyCache.advance_boot_level
  simp [hacc, hget, ha, hs, hctx.1 o str, core.hint.must_use,
    resultBranch, hi1, hsplit.1 s1.cache i1 (by omega)]


end Keystore2Verify.BootLevelKeys
