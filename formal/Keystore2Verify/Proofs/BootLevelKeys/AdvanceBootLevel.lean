import Keystore2Verify.Specs.Defs.BootLevelKeys

namespace Keystore2Verify.BootLevelKeys
open Aeneas Aeneas.Std Result keystore2 keystore2.boot_level_keys Keystore2Verify.Externals
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open keystore2.boot_level_keys.BootLevel.Insts
open CoreCloneClone renaming clone → bootLevelClone
open CoreCmpPartialEqBootLevel renaming eq → bootLevelEq
open CoreCmpOrd renaming cmp → bootLevelCmp
open CoreCmpPartialOrdBootLevel renaming partial_cmp → bootLevelPartialCmp
open keystore2.alloc.collections.vec_deque

/-- exact: if the level is not accessible and `advance_boot_level` returns normally, it returns
`Ok ()` and leaves the cache unchanged. In the Rust source this path only logs. -/
theorem BootLevelKeyCache_advance_boot_level_not_accessible
    (s s' : BootLevelKeyCache) (L : BootLevel) (r : core.result.Result Unit anyhow.Error)
    (hacc : BootLevelKeyCache.level_accessible s L = ok false)
    (h : BootLevelKeyCache.advance_boot_level s L = ok (r, s')) :
    r = ROk () ∧ s' = s := by
  sorry

/-- conditional: if the level is not accessible, `advance_boot_level` does not fail: it returns
`Ok ()` and the same cache. Hypotheses: the shared laws for the log calls (`max_level`,
`Level` comparison, `loc`, `log`) and for `VecDeque::len`, for the view `view` of the queue. -/
theorem BootLevelKeyCache_advance_boot_level_not_accessible_ok (view : View)
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) (hlen : VecDequeLenLaw view VecDeque.len)
    (s : BootLevelKeyCache) (L : BootLevel)
    (hacc : BootLevelKeyCache.level_accessible s L = ok false) :
    BootLevelKeyCache.advance_boot_level s L = ok (ROk (), s) := by
  sorry

/-- conditional: a level below the current level is not advanced to. `advance_boot_level`
returns `Ok ()` and the same cache, without a change. Hypotheses: the shared laws of
`advance_boot_level_not_accessible_ok`. -/
theorem BootLevelKeyCache_advance_boot_level_below (view : View)
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) (hlen : VecDequeLenLaw view VecDeque.len)
    (s : BootLevelKeyCache) (L : BootLevel) (hlt : L.val < s.current.val) :
    BootLevelKeyCache.advance_boot_level s L = ok (ROk (), s) := by
  sorry

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
  sorry

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
  sorry

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
    (hsplit : VecDequeSplitOffLaw view (VecDeque.split_off core.clone.CloneGlobal))
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (o : Option keystore2_crypto.zvec.ZVec)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk o, s1))
    (hle : s1.current.val ≤ L.val)
    (hlen : L.val - s1.current.val ≤ (view s1.cache).length) :
    ∃ s', BootLevelKeyCache.advance_boot_level s L = ok (ROk (), s') ∧
      s'.current = L ∧ view s'.cache = (view s1.cache).drop (L.val - s1.current.val) := by
  sorry

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
    (hsplit : VecDequeSplitOffLaw view (VecDeque.split_off core.clone.CloneGlobal))
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
  sorry

/-- conditional: if the level is accessible and `get_hkdf_key` panics (returns `fail x`), then
`advance_boot_level` fails with the same `x`. Hypotheses: the level is accessible (`hacc`) and
the outcome of `get_hkdf_key` (`hget`). No law is needed. -/
theorem BootLevelKeyCache_advance_boot_level_fail_get_hkdf_key
    (s : BootLevelKeyCache) (L : BootLevel) (x : Error)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = fail x) :
    BootLevelKeyCache.advance_boot_level s L = fail x := by
  sorry

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
  sorry

/-- conditional: if the level is accessible, `get_hkdf_key` returned `Ok` with a cache `s1` whose
current level is at most `L`, and the queue of `s1` has fewer than `L - current` entries, then
`advance_boot_level` panics: the shared law for `VecDeque::split_off` says the split fails when
the offset is beyond the length. Hypotheses: the outcome of `get_hkdf_key` (`hget`); `hle`;
`hover`; the law `VecDequeSplitOffLaw`; `ContextKeyLaw`; the laws `format` and
`from_str_nonconst`. Model limit: this is a conditional check on an arbitrary state returned by
the opaque `get_hkdf_key`. In the Rust source a successful lookup never returns such a state (it
has grown the queue to hold an element at the requested offset), so the Rust code cannot reach
this failure. -/
theorem BootLevelKeyCache_advance_boot_level_fail_split_off (view : View)
    (root : anyhow.Error → ErrRoot)
    (hsplit : VecDequeSplitOffLaw view (VecDeque.split_off core.clone.CloneGlobal))
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (o : Option keystore2_crypto.zvec.ZVec)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk o, s1))
    (hle : s1.current.val ≤ L.val)
    (hover : (view s1.cache).length < L.val - s1.current.val) :
    BootLevelKeyCache.advance_boot_level s L = fail Error.panic := by
  sorry


end Keystore2Verify.BootLevelKeys
