import Keystore2Verify.Specs.Defs.BootLevelKeys
import Keystore2Verify.Proofs.Lemmas.BootLevelKeysBind

namespace Keystore2Verify.BootLevelKeys
open Aeneas Aeneas.Std Result keystore2 keystore2.boot_level_keys Keystore2Verify.Externals
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open keystore2.boot_level_keys.BootLevel.Insts
open CoreCloneClone renaming clone → bootLevelClone
open CoreCmpPartialEqBootLevel renaming eq → bootLevelEq
open CoreCmpOrd renaming cmp → bootLevelCmp
open CoreCmpPartialOrdBootLevel renaming partial_cmp → bootLevelPartialCmp
open keystore2.keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8 renaming
  deref → zvecDeref
open BootLevelKeyCache.expand_key.closure.Insts
open Aeneas.Std.core.option.Option renaming map → optionMap
open keystore2.core.option.OptionResult renaming transpose → optionTranspose
open core.result.Result.Insts.CoreOpsTry renaming branch → resultBranch
open core.result.Result.Insts.CoreOpsTry_traitFromResidualResult renaming
  from_residual → resultFromResidual

/-- conditional: if `get_hkdf_key` returned the cache `s1`, then `expand_key` returns the cache
`s1`, whatever its result: `expand_key` itself changes nothing. Hypotheses: the call outcome
`get_hkdf_key s L = ok (r0, s1)` (`hget`), where `r0` and `s1` are otherwise arbitrary; and that
`expand_key` returned `ok (r, s')` (`h`). -/
theorem BootLevelKeyCache_expand_key_state
    (s s1 s' : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info : Slice Std.U8)
    (r0 : core.result.Result (Option keystore2_crypto.zvec.ZVec) anyhow.Error)
    (r : core.result.Result (Option keystore2_crypto.zvec.ZVec) anyhow.Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (r0, s1))
    (h : BootLevelKeyCache.expand_key s L n info = ok (r, s')) : s' = s1 := by
  unfold BootLevelKeyCache.expand_key at h
  simp [hget, bind_eq_ok_iff, core.hint.must_use, resultBranch] at h
  obtain ⟨a, -, str, -, r1, -, h⟩ := h
  rcases r1 with v | e
  · simp [bind_eq_ok_iff] at h
    grind
  · simp [resultFromResidual] at h
    exact h.2.symm

/-- conditional: if `get_hkdf_key` returned `Err e` with the cache `s1`, then `expand_key`
returns an `Err` with the same root cause and the cache `s1`. In the Rust source this path
returns before `hkdf_expand` is called; the statement does not say that. Hypotheses: the
outcome of `get_hkdf_key` (`hget`); the shared law `ResultContextLaw` for `Result::context`
(`ContextKeyLaw`); the laws `format` and `from_str_nonconst`. -/
theorem BootLevelKeyCache_expand_key_err_lookup (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info : Slice Std.U8)
    (e : anyhow.Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (RErr e, s1)) :
    ∃ e', BootLevelKeyCache.expand_key s L n info = ok (RErr e', s1) ∧
      root e' = root e := by
  obtain ⟨a, ha⟩ := hargs (toStr "keystore2/src/boot_level_keys.rs:279: Looking up HKDF key")
  obtain ⟨str, hs⟩ := hfmt a
  obtain ⟨e', he', hr⟩ := hctx.2 e str
  unfold BootLevelKeyCache.expand_key
  simp [hget, ha, hs, he', core.hint.must_use, resultBranch, resultFromResidual]
  exact hr

/-- conditional: if `get_hkdf_key` returned `Ok None` with cache `s1`, then `expand_key` returns
`Ok None` and cache `s1`. In the Rust source the lookup returns `Ok(None)` when the level is not
accessible, and the `Option::map` of this path has no key to pass to `hkdf_expand`; the statement
does not say either. Hypotheses: the outcome of `get_hkdf_key` (`hget`); `ContextKeyLaw` and
`ContextCryptoLaw` (an `Ok` stays `Ok`); the laws `format` and `from_str_nonconst`. -/
theorem BootLevelKeyCache_expand_key_none (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hcc : ContextCryptoLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info : Slice Std.U8)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk none, s1)) :
    BootLevelKeyCache.expand_key s L n info = ok (ROk none, s1) := by
  obtain ⟨a, ha⟩ := hargs (toStr "keystore2/src/boot_level_keys.rs:279: Looking up HKDF key")
  obtain ⟨str, hs⟩ := hfmt a
  obtain ⟨a1, ha1⟩ := hargs (toStr "keystore2/src/boot_level_keys.rs:282: Calling hkdf_expand")
  obtain ⟨str1, hs1⟩ := hfmt a1
  unfold BootLevelKeyCache.expand_key
  simp [hget, ha, hs, ha1, hs1, hctx.1 _ str, core.hint.must_use, resultBranch,
    resultFromResidual, optionMap,
    CoreOpsFunctionFnOnceTupleShared0ZVecResultZVecError.call_once,
    optionTranspose, hcc.1 _ str1]

/-- conditional: if `get_hkdf_key` returned `Ok (some k)` with the cache `s1`, and
`hkdf_expand n k info` returned `Ok z`, then `expand_key` returns `Ok (some z)` and the cache
`s1`. Hypotheses: the outcome of `get_hkdf_key` (`hget`); the view of `k` as a slice `sl`
(`hderef`) and the outcome of `hkdf_expand` on it (`hexp`); `ContextKeyLaw` and
`ContextCryptoLaw`; the laws `format` and `from_str_nonconst`. -/
theorem BootLevelKeyCache_expand_key_some (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hcc : ContextCryptoLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info sl : Slice Std.U8)
    (k z : keystore2_crypto.zvec.ZVec)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk (some k), s1))
    (hderef : zvecDeref k = ok sl)
    (hexp : keystore2_crypto.hkdf_expand n sl info = ok (ROk z)) :
    BootLevelKeyCache.expand_key s L n info = ok (ROk (some z), s1) := by
  obtain ⟨a, ha⟩ := hargs (toStr "keystore2/src/boot_level_keys.rs:279: Looking up HKDF key")
  obtain ⟨str, hs⟩ := hfmt a
  obtain ⟨a1, ha1⟩ := hargs (toStr "keystore2/src/boot_level_keys.rs:282: Calling hkdf_expand")
  obtain ⟨str1, hs1⟩ := hfmt a1
  unfold BootLevelKeyCache.expand_key
  simp [hget, ha, hs, ha1, hs1, hctx.1 _ str, core.hint.must_use, resultBranch,
    resultFromResidual, optionMap,
    CoreOpsFunctionFnOnceTupleShared0ZVecResultZVecError.call_once,
    optionTranspose, hderef, hexp, hcc.1 _ str1]

/-- conditional: if `get_hkdf_key` returned `Ok (some k)` with the cache `s1`, and
`hkdf_expand n k info` returned `Err ce`, then `expand_key` returns an `Err` whose root cause is
the crypto error `ce`, and the cache `s1`. Hypotheses: as in `expand_key_some`, with the outcome
`Err ce` of `hkdf_expand`. -/
theorem BootLevelKeyCache_expand_key_err_expand (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hcc : ContextCryptoLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info sl : Slice Std.U8)
    (k : keystore2_crypto.zvec.ZVec) (ce : keystore2_crypto.error.Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk (some k), s1))
    (hderef : zvecDeref k = ok sl)
    (hexp : keystore2_crypto.hkdf_expand n sl info = ok (RErr ce)) :
    ∃ e, BootLevelKeyCache.expand_key s L n info = ok (RErr e, s1) ∧
      root e = ErrRoot.crypto ce := by
  obtain ⟨a, ha⟩ := hargs (toStr "keystore2/src/boot_level_keys.rs:279: Looking up HKDF key")
  obtain ⟨str, hs⟩ := hfmt a
  obtain ⟨a1, ha1⟩ := hargs (toStr "keystore2/src/boot_level_keys.rs:282: Calling hkdf_expand")
  obtain ⟨str1, hs1⟩ := hfmt a1
  obtain ⟨e, he, hr⟩ := hcc.2 ce str1
  refine ⟨e, ?_, hr⟩
  unfold BootLevelKeyCache.expand_key
  simp [hget, ha, hs, ha1, hs1, hctx.1 _ str, core.hint.must_use, resultBranch,
    resultFromResidual, optionMap,
    CoreOpsFunctionFnOnceTupleShared0ZVecResultZVecError.call_once,
    optionTranspose, hderef, hexp, he]

/-- conditional: if `expand_key` returns `Ok (some z)`, then `z` has exactly `n` bytes.
Hypotheses: the shared law for the length of `hkdf_expand` (`KeystoreCryptoHkdfExpandSpec`);
`ContextCryptoLaw` for the final call to `context`. -/
theorem BootLevelKeyCache_expand_key_len (root : anyhow.Error → ErrRoot)
    (hhkdf : KeystoreCryptoHkdfExpandSpec) (hcc : ContextCryptoLaw root)
    (s s' : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info : Slice Std.U8)
    (z : keystore2_crypto.zvec.ZVec)
    (h : BootLevelKeyCache.expand_key s L n info = ok (ROk (some z), s')) :
    ∃ sl, zvecDeref z = ok sl ∧ sl.length = n.val := by
  unfold BootLevelKeyCache.expand_key at h
  simp [bind_eq_ok_iff, core.hint.must_use, resultBranch] at h
  obtain ⟨r, s1, -, a, -, str, -, r1, -, h⟩ := h
  rcases r1 with v | e
  · cases v with
    | none =>
      simp [optionMap, optionTranspose,
        bind_eq_ok_iff] at h
      obtain ⟨a1, -, str1, -, r3, hr3, h⟩ := h
      rw [hcc.1] at r3
      simp at r3
    | some k =>
      simp [optionMap, optionTranspose, bind_eq_ok_iff,
        CoreOpsFunctionFnOnceTupleShared0ZVecResultZVecError.call_once,
        ] at h
      obtain ⟨o, ho, m, hm, a1, -, str1, -, hc, -⟩ := h
      obtain ⟨mp, hmp, hmo⟩ := bind_eq_ok_iff.1 ho
      obtain ⟨sl, hsl, hx⟩ := bind_eq_ok_iff.1 hmp
      obtain rfl : o = some mp := by simpa using hmo.symm
      rcases mp with w | e
      · simp at hm
        subst hm
        rw [hcc.1] at hc
        simp at hc
        subst hc
        exact hhkdf n sl info w hx
      · simp at hm
        subst hm
        obtain ⟨e', he', -⟩ := hcc.2 e str1
        rw [he'] at hc
        simp at hc
  · simp [resultFromResidual] at h

/-- conditional: if `get_hkdf_key` fails (returns `fail x`), then `expand_key` fails with the same
`x`. Hypothesis: the outcome of `get_hkdf_key` (`hget`). No law is needed. -/
theorem BootLevelKeyCache_expand_key_fail_get_hkdf_key
    (s : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info : Slice Std.U8) (x : Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = fail x) :
    BootLevelKeyCache.expand_key s L n info = fail x := by
  unfold BootLevelKeyCache.expand_key
  simp [hget]

/-- conditional: if `get_hkdf_key` returned `Ok (some k)`, and `hkdf_expand n k info` fails
(returns `fail x`), then `expand_key` fails with the same `x`. Hypotheses: the outcome of
`get_hkdf_key` (`hget`); the view of `k` as a slice `sl` (`hderef`) and the outcome of
`hkdf_expand` on it (`hexp`); `ContextKeyLaw`; the laws `format` and `from_str_nonconst`. -/
theorem BootLevelKeyCache_expand_key_fail_expand (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info sl : Slice Std.U8)
    (k : keystore2_crypto.zvec.ZVec) (x : Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk (some k), s1))
    (hderef : zvecDeref k = ok sl)
    (hexp : keystore2_crypto.hkdf_expand n sl info = fail x) :
    BootLevelKeyCache.expand_key s L n info = fail x := by
  obtain ⟨a, ha⟩ := hargs (toStr "keystore2/src/boot_level_keys.rs:279: Looking up HKDF key")
  obtain ⟨str, hs⟩ := hfmt a
  unfold BootLevelKeyCache.expand_key
  simp [hget, ha, hs, hctx.1 _ str, core.hint.must_use, resultBranch,
    resultFromResidual, optionMap,
    CoreOpsFunctionFnOnceTupleShared0ZVecResultZVecError.call_once,
    optionTranspose, hderef, hexp]

/-- conditional: if `get_hkdf_key` returned `Ok (some k)`, and the view of `k` as a slice
(`zvecDeref k`) fails (returns `fail x`), then `expand_key` fails with the same `x`.
Hypotheses: the outcome of `get_hkdf_key` (`hget`); the outcome of the view (`hderef`);
`ContextKeyLaw`; the laws `format` and `from_str_nonconst`. -/
theorem BootLevelKeyCache_expand_key_fail_deref (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info : Slice Std.U8)
    (k : keystore2_crypto.zvec.ZVec) (x : Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk (some k), s1))
    (hderef : zvecDeref k = fail x) :
    BootLevelKeyCache.expand_key s L n info = fail x := by
  obtain ⟨a, ha⟩ := hargs (toStr "keystore2/src/boot_level_keys.rs:279: Looking up HKDF key")
  obtain ⟨str, hs⟩ := hfmt a
  unfold BootLevelKeyCache.expand_key
  simp [hget, ha, hs, hctx.1 _ str, core.hint.must_use, resultBranch,
    resultFromResidual, optionMap,
    CoreOpsFunctionFnOnceTupleShared0ZVecResultZVecError.call_once,
    optionTranspose, hderef]


end Keystore2Verify.BootLevelKeys
