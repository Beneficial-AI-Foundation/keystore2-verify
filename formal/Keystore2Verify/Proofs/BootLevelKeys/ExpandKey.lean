import Keystore2Verify.Specs.Defs.BootLevelKeys

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- conditional: if `expand_key` returns `Ok (some z)`, then `z` has exactly `n` bytes.
Hypotheses: the shared law for the length of `hkdf_expand` (`KeystoreCryptoHkdfExpandSpec`);
`ContextCryptoLaw` for the final call to `context`. -/
theorem BootLevelKeyCache_expand_key_len (root : anyhow.Error → ErrRoot)
    (hhkdf : KeystoreCryptoHkdfExpandSpec) (hcc : ContextCryptoLaw root)
    (s s' : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info : Slice Std.U8)
    (z : keystore2_crypto.zvec.ZVec)
    (h : BootLevelKeyCache.expand_key s L n info = ok (ROk (some z), s')) :
    ∃ sl, zvecDeref z = ok sl ∧ sl.length = n.val := by
  sorry

/-- conditional: if `get_hkdf_key` panics (returns `fail x`), then `expand_key` fails with the same
`x`. Hypothesis: the outcome of `get_hkdf_key` (`hget`). No law is needed. -/
theorem BootLevelKeyCache_expand_key_fail_get_hkdf_key
    (s : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info : Slice Std.U8) (x : Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = fail x) :
    BootLevelKeyCache.expand_key s L n info = fail x := by
  sorry

/-- conditional: if `get_hkdf_key` returned `Ok (some k)`, and `hkdf_expand n k info` panics
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
  sorry

/-- conditional: if `get_hkdf_key` returned `Ok (some k)`, and the view of `k` as a slice
(`zvecDeref k`) panics (returns `fail x`), then `expand_key` fails with the same `x`.
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
  sorry


end Keystore2Verify.BootLevelKeys
