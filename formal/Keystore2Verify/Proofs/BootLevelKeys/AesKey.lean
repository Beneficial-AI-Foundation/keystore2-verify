import Keystore2Verify.Specs.Defs.BootLevelKeys
import Keystore2Verify.Proofs.BootLevelKeys.ExpandKey
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
open core.result.Result.Insts.CoreOpsTry renaming branch → resultBranch

/-- conditional: if `expand_key` (called with the length `AES_256_KEY_LENGTH` and the info string
`HKDF_AES`) returned the cache `s1`, then `aes_key` returns the cache `s1`: `aes_key` itself
changes nothing. Hypotheses: the call outcome `expand_key s L AES_256_KEY_LENGTH HKDF_AES =
ok (r0, s1)` (`hexp`), where `r0` and `s1` are otherwise arbitrary; and that `aes_key` returned
`ok (r, s')` (`h`). -/
theorem BootLevelKeyCache_aes_key_state
    (s s1 s' : BootLevelKeyCache) (L : BootLevel)
    (r0 r : core.result.Result (Option keystore2_crypto.zvec.ZVec) anyhow.Error)
    (hexp : BootLevelKeyCache.expand_key s L keystore2_crypto.AES_256_KEY_LENGTH
      BootLevelKeyCache.HKDF_AES = ok (r0, s1))
    (h : BootLevelKeyCache.aes_key s L = ok (r, s')) : s' = s1 := by
  unfold BootLevelKeyCache.aes_key at h
  simp [hexp, bind_eq_ok_iff, core.hint.must_use] at h
  obtain ⟨a, -, str, -, -, h⟩ := h
  exact h.symm

/-- conditional: if `expand_key` (called with `AES_256_KEY_LENGTH` and `HKDF_AES`) returned
`Err e` with the cache `s1`, then `aes_key` returns an `Err` with the same root cause and the
cache `s1`. Hypotheses: the outcome of `expand_key` (`hexp`); `ContextKeyLaw`; the laws `format`
and `from_str_nonconst`. -/
theorem BootLevelKeyCache_aes_key_err (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (e : anyhow.Error)
    (hexp : BootLevelKeyCache.expand_key s L keystore2_crypto.AES_256_KEY_LENGTH
      BootLevelKeyCache.HKDF_AES = ok (RErr e, s1)) :
    ∃ e', BootLevelKeyCache.aes_key s L = ok (RErr e', s1) ∧
      root e' = root e := by
  obtain ⟨a, ha⟩ := hargs (toStr "keystore2/src/boot_level_keys.rs:288: expand_key failed")
  obtain ⟨str, hs⟩ := hfmt a
  obtain ⟨e', he', hr⟩ := hctx.2 e str
  refine ⟨e', ?_, hr⟩
  unfold BootLevelKeyCache.aes_key
  simp [hexp, ha, hs, he', core.hint.must_use]

/-- conditional: if `expand_key` (called with `AES_256_KEY_LENGTH` and `HKDF_AES`) returned
`Ok v` with the cache `s1`, then `aes_key` returns the same `Ok v` and the cache `s1`. This
covers `Ok None` (level not accessible) and `Ok (some key)`. Hypotheses: the outcome of
`expand_key` (`hexp`); `ContextKeyLaw`; the laws `format` and `from_str_nonconst`. -/
theorem BootLevelKeyCache_aes_key_ok (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (v : Option keystore2_crypto.zvec.ZVec)
    (hexp : BootLevelKeyCache.expand_key s L keystore2_crypto.AES_256_KEY_LENGTH
      BootLevelKeyCache.HKDF_AES = ok (ROk v, s1)) :
    BootLevelKeyCache.aes_key s L = ok (ROk v, s1) := by
  obtain ⟨a, ha⟩ := hargs (toStr "keystore2/src/boot_level_keys.rs:288: expand_key failed")
  obtain ⟨str, hs⟩ := hfmt a
  unfold BootLevelKeyCache.aes_key
  simp [hexp, ha, hs, hctx.1 v str, core.hint.must_use]

/-- conditional: if `aes_key` returns `Ok (some z)`, then `z` has exactly 32 bytes.
Hypotheses: the shared law for the length of `hkdf_expand` (`KeystoreCryptoHkdfExpandSpec`);
`ContextKeyLaw` and `ContextCryptoLaw`. -/
theorem BootLevelKeyCache_aes_key_len (root : anyhow.Error → ErrRoot)
    (hhkdf : KeystoreCryptoHkdfExpandSpec) (hctx : ContextKeyLaw root)
    (hcc : ContextCryptoLaw root)
    (s s' : BootLevelKeyCache) (L : BootLevel) (z : keystore2_crypto.zvec.ZVec)
    (h : BootLevelKeyCache.aes_key s L = ok (ROk (some z), s')) :
    ∃ sl, zvecDeref z = ok sl ∧ sl.length = 32 := by
  unfold BootLevelKeyCache.aes_key at h
  simp [bind_eq_ok_iff, core.hint.must_use] at h
  obtain ⟨r, hexp, a, -, str, -, h⟩ := h
  rcases r with v | e
  · rw [hctx.1] at h
    simp at h
    subst h
    obtain ⟨sl, hsl, hl⟩ := BootLevelKeyCache_expand_key_len root hhkdf hcc s s' L _ _ z hexp
    exact ⟨sl, hsl, by simpa [keystore2_crypto.AES_256_KEY_LENGTH] using hl⟩
  · obtain ⟨e', he', -⟩ := hctx.2 e str
    rw [he'] at h
    simp at h

/-- conditional: if `expand_key` (called with `AES_256_KEY_LENGTH` and `HKDF_AES`) fails
(returns `fail x`), then `aes_key` fails with the same `x`. Hypothesis: the outcome of
`expand_key` (`hexp`). No law is needed. -/
theorem BootLevelKeyCache_aes_key_fail_expand_key
    (s : BootLevelKeyCache) (L : BootLevel) (x : Error)
    (hexp : BootLevelKeyCache.expand_key s L keystore2_crypto.AES_256_KEY_LENGTH
      BootLevelKeyCache.HKDF_AES = fail x) :
    BootLevelKeyCache.aes_key s L = fail x := by
  unfold BootLevelKeyCache.aes_key
  simp [hexp]

/-- conditional: if `get_hkdf_key` fails (returns `fail x`), then `aes_key` fails with the same
`x`. Hypothesis: the outcome of `get_hkdf_key` (`hget`). No law is needed. -/
theorem BootLevelKeyCache_aes_key_fail_get_hkdf_key
    (s : BootLevelKeyCache) (L : BootLevel) (x : Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = fail x) :
    BootLevelKeyCache.aes_key s L = fail x := by
  exact BootLevelKeyCache_aes_key_fail_expand_key s L x
    (BootLevelKeyCache_expand_key_fail_get_hkdf_key s L _ _ x hget)

/-- conditional: if `get_hkdf_key` returned `Ok (some k)`, and `hkdf_expand` on `k` with
`AES_256_KEY_LENGTH` and `HKDF_AES` fails (returns `fail x`), then `aes_key` fails with the same
`x`. Hypotheses: the outcome of `get_hkdf_key` (`hget`); the view of `k` as a slice `sl`
(`hderef`) and the outcome of `hkdf_expand` on it (`hexp`); `ContextKeyLaw`; the laws `format`
and `from_str_nonconst`. -/
theorem BootLevelKeyCache_aes_key_fail_expand (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (sl : Slice Std.U8)
    (k : keystore2_crypto.zvec.ZVec) (x : Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk (some k), s1))
    (hderef : zvecDeref k = ok sl)
    (hexp : keystore2_crypto.hkdf_expand keystore2_crypto.AES_256_KEY_LENGTH sl
      BootLevelKeyCache.HKDF_AES = fail x) :
    BootLevelKeyCache.aes_key s L = fail x := by
  exact BootLevelKeyCache_aes_key_fail_expand_key s L x
    (BootLevelKeyCache_expand_key_fail_expand root hctx hfmt hargs s s1 L _ _ sl k x hget
      hderef hexp)

/-- conditional: if `get_hkdf_key` returned `Ok (some k)`, and the view of `k` as a slice
(`zvecDeref k`) fails (returns `fail x`), then `aes_key` fails with the same `x`.
Hypotheses: the outcome of `get_hkdf_key` (`hget`); the outcome of the view (`hderef`);
`ContextKeyLaw`; the laws `format` and `from_str_nonconst`. -/
theorem BootLevelKeyCache_aes_key_fail_deref (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel)
    (k : keystore2_crypto.zvec.ZVec) (x : Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk (some k), s1))
    (hderef : zvecDeref k = fail x) :
    BootLevelKeyCache.aes_key s L = fail x := by
  exact BootLevelKeyCache_aes_key_fail_expand_key s L x
    (BootLevelKeyCache_expand_key_fail_deref root hctx hfmt hargs s s1 L _ _ k x hget hderef)


end Keystore2Verify.BootLevelKeys
