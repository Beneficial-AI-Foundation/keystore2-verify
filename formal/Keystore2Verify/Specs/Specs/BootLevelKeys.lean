import Keystore2Verify.Proofs.BootLevelKeys.BootLevel
import Keystore2Verify.Proofs.BootLevelKeys.Constants
import Keystore2Verify.Proofs.BootLevelKeys.New
import Keystore2Verify.Proofs.BootLevelKeys.LevelAccessible
import Keystore2Verify.Proofs.BootLevelKeys.AdvanceBootLevel
import Keystore2Verify.Proofs.BootLevelKeys.Finish
import Keystore2Verify.Proofs.BootLevelKeys.ExpandKey
import Keystore2Verify.Proofs.BootLevelKeys.AesKey

namespace Keystore2Verify.BootLevelKeys
open Aeneas Aeneas.Std Result keystore2 keystore2.boot_level_keys Keystore2Verify.Externals
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open keystore2.boot_level_keys.BootLevel.Insts
open CoreCloneClone renaming clone → bootLevelClone
open CoreCmpPartialEqBootLevel renaming eq → bootLevelEq
open CoreCmpOrd renaming cmp → bootLevelCmp
open CoreCmpPartialOrdBootLevel renaming partial_cmp → bootLevelPartialCmp
open keystore2.alloc.collections.vec_deque
open keystore2.keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8 renaming
  deref → zvecDeref

recall boot_level_clone (a : BootLevel) :
    bootLevelClone a = ok a

recall boot_level_eq (a b : BootLevel) :
    ∃ r, bootLevelEq a b = ok r ∧ (r = true ↔ a.val = b.val)

recall boot_level_cmp (a b : BootLevel) :
    ∃ o, bootLevelCmp a b = ok o ∧
      (o = .lt ↔ a.val < b.val) ∧ (o = .eq ↔ a.val = b.val) ∧ (o = .gt ↔ b.val < a.val)

recall boot_level_partial_cmp (a b : BootLevel) :
    ∃ o, bootLevelPartialCmp a b = ok (some o) ∧
      (o = .lt ↔ a.val < b.val) ∧ (o = .eq ↔ a.val = b.val) ∧ (o = .gt ↔ b.val < a.val)

recall hkdf_advance_bytes : BytesAre BootLevelKeyCache.HKDF_ADVANCE.val "Advance KDF one step"

recall hkdf_aes_bytes : BytesAre BootLevelKeyCache.HKDF_AES.val "Generate AES-256-GCM key"

recall hkdf_key_size_val : BootLevelKeyCache.HKDF_KEY_SIZE.val = 32

recall BootLevelKeyCache_new_current (k : keystore2_crypto.zvec.ZVec) (s : BootLevelKeyCache)
    (h : BootLevelKeyCache.new k = ok s) : s.current.val = 0

recall BootLevelKeyCache_new_ok (view : View)
    (hnew : VecDequeNewLaw view (VecDequeTGlobal.new keystore2_crypto.zvec.ZVec))
    (hpush : VecDequePushBackLaw view VecDeque.push_back)
    (k : keystore2_crypto.zvec.ZVec) :
    ∃ s, BootLevelKeyCache.new k = ok s ∧ s.current.val = 0 ∧ view s.cache = [k]

recall BootLevelKeyCache_level_accessible_lt (s : BootLevelKeyCache) (L : BootLevel)
    (h : L.val < s.current.val) : BootLevelKeyCache.level_accessible s L = ok false

recall BootLevelKeyCache_level_accessible_iff (view : View)
    (hempty : VecDequeIsEmptyLaw view VecDeque.is_empty) (s : BootLevelKeyCache)
    (L : BootLevel) :
    ∃ b, BootLevelKeyCache.level_accessible s L = ok b ∧
      (b = true ↔ s.current.val ≤ L.val ∧ view s.cache ≠ [])

recall BootLevelKeyCache_advance_boot_level_not_accessible
    (s s' : BootLevelKeyCache) (L : BootLevel) (r : core.result.Result Unit anyhow.Error)
    (hacc : BootLevelKeyCache.level_accessible s L = ok false)
    (h : BootLevelKeyCache.advance_boot_level s L = ok (r, s')) :
    r = ROk () ∧ s' = s

recall BootLevelKeyCache_advance_boot_level_not_accessible_ok (view : View)
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) (hlen : VecDequeLenLaw view VecDeque.len)
    (s : BootLevelKeyCache) (L : BootLevel)
    (hacc : BootLevelKeyCache.level_accessible s L = ok false) :
    BootLevelKeyCache.advance_boot_level s L = ok (ROk (), s)

recall BootLevelKeyCache_advance_boot_level_below (view : View)
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) (hlen : VecDequeLenLaw view VecDeque.len)
    (s : BootLevelKeyCache) (L : BootLevel) (hlt : L.val < s.current.val) :
    BootLevelKeyCache.advance_boot_level s L = ok (ROk (), s)

recall BootLevelKeyCache_advance_boot_level_accessible_shape
    (s s1 s' : BootLevelKeyCache) (L : BootLevel)
    (r0 : core.result.Result (Option keystore2_crypto.zvec.ZVec) anyhow.Error)
    (r : core.result.Result Unit anyhow.Error)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (r0, s1))
    (h : BootLevelKeyCache.advance_boot_level s L = ok (r, s')) :
    (s' = s1 ∧ ∃ e, r = RErr e) ∨
      (r = ROk () ∧ s'.current = L)

recall BootLevelKeyCache_advance_boot_level_err (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (e : anyhow.Error)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (RErr e, s1)) :
    ∃ e', BootLevelKeyCache.advance_boot_level s L = ok (RErr e', s1) ∧
      root e' = root e

recall BootLevelKeyCache_advance_boot_level_ok (view : View) (root : anyhow.Error → ErrRoot)
    (hsplit : VecDequeSplitOffLaw view (VecDeque.split_off core.clone.CloneGlobal))
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (o : Option keystore2_crypto.zvec.ZVec)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk o, s1))
    (hle : s1.current.val ≤ L.val)
    (hlen : L.val - s1.current.val ≤ (view s1.cache).length) :
    ∃ s', BootLevelKeyCache.advance_boot_level s L = ok (ROk (), s') ∧
      s'.current = L ∧ view s'.cache = (view s1.cache).drop (L.val - s1.current.val)

recall BootLevelKeyCache_finish_current (s s' : BootLevelKeyCache)
    (h : BootLevelKeyCache.finish s = ok s') : s'.current = s.current

recall BootLevelKeyCache_finish_ok (view : View)
    (hclear : VecDequeClearLaw view VecDeque.clear) (s : BootLevelKeyCache) :
    ∃ s', BootLevelKeyCache.finish s = ok s' ∧ s'.current = s.current ∧ view s'.cache = []

recall BootLevelKeyCache_expand_key_state
    (s s1 s' : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info : Slice Std.U8)
    (r0 : core.result.Result (Option keystore2_crypto.zvec.ZVec) anyhow.Error)
    (r : core.result.Result (Option keystore2_crypto.zvec.ZVec) anyhow.Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (r0, s1))
    (h : BootLevelKeyCache.expand_key s L n info = ok (r, s')) : s' = s1

recall BootLevelKeyCache_expand_key_err_lookup (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info : Slice Std.U8)
    (e : anyhow.Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (RErr e, s1)) :
    ∃ e', BootLevelKeyCache.expand_key s L n info = ok (RErr e', s1) ∧
      root e' = root e

recall BootLevelKeyCache_expand_key_none (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hcc : ContextCryptoLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info : Slice Std.U8)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk none, s1)) :
    BootLevelKeyCache.expand_key s L n info = ok (ROk none, s1)

recall BootLevelKeyCache_expand_key_some (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hcc : ContextCryptoLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info sl : Slice Std.U8)
    (k z : keystore2_crypto.zvec.ZVec)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk (some k), s1))
    (hderef : zvecDeref k = ok sl)
    (hexp : keystore2_crypto.hkdf_expand n sl info = ok (ROk z)) :
    BootLevelKeyCache.expand_key s L n info = ok (ROk (some z), s1)

recall BootLevelKeyCache_expand_key_err_expand (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hcc : ContextCryptoLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info sl : Slice Std.U8)
    (k : keystore2_crypto.zvec.ZVec) (ce : keystore2_crypto.error.Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk (some k), s1))
    (hderef : zvecDeref k = ok sl)
    (hexp : keystore2_crypto.hkdf_expand n sl info = ok (RErr ce)) :
    ∃ e, BootLevelKeyCache.expand_key s L n info = ok (RErr e, s1) ∧
      root e = ErrRoot.crypto ce

recall BootLevelKeyCache_expand_key_len (root : anyhow.Error → ErrRoot)
    (hhkdf : KeystoreCryptoHkdfExpandSpec) (hctx : ContextKeyLaw root)
    (hcc : ContextCryptoLaw root)
    (s s' : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info : Slice Std.U8)
    (z : keystore2_crypto.zvec.ZVec)
    (h : BootLevelKeyCache.expand_key s L n info = ok (ROk (some z), s')) :
    ∃ sl, zvecDeref z = ok sl ∧ sl.length = n.val

recall BootLevelKeyCache_aes_key_state
    (s s1 s' : BootLevelKeyCache) (L : BootLevel)
    (r0 r : core.result.Result (Option keystore2_crypto.zvec.ZVec) anyhow.Error)
    (hexp : BootLevelKeyCache.expand_key s L keystore2_crypto.AES_256_KEY_LENGTH
      BootLevelKeyCache.HKDF_AES = ok (r0, s1))
    (h : BootLevelKeyCache.aes_key s L = ok (r, s')) : s' = s1

recall BootLevelKeyCache_aes_key_err (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (e : anyhow.Error)
    (hexp : BootLevelKeyCache.expand_key s L keystore2_crypto.AES_256_KEY_LENGTH
      BootLevelKeyCache.HKDF_AES = ok (RErr e, s1)) :
    ∃ e', BootLevelKeyCache.aes_key s L = ok (RErr e', s1) ∧
      root e' = root e

recall BootLevelKeyCache_aes_key_ok (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (v : Option keystore2_crypto.zvec.ZVec)
    (hexp : BootLevelKeyCache.expand_key s L keystore2_crypto.AES_256_KEY_LENGTH
      BootLevelKeyCache.HKDF_AES = ok (ROk v, s1)) :
    BootLevelKeyCache.aes_key s L = ok (ROk v, s1)

recall BootLevelKeyCache_aes_key_len (root : anyhow.Error → ErrRoot)
    (hhkdf : KeystoreCryptoHkdfExpandSpec) (hctx : ContextKeyLaw root)
    (hcc : ContextCryptoLaw root)
    (s s' : BootLevelKeyCache) (L : BootLevel) (z : keystore2_crypto.zvec.ZVec)
    (h : BootLevelKeyCache.aes_key s L = ok (ROk (some z), s')) :
    ∃ sl, zvecDeref z = ok sl ∧ sl.length = 32

end Keystore2Verify.BootLevelKeys
