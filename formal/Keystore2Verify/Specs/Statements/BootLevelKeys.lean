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

/-- info: 'Keystore2Verify.BootLevelKeys.boot_level_clone' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boot_level_clone

recall boot_level_eq (a b : BootLevel) :
    ∃ r, bootLevelEq a b = ok r ∧ (r = true ↔ a.val = b.val)

/-- info: 'Keystore2Verify.BootLevelKeys.boot_level_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms boot_level_eq

recall boot_level_cmp (a b : BootLevel) :
    bootLevelCmp a b = ok (compare a.val b.val)

/-- info: 'Keystore2Verify.BootLevelKeys.boot_level_cmp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms boot_level_cmp

recall boot_level_partial_cmp (a b : BootLevel) :
    bootLevelPartialCmp a b = ok (some (compare a.val b.val))

/-- info: 'Keystore2Verify.BootLevelKeys.boot_level_partial_cmp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boot_level_partial_cmp

recall hkdf_advance_bytes :
    BytesAre BootLevelKeyCache.HKDF_ADVANCE.val "Advance KDF one step"

/-- info: 'Keystore2Verify.BootLevelKeys.hkdf_advance_bytes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hkdf_advance_bytes

recall hkdf_aes_bytes : BytesAre BootLevelKeyCache.HKDF_AES.val "Generate AES-256-GCM key"

/-- info: 'Keystore2Verify.BootLevelKeys.hkdf_aes_bytes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hkdf_aes_bytes

recall hkdf_key_size_val : BootLevelKeyCache.HKDF_KEY_SIZE.val = 32

/-- info: 'Keystore2Verify.BootLevelKeys.hkdf_key_size_val' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hkdf_key_size_val

recall BootLevelKeyCache_new_current (k : keystore2_crypto.zvec.ZVec) (s : BootLevelKeyCache)
    (h : BootLevelKeyCache.new k = ok s) : s.current.val = 0

/-- info: 'Keystore2Verify.BootLevelKeys.BootLevelKeyCache_new_current' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 keystore2_crypto.zvec.ZVec,
 VecDeque,
 VecDeque.push_back,
 VecDequeTGlobal.new] -/
#guard_msgs (whitespace := lax) in
#print axioms BootLevelKeyCache_new_current

recall BootLevelKeyCache_new_ok (view : View)
    (hnew : ZVecQueueNewLaw view)
    (hpush : ZVecQueuePushBackLaw view)
    (k : keystore2_crypto.zvec.ZVec) :
    ∃ s, BootLevelKeyCache.new k = ok s ∧ s.current.val = 0 ∧ view s.cache = [k]

/-- info: 'Keystore2Verify.BootLevelKeys.BootLevelKeyCache_new_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 keystore2_crypto.zvec.ZVec,
 VecDeque,
 VecDeque.push_back,
 VecDequeTGlobal.new] -/
#guard_msgs (whitespace := lax) in
#print axioms BootLevelKeyCache_new_ok

recall BootLevelKeyCache_level_accessible_lt (s : BootLevelKeyCache) (L : BootLevel)
    (h : L.val < s.current.val) : BootLevelKeyCache.level_accessible s L = ok false

/-- info: 'Keystore2Verify.BootLevelKeys.BootLevelKeyCache_level_accessible_lt' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound,
 keystore2_crypto.zvec.ZVec,
 VecDeque,
 VecDeque.is_empty] -/
#guard_msgs (whitespace := lax) in
#print axioms BootLevelKeyCache_level_accessible_lt

recall BootLevelKeyCache_level_accessible_iff (view : View)
    (hempty : ZVecQueueIsEmptyLaw view) (s : BootLevelKeyCache)
    (L : BootLevel) :
    ∃ b, BootLevelKeyCache.level_accessible s L = ok b ∧
      (b = true ↔ s.current.val ≤ L.val ∧ view s.cache ≠ [])

/-- info: 'Keystore2Verify.BootLevelKeys.BootLevelKeyCache_level_accessible_iff' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound,
 keystore2_crypto.zvec.ZVec,
 VecDeque,
 VecDeque.is_empty] -/
#guard_msgs (whitespace := lax) in
#print axioms BootLevelKeyCache_level_accessible_iff

recall BootLevelKeyCache_advance_boot_level_not_accessible
    (s s' : BootLevelKeyCache) (L : BootLevel) (r : core.result.Result Unit anyhow.Error)
    (hacc : BootLevelKeyCache.level_accessible s L = ok false)
    (h : BootLevelKeyCache.advance_boot_level s L = ok (r, s')) :
    r = ROk () ∧ s' = s

/-- info:
'Keystore2Verify.BootLevelKeys.BootLevelKeyCache_advance_boot_level_not_accessible'
depends on axioms:
[propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 log.Metadata,
 log.Record,
 log.max_level,
 alloc.fmt.format,
 BootLevelKeyCache.get_hkdf_key,
 keystore2_crypto.zvec.ZVec,
 log.__private_api.loc,
 log.__private_api.log,
 Tuple.Insts.Log__private_apiSealedKVs.into_kvs,
 VecDeque,
 core.fmt.Arguments.from_str_nonconst,
 core.panic.location.Location,
 VecDeque.is_empty,
 VecDeque.len,
 VecDeque.split_off,
 anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
 log.Level.Insts.CoreCmpPartialEqLevelFilter.eq,
 log.Level.Insts.CoreCmpPartialOrdLevelFilter.partial_cmp,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 core.result.Result.Insts.AnyhowContext.context,
 log.__private_api.GlobalLogger.Insts.LogLog.enabled,
 log.__private_api.GlobalLogger.Insts.LogLog.flush,
 log.__private_api.GlobalLogger.Insts.LogLog.log] -/
#guard_msgs (whitespace := lax) in
#print axioms BootLevelKeyCache_advance_boot_level_not_accessible

recall BootLevelKeyCache_advance_boot_level_not_accessible_ok (view : View)
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) (hlen : ZVecQueueLenLaw view)
    (s : BootLevelKeyCache) (L : BootLevel)
    (hacc : BootLevelKeyCache.level_accessible s L = ok false) :
    BootLevelKeyCache.advance_boot_level s L = ok (ROk (), s)

/-- info:
'Keystore2Verify.BootLevelKeys.BootLevelKeyCache_advance_boot_level_not_accessible_ok'
depends on axioms:
[propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 log.Metadata,
 log.Record,
 log.max_level,
 alloc.fmt.format,
 BootLevelKeyCache.get_hkdf_key,
 keystore2_crypto.zvec.ZVec,
 log.__private_api.loc,
 log.__private_api.log,
 Tuple.Insts.Log__private_apiSealedKVs.into_kvs,
 VecDeque,
 core.fmt.Arguments.from_str_nonconst,
 core.panic.location.Location,
 VecDeque.is_empty,
 VecDeque.len,
 VecDeque.split_off,
 anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
 log.Level.Insts.CoreCmpPartialEqLevelFilter.eq,
 log.Level.Insts.CoreCmpPartialOrdLevelFilter.partial_cmp,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 core.result.Result.Insts.AnyhowContext.context,
 log.__private_api.GlobalLogger.Insts.LogLog.enabled,
 log.__private_api.GlobalLogger.Insts.LogLog.flush,
 log.__private_api.GlobalLogger.Insts.LogLog.log] -/
#guard_msgs (whitespace := lax) in
#print axioms BootLevelKeyCache_advance_boot_level_not_accessible_ok

recall BootLevelKeyCache_advance_boot_level_below (view : View)
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) (hlen : ZVecQueueLenLaw view)
    (s : BootLevelKeyCache) (L : BootLevel) (hlt : L.val < s.current.val) :
    BootLevelKeyCache.advance_boot_level s L = ok (ROk (), s)

/-- info:
'Keystore2Verify.BootLevelKeys.BootLevelKeyCache_advance_boot_level_below' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 log.Metadata,
 log.Record,
 log.max_level,
 alloc.fmt.format,
 BootLevelKeyCache.get_hkdf_key,
 keystore2_crypto.zvec.ZVec,
 log.__private_api.loc,
 log.__private_api.log,
 Tuple.Insts.Log__private_apiSealedKVs.into_kvs,
 VecDeque,
 core.fmt.Arguments.from_str_nonconst,
 core.panic.location.Location,
 VecDeque.is_empty,
 VecDeque.len,
 VecDeque.split_off,
 anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
 log.Level.Insts.CoreCmpPartialEqLevelFilter.eq,
 log.Level.Insts.CoreCmpPartialOrdLevelFilter.partial_cmp,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 core.result.Result.Insts.AnyhowContext.context,
 log.__private_api.GlobalLogger.Insts.LogLog.enabled,
 log.__private_api.GlobalLogger.Insts.LogLog.flush,
 log.__private_api.GlobalLogger.Insts.LogLog.log] -/
#guard_msgs (whitespace := lax) in
#print axioms BootLevelKeyCache_advance_boot_level_below

recall BootLevelKeyCache_advance_boot_level_accessible_shape
    (s s1 s' : BootLevelKeyCache) (L : BootLevel)
    (r0 : core.result.Result (Option keystore2_crypto.zvec.ZVec) anyhow.Error)
    (r : core.result.Result Unit anyhow.Error)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (r0, s1))
    (h : BootLevelKeyCache.advance_boot_level s L = ok (r, s')) :
    (s' = s1 ∧ ∃ e, r = RErr e) ∨
      (r = ROk () ∧ s'.current = L)

/-- info:
'Keystore2Verify.BootLevelKeys.BootLevelKeyCache_advance_boot_level_accessible_shape'
depends on axioms:
[propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 log.Metadata,
 log.Record,
 log.max_level,
 alloc.fmt.format,
 BootLevelKeyCache.get_hkdf_key,
 keystore2_crypto.zvec.ZVec,
 log.__private_api.loc,
 log.__private_api.log,
 Tuple.Insts.Log__private_apiSealedKVs.into_kvs,
 VecDeque,
 core.fmt.Arguments.from_str_nonconst,
 core.panic.location.Location,
 VecDeque.is_empty,
 VecDeque.len,
 VecDeque.split_off,
 anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
 log.Level.Insts.CoreCmpPartialEqLevelFilter.eq,
 log.Level.Insts.CoreCmpPartialOrdLevelFilter.partial_cmp,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 core.result.Result.Insts.AnyhowContext.context,
 log.__private_api.GlobalLogger.Insts.LogLog.enabled,
 log.__private_api.GlobalLogger.Insts.LogLog.flush,
 log.__private_api.GlobalLogger.Insts.LogLog.log] -/
#guard_msgs (whitespace := lax) in
#print axioms BootLevelKeyCache_advance_boot_level_accessible_shape

recall BootLevelKeyCache_advance_boot_level_err (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (e : anyhow.Error)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (RErr e, s1)) :
    ∃ e', BootLevelKeyCache.advance_boot_level s L = ok (RErr e', s1) ∧
      root e' = root e

/-- info:
'Keystore2Verify.BootLevelKeys.BootLevelKeyCache_advance_boot_level_err' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 log.Metadata,
 log.Record,
 log.max_level,
 alloc.fmt.format,
 BootLevelKeyCache.get_hkdf_key,
 keystore2_crypto.zvec.ZVec,
 log.__private_api.loc,
 log.__private_api.log,
 Tuple.Insts.Log__private_apiSealedKVs.into_kvs,
 VecDeque,
 core.fmt.Arguments.from_str_nonconst,
 core.panic.location.Location,
 VecDeque.is_empty,
 VecDeque.len,
 VecDeque.split_off,
 anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
 log.Level.Insts.CoreCmpPartialEqLevelFilter.eq,
 log.Level.Insts.CoreCmpPartialOrdLevelFilter.partial_cmp,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 core.result.Result.Insts.AnyhowContext.context,
 log.__private_api.GlobalLogger.Insts.LogLog.enabled,
 log.__private_api.GlobalLogger.Insts.LogLog.flush,
 log.__private_api.GlobalLogger.Insts.LogLog.log] -/
#guard_msgs (whitespace := lax) in
#print axioms BootLevelKeyCache_advance_boot_level_err

recall BootLevelKeyCache_advance_boot_level_ok (view : View) (root : anyhow.Error → ErrRoot)
    (hsplit : ZVecQueueSplitOffLaw view)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (o : Option keystore2_crypto.zvec.ZVec)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk o, s1))
    (hle : s1.current.val ≤ L.val)
    (hlen : L.val - s1.current.val ≤ (view s1.cache).length) :
    ∃ s', BootLevelKeyCache.advance_boot_level s L = ok (ROk (), s') ∧
      s'.current = L ∧ view s'.cache = (view s1.cache).drop (L.val - s1.current.val)

/-- info: 'Keystore2Verify.BootLevelKeys.BootLevelKeyCache_advance_boot_level_ok' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 log.Metadata,
 log.Record,
 log.max_level,
 alloc.fmt.format,
 BootLevelKeyCache.get_hkdf_key,
 keystore2_crypto.zvec.ZVec,
 log.__private_api.loc,
 log.__private_api.log,
 Tuple.Insts.Log__private_apiSealedKVs.into_kvs,
 VecDeque,
 core.fmt.Arguments.from_str_nonconst,
 core.panic.location.Location,
 VecDeque.is_empty,
 VecDeque.len,
 VecDeque.split_off,
 anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
 log.Level.Insts.CoreCmpPartialEqLevelFilter.eq,
 log.Level.Insts.CoreCmpPartialOrdLevelFilter.partial_cmp,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 core.result.Result.Insts.AnyhowContext.context,
 log.__private_api.GlobalLogger.Insts.LogLog.enabled,
 log.__private_api.GlobalLogger.Insts.LogLog.flush,
 log.__private_api.GlobalLogger.Insts.LogLog.log] -/
#guard_msgs (whitespace := lax) in
#print axioms BootLevelKeyCache_advance_boot_level_ok

recall BootLevelKeyCache_advance_boot_level_ok_retained (view : View)
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
      (view s'.cache).head? = (view s1.cache)[L.val - s1.current.val]?

/-- info:
'Keystore2Verify.BootLevelKeys.BootLevelKeyCache_advance_boot_level_ok_retained' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 log.Metadata,
 log.Record,
 log.max_level,
 alloc.fmt.format,
 BootLevelKeyCache.get_hkdf_key,
 keystore2_crypto.zvec.ZVec,
 log.__private_api.loc,
 log.__private_api.log,
 Tuple.Insts.Log__private_apiSealedKVs.into_kvs,
 VecDeque,
 core.fmt.Arguments.from_str_nonconst,
 core.panic.location.Location,
 VecDeque.is_empty,
 VecDeque.len,
 VecDeque.split_off,
 anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
 log.Level.Insts.CoreCmpPartialEqLevelFilter.eq,
 log.Level.Insts.CoreCmpPartialOrdLevelFilter.partial_cmp,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 core.result.Result.Insts.AnyhowContext.context,
 log.__private_api.GlobalLogger.Insts.LogLog.enabled,
 log.__private_api.GlobalLogger.Insts.LogLog.flush,
 log.__private_api.GlobalLogger.Insts.LogLog.log] -/
#guard_msgs (whitespace := lax) in
#print axioms BootLevelKeyCache_advance_boot_level_ok_retained

recall BootLevelKeyCache_advance_boot_level_fail_get_hkdf_key
    (s : BootLevelKeyCache) (L : BootLevel) (x : Error)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = fail x) :
    BootLevelKeyCache.advance_boot_level s L = fail x

/-- info:
'Keystore2Verify.BootLevelKeys.BootLevelKeyCache_advance_boot_level_fail_get_hkdf_key'
depends on axioms:
[propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 log.Metadata,
 log.Record,
 log.max_level,
 alloc.fmt.format,
 BootLevelKeyCache.get_hkdf_key,
 keystore2_crypto.zvec.ZVec,
 log.__private_api.loc,
 log.__private_api.log,
 Tuple.Insts.Log__private_apiSealedKVs.into_kvs,
 VecDeque,
 core.fmt.Arguments.from_str_nonconst,
 core.panic.location.Location,
 VecDeque.is_empty,
 VecDeque.len,
 VecDeque.split_off,
 anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
 log.Level.Insts.CoreCmpPartialEqLevelFilter.eq,
 log.Level.Insts.CoreCmpPartialOrdLevelFilter.partial_cmp,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 core.result.Result.Insts.AnyhowContext.context,
 log.__private_api.GlobalLogger.Insts.LogLog.enabled,
 log.__private_api.GlobalLogger.Insts.LogLog.flush,
 log.__private_api.GlobalLogger.Insts.LogLog.log] -/
#guard_msgs (whitespace := lax) in
#print axioms BootLevelKeyCache_advance_boot_level_fail_get_hkdf_key

recall BootLevelKeyCache_advance_boot_level_fail_sub (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (o : Option keystore2_crypto.zvec.ZVec)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk o, s1))
    (hlt : L.val < s1.current.val) :
    BootLevelKeyCache.advance_boot_level s L = fail Error.integerOverflow

/-- info:
'Keystore2Verify.BootLevelKeys.BootLevelKeyCache_advance_boot_level_fail_sub' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 log.Metadata,
 log.Record,
 log.max_level,
 alloc.fmt.format,
 BootLevelKeyCache.get_hkdf_key,
 keystore2_crypto.zvec.ZVec,
 log.__private_api.loc,
 log.__private_api.log,
 Tuple.Insts.Log__private_apiSealedKVs.into_kvs,
 VecDeque,
 core.fmt.Arguments.from_str_nonconst,
 core.panic.location.Location,
 VecDeque.is_empty,
 VecDeque.len,
 VecDeque.split_off,
 anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
 log.Level.Insts.CoreCmpPartialEqLevelFilter.eq,
 log.Level.Insts.CoreCmpPartialOrdLevelFilter.partial_cmp,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 core.result.Result.Insts.AnyhowContext.context,
 log.__private_api.GlobalLogger.Insts.LogLog.enabled,
 log.__private_api.GlobalLogger.Insts.LogLog.flush,
 log.__private_api.GlobalLogger.Insts.LogLog.log] -/
#guard_msgs (whitespace := lax) in
#print axioms BootLevelKeyCache_advance_boot_level_fail_sub

recall BootLevelKeyCache_advance_boot_level_fail_split_off (view : View)
    (root : anyhow.Error → ErrRoot)
    (hsplit : ZVecQueueSplitOffLaw view)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (o : Option keystore2_crypto.zvec.ZVec)
    (hacc : BootLevelKeyCache.level_accessible s L = ok true)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk o, s1))
    (hle : s1.current.val ≤ L.val)
    (hover : (view s1.cache).length < L.val - s1.current.val) :
    BootLevelKeyCache.advance_boot_level s L = fail Error.panic

/-- info:
'Keystore2Verify.BootLevelKeys.BootLevelKeyCache_advance_boot_level_fail_split_off'
depends on axioms:
[propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 log.Metadata,
 log.Record,
 log.max_level,
 alloc.fmt.format,
 BootLevelKeyCache.get_hkdf_key,
 keystore2_crypto.zvec.ZVec,
 log.__private_api.loc,
 log.__private_api.log,
 Tuple.Insts.Log__private_apiSealedKVs.into_kvs,
 VecDeque,
 core.fmt.Arguments.from_str_nonconst,
 core.panic.location.Location,
 VecDeque.is_empty,
 VecDeque.len,
 VecDeque.split_off,
 anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
 log.Level.Insts.CoreCmpPartialEqLevelFilter.eq,
 log.Level.Insts.CoreCmpPartialOrdLevelFilter.partial_cmp,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 core.result.Result.Insts.AnyhowContext.context,
 log.__private_api.GlobalLogger.Insts.LogLog.enabled,
 log.__private_api.GlobalLogger.Insts.LogLog.flush,
 log.__private_api.GlobalLogger.Insts.LogLog.log] -/
#guard_msgs (whitespace := lax) in
#print axioms BootLevelKeyCache_advance_boot_level_fail_split_off

recall BootLevelKeyCache_finish_current (s s' : BootLevelKeyCache)
    (h : BootLevelKeyCache.finish s = ok s') : s'.current = s.current

/-- info: 'Keystore2Verify.BootLevelKeys.BootLevelKeyCache_finish_current' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound,
 keystore2_crypto.zvec.ZVec,
 VecDeque,
 VecDeque.clear] -/
#guard_msgs (whitespace := lax) in
#print axioms BootLevelKeyCache_finish_current

recall BootLevelKeyCache_finish_ok (view : View)
    (hclear : ZVecQueueClearLaw view) (s : BootLevelKeyCache) :
    ∃ s', BootLevelKeyCache.finish s = ok s' ∧ s'.current = s.current ∧ view s'.cache = []

/-- info: 'Keystore2Verify.BootLevelKeys.BootLevelKeyCache_finish_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 keystore2_crypto.zvec.ZVec,
 VecDeque,
 VecDeque.clear] -/
#guard_msgs (whitespace := lax) in
#print axioms BootLevelKeyCache_finish_ok

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
    (hhkdf : KeystoreCryptoHkdfExpandSpec) (hcc : ContextCryptoLaw root)
    (s s' : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info : Slice Std.U8)
    (z : keystore2_crypto.zvec.ZVec)
    (h : BootLevelKeyCache.expand_key s L n info = ok (ROk (some z), s')) :
    ∃ sl, zvecDeref z = ok sl ∧ sl.length = n.val

recall BootLevelKeyCache_expand_key_fail_get_hkdf_key
    (s : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info : Slice Std.U8) (x : Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = fail x) :
    BootLevelKeyCache.expand_key s L n info = fail x

recall BootLevelKeyCache_expand_key_fail_expand (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info sl : Slice Std.U8)
    (k : keystore2_crypto.zvec.ZVec) (x : Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk (some k), s1))
    (hderef : zvecDeref k = ok sl)
    (hexp : keystore2_crypto.hkdf_expand n sl info = fail x) :
    BootLevelKeyCache.expand_key s L n info = fail x

recall BootLevelKeyCache_expand_key_fail_deref (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (n : Std.Usize) (info : Slice Std.U8)
    (k : keystore2_crypto.zvec.ZVec) (x : Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk (some k), s1))
    (hderef : zvecDeref k = fail x) :
    BootLevelKeyCache.expand_key s L n info = fail x

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

recall BootLevelKeyCache_aes_key_fail_expand_key
    (s : BootLevelKeyCache) (L : BootLevel) (x : Error)
    (hexp : BootLevelKeyCache.expand_key s L keystore2_crypto.AES_256_KEY_LENGTH
      BootLevelKeyCache.HKDF_AES = fail x) :
    BootLevelKeyCache.aes_key s L = fail x

recall BootLevelKeyCache_aes_key_fail_get_hkdf_key
    (s : BootLevelKeyCache) (L : BootLevel) (x : Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = fail x) :
    BootLevelKeyCache.aes_key s L = fail x

recall BootLevelKeyCache_aes_key_fail_expand (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel) (sl : Slice Std.U8)
    (k : keystore2_crypto.zvec.ZVec) (x : Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk (some k), s1))
    (hderef : zvecDeref k = ok sl)
    (hexp : keystore2_crypto.hkdf_expand keystore2_crypto.AES_256_KEY_LENGTH sl
      BootLevelKeyCache.HKDF_AES = fail x) :
    BootLevelKeyCache.aes_key s L = fail x

recall BootLevelKeyCache_aes_key_fail_deref (root : anyhow.Error → ErrRoot)
    (hctx : ContextKeyLaw root) (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (s s1 : BootLevelKeyCache) (L : BootLevel)
    (k : keystore2_crypto.zvec.ZVec) (x : Error)
    (hget : BootLevelKeyCache.get_hkdf_key s L = ok (ROk (some k), s1))
    (hderef : zvecDeref k = fail x) :
    BootLevelKeyCache.aes_key s L = fail x

end Keystore2Verify.BootLevelKeys
