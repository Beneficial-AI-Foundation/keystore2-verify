import Keystore2Verify.Proofs.MetricsStore.Default
import Keystore2Verify.Proofs.MetricsStore.GetAtoms
import Keystore2Verify.Proofs.MetricsStore.InsertAtom
import Keystore2Verify.Proofs.MetricsStore.ProcessSecurityLevel
import Keystore2Verify.Proofs.MetricsStore.ComputePaddingModeBitmap
import Keystore2Verify.Proofs.MetricsStore.ComputeDigestBitmap
import Keystore2Verify.Proofs.MetricsStore.ComputeBlockModeBitmap
import Keystore2Verify.Proofs.MetricsStore.ComputePurposeBitmap
import Keystore2Verify.Proofs.MetricsStore.RoundLogarithmic
import Keystore2Verify.Proofs.MetricsStore.RoundLatency
import Keystore2Verify.Proofs.MetricsStore.UpdateKeystoreCrashSysprop

namespace Keystore2Verify.MetricsStore
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

section Default
open android_security_metrics.aidl.android.security.metrics
open std.sync.poison.mutex
open std.sync.poison.mutex.Mutex.Insts.CoreDefaultDefault renaming default → mutexDefault
open std.collections.hash.map.HashMapKVSGlobal.Insts renaming CoreDefaultDefault → hashMapDefault
open std.hash.random.RandomState.Insts renaming CoreDefaultDefault → randomStateDefault
open metrics_store.MetricsStore.Insts.CoreDefaultDefault renaming default → metricsStoreDefault

recall MetricsStore_default_ok (m : Mutex AtomStore)
    (hm : mutexDefault (hashMapDefault AtomID.AtomID AtomMap randomStateDefault) = ok m) :
    metricsStoreDefault = ok { metrics_store := m }

end Default

section GetAtoms
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open android_security_metrics.aidl.android.security.metrics
open std.collections.hash.map
open std.sync.poison std.sync.poison.mutex
open MutexGuard.Insts.CoreOpsDerefDeref renaming deref → guardDeref
open KeystoreAtom.KeystoreAtom.Insts.CoreDefaultDefault renaming default → atomDefault
open std.hash.random.RandomState.Insts renaming
  CoreHashBuildHasherDefaultHasher → buildHasher
open AtomID.AtomID.Insts renaming CoreCmpEq → atomIdEq, CoreHashHash → atomIdHash

recall MetricsStore_get_atoms_storage_stats_ok
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id = 10103#i32)
    (hw : ∃ w, watchdog_helper.watchdog.watch
      (toStr "MetricsStore::get_atoms calling pull_storage_stats") = ok w)
    (v : alloc.vec.Vec Atom)
    (hpull : metrics_store.pull_storage_stats = ok (ROk v)) :
    metrics_store.MetricsStore.get_atoms self atom_id = ok (ROk v)

recall MetricsStore_get_atoms_storage_stats_err (root : anyhow.Error → ErrRoot)
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id = 10103#i32)
    (hw : ∃ w, watchdog_helper.watchdog.watch
      (toStr "MetricsStore::get_atoms calling pull_storage_stats") = ok w)
    (r : anyhow.Error)
    (hpull : metrics_store.pull_storage_stats = ok (RErr r)) :
    ∃ e, metrics_store.MetricsStore.get_atoms self atom_id = ok (RErr e) ∧
      root e = root r

recall MetricsStore_get_atoms_storage_stats_fail
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id = 10103#i32)
    (hw : ∃ w, watchdog_helper.watchdog.watch
      (toStr "MetricsStore::get_atoms calling pull_storage_stats") = ok w)
    (x : Error)
    (hpull : metrics_store.pull_storage_stats = fail x) :
    metrics_store.MetricsStore.get_atoms self atom_id = fail x

recall MetricsStore_get_atoms_keys_per_uid_ok
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id = 10248#i32)
    (hw : ∃ w, watchdog_helper.watchdog.watch
      (toStr "MetricsStore::get_atoms calling pull_keys_per_uid") = ok w)
    (v : alloc.vec.Vec Atom)
    (hpull : metrics_store.pull_keys_per_uid = ok (ROk v)) :
    metrics_store.MetricsStore.get_atoms self atom_id = ok (ROk v)

recall MetricsStore_get_atoms_keys_per_uid_err (root : anyhow.Error → ErrRoot)
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id = 10248#i32)
    (hw : ∃ w, watchdog_helper.watchdog.watch
      (toStr "MetricsStore::get_atoms calling pull_keys_per_uid") = ok w)
    (r : anyhow.Error)
    (hpull : metrics_store.pull_keys_per_uid = ok (RErr r)) :
    ∃ e, metrics_store.MetricsStore.get_atoms self atom_id = ok (RErr e) ∧
      root e = root r

recall MetricsStore_get_atoms_keys_per_uid_fail
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id = 10248#i32)
    (hw : ∃ w, watchdog_helper.watchdog.watch
      (toStr "MetricsStore::get_atoms calling pull_keys_per_uid") = ok w)
    (x : Error)
    (hpull : metrics_store.pull_keys_per_uid = fail x) :
    metrics_store.MetricsStore.get_atoms self atom_id = fail x

recall MetricsStore_get_atoms_crash_stats_some
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (count : Std.I32) (ka : Atom) (h : atom_id = 10125#i32)
    (hw : ∃ w, watchdog_helper.watchdog.watch
      (toStr "MetricsStore::get_atoms calling read_keystore_crash_count") = ok w)
    (hrd : metrics_store.read_keystore_crash_count = ok (ROk (some count)))
    (hka : atomDefault = ok ka) :
    ∃ v, metrics_store.MetricsStore.get_atoms self atom_id = ok (ROk v) ∧
      v.val = [{ ka with payload := (KeystoreAtomPayload.KeystoreAtomPayload.CrashStats
        ({ count_of_crash_events := count } : CrashStats.CrashStats)) }]

recall MetricsStore_get_atoms_crash_stats_none (root : anyhow.Error → ErrRoot)
    (hfe : AnyhowFormatErrSpec root) (hmu : AnyhowMustUseSpec root)
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id = 10125#i32)
    (hw : ∃ w, watchdog_helper.watchdog.watch
      (toStr "MetricsStore::get_atoms calling read_keystore_crash_count") = ok w)
    (hrd : metrics_store.read_keystore_crash_count = ok (ROk none)) :
    ∃ e, metrics_store.MetricsStore.get_atoms self atom_id = ok (RErr e) ∧
      root e = ErrRoot.other

recall MetricsStore_get_atoms_crash_stats_err (root : anyhow.Error → ErrRoot)
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (r : anyhow.Error) (h : atom_id = 10125#i32)
    (hw : ∃ w, watchdog_helper.watchdog.watch
      (toStr "MetricsStore::get_atoms calling read_keystore_crash_count") = ok w)
    (hrd : metrics_store.read_keystore_crash_count = ok (RErr r)) :
    ∃ e, metrics_store.MetricsStore.get_atoms self atom_id = ok (RErr e) ∧
      root e = root r

recall MetricsStore_get_atoms_poisoned
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id.val ∈ storedAtomIds)
    (p : PoisonError (MutexGuard AtomStore))
    (hlock : Mutex.lock self.metrics_store = ok (RErr p)) :
    metrics_store.MetricsStore.get_atoms self atom_id = fail Error.panic

recall MetricsStore_get_atoms_absent
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id.val ∈ storedAtomIds) (g : MutexGuard AtomStore) (hm : AtomStore)
    (hlock : Mutex.lock self.metrics_store = ok (ROk g))
    (hd : guardDeref g = ok hm)
    (hget : getAtom hm atom_id = ok none) (hmo : OptionMapOrSpec) :
    ∃ v, metrics_store.MetricsStore.get_atoms self atom_id = ok (ROk v) ∧ v.val = []

recall MetricsStore_get_atoms_present
    (entries : AtomMap → List (AtomPayload × Std.I32))
    (seqOf : AtomIter → List (AtomPayload × Std.I32))
    (hit : HashMapIterSpec entries seqOf) (hmap : IteratorMapSpec) (hnext : MapNextSpec seqOf)
    (hcl : AtomPayloadCloneSpec) (hmo : OptionMapOrSpec)
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id.val ∈ storedAtomIds) (g : MutexGuard AtomStore) (hm : AtomStore)
    (inner : AtomMap)
    (hlock : Mutex.lock self.metrics_store = ok (ROk g))
    (hd : guardDeref g = ok hm)
    (hget : getAtom hm atom_id = ok (some inner))
    (hlen : (entries inner).length ≤ Std.Usize.max) :
    ∃ v, metrics_store.MetricsStore.get_atoms self atom_id = ok (ROk v) ∧
      v.val = (entries inner).map (fun pc => ({ payload := pc.1, count := pc.2 } : Atom))

recall MetricsStore_get_atoms_unrecognized (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hmsg : AnyhowErrorMsgStringSpec root)
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id.val ∉ computedAtomIds ++ storedAtomIds) :
    ∃ e, metrics_store.MetricsStore.get_atoms self atom_id = ok (RErr e) ∧
      root e = ErrRoot.other

end GetAtoms

section InsertAtom
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open android_security_metrics.aidl.android.security.metrics
open std.collections.hash.map
open std.sync.poison std.sync.poison.mutex
open MutexGuard.Insts.CoreOpsDerefDerefMut renaming deref_mut → guardDerefMut
open std.hash.random.RandomState.Insts renaming
  CoreHashBuildHasherDefaultHasher → buildHasher, CoreDefaultDefault → randomStateDefault
open EntryAKVGlobal renaming or_default → entryOrDefault
open HashMapKVSGlobal.Insts renaming CoreDefaultDefault → hashMapDefault
open AtomID.AtomID.Insts renaming CoreCmpEq → atomIdEq, CoreHashHash → atomIdHash
open KeystoreAtomPayload.KeystoreAtomPayload.Insts renaming
  CoreCmpEq → payloadEq, CoreHashHash → payloadHash

recall insert_atom_poisoned
    (self : metrics_store.MetricsStore) (atom_id : Std.I32) (atom : AtomPayload)
    (p : PoisonError (MutexGuard AtomStore))
    (hlock : Mutex.lock self.metrics_store = ok (RErr p)) :
    metrics_store.MetricsStore.insert_atom self atom_id atom = fail Error.panic

recall insert_atom_count_ok
    (self : metrics_store.MetricsStore) (atom_id : Std.I32) (atom : AtomPayload)
    (g : MutexGuard AtomStore) (hm : AtomStore) (dmb : AtomStore → MutexGuard AtomStore)
    (e : Entry Std.I32 AtomMap alloc.alloc.Global)
    (eb : Entry Std.I32 AtomMap alloc.alloc.Global → AtomStore)
    (m : AtomMap) (odb : AtomMap → Entry Std.I32 AtomMap alloc.alloc.Global) (i : Std.Usize)
    (hlock : Mutex.lock self.metrics_store = ok (ROk g))
    (hdm : guardDerefMut g = ok (hm, dmb))
    (hent : HashMap.entry atomIdEq atomIdHash buildHasher hm atom_id = ok (e, eb))
    (hod : entryOrDefault (hashMapDefault AtomPayload Std.I32 randomStateDefault) e = ok (m, odb))
    (hlen : HashMap.len m = ok i)
    (e1 : Entry AtomPayload Std.I32 alloc.alloc.Global)
    (e1b : Entry AtomPayload Std.I32 alloc.alloc.Global → AtomMap)
    (c : Std.I32) (cb : Std.I32 → Entry AtomPayload Std.I32 alloc.alloc.Global)
    (hi : i.val < 250)
    (hent2 : HashMap.entry payloadEq payloadHash buildHasher m atom = ok (e1, e1b))
    (hins : Entry.or_insert e1 0#i32 = ok (c, cb))
    (hc : c.val < 2 ^ 31 - 1) :
    metrics_store.MetricsStore.insert_atom self atom_id atom = ok ()

recall insert_atom_count_overflow
    (self : metrics_store.MetricsStore) (atom_id : Std.I32) (atom : AtomPayload)
    (g : MutexGuard AtomStore) (hm : AtomStore) (dmb : AtomStore → MutexGuard AtomStore)
    (e : Entry Std.I32 AtomMap alloc.alloc.Global)
    (eb : Entry Std.I32 AtomMap alloc.alloc.Global → AtomStore)
    (m : AtomMap) (odb : AtomMap → Entry Std.I32 AtomMap alloc.alloc.Global) (i : Std.Usize)
    (hlock : Mutex.lock self.metrics_store = ok (ROk g))
    (hdm : guardDerefMut g = ok (hm, dmb))
    (hent : HashMap.entry atomIdEq atomIdHash buildHasher hm atom_id = ok (e, eb))
    (hod : entryOrDefault (hashMapDefault AtomPayload Std.I32 randomStateDefault) e = ok (m, odb))
    (hlen : HashMap.len m = ok i)
    (e1 : Entry AtomPayload Std.I32 alloc.alloc.Global)
    (e1b : Entry AtomPayload Std.I32 alloc.alloc.Global → AtomMap)
    (c : Std.I32) (cb : Std.I32 → Entry AtomPayload Std.I32 alloc.alloc.Global)
    (hi : i.val < 250)
    (hent2 : HashMap.entry payloadEq payloadHash buildHasher m atom = ok (e1, e1b))
    (hins : Entry.or_insert e1 0#i32 = ok (c, cb))
    (hc : c.val = 2 ^ 31 - 1) :
    metrics_store.MetricsStore.insert_atom self atom_id atom = fail Error.integerOverflow

recall insert_atom_overflow_ok
    (self : metrics_store.MetricsStore) (atom_id : Std.I32) (atom : AtomPayload)
    (g : MutexGuard AtomStore) (hm : AtomStore) (dmb : AtomStore → MutexGuard AtomStore)
    (e : Entry Std.I32 AtomMap alloc.alloc.Global)
    (eb : Entry Std.I32 AtomMap alloc.alloc.Global → AtomStore)
    (m : AtomMap) (odb : AtomMap → Entry Std.I32 AtomMap alloc.alloc.Global) (i : Std.Usize)
    (hlock : Mutex.lock self.metrics_store = ok (ROk g))
    (hdm : guardDerefMut g = ok (hm, dmb))
    (hent : HashMap.entry atomIdEq atomIdHash buildHasher hm atom_id = ok (e, eb))
    (hod : entryOrDefault (hashMapDefault AtomPayload Std.I32 randomStateDefault) e = ok (m, odb))
    (hlen : HashMap.len m = ok i)
    (hi : 250 ≤ i.val)
    (hm2 : AtomStore) (dmb2 : AtomStore → MutexGuard AtomStore) (ai : Std.I32)
    (e2 : Entry Std.I32 AtomMap alloc.alloc.Global)
    (eb2 : Entry Std.I32 AtomMap alloc.alloc.Global → AtomStore)
    (m2 : AtomMap) (odb2 : AtomMap → Entry Std.I32 AtomMap alloc.alloc.Global)
    (i1 : Std.Usize)
    (hdm2 : guardDerefMut (dmb (eb (odb m))) = ok (hm2, dmb2))
    (hai : AtomID.AtomID.KEYSTORE2_ATOM_WITH_OVERFLOW = ok ai)
    (he2 : HashMap.entry atomIdEq atomIdHash buildHasher hm2 ai = ok (e2, eb2))
    (hod2 : entryOrDefault (hashMapDefault AtomPayload Std.I32 randomStateDefault) e2 =
      ok (m2, odb2))
    (hlen2 : HashMap.len m2 = ok i1)
    (hi1 : i1.val < 250)
    (e3 : Entry AtomPayload Std.I32 alloc.alloc.Global)
    (e3b : Entry AtomPayload Std.I32 alloc.alloc.Global → AtomMap)
    (c : Std.I32) (cb : Std.I32 → Entry AtomPayload Std.I32 alloc.alloc.Global)
    (hent3 : HashMap.entry payloadEq payloadHash buildHasher m2
      (KeystoreAtomPayload.KeystoreAtomPayload.Keystore2AtomWithOverflow { atom_id := atom_id }) =
        ok (e3, e3b))
    (hins : Entry.or_insert e3 0#i32 = ok (c, cb))
    (hc : c.val < 2 ^ 31 - 1) :
    metrics_store.MetricsStore.insert_atom self atom_id atom = ok ()

recall insert_atom_overflow_count_overflow
    (self : metrics_store.MetricsStore) (atom_id : Std.I32) (atom : AtomPayload)
    (g : MutexGuard AtomStore) (hm : AtomStore) (dmb : AtomStore → MutexGuard AtomStore)
    (e : Entry Std.I32 AtomMap alloc.alloc.Global)
    (eb : Entry Std.I32 AtomMap alloc.alloc.Global → AtomStore)
    (m : AtomMap) (odb : AtomMap → Entry Std.I32 AtomMap alloc.alloc.Global) (i : Std.Usize)
    (hlock : Mutex.lock self.metrics_store = ok (ROk g))
    (hdm : guardDerefMut g = ok (hm, dmb))
    (hent : HashMap.entry atomIdEq atomIdHash buildHasher hm atom_id = ok (e, eb))
    (hod : entryOrDefault (hashMapDefault AtomPayload Std.I32 randomStateDefault) e = ok (m, odb))
    (hlen : HashMap.len m = ok i)
    (hi : 250 ≤ i.val)
    (hm2 : AtomStore) (dmb2 : AtomStore → MutexGuard AtomStore) (ai : Std.I32)
    (e2 : Entry Std.I32 AtomMap alloc.alloc.Global)
    (eb2 : Entry Std.I32 AtomMap alloc.alloc.Global → AtomStore)
    (m2 : AtomMap) (odb2 : AtomMap → Entry Std.I32 AtomMap alloc.alloc.Global)
    (i1 : Std.Usize)
    (hdm2 : guardDerefMut (dmb (eb (odb m))) = ok (hm2, dmb2))
    (hai : AtomID.AtomID.KEYSTORE2_ATOM_WITH_OVERFLOW = ok ai)
    (he2 : HashMap.entry atomIdEq atomIdHash buildHasher hm2 ai = ok (e2, eb2))
    (hod2 : entryOrDefault (hashMapDefault AtomPayload Std.I32 randomStateDefault) e2 =
      ok (m2, odb2))
    (hlen2 : HashMap.len m2 = ok i1)
    (hi1 : i1.val < 250)
    (e3 : Entry AtomPayload Std.I32 alloc.alloc.Global)
    (e3b : Entry AtomPayload Std.I32 alloc.alloc.Global → AtomMap)
    (c : Std.I32) (cb : Std.I32 → Entry AtomPayload Std.I32 alloc.alloc.Global)
    (hent3 : HashMap.entry payloadEq payloadHash buildHasher m2
      (KeystoreAtomPayload.KeystoreAtomPayload.Keystore2AtomWithOverflow { atom_id := atom_id }) =
        ok (e3, e3b))
    (hins : Entry.or_insert e3 0#i32 = ok (c, cb))
    (hc : c.val = 2 ^ 31 - 1) :
    metrics_store.MetricsStore.insert_atom self atom_id atom = fail Error.integerOverflow

recall insert_atom_full
    (self : metrics_store.MetricsStore) (atom_id : Std.I32) (atom : AtomPayload)
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec)
    (g : MutexGuard AtomStore) (hm : AtomStore) (dmb : AtomStore → MutexGuard AtomStore)
    (e : Entry Std.I32 AtomMap alloc.alloc.Global)
    (eb : Entry Std.I32 AtomMap alloc.alloc.Global → AtomStore)
    (m : AtomMap) (odb : AtomMap → Entry Std.I32 AtomMap alloc.alloc.Global) (i : Std.Usize)
    (hlock : Mutex.lock self.metrics_store = ok (ROk g))
    (hdm : guardDerefMut g = ok (hm, dmb))
    (hent : HashMap.entry atomIdEq atomIdHash buildHasher hm atom_id = ok (e, eb))
    (hod : entryOrDefault (hashMapDefault AtomPayload Std.I32 randomStateDefault) e = ok (m, odb))
    (hlen : HashMap.len m = ok i)
    (hi : 250 ≤ i.val)
    (hm2 : AtomStore) (dmb2 : AtomStore → MutexGuard AtomStore) (ai : Std.I32)
    (e2 : Entry Std.I32 AtomMap alloc.alloc.Global)
    (eb2 : Entry Std.I32 AtomMap alloc.alloc.Global → AtomStore)
    (m2 : AtomMap) (odb2 : AtomMap → Entry Std.I32 AtomMap alloc.alloc.Global)
    (i1 : Std.Usize)
    (hdm2 : guardDerefMut (dmb (eb (odb m))) = ok (hm2, dmb2))
    (hai : AtomID.AtomID.KEYSTORE2_ATOM_WITH_OVERFLOW = ok ai)
    (he2 : HashMap.entry atomIdEq atomIdHash buildHasher hm2 ai = ok (e2, eb2))
    (hod2 : entryOrDefault (hashMapDefault AtomPayload Std.I32 randomStateDefault) e2 =
      ok (m2, odb2))
    (hlen2 : HashMap.len m2 = ok i1)
    (hi1 : 250 ≤ i1.val) :
    metrics_store.MetricsStore.insert_atom self atom_id atom = ok ()

end InsertAtom

section ProcessSecurityLevel
open android_security_metrics.aidl.android.security.metrics.SecurityLevel.SecurityLevel

recall process_security_level_cases (sec_level : Std.I32) :
    metrics_store.process_security_level sec_level =
      if sec_level.val = 0 then SECURITY_LEVEL_SOFTWARE
      else if sec_level.val = 1 then SECURITY_LEVEL_TRUSTED_ENVIRONMENT
      else if sec_level.val = 2 then SECURITY_LEVEL_STRONGBOX
      else if sec_level.val = 100 then SECURITY_LEVEL_KEYSTORE
      else SECURITY_LEVEL_UNSPECIFIED

end ProcessSecurityLevel

section ComputePaddingModeBitmap


recall compute_padding_mode_bitmap_set (bitmap padding_mode : Std.I32) (k : Nat)
    (hk : paddingBitPos padding_mode.val = some k) :
    ∃ r, metrics_store.compute_padding_mode_bitmap bitmap padding_mode = ok r ∧
      r.bv = bitmap.bv ||| (1#32 <<< k)

recall compute_padding_mode_bitmap_other (bitmap padding_mode : Std.I32)
    (hk : paddingBitPos padding_mode.val = none) :
    metrics_store.compute_padding_mode_bitmap bitmap padding_mode = ok bitmap

end ComputePaddingModeBitmap

section ComputeDigestBitmap


recall compute_digest_bitmap_set (bitmap digest : Std.I32) (k : Nat)
    (hk : digestBitPos digest.val = some k) :
    ∃ r, metrics_store.compute_digest_bitmap bitmap digest = ok r ∧
      r.bv = bitmap.bv ||| (1#32 <<< k)

recall compute_digest_bitmap_other (bitmap digest : Std.I32)
    (hk : digestBitPos digest.val = none) :
    metrics_store.compute_digest_bitmap bitmap digest = ok bitmap

end ComputeDigestBitmap

section ComputeBlockModeBitmap


recall compute_block_mode_bitmap_set (bitmap block_mode : Std.I32) (k : Nat)
    (hk : blockModeBitPos block_mode.val = some k) :
    ∃ r, metrics_store.compute_block_mode_bitmap bitmap block_mode = ok r ∧
      r.bv = bitmap.bv ||| (1#32 <<< k)

recall compute_block_mode_bitmap_other (bitmap block_mode : Std.I32)
    (hk : blockModeBitPos block_mode.val = none) :
    metrics_store.compute_block_mode_bitmap bitmap block_mode = ok bitmap

end ComputeBlockModeBitmap

section ComputePurposeBitmap


recall compute_purpose_bitmap_set (bitmap purpose : Std.I32) (k : Nat)
    (hk : purposeBitPos purpose.val = some k) :
    ∃ r, metrics_store.compute_purpose_bitmap bitmap purpose = ok r ∧
      r.bv = bitmap.bv ||| (1#32 <<< k)

recall compute_purpose_bitmap_other (bitmap purpose : Std.I32)
    (hk : purposeBitPos purpose.val = none) :
    metrics_store.compute_purpose_bitmap bitmap purpose = ok bitmap

end ComputePurposeBitmap

section RoundLogarithmic


recall round_logarithmic_below (val : Std.U64) (buckets_per_decade : Std.U32)
    (min_step no_round_threshold : Std.U64) (h : val.val ≤ no_round_threshold.val) :
    ∃ r, metrics_store.round_logarithmic val buckets_per_decade min_step no_round_threshold =
        ok r ∧
      r.val = if val.val ≤ 2 ^ 63 - 1 then (val.val : Int) else (val.val : Int) - 2 ^ 64

recall round_logarithmic_rounded (hil : U64Ilog10Spec) (hpow : U64PowSpec)
    (val : Std.U64) (buckets_per_decade : Std.U32) (min_step no_round_threshold : Std.U64)
    (hgt : no_round_threshold.val < val.val) (hval : val.val < 10 ^ 19)
    (hb : 0 < buckets_per_decade.val)
    (hstep : 0 < roundLogStep val.val buckets_per_decade.val min_step.val)
    (hsum : val.val + roundLogStep val.val buckets_per_decade.val min_step.val / 2 < 2 ^ 64) :
    ∃ r, metrics_store.round_logarithmic val buckets_per_decade min_step no_round_threshold =
        ok r ∧
      r.val = (min (roundLogRounded val.val buckets_per_decade.val min_step.val)
        (2 ^ 63 - 1) : Nat)

recall round_logarithmic_zero_buckets (hil : U64Ilog10Spec) (hpow : U64PowSpec)
    (val : Std.U64) (buckets_per_decade : Std.U32) (min_step no_round_threshold : Std.U64)
    (hgt : no_round_threshold.val < val.val) (hval : val.val < 10 ^ 19)
    (hb : buckets_per_decade.val = 0) :
    metrics_store.round_logarithmic val buckets_per_decade min_step no_round_threshold =
      fail Error.divisionByZero

recall round_logarithmic_zero_step (hil : U64Ilog10Spec) (hpow : U64PowSpec)
    (val : Std.U64) (buckets_per_decade : Std.U32) (min_step no_round_threshold : Std.U64)
    (hgt : no_round_threshold.val < val.val) (hval : val.val < 10 ^ 19)
    (hb : 0 < buckets_per_decade.val)
    (hstep : roundLogStep val.val buckets_per_decade.val min_step.val = 0) :
    metrics_store.round_logarithmic val buckets_per_decade min_step no_round_threshold =
      fail Error.divisionByZero

recall round_logarithmic_sum_overflow (hil : U64Ilog10Spec) (hpow : U64PowSpec)
    (val : Std.U64) (buckets_per_decade : Std.U32) (min_step no_round_threshold : Std.U64)
    (hgt : no_round_threshold.val < val.val) (hval : val.val < 10 ^ 19)
    (hb : 0 < buckets_per_decade.val)
    (hstep : 0 < roundLogStep val.val buckets_per_decade.val min_step.val)
    (hsum : 2 ^ 64 ≤ val.val + roundLogStep val.val buckets_per_decade.val min_step.val / 2) :
    metrics_store.round_logarithmic val buckets_per_decade min_step no_round_threshold =
      fail Error.integerOverflow

recall round_logarithmic_pow_overflow (hil : U64Ilog10Spec) (hpow : U64PowSpec)
    (val : Std.U64) (buckets_per_decade : Std.U32) (min_step no_round_threshold : Std.U64)
    (hgt : no_round_threshold.val < val.val) (hval : 10 ^ 19 ≤ val.val) :
    ∃ x, metrics_store.round_logarithmic val buckets_per_decade min_step no_round_threshold =
      fail x

end RoundLogarithmic

section RoundLatency


recall round_latency_value (millis : core.time.Duration → Nat)
    (hms : DurationAsMillisSpec millis) (hil : U32Ilog10Spec) (hpow : U32PowSpec)
    (latency : core.time.Duration) :
    ∃ r, metrics_store.round_latency latency = ok r ∧
      r.val = (roundLatencyNat (millis latency) : Int)

end RoundLatency

section UpdateKeystoreCrashSysprop
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open alloc.string.ToString.Blanket renaming to_string → toStringBlanket
open alloc.string.String.Insts.CoreOpsDerefDerefStr renaming deref → stringDeref
open rustutils.android.system_properties renaming
  write → writeProperty, PropertyWatcherError → PropWatchErr

recall update_keystore_crash_sysprop_written (o : Option Std.I32) (n : Std.I32)
    (s : String) (s1 : Str)
    (hrd : metrics_store.read_keystore_crash_count = ok (ROk o))
    (hn : crashCountNext o = ok n)
    (hs : toStringBlanket I32.Insts.CoreFmtDisplay n = ok s)
    (hd : stringDeref s = ok s1)
    (hw : writeProperty metrics_store.KEYSTORE_CRASH_COUNT_PROPERTY s1 = ok (ROk ())) :
    metrics_store.update_keystore_crash_sysprop = ok ()

recall update_keystore_crash_sysprop_write_failed
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec)
    (o : Option Std.I32) (n : Std.I32) (s : String) (s1 : Str)
    (e : PropWatchErr)
    (hrd : metrics_store.read_keystore_crash_count = ok (ROk o))
    (hn : crashCountNext o = ok n)
    (hs : toStringBlanket I32.Insts.CoreFmtDisplay n = ok s)
    (hd : stringDeref s = ok s1)
    (hw : writeProperty metrics_store.KEYSTORE_CRASH_COUNT_PROPERTY s1 =
      ok (RErr e : core.result.Result Unit PropWatchErr)) :
    metrics_store.update_keystore_crash_sysprop = ok ()

recall update_keystore_crash_sysprop_read_failed
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) (e : anyhow.Error)
    (hrd : metrics_store.read_keystore_crash_count = ok (RErr e)) :
    metrics_store.update_keystore_crash_sysprop = ok ()

recall update_keystore_crash_sysprop_overflow (c : Std.I32) (hc : c.val = 2 ^ 31 - 1)
    (hrd : metrics_store.read_keystore_crash_count = ok (ROk (some c))) :
    metrics_store.update_keystore_crash_sysprop = fail Error.integerOverflow

end UpdateKeystoreCrashSysprop

end Keystore2Verify.MetricsStore
