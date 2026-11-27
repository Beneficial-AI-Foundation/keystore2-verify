import Keystore2Verify.Specs.Defs.MetricsStore

namespace Keystore2Verify.MetricsStore
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open android_security_metrics.aidl.android.security.metrics
open std.collections.hash.map
open std.sync.poison std.sync.poison.mutex
open MutexGuard.Insts.CoreOpsDerefDeref renaming deref → guardDeref
open KeystoreAtom.KeystoreAtom.Insts.CoreDefaultDefault renaming default → atomDefault
open std.hash.random.RandomState.Insts renaming
  CoreHashBuildHasherDefaultHasher → buildHasher
open AtomID.AtomID.Insts renaming CoreCmpEq → atomIdEq, CoreHashHash → atomIdHash

/-! `get_atoms` computes three atoms when it is called (storage stats, keys per uid, crash stats)
and reads eleven from the stored map. In the Rust source the watchdog guard is held to the end of
the arm; the translation drops it at once, which changes nothing here. -/

/-- conditional: for the atom number 10103 (`STORAGE_STATS`), if `pull_storage_stats` returns
the vector `v`, `get_atoms` returns `Ok v`. In the Rust source this path takes no lock.
Hypotheses: the outcome of the `watch` call, whose result is dropped, and the outcome of
`pull_storage_stats`. -/
theorem MetricsStore_get_atoms_storage_stats_ok
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id = 10103#i32)
    (hw : ∃ w, watchdog_helper.watchdog.watch
      (toStr "MetricsStore::get_atoms calling pull_storage_stats") = ok w)
    (v : alloc.vec.Vec Atom)
    (hpull : metrics_store.pull_storage_stats = ok (ROk v)) :
    metrics_store.MetricsStore.get_atoms self atom_id = ok (ROk v) := by
  sorry

/-- conditional: for the atom number 10103, if `pull_storage_stats` returns an error `r`,
`get_atoms` returns an error with the same root cause as `r`. Hypotheses: those of
`MetricsStore_get_atoms_storage_stats_ok`, with an error outcome of `pull_storage_stats`. -/
theorem MetricsStore_get_atoms_storage_stats_err (root : anyhow.Error → ErrRoot)
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id = 10103#i32)
    (hw : ∃ w, watchdog_helper.watchdog.watch
      (toStr "MetricsStore::get_atoms calling pull_storage_stats") = ok w)
    (r : anyhow.Error)
    (hpull : metrics_store.pull_storage_stats = ok (RErr r)) :
    ∃ e, metrics_store.MetricsStore.get_atoms self atom_id = ok (RErr e) ∧
      root e = root r := by
  sorry

/-- conditional: for the atom number 10103, if `pull_storage_stats` fails with `x`, `get_atoms`
fails with the same `x`. Hypotheses: those of `MetricsStore_get_atoms_storage_stats_ok`, with a
failing outcome of `pull_storage_stats`. -/
theorem MetricsStore_get_atoms_storage_stats_fail
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id = 10103#i32)
    (hw : ∃ w, watchdog_helper.watchdog.watch
      (toStr "MetricsStore::get_atoms calling pull_storage_stats") = ok w)
    (x : Error)
    (hpull : metrics_store.pull_storage_stats = fail x) :
    metrics_store.MetricsStore.get_atoms self atom_id = fail x := by
  sorry

/-- conditional: for the atom number 10248 (`KEYS_PER_UID`), if `pull_keys_per_uid` returns the
vector `v`, `get_atoms` returns `Ok v`. In the Rust source this path takes no lock. Hypotheses:
the outcome of the `watch` call, whose result is dropped, and the outcome of
`pull_keys_per_uid`. -/
theorem MetricsStore_get_atoms_keys_per_uid_ok
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id = 10248#i32)
    (hw : ∃ w, watchdog_helper.watchdog.watch
      (toStr "MetricsStore::get_atoms calling pull_keys_per_uid") = ok w)
    (v : alloc.vec.Vec Atom)
    (hpull : metrics_store.pull_keys_per_uid = ok (ROk v)) :
    metrics_store.MetricsStore.get_atoms self atom_id = ok (ROk v) := by
  sorry

/-- conditional: for the atom number 10248, if `pull_keys_per_uid` returns an error `r`, `get_atoms`
returns an error with the same root cause as `r`. Hypotheses: those of
`MetricsStore_get_atoms_keys_per_uid_ok`, with an error outcome of `pull_keys_per_uid`. -/
theorem MetricsStore_get_atoms_keys_per_uid_err (root : anyhow.Error → ErrRoot)
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id = 10248#i32)
    (hw : ∃ w, watchdog_helper.watchdog.watch
      (toStr "MetricsStore::get_atoms calling pull_keys_per_uid") = ok w)
    (r : anyhow.Error)
    (hpull : metrics_store.pull_keys_per_uid = ok (RErr r)) :
    ∃ e, metrics_store.MetricsStore.get_atoms self atom_id = ok (RErr e) ∧
      root e = root r := by
  sorry

/-- conditional: for the atom number 10248, if `pull_keys_per_uid` fails with `x`, `get_atoms`
fails with the same `x`. Hypotheses: those of `MetricsStore_get_atoms_keys_per_uid_ok`, with a
failing outcome of `pull_keys_per_uid`. -/
theorem MetricsStore_get_atoms_keys_per_uid_fail
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id = 10248#i32)
    (hw : ∃ w, watchdog_helper.watchdog.watch
      (toStr "MetricsStore::get_atoms calling pull_keys_per_uid") = ok w)
    (x : Error)
    (hpull : metrics_store.pull_keys_per_uid = fail x) :
    metrics_store.MetricsStore.get_atoms self atom_id = fail x := by
  sorry

/-- conditional: for the atom number 10125 (`CRASH_STATS`), if the read of the crash count
returns `Ok (some count)` and `KeystoreAtom::default()` returns `ka`, `get_atoms` returns a vector
with one atom: the default atom `ka` with its payload replaced by `CrashStats` holding `count`.
The `count` field of the atom stays that of `ka`. Hypotheses: the outcomes of `watch`, of the
read and of `default`. -/
theorem MetricsStore_get_atoms_crash_stats_some
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (count : Std.I32) (ka : Atom) (h : atom_id = 10125#i32)
    (hw : ∃ w, watchdog_helper.watchdog.watch
      (toStr "MetricsStore::get_atoms calling read_keystore_crash_count") = ok w)
    (hrd : metrics_store.read_keystore_crash_count = ok (ROk (some count)))
    (hka : atomDefault = ok ka) :
    ∃ v, metrics_store.MetricsStore.get_atoms self atom_id = ok (ROk v) ∧
      v.val = [{ ka with payload := (KeystoreAtomPayload.KeystoreAtomPayload.CrashStats
        ({ count_of_crash_events := count } : CrashStats.CrashStats)) }] := by
  sorry

/-- conditional: for the atom number 10125, if the read of the crash count returns `Ok none`,
`get_atoms` returns an error built from a message. Its root cause is not a keystore2 error
(`root e = ErrRoot.other`). Hypotheses: the outcomes of `watch` and of the read, and the
assumptions about `format_err` and `must_use`. -/
theorem MetricsStore_get_atoms_crash_stats_none (root : anyhow.Error → ErrRoot)
    (hfe : AnyhowFormatErrSpec root) (hmu : AnyhowMustUseSpec root)
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id = 10125#i32)
    (hw : ∃ w, watchdog_helper.watchdog.watch
      (toStr "MetricsStore::get_atoms calling read_keystore_crash_count") = ok w)
    (hrd : metrics_store.read_keystore_crash_count = ok (ROk none)) :
    ∃ e, metrics_store.MetricsStore.get_atoms self atom_id = ok (RErr e) ∧
      root e = ErrRoot.other := by
  sorry

/-- conditional: for the atom number 10125, if the read of the crash count returns the error `r`,
`get_atoms` returns an error with the same root cause as `r`, with no context added. Hypotheses:
the outcomes of `watch` and of the read. -/
theorem MetricsStore_get_atoms_crash_stats_err (root : anyhow.Error → ErrRoot)
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (r : anyhow.Error) (h : atom_id = 10125#i32)
    (hw : ∃ w, watchdog_helper.watchdog.watch
      (toStr "MetricsStore::get_atoms calling read_keystore_crash_count") = ok w)
    (hrd : metrics_store.read_keystore_crash_count = ok (RErr r)) :
    ∃ e, metrics_store.MetricsStore.get_atoms self atom_id = ok (RErr e) ∧
      root e = root r := by
  sorry

/-- conditional: for one of the eleven stored atom numbers (`storedAtomIds`), if `Mutex::lock`
returns a poison error, `get_atoms` fails with a panic (the `unwrap` of the lock result).
Hypothesis: the outcome of `lock`. -/
theorem MetricsStore_get_atoms_poisoned
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id.val ∈ storedAtomIds)
    (p : PoisonError (MutexGuard AtomStore))
    (hlock : Mutex.lock self.metrics_store = ok (RErr p)) :
    metrics_store.MetricsStore.get_atoms self atom_id = fail Error.panic := by
  sorry

/-- conditional: for one of the eleven stored atom numbers, if the store has no inner map for
`atom_id`, `get_atoms` returns the empty vector. Hypotheses: the outcomes of `lock`, of the
`deref` of the guard (the outer map `hm`), of `get` (no entry), and the assumption about
`Option::map_or`. -/
theorem MetricsStore_get_atoms_absent
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id.val ∈ storedAtomIds) (g : MutexGuard AtomStore) (hm : AtomStore)
    (hlock : Mutex.lock self.metrics_store = ok (ROk g))
    (hd : guardDeref g = ok hm)
    (hget : getAtom hm atom_id = ok none) (hmo : OptionMapOrSpec) :
    ∃ v, metrics_store.MetricsStore.get_atoms self atom_id = ok (ROk v) ∧ v.val = [] := by
  sorry

/-- conditional: for one of the eleven stored atom numbers, if the store has the inner map
`inner` for `atom_id`, `get_atoms` returns one atom for each pair `(payload, count)` of `inner`,
in the order of its iterator (`entries`): the payload, cloned, with the count of the pair. In
the Rust source this path only reads the store. Hypotheses: the outcomes of `lock`, `deref` and
`get`; the assumptions about `Option::map_or`, `HashMap::iter`, `Iterator::map`, `Map::next` and
the clone of a payload, for the views `entries` and `seqOf`; and that the vector length fits in
a `usize`. -/
theorem MetricsStore_get_atoms_present
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
      v.val = (entries inner).map (fun pc => ({ payload := pc.1, count := pc.2 } : Atom)) := by
  sorry

/-- conditional: for an atom number that is neither computed nor stored (`computedAtomIds`,
`storedAtomIds`), `get_atoms` returns an error built from a message, whose root cause is not a
keystore2 error (`root e = ErrRoot.other`). In the Rust source this path takes no lock. The text
of the message is not stated. Hypotheses: the assumptions about `format` and about
`Error::msg` for a `String`. -/
theorem MetricsStore_get_atoms_unrecognized (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hmsg : AnyhowErrorMsgStringSpec root)
    (self : metrics_store.MetricsStore) (atom_id : Std.I32)
    (h : atom_id.val ∉ computedAtomIds ++ storedAtomIds) :
    ∃ e, metrics_store.MetricsStore.get_atoms self atom_id = ok (RErr e) ∧
      root e = ErrRoot.other := by
  sorry

end Keystore2Verify.MetricsStore
