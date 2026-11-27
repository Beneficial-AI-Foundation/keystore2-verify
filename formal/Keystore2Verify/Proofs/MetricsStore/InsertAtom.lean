import Keystore2Verify.Specs.Defs.MetricsStore

namespace Keystore2Verify.MetricsStore
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
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

/-! `insert_atom` locks the store and counts `atom` under `atom_id`. The translation does not write
the modified map back: the function returns `()` and the `back` functions of the library calls are
dropped. So the statements say when `insert_atom` returns `()` and when it fails; they say nothing
about the counts that the store holds afterwards. Each theorem names the outcome of every call
that its path evaluates. In the Rust source the lock is taken first on every path. -/

/-- conditional: if `Mutex::lock` returns a poison error `p`, `insert_atom` fails with a panic (the
`unwrap` of the lock result). Hypothesis: the outcome of `lock`. -/
theorem insert_atom_poisoned
    (self : metrics_store.MetricsStore) (atom_id : Std.I32) (atom : AtomPayload)
    (p : PoisonError (MutexGuard AtomStore))
    (hlock : Mutex.lock self.metrics_store = ok (RErr p)) :
    metrics_store.MetricsStore.insert_atom self atom_id atom = fail Error.panic := by
  sorry

/-- conditional: if the inner map of `atom_id` has fewer than 250 entries (`i`) and the count `c`
that `or_insert` returns for `atom` is below `i32::MAX`, `insert_atom` returns `()`. Hypotheses:
the outcomes of `lock`, `deref_mut`, the two `entry` calls, `or_default`, `len` and `or_insert`. -/
theorem insert_atom_count_ok
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
    metrics_store.MetricsStore.insert_atom self atom_id atom = ok () := by
  sorry

/-- conditional: the same as `insert_atom_count_ok`, but the count `c` is `i32::MAX`: the
increment overflows and `insert_atom` fails with an integer overflow. -/
theorem insert_atom_count_overflow
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
    metrics_store.MetricsStore.insert_atom self atom_id atom = fail Error.integerOverflow := by
  sorry

/-- conditional: if the inner map of `atom_id` has 250 or more entries, the overflow map (the
inner map of `KEYSTORE2_ATOM_WITH_OVERFLOW`) has fewer than 250 (`i1`) and the count `c` that
`or_insert` returns for the overflow payload is below `i32::MAX`, `insert_atom` returns `()`. This
holds even if `atom` is already a key of the full map. Hypotheses: the outcomes of the calls on
this path, in the order of the Rust source. -/
theorem insert_atom_overflow_ok
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
    metrics_store.MetricsStore.insert_atom self atom_id atom = ok () := by
  sorry

/-- conditional: the same as `insert_atom_overflow_ok`, but the count `c` is `i32::MAX`: the
increment overflows and `insert_atom` fails with an integer overflow. -/
theorem insert_atom_overflow_count_overflow
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
    metrics_store.MetricsStore.insert_atom self atom_id atom = fail Error.integerOverflow := by
  sorry

/-- conditional: if both the inner map of `atom_id` and the overflow map have 250 or more
entries, `insert_atom` returns `()`. In the Rust source this path records nothing and logs an
error, if the log level allows it. Hypotheses: the outcomes of the calls on this path, and the
shared assumptions about the log calls (`max_level`, the `Level` comparison, `loc`, `log`). -/
theorem insert_atom_full
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
    metrics_store.MetricsStore.insert_atom self atom_id atom = ok () := by
  sorry

end Keystore2Verify.MetricsStore
