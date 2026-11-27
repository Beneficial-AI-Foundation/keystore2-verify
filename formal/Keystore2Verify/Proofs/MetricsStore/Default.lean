import Keystore2Verify.Specs.Defs.MetricsStore

namespace Keystore2Verify.MetricsStore
open Aeneas Aeneas.Std Result keystore2
open android_security_metrics.aidl.android.security.metrics
open std.sync.poison.mutex
open std.sync.poison.mutex.Mutex.Insts.CoreDefaultDefault renaming default → mutexDefault
open std.collections.hash.map.HashMapKVSGlobal.Insts renaming CoreDefaultDefault → hashMapDefault
open std.hash.random.RandomState.Insts renaming CoreDefaultDefault → randomStateDefault
open metrics_store.MetricsStore.Insts.CoreDefaultDefault renaming default → metricsStoreDefault

/-- conditional: if `Mutex::default` for the map of maps returns the mutex `m`, then the derived
`default` of `MetricsStore` returns the store whose only field is `m`. In the Rust source the
mutex is created around the default (empty) map of maps. Hypothesis: the outcome of
`Mutex::default`. The emptiness of the map is not stated: no merged assumption describes the
default map or the contents of a mutex. -/
theorem MetricsStore_default_ok (m : Mutex AtomStore)
    (hm : mutexDefault (hashMapDefault AtomID.AtomID AtomMap randomStateDefault) = ok m) :
    metricsStoreDefault = ok { metrics_store := m } := by
  sorry

end Keystore2Verify.MetricsStore
