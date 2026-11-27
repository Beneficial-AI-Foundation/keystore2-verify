import Keystore2Verify.Specs.Defs.Externals

namespace Keystore2Verify.Entropy
open Aeneas Aeneas.Std Result keystore2
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open entropy.FeederInfo.Insts.CoreDefaultDefault renaming default → feederDefault
open std.collections.hash.map.HashMapKVSGlobal.Insts.CoreDefaultDefault
  renaming default → hashMapDefault

/-- conditional: if the default hash map of `SecurityLevel` to `Instant` is `hm`, the default
`FeederInfo` is `{ last_feed := hm }`. Hypothesis: the outcome of `HashMap::default`. In the Rust
source the map is empty. -/
theorem feeder_info_default (hm : std.collections.hash.map.HashMap SecurityLevel.SecurityLevel
      std.time.Instant std.hash.random.RandomState alloc.alloc.Global)
    (h : hashMapDefault SecurityLevel.SecurityLevel std.time.Instant
      std.hash.random.RandomState.Insts.CoreDefaultDefault = ok hm) :
    feederDefault = ok { last_feed := hm } := by
  sorry
