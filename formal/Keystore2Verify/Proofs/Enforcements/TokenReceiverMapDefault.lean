import Keystore2Verify.Specs.Defs.Enforcements

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2
open std.collections.hash.map
open std.hash.random
open std.sync.poison.mutex
open enforcements.TokenReceiverMap.Insts.CoreDefaultDefault renaming
  default → tokenReceiverMapDefault

/-- conditional: `default` stores the pair of a new `HashMap` and the cleanup counter
`CLEANUP_PERIOD + 1` in a mutex. The counter is 26: the `u8` addition cannot overflow, and the
statement names the pair `(hm, 26)` that goes into the mutex. What the map holds (it is empty in the
Rust source) and what the mutex holds are not observable: both types are opaque. Hypotheses: the
outcome of `HashMap::new` (it returns `hm`) and of `Mutex::new((hm, 26))` (it returns `m`). The
result is then the map whose field `map_and_cleanup_counter` is `m`. -/
theorem token_receiver_map_default
    (hm : HashMap utils.Challenge enforcements.TokenReceiver
      RandomState alloc.alloc.Global)
    (m : Mutex ((HashMap utils.Challenge enforcements.TokenReceiver
      RandomState alloc.alloc.Global) × Std.U8))
    (hnew : HashMapKVRandomStateGlobal.new utils.Challenge
      enforcements.TokenReceiver = ok hm)
    (hmutex : Mutex.new (hm, 26#u8) = ok m) :
    tokenReceiverMapDefault
      = ok { map_and_cleanup_counter := m } := by
  sorry
