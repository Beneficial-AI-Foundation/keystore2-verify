import Keystore2Verify.Specs.Defs.Enforcements

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2
open std.hash.random
open std.collections.hash.map
open std.sync.poison
open std.collections.hash.set
open mutex.Mutex.Insts renaming CoreDefaultDefault → mutexDefaultInst
open mutex.Mutex.Insts.CoreDefaultDefault renaming default → mutexDefault
open rwlock.RwLock.Insts.CoreDefaultDefault renaming default → rwLockDefault
open core.option.Option.Insts renaming CoreDefaultDefault → optionDefaultInst
open alloc.sync.Arc.Insts.CoreDefaultDefault renaming default → arcDefault
open HashSetTSGlobal.Insts renaming CoreDefaultDefault → hashSetDefaultInst
open RandomState.Insts renaming CoreDefaultDefault → randomStateDefaultInst
open enforcements.TokenReceiverMap.Insts.CoreDefaultDefault renaming
  default → tokenReceiverMapDefault
open enforcements.Enforcements.Insts.CoreDefaultDefault renaming default → enforcementsDefault

/-- conditional: forwarding result. `default` builds the four fields with the `default` of each
field type, in the order of the declaration. The theorem states which values the generated body
passes on. It does not state the contents of the opaque wrappers: that the set of unlocked users is
empty, that the lock-state task and the confirmation token slots are absent, and what the map holds
are not observable here. The map field is composed from its own translated `default`: it is the
`TokenReceiverMap` whose mutex `m2` holds the pair of a new `HashMap` `hm` and the counter 26.
Hypotheses: the outcomes of `Mutex::default` for the set (it returns `m`), `RwLock::default` (it
returns `rl`), `HashMap::new` (it returns `hm`), `Mutex::new((hm, 26))` (it returns `m2`) and
`Arc::default` for the slot (it returns `a`). The result is then the struct with those fields. -/
theorem enforcements_default
    (m : mutex.Mutex (HashSet utils.AndroidUserId RandomState alloc.alloc.Global))
    (rl : rwlock.RwLock (Option (alloc.sync.Arc async_task.AsyncTask)))
    (hm : HashMap utils.Challenge enforcements.TokenReceiver RandomState alloc.alloc.Global)
    (m2 : mutex.Mutex ((HashMap utils.Challenge enforcements.TokenReceiver
      RandomState alloc.alloc.Global) × Std.U8))
    (a : alloc.sync.Arc (mutex.Mutex (Option ByteReceiver)))
    (hmd : mutexDefault (hashSetDefaultInst utils.AndroidUserId randomStateDefaultInst) = ok m)
    (hrl : rwLockDefault (optionDefaultInst (alloc.sync.Arc async_task.AsyncTask)) = ok rl)
    (hnew : HashMapKVRandomStateGlobal.new utils.Challenge enforcements.TokenReceiver = ok hm)
    (hmutex : mutex.Mutex.new (hm, 26#u8) = ok m2)
    (ha : arcDefault (mutexDefaultInst (optionDefaultInst ByteReceiver)) = ok a) :
    enforcementsDefault
      = ok { device_unlocked_set := m, lock_state_task := rl,
             op_auth_map := { map_and_cleanup_counter := m2 },
             confirmation_token_receiver := a } := by
  sorry
