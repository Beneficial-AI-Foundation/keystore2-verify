import Keystore2Verify.Specs.Defs.Globals

namespace Keystore2Verify.Globals
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals
open globals.DevicesMap.Insts
open std.collections.hash.map
open std.collections.hash.map.HashMapKVSGlobal.Insts
open std.hash.random.RandomState

/-- conditional: the default `DevicesMap` has two maps with no entry. Hypotheses: the assumption for
`HashMap::new`, which makes `devices_by_uuid`, and the assumption for `Default::default`, which
makes `uuid_by_sec_level`. -/
theorem DevicesMap_default {T : Type} (inst : binder.FromIBinder T)
    (entsD : Entries database.Uuid (Device T)) (entsS : Entries SecLevel database.Uuid)
    (hD : HashMapNewAssumption entsD
      (HashMapKVRandomStateGlobal.new database.Uuid (Device T)))
    (hS : HashMapDefaultAssumption entsS
      (CoreDefaultDefault.default SecLevel
        database.Uuid Insts.CoreDefaultDefault)) :
    ∃ d, CoreDefaultDefault.default inst = ok d ∧
      entsD d.devices_by_uuid = [] ∧ entsS d.uuid_by_sec_level = [] := by
  sorry

end Keystore2Verify.Globals
