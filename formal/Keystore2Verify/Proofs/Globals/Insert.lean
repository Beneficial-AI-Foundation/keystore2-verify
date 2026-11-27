import Keystore2Verify.Specs.Defs.Globals

namespace Keystore2Verify.Globals
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals
open database.Uuid.Insts

/-- conditional: `insert` makes the key `uuid` from the requested level `sec` with
`Uuid::from`, binds `uuid` to `(dev, hw)` in `devices_by_uuid`, and binds `sec` to `uuid` in
`uuid_by_sec_level`. Every other entry of both maps stays, and an entry that had the same key is
replaced. The security level in `hw` need not equal `sec`. The statement names the key as the
result of the translated function `Uuid::from`; that function is outside this file. Hypotheses:
the assumptions for `HashMap::insert` on both maps, read through `entsD` and `entsS`. -/
theorem DevicesMap_insert {T : Type} (inst : binder.FromIBinder T)
    (entsD : Entries database.Uuid (Device T)) (entsS : Entries SecLevel database.Uuid)
    (hD : DevicesInsertSpec entsD) (hS : SecLevelInsertSpec entsS)
    (self : globals.DevicesMap T) (sec : SecLevel) (dev : binder.Strong T) (hw : KmHwInfo) :
    ∃ uuid m m', CoreConvertFromSecurityLevel.from sec = ok uuid ∧
      globals.DevicesMap.insert inst self sec dev hw =
        ok { devices_by_uuid := m, uuid_by_sec_level := m' } ∧
      MapUpdate entsD self.devices_by_uuid m uuid (dev, hw) ∧
      MapUpdate entsS self.uuid_by_sec_level m' sec uuid := by
  sorry

end Keystore2Verify.Globals
