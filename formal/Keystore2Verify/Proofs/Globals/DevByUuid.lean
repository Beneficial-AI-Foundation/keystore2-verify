import Keystore2Verify.Specs.Defs.Globals

namespace Keystore2Verify.Globals
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals

/-- conditional: if `uuid` is a key of `devices_by_uuid` with the device `dev` and the hardware
information `hw`, the function returns `Some((dev, hw, uuid))`: clones of the stored values and
the requested UUID. The map is not changed (the Rust takes `&self`). Hypotheses: the assumptions for
`HashMap::get` on `devices_by_uuid` (read through `ents`), for the clone of the binder handle and
for the clone of the hardware information. -/
theorem DevicesMap_dev_by_uuid_found {T : Type} (inst : binder.FromIBinder T)
    (ents : Entries database.Uuid (Device T)) (hget : DevicesGetSpec ents)
    (hdev : StrongCloneSpec inst) (hhw : KmHwInfoCloneSpec)
    (self : globals.DevicesMap T) (uuid : database.Uuid) (dev : binder.Strong T) (hw : KmHwInfo)
    (h : (uuid, (dev, hw)) ∈ ents self.devices_by_uuid) :
    globals.DevicesMap.dev_by_uuid inst self uuid = ok (some (dev, hw, uuid)) := by
  sorry

/-- conditional: if `uuid` is not a key of `devices_by_uuid`, the function returns `None`. The
only hypothesis is the assumption for `HashMap::get` on `devices_by_uuid`. -/
theorem DevicesMap_dev_by_uuid_missing {T : Type} (inst : binder.FromIBinder T)
    (ents : Entries database.Uuid (Device T)) (hget : DevicesGetSpec ents)
    (self : globals.DevicesMap T) (uuid : database.Uuid)
    (h : ∀ v, (uuid, v) ∉ ents self.devices_by_uuid) :
    globals.DevicesMap.dev_by_uuid inst self uuid = ok none := by
  sorry

end Keystore2Verify.Globals
