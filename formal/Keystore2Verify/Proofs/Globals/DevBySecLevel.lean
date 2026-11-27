import Keystore2Verify.Specs.Defs.Globals

namespace Keystore2Verify.Globals
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals

/-- conditional: if `uuid_by_sec_level` maps `sec` to `uuid`, and `devices_by_uuid` maps `uuid` to
the device `dev` with the hardware information `hw`, the function returns `Some((dev, hw, uuid))`.
The map is not changed (the Rust takes `&self`). Hypotheses: the assumptions for `HashMap::get` on
both maps (read through `entsS` and `entsD`), for `Option::and_then` at the closure of this
function, and for the clones of the handle and of the hardware information. -/
theorem DevicesMap_dev_by_sec_level_found {T : Type} (inst : binder.FromIBinder T)
    (entsS : Entries SecLevel database.Uuid) (entsD : Entries database.Uuid (Device T))
    (hS : SecLevelGetSpec entsS) (hD : DevicesGetSpec entsD) (hand : DevBySecLevelAndThenSpec inst)
    (hdev : StrongCloneSpec inst) (hhw : KmHwInfoCloneSpec)
    (self : globals.DevicesMap T) (sec : SecLevel) (uuid : database.Uuid)
    (dev : binder.Strong T) (hw : KmHwInfo)
    (hs : (sec, uuid) ∈ entsS self.uuid_by_sec_level)
    (hd : (uuid, (dev, hw)) ∈ entsD self.devices_by_uuid) :
    globals.DevicesMap.dev_by_sec_level inst self sec = ok (some (dev, hw, uuid)) := by
  sorry

/-- conditional: if `sec` is not a key of `uuid_by_sec_level`, the function returns `None`.
Hypotheses: the assumptions for `HashMap::get` on `uuid_by_sec_level` and for `Option::and_then` at
the closure of this function. -/
theorem DevicesMap_dev_by_sec_level_unknown {T : Type} (inst : binder.FromIBinder T)
    (entsS : Entries SecLevel database.Uuid) (hS : SecLevelGetSpec entsS)
    (hand : DevBySecLevelAndThenSpec inst)
    (self : globals.DevicesMap T) (sec : SecLevel)
    (hs : ∀ u, (sec, u) ∉ entsS self.uuid_by_sec_level) :
    globals.DevicesMap.dev_by_sec_level inst self sec = ok none := by
  sorry

/-- conditional: if `uuid_by_sec_level` maps `sec` to a `uuid` that is not a key of
`devices_by_uuid` (a dangling entry), the function returns `None`. Hypotheses: the assumptions for
`HashMap::get` on both maps and for `Option::and_then` at the closure of this function. -/
theorem DevicesMap_dev_by_sec_level_dangling {T : Type} (inst : binder.FromIBinder T)
    (entsS : Entries SecLevel database.Uuid) (entsD : Entries database.Uuid (Device T))
    (hS : SecLevelGetSpec entsS) (hD : DevicesGetSpec entsD) (hand : DevBySecLevelAndThenSpec inst)
    (self : globals.DevicesMap T) (sec : SecLevel) (uuid : database.Uuid)
    (hs : (sec, uuid) ∈ entsS self.uuid_by_sec_level)
    (hd : ∀ v, (uuid, v) ∉ entsD self.devices_by_uuid) :
    globals.DevicesMap.dev_by_sec_level inst self sec = ok none := by
  sorry

end Keystore2Verify.Globals
