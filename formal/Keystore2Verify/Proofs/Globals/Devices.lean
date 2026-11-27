import Keystore2Verify.Specs.Defs.Globals

namespace Keystore2Verify.Globals
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals

/-- conditional: `devices` returns a `Vec` that holds, in some order, one pair `(dev,
hw.securityLevel)` for each entry `(uuid, (dev, hw))` of `devices_by_uuid`. The order is that of the
iteration of the hash map, which the Rust does not fix, so the statement is about the elements as a
multiset (`List.Perm`); an empty map gives the empty `Vec`. The security level is the one in the
hardware information, which can differ from the key of `uuid_by_sec_level`. The map is not changed
(the Rust takes `&self`). Hypotheses: the assumptions for `HashMap::values`, for `next` of the
`Values` iterator (both read through `ents` and `elems`, the values the iterator has left), for
`Iterator::map` and for `next` of the `Map` adapter at the closure of this function, and for the
clone of the binder handle; and that the map has at most `usize::MAX` entries (the conversion of the
list into a `Vec` panics above this). -/
theorem DevicesMap_devices {T : Type} (inst : binder.FromIBinder T)
    (ents : Entries database.Uuid (Device T))
    (elems : Vals database.Uuid (Device T) → List (Device T))
    (hvals : DevicesValuesSpec ents elems) (hnext : DevicesValuesNextSpec elems)
    (hmap : DevicesMapSpec inst) (hmapnext : DevicesMapNextSpec inst)
    (hdev : StrongCloneSpec inst)
    (self : globals.DevicesMap T) (hlen : (ents self.devices_by_uuid).length ≤ Std.Usize.max) :
    ∃ r, globals.DevicesMap.devices inst self = ok r ∧
      r.val.Perm ((ents self.devices_by_uuid).map fun e => (e.2.1, e.2.2.securityLevel)) := by
  sorry

end Keystore2Verify.Globals
