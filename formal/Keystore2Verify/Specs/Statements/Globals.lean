import Keystore2Verify.Proofs.Globals.DevByUuid
import Keystore2Verify.Proofs.Globals.DevBySecLevel
import Keystore2Verify.Proofs.Globals.Devices
import Keystore2Verify.Proofs.Globals.Insert
import Keystore2Verify.Proofs.Globals.Default
import Keystore2Verify.Proofs.Globals.GetRemotelyProvisionedComponentName
import Keystore2Verify.Proofs.Globals.BootCompleted
import Keystore2Verify.Proofs.Globals.WatchForBootCompleted

namespace Keystore2Verify.Globals

section DevByUuid
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals

recall DevicesMap_dev_by_uuid_found {T : Type} (inst : binder.FromIBinder T)
    (ents : Entries database.Uuid (Device T)) (hget : DevicesGetSpec ents)
    (hdev : StrongCloneSpec inst) (hhw : KmHwInfoCloneSpec)
    (self : globals.DevicesMap T) (uuid : database.Uuid) (dev : binder.Strong T) (hw : KmHwInfo)
    (h : (uuid, (dev, hw)) ∈ ents self.devices_by_uuid) :
    globals.DevicesMap.dev_by_uuid inst self uuid = ok (some (dev, hw, uuid))

recall DevicesMap_dev_by_uuid_missing {T : Type} (inst : binder.FromIBinder T)
    (ents : Entries database.Uuid (Device T)) (hget : DevicesGetSpec ents)
    (self : globals.DevicesMap T) (uuid : database.Uuid)
    (h : ∀ v, (uuid, v) ∉ ents self.devices_by_uuid) :
    globals.DevicesMap.dev_by_uuid inst self uuid = ok none

end DevByUuid

section DevBySecLevel
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals

recall DevicesMap_dev_by_sec_level_found {T : Type} (inst : binder.FromIBinder T)
    (entsS : Entries SecLevel database.Uuid) (entsD : Entries database.Uuid (Device T))
    (hS : SecLevelGetSpec entsS) (hD : DevicesGetSpec entsD) (hand : DevBySecLevelAndThenSpec inst)
    (hdev : StrongCloneSpec inst) (hhw : KmHwInfoCloneSpec)
    (self : globals.DevicesMap T) (sec : SecLevel) (uuid : database.Uuid)
    (dev : binder.Strong T) (hw : KmHwInfo)
    (hs : (sec, uuid) ∈ entsS self.uuid_by_sec_level)
    (hd : (uuid, (dev, hw)) ∈ entsD self.devices_by_uuid) :
    globals.DevicesMap.dev_by_sec_level inst self sec = ok (some (dev, hw, uuid))

recall DevicesMap_dev_by_sec_level_unknown {T : Type} (inst : binder.FromIBinder T)
    (entsS : Entries SecLevel database.Uuid) (hS : SecLevelGetSpec entsS)
    (hand : DevBySecLevelAndThenSpec inst)
    (self : globals.DevicesMap T) (sec : SecLevel)
    (hs : ∀ u, (sec, u) ∉ entsS self.uuid_by_sec_level) :
    globals.DevicesMap.dev_by_sec_level inst self sec = ok none

recall DevicesMap_dev_by_sec_level_dangling {T : Type} (inst : binder.FromIBinder T)
    (entsS : Entries SecLevel database.Uuid) (entsD : Entries database.Uuid (Device T))
    (hS : SecLevelGetSpec entsS) (hD : DevicesGetSpec entsD) (hand : DevBySecLevelAndThenSpec inst)
    (self : globals.DevicesMap T) (sec : SecLevel) (uuid : database.Uuid)
    (hs : (sec, uuid) ∈ entsS self.uuid_by_sec_level)
    (hd : ∀ v, (uuid, v) ∉ entsD self.devices_by_uuid) :
    globals.DevicesMap.dev_by_sec_level inst self sec = ok none

end DevBySecLevel

section Devices
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals

recall DevicesMap_devices {T : Type} (inst : binder.FromIBinder T)
    (ents : Entries database.Uuid (Device T))
    (elems : Vals database.Uuid (Device T) → List (Device T))
    (hvals : DevicesValuesSpec ents elems) (hnext : DevicesValuesNextSpec elems)
    (hmap : DevicesMapSpec inst) (hmapnext : DevicesMapNextSpec inst)
    (hdev : StrongCloneSpec inst)
    (self : globals.DevicesMap T) (hlen : (ents self.devices_by_uuid).length ≤ Std.Usize.max) :
    ∃ r, globals.DevicesMap.devices inst self = ok r ∧
      r.val.Perm ((ents self.devices_by_uuid).map fun e => (e.2.1, e.2.2.securityLevel))

end Devices

section Insert
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals
open database.Uuid.Insts

recall DevicesMap_insert {T : Type} (inst : binder.FromIBinder T)
    (entsD : Entries database.Uuid (Device T)) (entsS : Entries SecLevel database.Uuid)
    (hD : DevicesInsertSpec entsD) (hS : SecLevelInsertSpec entsS)
    (self : globals.DevicesMap T) (sec : SecLevel) (dev : binder.Strong T) (hw : KmHwInfo) :
    ∃ uuid m m', CoreConvertFromSecurityLevel.from sec = ok uuid ∧
      globals.DevicesMap.insert inst self sec dev hw =
        ok { devices_by_uuid := m, uuid_by_sec_level := m' } ∧
      MapUpdate entsD self.devices_by_uuid m uuid (dev, hw) ∧
      MapUpdate entsS self.uuid_by_sec_level m' sec uuid

end Insert

section Default
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals
open globals.DevicesMap.Insts
open std.collections.hash.map
open std.collections.hash.map.HashMapKVSGlobal.Insts
open std.hash.random.RandomState

recall DevicesMap_default {T : Type} (inst : binder.FromIBinder T)
    (entsD : Entries database.Uuid (Device T)) (entsS : Entries SecLevel database.Uuid)
    (hD : HashMapNewAssumption entsD
      (HashMapKVRandomStateGlobal.new database.Uuid (Device T)))
    (hS : HashMapDefaultAssumption entsS
      (CoreDefaultDefault.default SecLevel
        database.Uuid Insts.CoreDefaultDefault)) :
    ∃ d, CoreDefaultDefault.default inst = ok d ∧
      entsD d.devices_by_uuid = [] ∧ entsS d.uuid_by_sec_level = []

end Default

section GetRemotelyProvisionedComponentName
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals
open alloc.string.String.Insts
open android_hardware_security_keymint.aidl.android.hardware.security.keymint

recall get_remotely_provisioned_component_name_declared (root : anyhow.Error → ErrRoot)
    (hctx : KsCtxSpec root String) (ec : ErrorCode.ErrorCode)
    (hec : ErrorCode.ErrorCode.HARDWARE_TYPE_UNAVAILABLE = ok ec)
    (sl : SecLevel) (hsl : sl = 1#i32 ∨ sl = 2#i32) (s : String) (s1 : Str)
    (hfmt : alloc.fmt.format () = ok s)
    (hview : CoreOpsDerefDerefStr.deref s = ok s1)
    (hdecl : binder.is_declared s1 = ok (.Ok true)) :
    globals.get_remotely_provisioned_component_name sl = ok (.Ok s)

recall get_remotely_provisioned_component_name_undeclared (root : anyhow.Error → ErrRoot)
    (hctx : KsCtxSpec root String) (ec : ErrorCode.ErrorCode)
    (hec : ErrorCode.ErrorCode.HARDWARE_TYPE_UNAVAILABLE = ok ec)
    (sl : SecLevel) (hsl : sl = 1#i32 ∨ sl = 2#i32) (s : String) (s1 : Str)
    (hfmt : alloc.fmt.format () = ok s)
    (hview : CoreOpsDerefDerefStr.deref s = ok s1)
    (hdecl : binder.is_declared s1 = ok (.Ok false)) :
    ∃ e, globals.get_remotely_provisioned_component_name sl = ok (.Err e) ∧
      KmRoot root ec e

recall get_remotely_provisioned_component_name_other_level (root : anyhow.Error → ErrRoot)
    (hctx : KsCtxSpec root String) (hfmt : AllocFmtFormatSpec) (ec : ErrorCode.ErrorCode)
    (hec : ErrorCode.ErrorCode.HARDWARE_TYPE_UNAVAILABLE = ok ec)
    (sl : SecLevel) (h1 : sl ≠ 1#i32) (h2 : sl ≠ 2#i32) :
    ∃ e, globals.get_remotely_provisioned_component_name sl = ok (.Err e) ∧
      KmRoot root ec e

recall get_remotely_provisioned_component_name_status_error (root : anyhow.Error → ErrRoot)
    (hfrom : StatusCodeFromSpec root)
    (sl : SecLevel) (hsl : sl = 1#i32 ∨ sl = 2#i32) (s : String) (s1 : Str)
    (st : binder.StatusCode)
    (hfmt : alloc.fmt.format () = ok s)
    (hview : CoreOpsDerefDerefStr.deref s = ok s1)
    (hdecl : binder.is_declared s1 = ok (.Err st)) :
    ∃ e, globals.get_remotely_provisioned_component_name sl = ok (.Err e) ∧
      root e = ErrRoot.other

end GetRemotelyProvisionedComponentName

section BootCompleted
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals
open core.sync.atomic
open core.sync.atomic.private
open android_hardware_security_keymint.aidl.android.hardware.security.keymint

recall boot_completed_load (a : Atomic Bool
      (Align1 Std.U8))
    (b : Bool) (hstatic : globals.BOOT_COMPLETED = ok a)
    (hload : AtomicBoolAlign1U8.load a Ordering.Acquire = ok b) :
    globals.boot_completed = ok b

end BootCompleted

section WatchForBootCompleted
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals
open android_hardware_security_keymint.aidl.android.hardware.security.keymint

open rustutils.android.system_properties

recall watch_for_boot_completed_ok (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx1 : WatcherCtxSpec root PropertyWatcher) (hctx2 : WatcherCtxSpec root Unit)
    (w w' : PropertyWatcher)
    (hnew : PropertyWatcher.new (toStr "sys.boot_completed") = ok (.Ok w))
    (hwait : PropertyWatcher.wait_for_value w (toStr "1") none = ok (.Ok (), w')) :
    globals.watch_for_boot_completed = ok (.Ok ())

recall watch_for_boot_completed_new_error (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx1 : WatcherCtxSpec root PropertyWatcher) (e : PropertyWatcherError)
    (hnew : PropertyWatcher.new (toStr "sys.boot_completed") = ok (.Err e)) :
    ∃ e', globals.watch_for_boot_completed = ok (.Err e') ∧ root e' = ErrRoot.other

recall watch_for_boot_completed_wait_error (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx1 : WatcherCtxSpec root PropertyWatcher) (hctx2 : WatcherCtxSpec root Unit)
    (w w' : PropertyWatcher) (e : PropertyWatcherError)
    (hnew : PropertyWatcher.new (toStr "sys.boot_completed") = ok (.Ok w))
    (hwait : PropertyWatcher.wait_for_value w (toStr "1") none = ok (.Err e, w')) :
    ∃ e', globals.watch_for_boot_completed = ok (.Err e') ∧ root e' = ErrRoot.other

end WatchForBootCompleted

end Keystore2Verify.Globals
