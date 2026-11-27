import Keystore2Verify.Proofs.AuditLog.KeyOwner
import Keystore2Verify.Proofs.AuditLog.LogKeyGenerated
import Keystore2Verify.Proofs.AuditLog.LogKeyImported
import Keystore2Verify.Proofs.AuditLog.LogKeyDeleted

namespace Keystore2Verify.AuditLog

section KeyOwner
open Aeneas Aeneas.Std Result keystore2
open android_system_keystore2.aidl.android.system.keystore2

recall key_owner_app (nspace : Std.I64) (uid : Std.I32) :
    audit_log.key_owner (0#i32 : Domain.Domain) nspace uid = ok uid

recall key_owner_selinux (nspace : Std.I64) (uid : Std.I32) :
    ∃ r, audit_log.key_owner (2#i32 : Domain.Domain) nspace uid = ok r ∧
      r.bv = nspace.bv.setWidth 32 ||| 0x80000000#32 ∧ r.val < 0

recall key_owner_other (hcmp : LogLevelPartialCmpSpec) (hmax : LogMaxLevelSpec)
    (hloc : LogLocSpec) (hlog : LogPrivateApiLogSpec)
    (domain : Domain.Domain) (h0 : domain ≠ 0#i32) (h2 : domain ≠ 2#i32)
    (nspace : Std.I64) (uid : Std.I32) :
    audit_log.key_owner domain nspace uid = ok 0#i32

end KeyOwner

section LogKeyGenerated
open Aeneas Aeneas.Std Result keystore2
open android_system_keystore2.aidl.android.system.keystore2

recall log_key_generated_eq_log_key_event (key : KeyDescriptor.KeyDescriptor)
    (calling_app : Std.U32) (success : Bool) :
    audit_log.log_key_generated key calling_app success =
      audit_log.log_key_event audit_log.TAG_KEY_GENERATED key calling_app success ∧
    audit_log.TAG_KEY_GENERATED = 210024#u32

end LogKeyGenerated

section LogKeyImported
open Aeneas Aeneas.Std Result keystore2
open android_system_keystore2.aidl.android.system.keystore2

recall log_key_imported_eq_log_key_event (key : KeyDescriptor.KeyDescriptor)
    (calling_app : Std.U32) (success : Bool) :
    audit_log.log_key_imported key calling_app success =
      audit_log.log_key_event audit_log.TAG_KEY_IMPORTED key calling_app success ∧
    audit_log.TAG_KEY_IMPORTED = 210025#u32

end LogKeyImported

section LogKeyDeleted
open Aeneas Aeneas.Std Result keystore2
open android_system_keystore2.aidl.android.system.keystore2

recall log_key_deleted_eq_log_key_event (key : KeyDescriptor.KeyDescriptor)
    (calling_app : Std.U32) (success : Bool) :
    audit_log.log_key_deleted key calling_app success =
      audit_log.log_key_event audit_log.TAG_KEY_DESTROYED key calling_app success ∧
    audit_log.TAG_KEY_DESTROYED = 210026#u32

end LogKeyDeleted

end Keystore2Verify.AuditLog
