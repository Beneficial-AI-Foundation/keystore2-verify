import Keystore2Verify.Specs.Defs.Externals

namespace Keystore2Verify.AuditLog
open Aeneas Aeneas.Std Result keystore2
open android_system_keystore2.aidl.android.system.keystore2

/-- exact: `log_key_imported` returns what `log_key_event` returns for the tag
`TAG_KEY_IMPORTED` and the same key descriptor,
calling uid and success flag. The tag is 210025. The function has no other effect and no other
failure. -/
theorem log_key_imported_eq_log_key_event (key : KeyDescriptor.KeyDescriptor)
    (calling_app : Std.U32) (success : Bool) :
    audit_log.log_key_imported key calling_app success =
      audit_log.log_key_event audit_log.TAG_KEY_IMPORTED key calling_app success ∧
    audit_log.TAG_KEY_IMPORTED = 210025#u32 := by
  sorry
