import Keystore2Verify.Specs.Defs.Externals

namespace Keystore2Verify.AuditLog
open Aeneas Aeneas.Std Result keystore2
open android_system_keystore2.aidl.android.system.keystore2

/-- exact: `log_key_generated` returns what `log_key_event` returns for the tag
`TAG_KEY_GENERATED` and the same key descriptor,
calling uid and success flag. The tag is 210024. The function has no other effect and no other
failure. -/
theorem log_key_generated_eq_log_key_event (key : KeyDescriptor.KeyDescriptor)
    (calling_app : Std.U32) (success : Bool) :
    audit_log.log_key_generated key calling_app success =
      audit_log.log_key_event audit_log.TAG_KEY_GENERATED key calling_app success ∧
    audit_log.TAG_KEY_GENERATED = 210024#u32 := by
  sorry
