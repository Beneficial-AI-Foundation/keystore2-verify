import Keystore2Verify.Specs.Defs.Externals

namespace Keystore2Verify.AuditLog
open Aeneas Aeneas.Std Result keystore2
open android_system_keystore2.aidl.android.system.keystore2

/-- exact: for the domain `APP` (0), `key_owner` returns `uid`. The namespace is ignored. -/
theorem key_owner_app (nspace : Std.I64) (uid : Std.I32) :
    audit_log.key_owner (0#i32 : Domain.Domain) nspace uid = ok uid := by
  sorry

/-- exact: for the domain `SELINUX` (2), `key_owner` returns the 32 low bits of `nspace`, with
bit 31 set, read as an `i32`. Rust: `(nspace | 0x80000000) as i32`. The result is negative, and
`uid` is ignored. -/
theorem key_owner_selinux (nspace : Std.I64) (uid : Std.I32) :
    ∃ r, audit_log.key_owner (2#i32 : Domain.Domain) nspace uid = ok r ∧
      r.bv = nspace.bv.setWidth 32 ||| 0x80000000#32 ∧ r.val < 0 := by
  sorry

/-- conditional: for every other domain (`GRANT`, `BLOB`, `KEY_ID` and any other number),
`key_owner` returns 0, and `nspace` and `uid` are ignored. Before returning, the Rust source
writes an information log line. Hypotheses: the logging calls do not fail
(`LogLevelPartialCmpSpec`, `LogMaxLevelSpec`, `LogLocSpec`, `LogPrivateApiLogSpec`). Whether the
line is written is not modelled. -/
theorem key_owner_other (hcmp : LogLevelPartialCmpSpec) (hmax : LogMaxLevelSpec)
    (hloc : LogLocSpec) (hlog : LogPrivateApiLogSpec)
    (domain : Domain.Domain) (h0 : domain ≠ 0#i32) (h2 : domain ≠ 2#i32)
    (nspace : Std.I64) (uid : Std.I32) :
    audit_log.key_owner domain nspace uid = ok 0#i32 := by
  sorry
