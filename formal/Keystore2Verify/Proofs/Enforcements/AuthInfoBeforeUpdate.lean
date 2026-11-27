import Keystore2Verify.Specs.Defs.Enforcements

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2

/-- exact: `before_update` returns exactly what `AuthInfo::get_auth_tokens` returns for the same
auth info: the result and the new auth info. It adds nothing and fails in no other way. -/
theorem auth_info_before_update (self : enforcements.AuthInfo) :
    enforcements.AuthInfo.before_update self = enforcements.AuthInfo.get_auth_tokens self := by
  sorry
