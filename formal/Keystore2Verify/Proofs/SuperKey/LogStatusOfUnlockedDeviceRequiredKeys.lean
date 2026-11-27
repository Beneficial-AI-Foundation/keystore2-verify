import Keystore2Verify.Specs.Defs.SuperKey

namespace Keystore2Verify.SuperKey
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

/-- conditional: the function returns `()` for every user and every `UserSuperKeys`; the entry is
not changed (the Rust takes `&UserSuperKeys`). The text that the Rust logs depends on whether
`unlocked_device_required_symmetric` and `biometric_unlock` are `Some`; the translation does not
model the log output, so the statement does not give it. Hypotheses: the merged assumptions about
the logging functions that the `info!` macro calls. -/
theorem SuperKeyManager_log_status_of_unlocked_device_required_keys
    (hcmp : LogLevelPartialCmpSpec) (hmax : LogMaxLevelSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) (user : utils.AndroidUserId)
    (entry : super_key.UserSuperKeys) :
    super_key.SuperKeyManager.log_status_of_unlocked_device_required_keys user entry =
      ok () := by
  sorry

end Keystore2Verify.SuperKey
