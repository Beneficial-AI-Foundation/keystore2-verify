import Keystore2Verify.Specs.Defs.Enforcements

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2
open android_system_keystore2.aidl.android.system.keystore2
open IKeystoreSecurityLevel renaming
  KEY_FLAG_AUTH_BOUND_WITHOUT_CRYPTOGRAPHIC_LSKF_BINDING → lskfFlag
open Domain.Domain renaming APP → domainApp
open Domain.Domain.Insts.CoreCmpPartialEqDomain renaming eq → domainEq

/-! `superEncChoose isApp kps (0, None)` is the choice of the loop: see `Specs/Defs/Enforcements`.
`isApp` is the value that the comparison of the domain with `Domain::APP` returns. -/

/-- conditional: if the flags are `Some f` and `f` has a bit of the flag
`KEY_FLAG_AUTH_BOUND_WITHOUT_CRYPTOGRAPHIC_LSKF_BINDING`, `super_encryption_required` returns
`SuperEncryptionType::None`, whatever the parameters. In the Rust source this path returns before
the parameters are read. Hypothesis: the constant of the flag is `k`, and `f &&& k` is not 0. -/
theorem super_encryption_required_flag_set (domain : Domain.Domain)
    (key_parameters : Slice key_parameter.KeyParameter) (f k : Std.I32)
    (hk : lskfFlag = ok k) (hbit : (f &&& k) ≠ 0#i32) :
    enforcements.Enforcements.super_encryption_required domain key_parameters (some f)
      = ok super_key.SuperEncryptionType.None := by
  sorry

/-- exact: if the flags are `None` and no parameter is `UnlockedDeviceRequired` or `UserSecureID`,
`super_encryption_required` returns the choice of the loop. `MaxBootLevel(level)` has priority 3
and gives `BootLevel(level as usize)`; every other parameter has priority 0 and gives `None`. The
first parameter of the highest priority wins, and an empty list gives `None`. The domain does not
matter, and no external function is assumed. -/
theorem super_encryption_required_no_flags_domain_free (domain : Domain.Domain)
    (key_parameters : Slice key_parameter.KeyParameter)
    (hfree : ∀ kp ∈ key_parameters.val, ¬ DomainDependent kp.value) :
    enforcements.Enforcements.super_encryption_required domain key_parameters none
      = ok (superEncChoose false key_parameters.val (0, super_key.SuperEncryptionType.None)) := by
  sorry

/-- conditional: if the flags are `None`, `super_encryption_required` returns the choice of the
loop, where `isApp` is the value that the comparison of the domain with `Domain::APP` returns.
`MaxBootLevel(level)` has priority 3 and gives `BootLevel(level as usize)`. `UnlockedDeviceRequired`
has priority 2 and gives `UnlockedDeviceRequired`, and `UserSecureID` has priority 1 and gives
`CredentialEncrypted`, both only when the domain is `APP`. Every other parameter has priority 0 and
gives `None`. The first parameter of the highest priority wins. Hypothesis: if some parameter is
`UnlockedDeviceRequired` or `UserSecureID`, the constant `Domain::APP` is `a` and the comparison of
`domain` with `a` returns `isApp`. In the Rust source these two calls run only for such a parameter,
so the hypothesis is empty for the other lists. -/
theorem super_encryption_required_no_flags (domain : Domain.Domain)
    (key_parameters : Slice key_parameter.KeyParameter) (a : Domain.Domain) (isApp : Bool)
    (hdom : (∃ kp ∈ key_parameters.val, DomainDependent kp.value) →
      domainApp = ok a ∧ domainEq domain a = ok isApp) :
    enforcements.Enforcements.super_encryption_required domain key_parameters none
      = ok (superEncChoose isApp key_parameters.val (0, super_key.SuperEncryptionType.None)) := by
  sorry

/-- conditional: if the flags are `Some f` and `f` has no bit of the flag
`KEY_FLAG_AUTH_BOUND_WITHOUT_CRYPTOGRAPHIC_LSKF_BINDING`, `super_encryption_required` returns the
same choice as for no flags (`super_encryption_required_no_flags`). Hypotheses: the constant of the
flag is `k`, and `f &&& k` is 0; and the conditional hypothesis on `Domain::APP` and the
comparison of `super_encryption_required_no_flags`. -/
theorem super_encryption_required_flag_clear (domain : Domain.Domain)
    (key_parameters : Slice key_parameter.KeyParameter) (f k : Std.I32)
    (a : Domain.Domain) (isApp : Bool)
    (hk : lskfFlag = ok k) (hbit : (f &&& k) = 0#i32)
    (hdom : (∃ kp ∈ key_parameters.val, DomainDependent kp.value) →
      domainApp = ok a ∧ domainEq domain a = ok isApp) :
    enforcements.Enforcements.super_encryption_required domain key_parameters (some f)
      = ok (superEncChoose isApp key_parameters.val (0, super_key.SuperEncryptionType.None)) := by
  sorry
