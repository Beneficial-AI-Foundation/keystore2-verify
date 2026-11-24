import Keystore2Verify.Specs.Defs.Permission

namespace Keystore2Verify.Permission
open Aeneas Aeneas.Std Result keystore2
open I32.Insts.CoreConvertFromKeystorePerm renaming «from» → i32FromKeystorePerm
open permission.KeystorePerm.Insts
open CoreConvertFromI32 renaming «from» → keystorePermFromI32
open Keystore2_selinuxClassPermission renaming «name» → keystorePermName
open Keystore2_selinuxClassPermission renaming class_name → keystorePermClassName
open CoreCmpPartialEqKeystorePerm renaming eq → keystorePermEq
open CoreCloneClone renaming clone → keystorePermClone

/-- exact: `KeystorePerm::from` never fails. If the number is one of the numbers of a `KeystorePerm`
(`keystorePermNumbers`), the result is the variant with that number. Every other number, including
the sum of two bits, negative numbers and 32768 and above, gives `KeystorePerm::None`. -/
theorem keystore_perm_from_i32 (x : Std.I32) :
    ∃ p, keystorePermFromI32 x = ok p ∧
      (x.val ∈ keystorePermNumbers → keystorePermValue p = x.val) ∧
      (x.val ∉ keystorePermNumbers → p = permission.KeystorePerm.None) := by
  sorry

/-- exact: `i32::from(KeystorePerm)` never fails and returns the number of the permission
(`keystorePermValue`). -/
theorem keystore_perm_into_i32 (p : permission.KeystorePerm) :
    ∃ v, i32FromKeystorePerm p = ok v ∧ v.val = keystorePermValue p := by
  sorry

/-- exact: `KeystorePerm::from(i32::from(p))` is `p` for every variant. -/
theorem keystore_perm_round_trip (p : permission.KeystorePerm) (v : Std.I32)
    (h : i32FromKeystorePerm p = ok v) :
    keystorePermFromI32 v = ok p := by
  sorry

/-- exact: two variants with the same number are equal (`i32::from` is injective). -/
theorem keystore_perm_into_i32_injective (p q : permission.KeystorePerm) (v : Std.I32)
    (hp : i32FromKeystorePerm p = ok v)
    (hq : i32FromKeystorePerm q = ok v) : p = q := by
  sorry

/-- exact: `name` never fails and returns the SELinux permission name of each variant. -/
theorem keystore_perm_name :
    keystorePermName .None = ok (toStr "none") ∧
    keystorePermName .AddAuth = ok (toStr "add_auth") ∧
    keystorePermName .ClearNs = ok (toStr "clear_ns") ∧
    keystorePermName .List = ok (toStr "list") ∧
    keystorePermName .Lock = ok (toStr "lock") ∧
    keystorePermName .Reset = ok (toStr "reset") ∧
    keystorePermName .Unlock = ok (toStr "unlock") ∧
    keystorePermName .ChangeUser = ok (toStr "change_user") ∧
    keystorePermName .ChangePassword = ok (toStr "change_password") ∧
    keystorePermName .ClearUID = ok (toStr "clear_uid") ∧
    keystorePermName .GetAuthToken = ok (toStr "get_auth_token") ∧
    keystorePermName .EarlyBootEnded = ok (toStr "early_boot_ended") ∧
    keystorePermName .PullMetrics = ok (toStr "pull_metrics") ∧
    keystorePermName .DeleteAllKeys = ok (toStr "delete_all_keys") ∧
    keystorePermName .GetAttestationKey = ok (toStr "get_attestation_key") ∧
    keystorePermName .GetLastAuthTime = ok (toStr "get_last_auth_time") := by
  sorry

/-- exact: two variants with the same name are equal (the names are pairwise different). -/
theorem keystore_perm_name_injective (p q : permission.KeystorePerm) (s : Str)
    (hp : keystorePermName p = ok s) (hq : keystorePermName q = ok s) : p = q := by
  sorry

/-- exact: `class_name` returns the SELinux class `keystore2` for every variant,
`None` included. -/
theorem keystore_perm_class_name (p : permission.KeystorePerm) :
    keystorePermClassName p = ok (toStr "keystore2") := by
  sorry

/-- exact: `clone` returns the same variant. -/
theorem keystore_perm_clone (p : permission.KeystorePerm) : keystorePermClone p = ok p := by
  sorry

/-- exact: `eq` never fails and is `true` exactly for the same variant. -/
theorem keystore_perm_eq (p q : permission.KeystorePerm) :
    ∃ b, keystorePermEq p q = ok b ∧ (b = true ↔ p = q) := by
  sorry

end Keystore2Verify.Permission
