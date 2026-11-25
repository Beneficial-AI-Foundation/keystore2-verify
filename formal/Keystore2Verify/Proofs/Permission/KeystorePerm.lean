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

/-- A number is one of the numbers of a `KeystorePerm` exactly when it is in this explicit list. -/
private theorem keystorePermNumbers_iff (v : Int) : v ∈ keystorePermNumbers ↔
    v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 4 ∨ v = 8 ∨ v = 16 ∨ v = 32 ∨ v = 64 ∨ v = 128 ∨ v = 256 ∨ v =
      512 ∨ v = 1024 ∨ v = 2048 ∨ v = 4096 ∨ v = 8192 ∨ v = 16384 := by
  constructor
  · rintro ⟨p, rfl⟩; cases p <;> simp [keystorePermValue]
  · rintro (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
    exacts [⟨.None, rfl⟩, ⟨.AddAuth, rfl⟩, ⟨.ClearNs, rfl⟩, ⟨.List, rfl⟩, ⟨.Lock, rfl⟩, ⟨.Reset,
      rfl⟩, ⟨.Unlock, rfl⟩, ⟨.ChangeUser, rfl⟩, ⟨.ChangePassword, rfl⟩, ⟨.ClearUID,
      rfl⟩, ⟨.GetAuthToken, rfl⟩, ⟨.EarlyBootEnded, rfl⟩, ⟨.PullMetrics, rfl⟩,
      ⟨.DeleteAllKeys, rfl⟩, ⟨.GetAttestationKey, rfl⟩, ⟨.GetLastAuthTime, rfl⟩]

/-- The numbers of two variants of `KeystorePerm` are equal only for the same variant. -/
private theorem keystorePermValue_injective {p q : permission.KeystorePerm}
    (h : keystorePermValue p = keystorePermValue q) : p = q := by
  cases p <;> cases q <;> first | rfl | (exfalso; revert h; decide)

/-- The `i32` made from the discriminant of a `KeystorePerm` has the number of the variant. -/
private theorem castVal (p : permission.KeystorePerm) :
    (IScalar.cast .I32 (read_discriminant p)).val = keystorePermValue p := by
  cases p <;> simp [keystorePermValue, IScalar.cast_val_eq, read_discriminant,
    permission.KeystorePerm.read_discriminant]

/-- exact: `KeystorePerm::from` never fails. If the number is one of the numbers of a `KeystorePerm`
(`keystorePermNumbers`), the result is the variant with that number. Every other number, including
the sum of two bits, negative numbers and 32768 and above, gives `KeystorePerm::None`. -/
theorem keystore_perm_from_i32 (x : Std.I32) :
    ∃ p, keystorePermFromI32 x = ok p ∧
      (x.val ∈ keystorePermNumbers → keystorePermValue p = x.val) ∧
      (x.val ∉ keystorePermNumbers → p = permission.KeystorePerm.None) := by
  unfold keystorePermFromI32
  split
  all_goals refine ⟨_, rfl, ?_, ?_⟩
  all_goals simp only [keystorePermNumbers_iff, keystorePermValue]
  all_goals try (first | decide | (intro h; exact (h (by decide)).elim))
  · rintro (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h) <;> simp_all <;> contradiction
  · intro _; trivial

/-- exact: `i32::from(KeystorePerm)` never fails and returns the number of the permission
(`keystorePermValue`). -/
theorem keystore_perm_into_i32 (p : permission.KeystorePerm) :
    ∃ v, i32FromKeystorePerm p = ok v ∧ v.val = keystorePermValue p := by
  cases p <;> exact ⟨_, rfl, castVal _⟩

/-- exact: `KeystorePerm::from(i32::from(p))` is `p` for every variant. -/
theorem keystore_perm_round_trip (p : permission.KeystorePerm) (v : Std.I32)
    (h : i32FromKeystorePerm p = ok v) :
    keystorePermFromI32 v = ok p := by
  obtain ⟨v', hv', hval⟩ := keystore_perm_into_i32 p
  have hv : v = v' := by rw [h] at hv'; simpa using hv'
  subst hv
  obtain ⟨p', hp', hin, -⟩ := keystore_perm_from_i32 v
  have hmem : v.val ∈ keystorePermNumbers := hval ▸ ⟨p, rfl⟩
  rw [hp', keystorePermValue_injective (hin hmem |>.trans hval)]

/-- exact: two variants with the same number are equal (`i32::from` is injective). -/
theorem keystore_perm_into_i32_injective (p q : permission.KeystorePerm) (v : Std.I32)
    (hp : i32FromKeystorePerm p = ok v)
    (hq : i32FromKeystorePerm q = ok v) : p = q := by
  obtain ⟨vp, hvp, hp'⟩ := keystore_perm_into_i32 p
  obtain ⟨vq, hvq, hq'⟩ := keystore_perm_into_i32 q
  rw [hp] at hvp
  rw [hq] at hvq
  simp only [Result.ok.injEq] at hvp hvq
  subst hvp hvq
  exact keystorePermValue_injective (hp'.symm.trans hq')

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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- exact: two variants with the same name are equal (the names are pairwise different). -/
theorem keystore_perm_name_injective (p q : permission.KeystorePerm) (s : Str)
    (hp : keystorePermName p = ok s) (hq : keystorePermName q = ok s) : p = q := by
  have h := hp.trans hq.symm
  cases p <;> cases q <;> first
    | rfl
    | (exfalso; simp only [keystorePermName, Result.ok.injEq] at h; revert h; decide +kernel)

/-- exact: `class_name` returns the SELinux class `keystore2` for every variant,
`None` included. -/
theorem keystore_perm_class_name (p : permission.KeystorePerm) :
    keystorePermClassName p = ok (toStr "keystore2") := by
  rfl

/-- exact: `clone` returns the same variant. -/
theorem keystore_perm_clone (p : permission.KeystorePerm) : keystorePermClone p = ok p := by
  rfl

/-- exact: `eq` never fails and is `true` exactly for the same variant. -/
theorem keystore_perm_eq (p q : permission.KeystorePerm) :
    ∃ b, keystorePermEq p q = ok b ∧ (b = true ↔ p = q) := by
  refine ⟨_, rfl, ?_⟩
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    apply keystorePermValue_injective
    rw [← castVal p, ← castVal q]
    exact congrArg (fun d => (IScalar.cast .I32 d).val) h
  · rintro rfl; rfl

end Keystore2Verify.Permission
