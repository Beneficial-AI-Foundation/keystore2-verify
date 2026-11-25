import Keystore2Verify.Specs.Defs.Permission

namespace Keystore2Verify.Permission
open Aeneas Aeneas.Std Result keystore2
open I32.Insts.CoreConvertFromKeyPerm renaming «from» → i32FromKeyPerm
open permission.KeyPerm.Insts
open CoreConvertFromI32 renaming «from» → keyPermFromI32
open Keystore2_selinuxClassPermission renaming «name» → keyPermName
open Keystore2_selinuxClassPermission renaming class_name → keyPermClassName
open CoreCmpPartialEqKeyPerm renaming eq → keyPermEq
open CoreCloneClone renaming clone → keyPermClone

/-- A number is one of the numbers of a `KeyPerm` exactly when it is in this explicit list. -/
private theorem keyPermNumbers_iff (v : Int) : v ∈ keyPermNumbers ↔
    v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 4 ∨ v = 8 ∨ v = 16 ∨ v = 32 ∨ v = 64 ∨ v = 128 ∨ v = 256 ∨
      v = 512 ∨ v = 2048 := by
  constructor
  · rintro ⟨p, rfl⟩; cases p <;> simp [keyPermValue]
  · rintro (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
    exacts [⟨.None, rfl⟩, ⟨.Delete, rfl⟩, ⟨.GenUniqueId, rfl⟩, ⟨.GetInfo, rfl⟩, ⟨.Grant, rfl⟩,
      ⟨.ManageBlob, rfl⟩, ⟨.Rebind, rfl⟩, ⟨.ReqForcedOp, rfl⟩, ⟨.Update, rfl⟩, ⟨.Use, rfl⟩,
      ⟨.UseDevId, rfl⟩, ⟨.ConvertStorageKeyToEphemeral, rfl⟩]

/-- exact: `KeyPerm::from` never fails. If the number is one of the numbers of a `KeyPerm`
(`keyPermNumbers`), the result is the variant with that number. Every other number, including 1024,
the sum of two bits, negative numbers and the bits 12 to 31, gives `KeyPerm::None`. -/
theorem key_perm_from_i32 (x : Std.I32) :
    ∃ p, keyPermFromI32 x = ok p ∧
      (x.val ∈ keyPermNumbers → keyPermValue p = x.val) ∧
      (x.val ∉ keyPermNumbers → p = permission.KeyPerm.None) := by
  unfold keyPermFromI32
  split
  all_goals refine ⟨_, rfl, ?_, ?_⟩
  all_goals simp only [keyPermNumbers_iff, keyPermValue]
  all_goals try (first | decide | (intro h; exact (h (by decide)).elim))
  · rintro (h|h|h|h|h|h|h|h|h|h|h|h) <;> simp_all <;> contradiction
  · intro _; trivial

/-- exact: `i32::from(KeyPerm)` never fails and returns the number of the permission
(`keyPermValue`). -/
theorem key_perm_into_i32 (p : permission.KeyPerm) :
    ∃ v, i32FromKeyPerm p = ok v ∧ v.val = keyPermValue p := by
  cases p <;> exact ⟨_, rfl, rfl⟩

/-- exact: `KeyPerm::from(i32::from(p))` is `p` for every variant. -/
theorem key_perm_round_trip (p : permission.KeyPerm) (v : Std.I32)
    (h : i32FromKeyPerm p = ok v) :
    keyPermFromI32 v = ok p := by
  cases p <;> (simp [i32FromKeyPerm] at h; subst h; rfl)

/-- exact: two variants with the same number are equal (`i32::from` is injective). -/
theorem key_perm_into_i32_injective (p q : permission.KeyPerm) (v : Std.I32)
    (hp : i32FromKeyPerm p = ok v)
    (hq : i32FromKeyPerm q = ok v) : p = q := by
  have h := hp.trans hq.symm
  cases p <;> cases q <;> first
    | rfl
    | (exfalso; simp only [i32FromKeyPerm, Result.ok.injEq] at h; revert h; decide)

/-- exact: `name` never fails and returns the SELinux permission name of each variant. -/
theorem key_perm_name :
    keyPermName .None = ok (toStr "none") ∧
    keyPermName .Delete = ok (toStr "delete") ∧
    keyPermName .GenUniqueId = ok (toStr "gen_unique_id") ∧
    keyPermName .GetInfo = ok (toStr "get_info") ∧
    keyPermName .Grant = ok (toStr "grant") ∧
    keyPermName .ManageBlob = ok (toStr "manage_blob") ∧
    keyPermName .Rebind = ok (toStr "rebind") ∧
    keyPermName .ReqForcedOp = ok (toStr "req_forced_op") ∧
    keyPermName .Update = ok (toStr "update") ∧
    keyPermName .Use = ok (toStr "use") ∧
    keyPermName .UseDevId = ok (toStr "use_dev_id") ∧
    keyPermName .ConvertStorageKeyToEphemeral = ok (toStr "convert_storage_key_to_ephemeral") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- exact: two variants with the same name are equal (the names are pairwise different). -/
theorem key_perm_name_injective (p q : permission.KeyPerm) (s : Str)
    (hp : keyPermName p = ok s) (hq : keyPermName q = ok s) : p = q := by
  have h := hp.trans hq.symm
  cases p <;> cases q <;> first
    | rfl
    | (exfalso; simp only [keyPermName, Result.ok.injEq] at h; revert h; decide +kernel)

/-- exact: `class_name` returns the SELinux class `keystore2_key` for every variant,
`None` included. -/
theorem key_perm_class_name (p : permission.KeyPerm) :
    keyPermClassName p = ok (toStr "keystore2_key") := by
  rfl

/-- exact: `clone` returns the same variant. -/
theorem key_perm_clone (p : permission.KeyPerm) : keyPermClone p = ok p := by
  rfl

/-- exact: `eq` never fails and is `true` exactly for the same variant. -/
theorem key_perm_eq (p q : permission.KeyPerm) :
    ∃ b, keyPermEq p q = ok b ∧ (b = true ↔ p = q) := by
  cases p <;> cases q <;> exact ⟨_, rfl, by first | simp; done | (simp; decide)⟩

end Keystore2Verify.Permission
