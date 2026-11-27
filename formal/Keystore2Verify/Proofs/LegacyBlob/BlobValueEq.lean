import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open legacy_blob.BlobValue.Insts renaming CoreCmpPartialEqBlobValue.eq → blobValueEq
open keystore2_crypto.zvec.ZVec.Insts renaming CoreCmpPartialEqZVec.eq → zvecEq

/-- exact: two values of different variants are not equal. The comparison returns `false` and
looks at no field. -/
theorem blob_value_eq_variant_ne (a b : legacy_blob.BlobValue)
    (h : blobValueIndex a ≠ blobValueIndex b) : blobValueEq a b = ok false := by
  sorry

/-- exact: two `Generic` values are equal exactly when their bytes are. -/
theorem blob_value_eq_generic (a b : alloc.vec.Vec Std.U8) :
    blobValueEq (.Generic a) (.Generic b) = ok (decide (a.val = b.val)) := by
  sorry

/-- exact: two `Characteristics` values are equal exactly when their bytes are. -/
theorem blob_value_eq_characteristics (a b : alloc.vec.Vec Std.U8) :
    blobValueEq (.Characteristics a) (.Characteristics b) = ok (decide (a.val = b.val)) := by
  sorry

/-- exact: two `CharacteristicsCache` values are equal exactly when their bytes are. -/
theorem blob_value_eq_characteristics_cache (a b : alloc.vec.Vec Std.U8) :
    blobValueEq (.CharacteristicsCache a) (.CharacteristicsCache b) =
      ok (decide (a.val = b.val)) := by
  sorry

/-- exact: two `EncryptedCharacteristics` values are equal exactly when their `iv`, `tag` and
`data` are. The Rust code compares them in this order and stops at the first difference. -/
theorem blob_value_eq_encrypted_characteristics
    (iv tag data iv' tag' data' : alloc.vec.Vec Std.U8) :
    blobValueEq (.EncryptedCharacteristics iv tag data) (.EncryptedCharacteristics iv' tag' data') =
      ok (decide (iv.val = iv'.val ∧ tag.val = tag'.val ∧ data.val = data'.val)) := by
  sorry

/-- exact: two `PwEncrypted` values are equal exactly when their `iv`, `tag`, `data`, `salt`
and `key_size` are. -/
theorem blob_value_eq_pw_encrypted (iv tag data salt iv' tag' data' salt' : alloc.vec.Vec Std.U8)
    (n n' : Std.Usize) :
    blobValueEq (.PwEncrypted iv tag data salt n) (.PwEncrypted iv' tag' data' salt' n') =
      ok (decide (iv.val = iv'.val ∧ tag.val = tag'.val ∧ data.val = data'.val ∧
        salt.val = salt'.val ∧ n.val = n'.val)) := by
  sorry

/-- exact: two `Encrypted` values are equal exactly when their `iv`, `tag` and `data` are. -/
theorem blob_value_eq_encrypted (iv tag data iv' tag' data' : alloc.vec.Vec Std.U8) :
    blobValueEq (.Encrypted iv tag data) (.Encrypted iv' tag' data') =
      ok (decide (iv.val = iv'.val ∧ tag.val = tag'.val ∧ data.val = data'.val)) := by
  sorry

/-- exact: two `EncryptedGeneric` values are equal exactly when their `iv`, `tag` and `data`
are. -/
theorem blob_value_eq_encrypted_generic (iv tag data iv' tag' data' : alloc.vec.Vec Std.U8) :
    blobValueEq (.EncryptedGeneric iv tag data) (.EncryptedGeneric iv' tag' data') =
      ok (decide (iv.val = iv'.val ∧ tag.val = tag'.val ∧ data.val = data'.val)) := by
  sorry

/-- exact: the comparison of two `Decrypted` values is the comparison of their secret vectors,
whatever it returns. The comparison of `ZVec` is an external function, so this statement says
nothing about its result. -/
theorem blob_value_eq_decrypted (a b : keystore2_crypto.zvec.ZVec) :
    blobValueEq (.Decrypted a) (.Decrypted b) = zvecEq a b := by
  sorry

/-- conditional: two `Decrypted` values are equal exactly when the buffers and lengths of their
secret vectors are equal (`view`); equal secret bytes are not enough. Hypothesis: the assumption
about the comparison of `ZVec`, an external function (`ZVecEqSpec`). -/
theorem blob_value_eq_decrypted_content {α : Type} (view : keystore2_crypto.zvec.ZVec → α)
    (h : ZVecEqSpec view) (a b : keystore2_crypto.zvec.ZVec) :
    ∃ r, blobValueEq (.Decrypted a) (.Decrypted b) = ok r ∧ (r = true ↔ view a = view b) := by
  sorry

end Keystore2Verify.LegacyBlob
