import Keystore2Verify.Specs.Defs.Externals

/-!
# Definitions for the statements about `ec_crypto.rs`

Short names for the context laws that the translation uses, the `info` string of the key
derivation, and four laws about the lengths of crypto results. Nothing here is an axiom.
-/

namespace Keystore2Verify.EcCrypto
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2_crypto.zvec.ZVec.Insts

/-- The view of a secret vector as a slice: the `deref` of `ZVec`. -/
noncomputable abbrev zvecDeref : keystore2_crypto.zvec.ZVec → Result (Slice Std.U8) :=
  CoreOpsDerefDerefSliceU8.deref

/-- The `info` argument of the key derivation in `agree_key`: the 15 ASCII bytes of `AES-256-GCM
key`, with no terminator. -/
def aesKeyInfo : Slice Std.U8 :=
  Array.to_slice (Array.make 15#usize [
    65#u8, 69#u8, 83#u8, 45#u8, 50#u8, 53#u8, 54#u8, 45#u8,
    71#u8, 67#u8, 77#u8, 32#u8, 107#u8, 101#u8, 121#u8])

/-- Law for the length of a marshalled private key, over the observation `deref` of a secret vector
as a slice. If `marshal key` returns `Ok z`, then `z` has 73 bytes. Nothing is said when the call
returns `Err` or panics. -/
def EcKeyMarshalLenLaw {K Z : Type} (deref : Z → Result (Slice Std.U8))
    (marshal : K →
      Result (core.result.Result Z keystore2_crypto.error.Error)) : Prop :=
  ∀ key z, marshal key = ok (.Ok z) → ∃ s, deref z = ok s ∧ s.length = 73

/-- Law for `keystore2_crypto::ec_key_marshal_private_key` (register record
`ks2-ext-keystore2-crypto-ec-key-marshal-private-key`). If the call returns `Ok z`, then `z` has 73
bytes. Source: `crypto/lib.rs`, which makes the vector with `ZVec::new(73)` and returns it only if
the written length is 73. -/
def EcKeyMarshalPrivateKeySpec : Prop :=
  EcKeyMarshalLenLaw zvecDeref keystore2_crypto.ec_key_marshal_private_key

/-- Law for the length of a point in octet form. If `to_oct p` returns `Ok v`, then `v` has at least
1 and at most 133 bytes. Nothing is said when the call returns `Err` or panics. -/
def PointToOctLenLaw {P : Type}
    (to_oct : P →
      Result (core.result.Result (alloc.vec.Vec Std.U8) keystore2_crypto.error.Error)) : Prop :=
  ∀ p v, to_oct p = ok (.Ok v) → 1 ≤ v.val.length ∧ v.val.length ≤ 133

/-- Law for `keystore2_crypto::ec_point_point_to_oct` (register record
`ks2-ext-keystore2-crypto-ec-point-point-to-oct`). If the call returns `Ok v`, then `v` has between
1 and 133 bytes. Source: `crypto/lib.rs`, which makes a buffer of 133 bytes, rejects the lengths 0
and more than 133, and cuts the buffer to the length that BoringSSL reports. -/
def EcPointPointToOctSpec : Prop :=
  PointToOctLenLaw keystore2_crypto.ec_point_point_to_oct

/-- Law for the lengths of the result of an AES-GCM encryption. If `enc m k` returns `Ok
(ciphertext, iv, tag)`, then the ciphertext is as long as `m`, the IV has 12 bytes and the tag has
16 bytes. Nothing is said when the call returns `Err` or panics. -/
def AesGcmEncryptLenLaw
    (enc : Slice Std.U8 → Slice Std.U8 → Result (core.result.Result
      (alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8)
      keystore2_crypto.error.Error)) : Prop :=
  ∀ m k ct iv tag, enc m k = ok (.Ok (ct, iv, tag)) →
    ct.val.length = m.length ∧ iv.val.length = 12 ∧ tag.val.length = 16

/-- Law for `keystore2_crypto::aes_gcm_encrypt` (register record
`ks2-ext-keystore2-crypto-aes-gcm-encrypt`). If the call returns `Ok (ciphertext, iv, tag)`, the
lengths are those of `AesGcmEncryptLenLaw`. Source: `crypto/lib.rs`, which makes the three buffers
with `vec![0; plaintext.len()]`, `vec![0; GCM_IV_LENGTH]` and `vec![0; TAG_LENGTH]` and does not
resize them. -/
def AesGcmEncryptSpec : Prop :=
  AesGcmEncryptLenLaw keystore2_crypto.aes_gcm_encrypt

/-- Law for the length of the result of an AES-GCM decryption, over the observation `deref` of a
secret vector as a slice. If `dec data iv tag key` returns `Ok p`, then `p` is as long as `data`.
Nothing is said when the call returns `Err` or panics. -/
def AesGcmDecryptLenLaw {Z : Type} (deref : Z → Result (Slice Std.U8))
    (dec : Slice Std.U8 → Slice Std.U8 → Slice Std.U8 → Slice Std.U8 →
      Result (core.result.Result Z keystore2_crypto.error.Error)) : Prop :=
  ∀ data iv tag key p, dec data iv tag key = ok (.Ok p) →
    ∃ s, deref p = ok s ∧ s.length = data.length

/-- Law for `keystore2_crypto::aes_gcm_decrypt` (register record
`ks2-ext-keystore2-crypto-aes-gcm-decrypt`). If the call returns `Ok p`, then `p` is as long as the
ciphertext. The view of `p` as a slice is the `deref` axiom of `ZVec`. Source: `crypto/lib.rs`,
which makes the vector with `ZVec::new(data.len())` and returns it unshortened. -/
def AesGcmDecryptSpec : Prop :=
  AesGcmDecryptLenLaw zvecDeref keystore2_crypto.aes_gcm_decrypt

end Keystore2Verify.EcCrypto
