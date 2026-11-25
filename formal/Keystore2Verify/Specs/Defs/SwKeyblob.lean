import Keystore2Verify.Specs.Defs.Externals

/-!
# Definitions for the statements about `sw_keyblob.rs`

The code parses a software key blob: a version byte, the key material, two lists of key
parameters and an 8 byte MAC. The definitions below name the byte layouts that the statements
talk about, the error class that every `bloberr!` error has, the shared laws that the error
paths need, and the one law this file adds (the clone of a `KeyParameter`). Nothing here is an
axiom.
-/

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open keystore2_crypto.error.Error.Insts renaming CoreErrorError → cryptoErrorError
open anyhow.Error.Insts.CoreConvertFrom renaming «from» → anyhowFrom
open KeyParameter.KeyParameter.Insts.CoreCloneClone renaming clone → keyParamClone
open alloc.vec
open anyhow.error.Error renaming new → anyhowNew, context → anyhowContext
open error.Error.Insts renaming CoreErrorError → ksErrorError
open alloc.string.String.Insts renaming CoreFmtDisplay → stringDisplay

/-- A key parameter of the AIDL interface. -/
abbrev KeyParam := KeyParameter.KeyParameter

/-- The value of a key parameter. -/
abbrev ParamValue := KeyParameterValue.KeyParameterValue

/-- The parameter value `Algorithm(a)`. -/
abbrev algV (a : Algorithm.Algorithm) : ParamValue :=
  KeyParameterValue.KeyParameterValue.Algorithm a

/-- The parameter value `EcCurve(c)`. -/
abbrev curveV (c : EcCurve.EcCurve) : ParamValue := KeyParameterValue.KeyParameterValue.EcCurve c

/-! ## Constants of the AIDL interface

The translation keeps these enum values only as literals in `match` arms, so the values are
written here (AIDL `Algorithm` and `EcCurve`). -/

/-- `Algorithm::RSA` -/
def algRSA : Algorithm.Algorithm := 1#i32

/-- `Algorithm::EC` -/
def algEC : Algorithm.Algorithm := 3#i32

/-- `Algorithm::AES` -/
def algAES : Algorithm.Algorithm := 32#i32

/-- `Algorithm::TRIPLE_DES` -/
def algTripleDes : Algorithm.Algorithm := 33#i32

/-- `Algorithm::HMAC` -/
def algHMAC : Algorithm.Algorithm := 128#i32

/-- `EcCurve::CURVE_25519` -/
def curve25519 : EcCurve.EcCurve := 4#i32

/-! ## Errors -/

/-- The error `e` has the root cause `Error::Km(ErrorCode::INVALID_KEY_BLOB)`. Every error that
the `bloberr!` macro makes has this root cause. The classifier `root` is the shared observation
of `anyhow::Error`. -/
def IsBlobErr (root : anyhow.Error → ErrRoot) (e : anyhow.Error) : Prop :=
  root e = ErrRoot.ks (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)

/-- The shared laws that the `bloberr!` macro needs: `anyhow::Error::new` of a keystore2 error
(`ErrorNewLaw`), `Error::context` with a `String` (`ErrorContextLaw`), `format` and
`from_str_nonconst`. With them, each `bloberr!` error has the root cause of `IsBlobErr`. -/
def BlobErrLaws (root : anyhow.Error → ErrRoot) : Prop :=
  ErrorNewLaw root ErrRoot.ks (anyhowNew ksErrorError) ∧
  ErrorContextLaw root (anyhowContext stringDisplay) ∧
  AllocFmtFormatSpec ∧ CoreFmtArgumentsFromStrNonconstSpec

/-- The shared law `ErrorFromLaw` for the conversion of a `keystore2_crypto` error into an
`anyhow::Error`, which `?` applies to the result of `hmac_sha256`. -/
def CryptoFromLaw (root : anyhow.Error → ErrRoot) : Prop :=
  ErrorFromLaw root ErrRoot.crypto
    (anyhowFrom cryptoErrorError)

/-- Law for the clone of a `KeyParameter` (register record
`ks2-ext-android-hardware-security-keymint-aidl-android-hardware-security-keymint-keyparameter-keyparameter-insts-corecloneclone-clone`).
`clone p` never panics and returns a value equal to `p`. Idealisation: allocation never fails.
Source: the AIDL stand-in derives `Clone` for `KeyParameter`, and a derived clone copies each
field. -/
def KeyParameterCloneLaw : Prop :=
  ∀ p : KeyParam,
    keyParamClone p = ok p

/-! ## Bytes -/

/-- The numbers of a list of bytes. -/
def nums (l : List Std.U8) : List Nat := l.map (·.val)

/-- The little-endian number made of the 4 bytes of `l` that start at index `i`. It is the value
that `u32::from_ne_bytes` gives on a little-endian target (the law `CoreNumU32FromNeBytesSpec`).
When fewer than 4 bytes remain, the missing high bytes count as 0. -/
def u32At (l : List Std.U8) (i : Nat) : Nat := leNat ((l.drop i).take 4)

/-- The DER encoding of a length, as numbers: `[n]` up to `0x7f`, `[0x81, n]` up to `0xff` and
`[0x82, n / 256, n % 256]` up to `0xffff`. It is used as a DER encoding only for
`n ≤ 0xffff`; for larger values the definition gives a value that nothing relies on. -/
def derLen (n : Nat) : List Nat :=
  if n ≤ 0x7f then [n]
  else if n ≤ 0xff then [0x81, n]
  else [0x82, n / 256, n % 256]

/-- The content of the PKCS#8 `PrivateKeyInfo` that wraps the key `key` for the algorithm
identifier `alg`: the version `[2, 1, 0]`, `alg`, and the octet string `[4] ++ derLen n ++ key`. -/
def pkcs8Body (alg key : List Nat) : List Nat :=
  [2, 1, 0] ++ alg ++ ([4] ++ derLen key.length ++ key)

/-- The whole `PrivateKeyInfo`: the byte `0x30`, the DER length of the content, and the
content. -/
def pkcs8Wrap (alg key : List Nat) : List Nat :=
  [0x30] ++ derLen (pkcs8Body alg key).length ++ pkcs8Body alg key

/-- `alg` is the constant `AlgorithmIdentifier` that the code uses for the NIST curve `curve`. -/
def NistAlgId (curve : EcCurve.EcCurve) (alg : Slice Std.U8) : Prop :=
  (curve = EcCurve.EcCurve.P_224 ∧ alg = sw_keyblob.DER_ALGORITHM_ID_P224) ∨
  (curve = EcCurve.EcCurve.P_256 ∧ alg = sw_keyblob.DER_ALGORITHM_ID_P256) ∨
  (curve = EcCurve.EcCurve.P_384 ∧ alg = sw_keyblob.DER_ALGORITHM_ID_P384) ∨
  (curve = EcCurve.EcCurve.P_521 ∧ alg = sw_keyblob.DER_ALGORITHM_ID_P521)

/-- `curve` is one of the four NIST curves that `pkcs8_wrap_nist_key` knows. -/
def NistCurve (curve : EcCurve.EcCurve) : Prop := ∃ alg, NistAlgId curve alg

/-! ## Blobs -/

/-- The least length of a blob: the version byte, three 4 byte lengths and the 8 byte MAC. -/
def minBlobLen : Nat := 21

/-- The shared outcome of the first checks of `new_from_serialized`, up to the MAC check. The
blob has at least `minBlobLen` bytes, and the call `compute_hmac` on all bytes but the last 8
returns a MAC that equals the last 8 bytes. -/
def MacOk (data : Slice Std.U8) (hidden : Slice KeyParam) : Prop :=
  minBlobLen ≤ data.val.length ∧
  ∃ (s : Slice Std.U8) (m : alloc.vec.Vec Std.U8),
    s.val = data.val.take (data.val.length - 8) ∧
    sw_keyblob.KeyBlob.compute_hmac s hidden = ok (.Ok m) ∧
    data.val.drop (data.val.length - 8) = m.val

/-- All checks of `new_from_serialized` before the parameter lists pass: the MAC is good (`MacOk`),
the version byte is 0, and the length of the key material fits in the bytes after it. -/
def PastKey (data : Slice Std.U8) (hidden : Slice KeyParam) : Prop :=
  MacOk data hidden ∧ data.val.head? = some 0#u8 ∧ u32At data.val 1 ≤ data.val.length - 5

/-- The slice `hidden` is the hidden input that `export_key` builds for `params`: the result of
`hidden_params` on `params` and the software root of trust. The statement assumes the result of
`hidden_params`, which the translation leaves opaque. -/
def HiddenOf (params hidden : Slice KeyParam) : Prop :=
  ∃ (rots : Slice (Slice Std.U8)) (hv : alloc.vec.Vec KeyParam),
    rots = Array.to_slice (Array.make 1#usize [sw_keyblob.SOFTWARE_ROOT_OF_TRUST]) ∧
    sw_keyblob.hidden_params params rots = ok hv ∧ hidden = Vec.deref hv

/-- The call `new_from_serialized` that `export_key` makes has the result `r`: it parses `data`
with the hidden input of `params` (`HiddenOf`). -/
def ParsesTo (data : Slice Std.U8) (params : Slice KeyParam)
    (r : Result (core.result.Result sw_keyblob.KeyBlob anyhow.Error)) : Prop :=
  ∃ hidden, HiddenOf params hidden ∧ sw_keyblob.KeyBlob.new_from_serialized data hidden = r

/-- The slice `comb` holds the hardware enforced parameters of `kb` and then the software
enforced ones. -/
def CombinedOf (kb : sw_keyblob.KeyBlob) (comb : Slice KeyParam) : Prop :=
  comb.val = kb.hw_enforced.val ++ kb.sw_enforced.val

/-- The two parameter lists of `kb` fit together in one vector, in the sense of the Aeneas vector
model: the combined element count is at most `usize::MAX`. Rust is stricter. A `Vec` may hold at
most `isize::MAX` bytes, a limit that is reached earlier, and for `KeyParameter` the element size
lowers the count further. Between the two bounds the model returns a value where Rust panics with
a capacity overflow. So the statements that use this definition describe the model. They are not
a capacity guarantee for the Rust code. -/
def CombinedFits (kb : sw_keyblob.KeyBlob) : Prop :=
  kb.hw_enforced.length + kb.sw_enforced.length ≤ Std.Usize.max

/-! ## Algorithms and curves -/

/-- The algorithms whose key `export_key` returns as it is: AES, triple DES and HMAC. -/
def RawAlgorithm (a : Algorithm.Algorithm) : Prop :=
  a = algAES ∨ a = algTripleDes ∨
    a = algHMAC

/-- The values that `export_key` accepts for the algorithm: `Algorithm(a)` where `a` is a raw
algorithm, RSA or EC. -/
def KnownAlgorithm (v : ParamValue) : Prop :=
  ∃ a, v = algV a ∧ (RawAlgorithm a ∨ a = algRSA ∨ a = algEC)

/-- The values that `export_key` accepts for the curve: `EcCurve(c)` where `c` is Curve25519 or
one of the four NIST curves. -/
def KnownCurve (v : ParamValue) : Prop :=
  ∃ c, v = curveV c ∧ (c = curve25519 ∨ NistCurve c)

end Keystore2Verify.SwKeyblob
