import Keystore2Verify.Specs.Defs.SwKeyblob

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open alloc.vec

/-! Each statement fixes one outcome of the calls that `export_key` makes and says what the
function returns. `ParsesTo` is the call of `new_from_serialized`, `comb` is the hardware
enforced parameters followed by the software enforced ones, and the tag lookups are
`get_tag_value` on `comb`. The outcomes of the opaque functions `hidden_params`,
`deserialize_params`, `serialize_params` and `get_tag_value` are hypotheses. -/

/-- conditional: if `hidden_params` panics, `export_key` panics in the same way. The translated
`hidden_params` returns a vector, never `Err`, so there is no error case to state. It is the
first call of `export_key`. Hypothesis: the panic `x` as the outcome of `hidden_params` on
`params` and the software root of trust. -/
theorem export_key_fail_hidden (data : Slice Std.U8) (params : Slice KeyParam) (x : Error)
    (hh : sw_keyblob.hidden_params params
      (Array.to_slice (Array.make 1#usize [sw_keyblob.SOFTWARE_ROOT_OF_TRUST])) = fail x) :
    sw_keyblob.export_key data params = fail x := by
  sorry

/-- conditional: if `export_key` returns `Ok`, the blob passed the MAC check. There is a hidden
input `hidden`, the outcome of `hidden_params` on `params` (`HiddenOf`), such that the blob has at
least 21 bytes and its last 8 bytes equal the MAC computed over the other bytes and `hidden`
(`MacOk`). The outcome of `hidden_params` is derived from the observed success, not assumed. This
is a fact about the control flow of the function; it says nothing about the strength of the MAC.
Hypotheses: the laws `CoreMemSizeOfSpec` and `Shared0SliceNeSpec`. -/
theorem export_key_ok_mac (hsize : CoreMemSizeOfSpec) (hne : Shared0SliceNeSpec)
    (data : Slice Std.U8) (params : Slice KeyParam)
    (out : KeyFormat.KeyFormat × alloc.vec.Vec Std.U8 × alloc.vec.Vec KeyParam)
    (h : sw_keyblob.export_key data params = ok (.Ok out)) :
    ∃ hidden, HiddenOf params hidden ∧ MacOk data hidden := by
  sorry

/-- conditional: a blob of fewer than 21 bytes gives an error whose root cause is
`INVALID_KEY_BLOB`. Hypotheses: `HiddenOf` (the outcome of `hidden_params`), `BlobErrFmtLaws`, and
the law `CoreMemSizeOfSpec`. -/
theorem export_key_err_short (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : CoreMemSizeOfSpec) (data : Slice Std.U8) (params hidden : Slice KeyParam)
    (hid : HiddenOf params hidden) (h : data.val.length < minBlobLen) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e := by
  sorry

/-- conditional: if the MAC of the blob does not match, `export_key` returns an error whose root
cause is `INVALID_KEY_BLOB`. Hypotheses: `HiddenOf`, the blob has at least 21 bytes, the outcome
of `compute_hmac` on all bytes but the last 8 (`s`) and the hidden input, the last 8 bytes
differ from it, `BlobErrLaws`, and the laws `CoreMemSizeOfSpec` and `Shared0SliceNeSpec`. -/
theorem export_key_err_mac (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hsize : CoreMemSizeOfSpec) (hne : Shared0SliceNeSpec) (data : Slice Std.U8)
    (params hidden : Slice KeyParam) (hid : HiddenOf params hidden)
    (h : minBlobLen ≤ data.val.length) (s : Slice Std.U8)
    (hs : s.val = data.val.take (data.val.length - 8)) (m : alloc.vec.Vec Std.U8)
    (hmac : sw_keyblob.KeyBlob.compute_hmac s hidden = ok (.Ok m))
    (hbad : data.val.drop (data.val.length - 8) ≠ m.val) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e := by
  sorry

/-- conditional: if the parser returns `Err e`, then `export_key` returns the same
error `e`: the error value is passed through unchanged. This covers every error of
`new_from_serialized`. Hypothesis: `ParsesTo` with the result `Err e`. -/
theorem export_key_err_parse (data : Slice Std.U8)
    (params : Slice KeyParam) (e : anyhow.Error)
    (hp : ParsesTo data params (ok (.Err e))) :
    sw_keyblob.export_key data params = ok (.Err e) := by
  sorry

/-- conditional: if the parser panics, then `export_key` panics in the same way. Hypothesis:
`ParsesTo` with the panic `x`. -/
theorem export_key_fail_parse (data : Slice Std.U8) (params : Slice KeyParam) (x : Error)
    (hp : ParsesTo data params (fail x)) :
    sw_keyblob.export_key data params = fail x := by
  sorry

/-- conditional: a blob with a good MAC can still make `export_key` panic. If both parameter
lists parse and fewer than 8 bytes are left, the slice `data[8..]` in the parser is out of range
and `export_key` panics (`sw_keyblob.rs:255`). The parser reads from the whole blob, the MAC
bytes included. Hypotheses: `HiddenOf`, `PastKey` (the MAC is good, the version is 0, and the
key material fits), both calls of `deserialize_params` return `Ok`, the slice `d4` that is left
is shorter than 8 bytes, and the laws `CoreMemSizeOfSpec`, `Shared0SliceNeSpec`,
`CoreSliceFirstSpec` and `CoreNumU32FromNeBytesSpec`. -/
theorem export_key_fail_rest (hsize : CoreMemSizeOfSpec) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (params hidden : Slice KeyParam) (hid : HiddenOf params hidden)
    (hpast : PastKey data hidden) (d2 : Slice Std.U8)
    (hd2 : d2.val = data.val.drop (5 + u32At data.val 1))
    (hw : alloc.vec.Vec KeyParam) (d3 : Slice Std.U8)
    (hdes1 : sw_keyblob.deserialize_params d2 = ok (.Ok hw, d3))
    (sw : alloc.vec.Vec KeyParam) (d4 : Slice Std.U8)
    (hdes2 : sw_keyblob.deserialize_params d3 = ok (.Ok sw, d4))
    (hrest : d4.val.length < 8) :
    ∃ x, sw_keyblob.export_key data params = fail x := by
  sorry

/-- conditional: if the parser returns a blob whose two parameter lists do not fit in one vector,
`export_key` panics. Hypotheses: `ParsesTo` with `Ok kb`, and the lengths of the two lists add up
to more than `Usize.max`. That is the bound of the Aeneas vector model (`CombinedFits`); in Rust
the panic comes at the lower limit of `isize::MAX` bytes, which for `KeyParameter` is a smaller
count. So this statement describes the model and is not a capacity guarantee for the Rust code. -/
theorem export_key_fail_capacity (data : Slice Std.U8) (params : Slice KeyParam)
    (kb : sw_keyblob.KeyBlob) (hp : ParsesTo data params (ok (.Ok kb)))
    (hover : ¬ CombinedFits kb) :
    ∃ x, sw_keyblob.export_key data params = fail x := by
  sorry

/-- conditional: if no parameter has the tag `ALGORITHM`, `export_key` returns an error whose root
cause is `INVALID_KEY_BLOB`. Hypotheses: `ParsesTo` with `Ok kb`, `comb` is the two lists joined,
they fit, `get_tag_value comb ALGORITHM` returns `none`, `BlobErrLaws`, and the law
`KeyParameterCloneLaw`. The bound in `hfit` is that of the Aeneas vector model (see
`CombinedFits`): Rust's limit of `isize::MAX` bytes is reached earlier, so this statement
describes the model and is not a capacity guarantee for the Rust code. -/
theorem export_key_err_no_algorithm (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hclone : KeyParameterCloneLaw) (data : Slice Std.U8) (params : Slice KeyParam)
    (kb : sw_keyblob.KeyBlob) (hp : ParsesTo data params (ok (.Ok kb)))
    (comb : Slice KeyParam) (hcomb : CombinedOf kb comb) (hfit : CombinedFits kb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok none) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e := by
  sorry

/-- conditional: if the first `ALGORITHM` value is not `Algorithm` of AES, triple DES, HMAC, RSA
or EC (ML-DSA, any other integer, or a value of another kind), `export_key` returns an error whose
root cause is `INVALID_KEY_BLOB`. Hypotheses: as for `export_key_err_no_algorithm`, with
`BlobErrFmtLaws` in place of `BlobErrLaws`, `get_tag_value` returning `some v` and `v` not a
`KnownAlgorithm`, and the law `KeyParameterCloneLaw`. The bound in `hfit` is that of the Aeneas
vector model (see `CombinedFits`): Rust's limit of `isize::MAX` bytes is reached earlier, so this
statement describes the model and is not a capacity guarantee for the Rust code. -/
theorem export_key_err_algorithm (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hclone : KeyParameterCloneLaw) (data : Slice Std.U8) (params : Slice KeyParam)
    (kb : sw_keyblob.KeyBlob) (hp : ParsesTo data params (ok (.Ok kb)))
    (comb : Slice KeyParam) (hcomb : CombinedOf kb comb) (hfit : CombinedFits kb)
    (v : ParamValue) (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some v))
    (hv : ¬ KnownAlgorithm v) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e := by
  sorry

/-- conditional: for an AES, triple DES or HMAC key, `export_key` returns `Ok` of the format
`RAW`, the key material of the blob without change, and the two parameter lists joined (hardware
enforced first). In the Rust source this branch does not look up the curve. Hypotheses: as for
`export_key_err_no_algorithm` without `BlobErrLaws`, with `get_tag_value` returning `Algorithm(a)`
for a `RawAlgorithm a`, and the law `KeyParameterCloneLaw`. The bound in `hfit` is that of the
Aeneas vector model (see `CombinedFits`): Rust's limit of `isize::MAX` bytes is reached earlier,
so this statement describes the model and is not a capacity guarantee for the Rust code. -/
theorem export_key_ok_raw (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb) (hfit : CombinedFits kb) (a : Algorithm.Algorithm)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV a)))
    (ha : RawAlgorithm a) :
    ∃ c, sw_keyblob.export_key data params
        = ok (.Ok (KeyFormat.KeyFormat.RAW, kb.key_material, c)) ∧ c.val = comb.val := by
  sorry

/-- conditional: for an RSA key, `export_key` returns an error whose root cause is
`INVALID_KEY_BLOB`: the format is `PKCS8` but no arm handles it. An RSA key never succeeds.
Hypotheses: as for `export_key_ok_raw`, with `Algorithm(RSA)`, and `BlobErrFmtLaws`. The bound in
`hfit` is that of the Aeneas vector model (see `CombinedFits`): Rust's limit of `isize::MAX` bytes
is reached earlier, so this statement describes the model and is not a capacity guarantee for the
Rust code. -/
theorem export_key_err_rsa (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hclone : KeyParameterCloneLaw) (data : Slice Std.U8) (params : Slice KeyParam)
    (kb : sw_keyblob.KeyBlob) (hp : ParsesTo data params (ok (.Ok kb)))
    (comb : Slice KeyParam) (hcomb : CombinedOf kb comb) (hfit : CombinedFits kb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algRSA))) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e := by
  sorry

/-- conditional: for an EC key with no parameter that has the tag `EC_CURVE`, `export_key` returns
an error whose root cause is `INVALID_KEY_BLOB`. Hypotheses: as for `export_key_ok_raw`, with
`Algorithm(EC)`, `get_tag_value comb EC_CURVE` returning `none`, and `BlobErrLaws`. The bound in
`hfit` is that of the Aeneas vector model (see `CombinedFits`): Rust's limit of `isize::MAX` bytes
is reached earlier, so this statement describes the model and is not a capacity guarantee for the
Rust code. -/
theorem export_key_err_no_curve (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hclone : KeyParameterCloneLaw) (data : Slice Std.U8) (params : Slice KeyParam)
    (kb : sw_keyblob.KeyBlob) (hp : ParsesTo data params (ok (.Ok kb)))
    (comb : Slice KeyParam) (hcomb : CombinedOf kb comb) (hfit : CombinedFits kb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = ok none) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e := by
  sorry

/-- conditional: if `get_tag_value comb ALGORITHM` panics, `export_key` panics in the same way.
The translated `get_tag_value` returns an `Option`, never `Err`, so there is no error case to
state. Hypotheses: `ParsesTo` with `Ok kb`, `comb` is the two lists joined, they fit, the panic
`x` as the outcome of `get_tag_value`, and the law `KeyParameterCloneLaw`. The bound in `hfit` is
that of the Aeneas vector model (see `CombinedFits`): Rust's limit of `isize::MAX` bytes is
reached earlier, so this statement describes the model and is not a capacity guarantee for the
Rust code. -/
theorem export_key_fail_get_algorithm (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb) (hfit : CombinedFits kb) (x : Error)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = fail x) :
    sw_keyblob.export_key data params = fail x := by
  sorry

/-- conditional: for an EC key, if `get_tag_value comb EC_CURVE` panics, `export_key` panics in
the same way. Hypotheses: as for `export_key_fail_get_algorithm`, with `Algorithm(EC)` as the
outcome of the first lookup and the panic `x` as the outcome of the second. The bound in `hfit`
is that of the Aeneas vector model (see `CombinedFits`): Rust's limit of `isize::MAX` bytes is
reached earlier, so this statement describes the model and is not a capacity guarantee for the
Rust code. -/
theorem export_key_fail_get_curve (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb) (hfit : CombinedFits kb) (x : Error)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = fail x) :
    sw_keyblob.export_key data params = fail x := by
  sorry

/-- conditional: for an EC key whose first `EC_CURVE` value is not `EcCurve` of P-224, P-256,
P-384, P-521 or Curve25519, `export_key` returns an error whose root cause is `INVALID_KEY_BLOB`.
Hypotheses: as for `export_key_err_no_curve`, with `BlobErrFmtLaws` in place of `BlobErrLaws`,
`get_tag_value comb EC_CURVE` returning `some cv` and `cv` not a `KnownCurve`. The bound in `hfit`
is that of the Aeneas vector model (see `CombinedFits`): Rust's limit of `isize::MAX` bytes is
reached earlier, so this statement describes the model and is not a capacity guarantee for the
Rust code. -/
theorem export_key_err_curve (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hclone : KeyParameterCloneLaw) (data : Slice Std.U8) (params : Slice KeyParam)
    (kb : sw_keyblob.KeyBlob) (hp : ParsesTo data params (ok (.Ok kb)))
    (comb : Slice KeyParam) (hcomb : CombinedOf kb comb) (hfit : CombinedFits kb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (cv : ParamValue) (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = ok (some cv))
    (hcv : ¬ KnownCurve cv) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e := by
  sorry

/-- conditional: for an EC key on Curve25519, `export_key` returns `Ok` of the format `PKCS8`, the
key material of the blob without change, and the two parameter lists joined. In the Rust source
this branch neither checks nor wraps the key material. Hypotheses: as for
`export_key_err_no_curve` without `BlobErrLaws`, with `get_tag_value comb EC_CURVE` returning
`EcCurve(CURVE_25519)` in place of `none`. The bound in `hfit` is that of the Aeneas vector model
(see `CombinedFits`): Rust's limit of `isize::MAX` bytes is reached earlier, so this statement
describes the model and is not a capacity guarantee for the Rust code. -/
theorem export_key_ok_curve25519 (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb) (hfit : CombinedFits kb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = ok (some (curveV curve25519))) :
    ∃ c, sw_keyblob.export_key data params
        = ok (.Ok (KeyFormat.KeyFormat.PKCS8, kb.key_material, c)) ∧ c.val = comb.val := by
  sorry

/-- conditional: for an EC key on a NIST curve whose wrapped content is at most `0xffff` bytes
long, `export_key` returns `Ok` of the format `PKCS8`, the PKCS#8 `PrivateKeyInfo` of the key
material (`pkcs8Wrap`, built with the algorithm identifier `alg` of the curve), and the two
parameter lists joined. `pkcs8_wrap_nist_key` is translated, so its outcome is derived, not
assumed. The success path of `pkcs8_wrap_nist_key` evaluates no opaque call, and no push on it
comes near the capacity bound. Hypotheses: as for `export_key_err_no_curve` without `BlobErrLaws`,
with `get_tag_value comb EC_CURVE` returning `EcCurve(c)` in place of `none`, `alg` the identifier
of `c`, and the length of the content `pkcs8Body alg key` at most `0xffff`. The bound in `hfit` is
that of the Aeneas vector model (see `CombinedFits`): Rust's limit of `isize::MAX` bytes is
reached earlier, so this statement describes the model and is not a capacity guarantee for the
Rust code. -/
theorem export_key_ok_nist (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb) (hfit : CombinedFits kb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (c : EcCurve.EcCurve)
    (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = ok (some (curveV c)))
    (alg : Slice Std.U8) (hc : NistAlgId c alg)
    (hbody : (pkcs8Body (nums alg.val) (nums (Vec.deref kb.key_material).val)).length ≤ 0xffff) :
    ∃ w cs, sw_keyblob.export_key data params = ok (.Ok (KeyFormat.KeyFormat.PKCS8, w, cs)) ∧
      nums w.val = pkcs8Wrap (nums alg.val) (nums (Vec.deref kb.key_material).val) ∧
      cs.val = comb.val := by
  sorry

/-- conditional: for an EC key on a NIST curve and a key material longer than `0xffff` bytes,
`export_key` returns an error whose root cause is `INVALID_KEY_BLOB` (`pkcs8_wrap_nist_key` cannot
encode the length). Hypotheses: as for `export_key_ok_nist`, with `c` a `NistCurve` in place of
`alg` and the bound on the content, the key material longer than `0xffff` bytes, and
`BlobErrFmtLaws`. The bound in `hfit` is that of the Aeneas vector model (see `CombinedFits`):
Rust's limit of `isize::MAX` bytes is reached earlier, so this statement describes the model and
is not a capacity guarantee for the Rust code. -/
theorem export_key_err_nist_key_len (root : anyhow.Error → ErrRoot)
    (hlaw : BlobErrFmtLaws root) (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb) (hfit : CombinedFits kb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (c : EcCurve.EcCurve)
    (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = ok (some (curveV c)))
    (hc : NistCurve c) (hkey : 0xffff < (Vec.deref kb.key_material).val.length) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e := by
  sorry

/-- conditional: for an EC key on a NIST curve, a key material of at most `0xffff` bytes and a
wrapped content longer than `0xffff` bytes, `export_key` returns an error whose root cause is
`INVALID_KEY_BLOB`. Together with `export_key_ok_nist` and `export_key_err_nist_key_len` this
covers every outcome of `pkcs8_wrap_nist_key` on a NIST curve, under `BlobErrFmtLaws`. Those laws
keep the opaque calls that build the error (`Error::new`, `format`, `context`) from panicking;
without them a panic is possible on the two error paths. The success path evaluates no opaque
call: the generated body only pushes, extends, measures lengths and adds small numbers, and no
push comes near the capacity bound. Hypotheses: as for `export_key_ok_nist`, with the key at most
`0xffff` bytes, the content longer than `0xffff` bytes in place of the bound on it, and
`BlobErrFmtLaws`. The bound in `hfit` is that of the Aeneas vector model (see `CombinedFits`):
Rust's limit of `isize::MAX` bytes is reached earlier, so this statement describes the model and
is not a capacity guarantee for the Rust code. -/
theorem export_key_err_nist_body_len (root : anyhow.Error → ErrRoot)
    (hlaw : BlobErrFmtLaws root) (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb) (hfit : CombinedFits kb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (c : EcCurve.EcCurve)
    (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = ok (some (curveV c)))
    (alg : Slice Std.U8) (hc : NistAlgId c alg)
    (hkey : (Vec.deref kb.key_material).val.length ≤ 0xffff)
    (hbody : 0xffff < (pkcs8Body (nums alg.val) (nums (Vec.deref kb.key_material).val)).length) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e := by
  sorry
end Keystore2Verify.SwKeyblob
