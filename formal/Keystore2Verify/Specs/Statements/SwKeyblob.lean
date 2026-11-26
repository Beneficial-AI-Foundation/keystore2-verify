import Keystore2Verify.Proofs.SwKeyblob.TagType
import Keystore2Verify.Proofs.SwKeyblob.AddDerLen
import Keystore2Verify.Proofs.SwKeyblob.Pkcs8WrapNistKey
import Keystore2Verify.Proofs.SwKeyblob.ConsumeU8
import Keystore2Verify.Proofs.SwKeyblob.ConsumeBool
import Keystore2Verify.Proofs.SwKeyblob.ConsumeU32
import Keystore2Verify.Proofs.SwKeyblob.ConsumeI32
import Keystore2Verify.Proofs.SwKeyblob.ConsumeI64
import Keystore2Verify.Proofs.SwKeyblob.ConsumeVec
import Keystore2Verify.Proofs.SwKeyblob.ConsumeBlob
import Keystore2Verify.Proofs.SwKeyblob.ComputeHmac
import Keystore2Verify.Proofs.SwKeyblob.NewFromSerialized
import Keystore2Verify.Proofs.SwKeyblob.ExportKey

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open alloc.vec

recall tag_type_bv (tag : Tag.Tag) :
    ∃ t, sw_keyblob.tag_type tag = ok t ∧ t.bv = tag.bv &&& 0xF0000000#32

/-- info: 'Keystore2Verify.SwKeyblob.tag_type_bv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tag_type_bv

recall tag_type_same_top_bits (t1 t2 : Tag.Tag) (h : t1.bv >>> 28 = t2.bv >>> 28) :
    ∃ r, sw_keyblob.tag_type t1 = ok r ∧ sw_keyblob.tag_type t2 = ok r

/-- info: 'Keystore2Verify.SwKeyblob.tag_type_same_top_bits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tag_type_same_top_bits

recall add_der_len_ok (buf : alloc.vec.Vec Std.U8) (len : Std.Usize)
    (hlen : len.val ≤ 0xffff)
    (hcap : buf.val.length + (derLen len.val).length ≤ Std.Usize.max) :
    ∃ buf', sw_keyblob.add_der_len buf len = ok (.Ok (), buf') ∧
      nums buf'.val = nums buf.val ++ derLen len.val

/-- info: 'Keystore2Verify.SwKeyblob.add_der_len_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms add_der_len_ok

recall add_der_len_fail_capacity (buf : alloc.vec.Vec Std.U8) (len : Std.Usize)
    (hlen : len.val ≤ 0xffff)
    (hover : Std.Usize.max < buf.val.length + (derLen len.val).length) :
    sw_keyblob.add_der_len buf len = fail .maximumSizeExceeded

/-- info: 'Keystore2Verify.SwKeyblob.add_der_len_fail_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms add_der_len_fail_capacity

recall add_der_len_err (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (buf : alloc.vec.Vec Std.U8) (len : Std.Usize) (hlen : 0xffff < len.val) :
    ∃ e, sw_keyblob.add_der_len buf len = ok (.Err e, buf) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.add_der_len_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms add_der_len_err

recall pkcs8_wrap_nist_key_ok (nist_key : Slice Std.U8) (curve : EcCurve.EcCurve)
    (alg : Slice Std.U8) (hc : NistAlgId curve alg)
    (hbody : (pkcs8Body (nums alg.val) (nums nist_key.val)).length ≤ 0xffff) :
    ∃ out, sw_keyblob.pkcs8_wrap_nist_key nist_key curve = ok (.Ok out) ∧
      nums out.val = pkcs8Wrap (nums alg.val) (nums nist_key.val)

/-- info: 'Keystore2Verify.SwKeyblob.pkcs8_wrap_nist_key_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms pkcs8_wrap_nist_key_ok

recall pkcs8_wrap_nist_key_err_curve (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (nist_key : Slice Std.U8) (curve : EcCurve.EcCurve) (hc : ¬ NistCurve curve) :
    ∃ e, sw_keyblob.pkcs8_wrap_nist_key nist_key curve = ok (.Err e) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.pkcs8_wrap_nist_key_err_curve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms pkcs8_wrap_nist_key_err_curve

recall pkcs8_wrap_nist_key_err_key_len (root : anyhow.Error → ErrRoot)
    (hlaw : BlobErrFmtLaws root) (nist_key : Slice Std.U8) (curve : EcCurve.EcCurve)
    (hc : NistCurve curve) (hkey : 0xffff < nist_key.val.length) :
    ∃ e, sw_keyblob.pkcs8_wrap_nist_key nist_key curve = ok (.Err e) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.pkcs8_wrap_nist_key_err_key_len' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms pkcs8_wrap_nist_key_err_key_len

recall pkcs8_wrap_nist_key_err_body_len (root : anyhow.Error → ErrRoot)
    (hlaw : BlobErrFmtLaws root) (nist_key : Slice Std.U8) (curve : EcCurve.EcCurve)
    (alg : Slice Std.U8) (hc : NistAlgId curve alg) (hkey : nist_key.val.length ≤ 0xffff)
    (hbody : 0xffff < (pkcs8Body (nums alg.val) (nums nist_key.val)).length) :
    ∃ e, sw_keyblob.pkcs8_wrap_nist_key nist_key curve = ok (.Err e) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.pkcs8_wrap_nist_key_err_body_len' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms pkcs8_wrap_nist_key_err_body_len

recall consume_u8_err (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hfirst : CoreSliceFirstSpec) (data : Slice Std.U8) (h : data.val = []) :
    ∃ e, sw_keyblob.consume_u8 data = ok (.Err e, data) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.consume_u8_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.slice.Slice.first,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_u8_err

recall consume_u8_ok (hfirst : CoreSliceFirstSpec) (data : Slice Std.U8) (b : Std.U8)
    (rest : List Std.U8) (h : data.val = b :: rest) :
    ∃ data', sw_keyblob.consume_u8 data = ok (.Ok b, data') ∧ data'.val = rest

/-- info: 'Keystore2Verify.SwKeyblob.consume_u8_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.slice.Slice.first,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_u8_ok

recall consume_bool_err_empty (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hfirst : CoreSliceFirstSpec) (data : Slice Std.U8) (h : data.val = []) :
    ∃ e, sw_keyblob.consume_bool data = ok (.Err e, data) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.consume_bool_err_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.slice.Slice.first,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_bool_err_empty

recall consume_bool_true (hfirst : CoreSliceFirstSpec) (data : Slice Std.U8)
    (rest : List Std.U8) (h : data.val = 1#u8 :: rest) :
    ∃ data', sw_keyblob.consume_bool data = ok (.Ok true, data') ∧ data'.val = rest

/-- info: 'Keystore2Verify.SwKeyblob.consume_bool_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.slice.Slice.first,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_bool_true

recall consume_bool_err_value (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hfirst : CoreSliceFirstSpec) (data : Slice Std.U8) (b : Std.U8) (rest : List Std.U8)
    (h : data.val = b :: rest) (hb : b.val ≠ 1) :
    ∃ e data', sw_keyblob.consume_bool data = ok (.Err e, data') ∧ IsBlobErr root e ∧
      data'.val = rest

/-- info: 'Keystore2Verify.SwKeyblob.consume_bool_err_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.slice.Slice.first,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_bool_err_value

recall consume_u32_err (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8) (h : data.val.length < 4) :
    ∃ e, sw_keyblob.consume_u32 data = ok (.Err e, data) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.consume_u32_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 core.mem.size_of,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.num.U32.from_ne_bytes,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_u32_err

recall consume_u32_ok (hsize : SizeOfLaw Std.U32 4) (hfrom : CoreNumU32FromNeBytesSpec)
    (data : Slice Std.U8) (h : 4 ≤ data.val.length) :
    ∃ x data', sw_keyblob.consume_u32 data = ok (.Ok x, data') ∧
      x.val = u32At data.val 0 ∧ data'.val = data.val.drop 4

/-- info: 'Keystore2Verify.SwKeyblob.consume_u32_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 core.mem.size_of,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.num.U32.from_ne_bytes,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_u32_ok

recall consume_i32_err (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.I32 4) (data : Slice Std.U8) (h : data.val.length < 4) :
    ∃ e, sw_keyblob.consume_i32 data = ok (.Err e, data) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.consume_i32_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 core.mem.size_of,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.num.I32.from_ne_bytes,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_i32_err

recall consume_i32_ok (hsize : SizeOfLaw Std.I32 4) (hfrom : CoreNumI32FromNeBytesSpec)
    (data : Slice Std.U8) (h : 4 ≤ data.val.length) :
    ∃ x data', sw_keyblob.consume_i32 data = ok (.Ok x, data') ∧
      x.bv = BitVec.ofNat 32 (u32At data.val 0) ∧ data'.val = data.val.drop 4

/-- info: 'Keystore2Verify.SwKeyblob.consume_i32_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 core.mem.size_of,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.num.I32.from_ne_bytes,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_i32_ok

recall consume_i64_err (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.I64 8) (data : Slice Std.U8) (h : data.val.length < 8) :
    ∃ e, sw_keyblob.consume_i64 data = ok (.Err e, data) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.consume_i64_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 core.mem.size_of,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.num.I64.from_ne_bytes,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_i64_err

recall consume_i64_ok (hsize : SizeOfLaw Std.I64 8) (hfrom : CoreNumI64FromNeBytesSpec)
    (data : Slice Std.U8) (h : 8 ≤ data.val.length) :
    ∃ x data', sw_keyblob.consume_i64 data = ok (.Ok x, data') ∧
      x.bv = BitVec.ofNat 64 (leNat (data.val.take 8)) ∧ data'.val = data.val.drop 8

/-- info: 'Keystore2Verify.SwKeyblob.consume_i64_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 core.mem.size_of,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.num.I64.from_ne_bytes,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_i64_ok

recall consume_vec_err_prefix (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8) (h : data.val.length < 4) :
    ∃ e, sw_keyblob.consume_vec data = ok (.Err e, data) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.consume_vec_err_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 core.mem.size_of,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.num.U32.from_ne_bytes,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_vec_err_prefix

recall consume_vec_err_len (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (h : 4 ≤ data.val.length) (hlen : data.val.length - 4 < u32At data.val 0) :
    ∃ e data', sw_keyblob.consume_vec data = ok (.Err e, data') ∧ IsBlobErr root e ∧
      data'.val = data.val.drop 4

/-- info: 'Keystore2Verify.SwKeyblob.consume_vec_err_len' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 core.mem.size_of,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.num.U32.from_ne_bytes,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_vec_err_len

recall consume_vec_ok (hsize : SizeOfLaw Std.U32 4) (hfrom : CoreNumU32FromNeBytesSpec)
    (data : Slice Std.U8) (h : 4 ≤ data.val.length)
    (hlen : u32At data.val 0 ≤ data.val.length - 4) :
    ∃ v data', sw_keyblob.consume_vec data = ok (.Ok v, data') ∧
      v.val = (data.val.drop 4).take (u32At data.val 0) ∧
      data'.val = data.val.drop (4 + u32At data.val 0)

/-- info: 'Keystore2Verify.SwKeyblob.consume_vec_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 core.mem.size_of,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.num.U32.from_ne_bytes,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_vec_ok

recall consume_blob_err_len (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8) (next : Std.Usize)
    (blob : Slice Std.U8) (h : data.val.length < 4) :
    ∃ e, sw_keyblob.consume_blob data next blob = ok (.Err e, data, next) ∧
      IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.consume_blob_err_len' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 core.mem.size_of,
 Mut0T.Insts.CoreFmtDisplay.fmt,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.num.U32.from_ne_bytes,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_blob_err_len

recall consume_blob_err_offset (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (next : Std.Usize) (blob : Slice Std.U8) (h4 : 4 ≤ data.val.length)
    (h8 : data.val.length < 8) :
    ∃ e data', sw_keyblob.consume_blob data next blob = ok (.Err e, data', next) ∧
      IsBlobErr root e ∧ data'.val = data.val.drop 4

/-- info: 'Keystore2Verify.SwKeyblob.consume_blob_err_offset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 core.mem.size_of,
 Mut0T.Insts.CoreFmtDisplay.fmt,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.num.U32.from_ne_bytes,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_blob_err_offset

recall consume_blob_err_mismatch (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (next : Std.Usize) (blob : Slice Std.U8) (h : 8 ≤ data.val.length)
    (hoff : u32At data.val 4 ≠ next.val) :
    ∃ e data', sw_keyblob.consume_blob data next blob = ok (.Err e, data', next) ∧
      IsBlobErr root e ∧ data'.val = data.val.drop 8

/-- info: 'Keystore2Verify.SwKeyblob.consume_blob_err_mismatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 core.mem.size_of,
 Mut0T.Insts.CoreFmtDisplay.fmt,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.num.U32.from_ne_bytes,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_blob_err_mismatch

recall consume_blob_err_past_end (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (next : Std.Usize) (blob : Slice Std.U8) (h : 8 ≤ data.val.length)
    (hoff : u32At data.val 4 = next.val)
    (hfit : next.val + u32At data.val 0 ≤ Std.Usize.max)
    (hend : blob.val.length < next.val + u32At data.val 0) :
    ∃ e data', sw_keyblob.consume_blob data next blob = ok (.Err e, data', next) ∧
      IsBlobErr root e ∧ data'.val = data.val.drop 8

/-- info: 'Keystore2Verify.SwKeyblob.consume_blob_err_past_end' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 core.mem.size_of,
 Mut0T.Insts.CoreFmtDisplay.fmt,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.num.U32.from_ne_bytes,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_blob_err_past_end

recall consume_blob_fail_overflow (hsize : SizeOfLaw Std.U32 4)
    (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8) (next : Std.Usize)
    (blob : Slice Std.U8) (h : 8 ≤ data.val.length) (hoff : u32At data.val 4 = next.val)
    (hover : Std.Usize.max < next.val + u32At data.val 0) :
    sw_keyblob.consume_blob data next blob = fail .integerOverflow

/-- info: 'Keystore2Verify.SwKeyblob.consume_blob_fail_overflow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 core.mem.size_of,
 Mut0T.Insts.CoreFmtDisplay.fmt,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.num.U32.from_ne_bytes,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_blob_fail_overflow

recall consume_blob_ok (hsize : SizeOfLaw Std.U32 4) (hfrom : CoreNumU32FromNeBytesSpec)
    (data : Slice Std.U8) (next : Std.Usize) (blob : Slice Std.U8) (h : 8 ≤ data.val.length)
    (hoff : u32At data.val 4 = next.val)
    (hend : next.val + u32At data.val 0 ≤ blob.val.length) :
    ∃ v data' next', sw_keyblob.consume_blob data next blob = ok (.Ok v, data', next') ∧
      v.val = (blob.val.drop next.val).take (u32At data.val 0) ∧
      data'.val = data.val.drop 8 ∧ next'.val = next.val + u32At data.val 0

/-- info: 'Keystore2Verify.SwKeyblob.consume_blob_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 alloc.fmt.format,
 core.mem.size_of,
 Mut0T.Insts.CoreFmtDisplay.fmt,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.num.U32.from_ne_bytes,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms consume_blob_ok

recall compute_hmac_ok (htrunc : AllocVecTruncateSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (hd tag : alloc.vec.Vec Std.U8) (msg : Slice Std.U8)
    (hser : sw_keyblob.serialize_params hidden = ok (.Ok hd))
    (hmsg : msg.val = data.val ++ hd.val)
    (hhmac : keystore2_crypto.hmac_sha256 sw_keyblob.KeyBlob.LEGACY_HMAC_KEY msg
      = ok (.Ok tag)) :
    ∃ t, sw_keyblob.KeyBlob.compute_hmac data hidden = ok (.Ok t) ∧
      t.val = tag.val.take 8

/-- info: 'Keystore2Verify.SwKeyblob.compute_hmac_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.serialize_params,
 Vec.truncate,
 anyhow.Error.Insts.CoreConvertFrom.from,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms compute_hmac_ok

recall compute_hmac_ok_length (htrunc : AllocVecTruncateSpec)
    (hlen : KeystoreCryptoHmacSha256Spec) (data : Slice Std.U8) (hidden : Slice KeyParam)
    (hd tag : alloc.vec.Vec Std.U8) (msg : Slice Std.U8)
    (hser : sw_keyblob.serialize_params hidden = ok (.Ok hd))
    (hmsg : msg.val = data.val ++ hd.val)
    (hhmac : keystore2_crypto.hmac_sha256 sw_keyblob.KeyBlob.LEGACY_HMAC_KEY msg
      = ok (.Ok tag)) :
    ∃ t, sw_keyblob.KeyBlob.compute_hmac data hidden = ok (.Ok t) ∧ t.val.length = 8

/-- info: 'Keystore2Verify.SwKeyblob.compute_hmac_ok_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.serialize_params,
 Vec.truncate,
 anyhow.Error.Insts.CoreConvertFrom.from,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms compute_hmac_ok_length

recall compute_hmac_err_serialize (data : Slice Std.U8)
    (hidden : Slice KeyParam) (e : anyhow.Error)
    (hser : sw_keyblob.serialize_params hidden = ok (.Err e)) :
    sw_keyblob.KeyBlob.compute_hmac data hidden = ok (.Err e)

/-- info: 'Keystore2Verify.SwKeyblob.compute_hmac_err_serialize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.serialize_params,
 Vec.truncate,
 anyhow.Error.Insts.CoreConvertFrom.from,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms compute_hmac_err_serialize

recall compute_hmac_fail_serialize (data : Slice Std.U8) (hidden : Slice KeyParam) (x : Error)
    (hser : sw_keyblob.serialize_params hidden = fail x) :
    sw_keyblob.KeyBlob.compute_hmac data hidden = fail x

/-- info: 'Keystore2Verify.SwKeyblob.compute_hmac_fail_serialize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.serialize_params,
 Vec.truncate,
 anyhow.Error.Insts.CoreConvertFrom.from,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms compute_hmac_fail_serialize

recall compute_hmac_err_hmac (root : anyhow.Error → ErrRoot) (hfrom : CryptoFromLaw root)
    (data : Slice Std.U8) (hidden : Slice KeyParam) (hd : alloc.vec.Vec Std.U8)
    (msg : Slice Std.U8) (x : keystore2_crypto.error.Error)
    (hser : sw_keyblob.serialize_params hidden = ok (.Ok hd))
    (hmsg : msg.val = data.val ++ hd.val)
    (hhmac : keystore2_crypto.hmac_sha256 sw_keyblob.KeyBlob.LEGACY_HMAC_KEY msg
      = ok (.Err x)) :
    ∃ e', sw_keyblob.KeyBlob.compute_hmac data hidden = ok (.Err e') ∧
      root e' = ErrRoot.crypto x

/-- info: 'Keystore2Verify.SwKeyblob.compute_hmac_err_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.serialize_params,
 Vec.truncate,
 anyhow.Error.Insts.CoreConvertFrom.from,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms compute_hmac_err_hmac

recall compute_hmac_fail_hmac (data : Slice Std.U8) (hidden : Slice KeyParam)
    (hd : alloc.vec.Vec Std.U8) (msg : Slice Std.U8) (x : Error)
    (hser : sw_keyblob.serialize_params hidden = ok (.Ok hd))
    (hmsg : msg.val = data.val ++ hd.val)
    (hhmac : keystore2_crypto.hmac_sha256 sw_keyblob.KeyBlob.LEGACY_HMAC_KEY msg = fail x) :
    sw_keyblob.KeyBlob.compute_hmac data hidden = fail x

/-- info: 'Keystore2Verify.SwKeyblob.compute_hmac_fail_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.serialize_params,
 Vec.truncate,
 anyhow.Error.Insts.CoreConvertFrom.from,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms compute_hmac_fail_hmac

recall compute_hmac_fail_capacity (data : Slice Std.U8) (hidden : Slice KeyParam)
    (hd : alloc.vec.Vec Std.U8) (hser : sw_keyblob.serialize_params hidden = ok (.Ok hd))
    (hover : Std.Usize.max < data.val.length + hd.val.length) :
    sw_keyblob.KeyBlob.compute_hmac data hidden = fail .panic

/-- info: 'Keystore2Verify.SwKeyblob.compute_hmac_fail_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.serialize_params,
 Vec.truncate,
 anyhow.Error.Insts.CoreConvertFrom.from,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms compute_hmac_fail_capacity

recall compute_hmac_ok_of_result (htrunc : AllocVecTruncateSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (t : alloc.vec.Vec Std.U8)
    (h : sw_keyblob.KeyBlob.compute_hmac data hidden = ok (.Ok t)) :
    ∃ (hd : alloc.vec.Vec Std.U8) (msg : Slice Std.U8) (tag : alloc.vec.Vec Std.U8),
      sw_keyblob.serialize_params hidden = ok (.Ok hd) ∧
      msg.val = data.val ++ hd.val ∧
      keystore2_crypto.hmac_sha256 sw_keyblob.KeyBlob.LEGACY_HMAC_KEY msg = ok (.Ok tag) ∧
      t.val = tag.val.take 8

/-- info: 'Keystore2Verify.SwKeyblob.compute_hmac_ok_of_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.serialize_params,
 Vec.truncate,
 anyhow.Error.Insts.CoreConvertFrom.from,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms compute_hmac_ok_of_result

recall compute_hmac_ok_length_of_result (htrunc : AllocVecTruncateSpec)
    (hlen : KeystoreCryptoHmacSha256Spec) (data : Slice Std.U8) (hidden : Slice KeyParam)
    (t : alloc.vec.Vec Std.U8) (h : sw_keyblob.KeyBlob.compute_hmac data hidden = ok (.Ok t)) :
    t.val.length = 8

/-- info: 'Keystore2Verify.SwKeyblob.compute_hmac_ok_length_of_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.serialize_params,
 Vec.truncate,
 anyhow.Error.Insts.CoreConvertFrom.from,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms compute_hmac_ok_length_of_result

recall new_from_serialized_err_short (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8) (hidden : Slice KeyParam)
    (h : data.val.length < minBlobLen) :
    ∃ e, sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Err e) ∧
      IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.new_from_serialized_err_short' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms new_from_serialized_err_short

recall new_from_serialized_err_hmac
    (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8) (hidden : Slice KeyParam)
    (h : minBlobLen ≤ data.val.length) (s : Slice Std.U8)
    (hs : s.val = data.val.take (data.val.length - 8)) (e : anyhow.Error)
    (hmac : sw_keyblob.KeyBlob.compute_hmac s hidden = ok (.Err e)) :
    sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Err e)

/-- info: 'Keystore2Verify.SwKeyblob.new_from_serialized_err_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms new_from_serialized_err_hmac

recall new_from_serialized_fail_hmac (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (h : minBlobLen ≤ data.val.length) (s : Slice Std.U8)
    (hs : s.val = data.val.take (data.val.length - 8)) (x : Error)
    (hmac : sw_keyblob.KeyBlob.compute_hmac s hidden = fail x) :
    sw_keyblob.KeyBlob.new_from_serialized data hidden = fail x

/-- info: 'Keystore2Verify.SwKeyblob.new_from_serialized_fail_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms new_from_serialized_fail_hmac

recall new_from_serialized_err_mac (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (h : minBlobLen ≤ data.val.length) (s : Slice Std.U8)
    (hs : s.val = data.val.take (data.val.length - 8)) (m : alloc.vec.Vec Std.U8)
    (hmac : sw_keyblob.KeyBlob.compute_hmac s hidden = ok (.Ok m))
    (hbad : data.val.drop (data.val.length - 8) ≠ m.val) :
    ∃ e, sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Err e) ∧
      IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.new_from_serialized_err_mac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms new_from_serialized_err_mac

recall new_from_serialized_err_version (root : anyhow.Error → ErrRoot)
    (hlaw : BlobErrFmtLaws root) (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (data : Slice Std.U8) (hidden : Slice KeyParam)
    (hmac : MacOk data hidden) (v : Std.U8) (hv : data.val.head? = some v) (hv0 : v.val ≠ 0) :
    ∃ e, sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Err e) ∧
      IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.new_from_serialized_err_version' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms new_from_serialized_err_version

recall new_from_serialized_err_key_len (root : anyhow.Error → ErrRoot)
    (hlaw : BlobErrFmtLaws root) (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (hmac : MacOk data hidden) (hv : data.val.head? = some 0#u8)
    (hlen : data.val.length - 5 < u32At data.val 1) :
    ∃ e, sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Err e) ∧
      IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.new_from_serialized_err_key_len' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms new_from_serialized_err_key_len

recall new_from_serialized_err_hw
    (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec) (hfirst : CoreSliceFirstSpec)
    (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8) (hidden : Slice KeyParam)
    (hpast : PastKey data hidden) (d2 : Slice Std.U8)
    (hd2 : d2.val = data.val.drop (5 + u32At data.val 1)) (e : anyhow.Error)
    (d3 : Slice Std.U8) (hdes : sw_keyblob.deserialize_params d2 = ok (.Err e, d3)) :
    sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Err e)

/-- info: 'Keystore2Verify.SwKeyblob.new_from_serialized_err_hw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms new_from_serialized_err_hw

recall new_from_serialized_fail_hw (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (hpast : PastKey data hidden) (d2 : Slice Std.U8)
    (hd2 : d2.val = data.val.drop (5 + u32At data.val 1)) (x : Error)
    (hdes : sw_keyblob.deserialize_params d2 = fail x) :
    sw_keyblob.KeyBlob.new_from_serialized data hidden = fail x

/-- info: 'Keystore2Verify.SwKeyblob.new_from_serialized_fail_hw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms new_from_serialized_fail_hw

recall new_from_serialized_err_sw
    (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec) (hfirst : CoreSliceFirstSpec)
    (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8) (hidden : Slice KeyParam)
    (hpast : PastKey data hidden) (d2 : Slice Std.U8)
    (hd2 : d2.val = data.val.drop (5 + u32At data.val 1))
    (hw : alloc.vec.Vec KeyParam) (d3 : Slice Std.U8)
    (hdes1 : sw_keyblob.deserialize_params d2 = ok (.Ok hw, d3)) (e : anyhow.Error)
    (d4 : Slice Std.U8) (hdes2 : sw_keyblob.deserialize_params d3 = ok (.Err e, d4)) :
    sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Err e)

/-- info: 'Keystore2Verify.SwKeyblob.new_from_serialized_err_sw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms new_from_serialized_err_sw

recall new_from_serialized_fail_sw (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (hpast : PastKey data hidden) (d2 : Slice Std.U8)
    (hd2 : d2.val = data.val.drop (5 + u32At data.val 1))
    (hw : alloc.vec.Vec KeyParam) (d3 : Slice Std.U8)
    (hdes1 : sw_keyblob.deserialize_params d2 = ok (.Ok hw, d3)) (x : Error)
    (hdes2 : sw_keyblob.deserialize_params d3 = fail x) :
    sw_keyblob.KeyBlob.new_from_serialized data hidden = fail x

/-- info: 'Keystore2Verify.SwKeyblob.new_from_serialized_fail_sw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms new_from_serialized_fail_sw

recall new_from_serialized_fail_rest (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (hpast : PastKey data hidden) (d2 : Slice Std.U8)
    (hd2 : d2.val = data.val.drop (5 + u32At data.val 1))
    (hw : alloc.vec.Vec KeyParam) (d3 : Slice Std.U8)
    (hdes1 : sw_keyblob.deserialize_params d2 = ok (.Ok hw, d3))
    (sw : alloc.vec.Vec KeyParam) (d4 : Slice Std.U8)
    (hdes2 : sw_keyblob.deserialize_params d3 = ok (.Ok sw, d4))
    (hrest : d4.val.length < 8) :
    ∃ x, sw_keyblob.KeyBlob.new_from_serialized data hidden = fail x

/-- info: 'Keystore2Verify.SwKeyblob.new_from_serialized_fail_rest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms new_from_serialized_fail_rest

recall new_from_serialized_err_extra (root : anyhow.Error → ErrRoot)
    (hlaw : BlobErrFmtLaws root) (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (hpast : PastKey data hidden) (d2 : Slice Std.U8)
    (hd2 : d2.val = data.val.drop (5 + u32At data.val 1))
    (hw : alloc.vec.Vec KeyParam) (d3 : Slice Std.U8)
    (hdes1 : sw_keyblob.deserialize_params d2 = ok (.Ok hw, d3))
    (sw : alloc.vec.Vec KeyParam) (d4 : Slice Std.U8)
    (hdes2 : sw_keyblob.deserialize_params d3 = ok (.Ok sw, d4))
    (hrest : 8 < d4.val.length) :
    ∃ e, sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Err e) ∧
      IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.new_from_serialized_err_extra' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms new_from_serialized_err_extra

recall new_from_serialized_ok (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (hpast : PastKey data hidden) (d2 : Slice Std.U8)
    (hd2 : d2.val = data.val.drop (5 + u32At data.val 1))
    (hw : alloc.vec.Vec KeyParam) (d3 : Slice Std.U8)
    (hdes1 : sw_keyblob.deserialize_params d2 = ok (.Ok hw, d3))
    (sw : alloc.vec.Vec KeyParam) (d4 : Slice Std.U8)
    (hdes2 : sw_keyblob.deserialize_params d3 = ok (.Ok sw, d4))
    (hrest : d4.val.length = 8) :
    ∃ kb, sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Ok kb) ∧
      kb.key_material.val = (data.val.drop 5).take (u32At data.val 1) ∧
      kb.hw_enforced = hw ∧ kb.sw_enforced = sw

/-- info: 'Keystore2Verify.SwKeyblob.new_from_serialized_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms new_from_serialized_ok

recall new_from_serialized_ok_mac (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (data : Slice Std.U8) (hidden : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (h : sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Ok kb)) :
    MacOk data hidden

/-- info: 'Keystore2Verify.SwKeyblob.new_from_serialized_ok_mac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms new_from_serialized_ok_mac

recall new_from_serialized_ok_layout_of_result (hsize : SizeOfLaw Std.U32 4)
    (hne : Shared0SliceNeSpec) (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec)
    (data : Slice Std.U8) (hidden : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (h : sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Ok kb)) :
    PastKey data hidden ∧ kb.key_material.val = (data.val.drop 5).take (u32At data.val 1) ∧
      ∃ d2 d3 d4, d2.val = data.val.drop (5 + u32At data.val 1) ∧
        sw_keyblob.deserialize_params d2 = ok (.Ok kb.hw_enforced, d3) ∧
        sw_keyblob.deserialize_params d3 = ok (.Ok kb.sw_enforced, d4) ∧ d4.val.length = 8

/-- info: 'Keystore2Verify.SwKeyblob.new_from_serialized_ok_layout_of_result'
 depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms new_from_serialized_ok_layout_of_result

recall export_key_fail_hidden (data : Slice Std.U8) (params : Slice KeyParam) (x : Error)
    (hh : sw_keyblob.hidden_params params
      (Array.to_slice (Array.make 1#usize [sw_keyblob.SOFTWARE_ROOT_OF_TRUST])) = fail x) :
    sw_keyblob.export_key data params = fail x

/-- info: 'Keystore2Verify.SwKeyblob.export_key_fail_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_fail_hidden

recall export_key_ok_mac (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (data : Slice Std.U8) (params : Slice KeyParam)
    (out : KeyFormat.KeyFormat × alloc.vec.Vec Std.U8 × alloc.vec.Vec KeyParam)
    (h : sw_keyblob.export_key data params = ok (.Ok out)) :
    ∃ hidden, HiddenOf params hidden ∧ MacOk data hidden

/-- info: 'Keystore2Verify.SwKeyblob.export_key_ok_mac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_ok_mac

recall export_key_err_short (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8) (params hidden : Slice KeyParam)
    (hid : HiddenOf params hidden) (h : data.val.length < minBlobLen) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.export_key_err_short' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_err_short

recall export_key_err_mac (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec) (data : Slice Std.U8)
    (params hidden : Slice KeyParam) (hid : HiddenOf params hidden)
    (h : minBlobLen ≤ data.val.length) (s : Slice Std.U8)
    (hs : s.val = data.val.take (data.val.length - 8)) (m : alloc.vec.Vec Std.U8)
    (hmac : sw_keyblob.KeyBlob.compute_hmac s hidden = ok (.Ok m))
    (hbad : data.val.drop (data.val.length - 8) ≠ m.val) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.export_key_err_mac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_err_mac

recall export_key_err_parse (data : Slice Std.U8)
    (params : Slice KeyParam) (e : anyhow.Error)
    (hp : ParsesTo data params (ok (.Err e))) :
    sw_keyblob.export_key data params = ok (.Err e)

/-- info: 'Keystore2Verify.SwKeyblob.export_key_err_parse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_err_parse

recall export_key_fail_parse (data : Slice Std.U8) (params : Slice KeyParam) (x : Error)
    (hp : ParsesTo data params (fail x)) :
    sw_keyblob.export_key data params = fail x

/-- info: 'Keystore2Verify.SwKeyblob.export_key_fail_parse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_fail_parse

recall export_key_fail_rest (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (params hidden : Slice KeyParam) (hid : HiddenOf params hidden)
    (hpast : PastKey data hidden) (d2 : Slice Std.U8)
    (hd2 : d2.val = data.val.drop (5 + u32At data.val 1))
    (hw : alloc.vec.Vec KeyParam) (d3 : Slice Std.U8)
    (hdes1 : sw_keyblob.deserialize_params d2 = ok (.Ok hw, d3))
    (sw : alloc.vec.Vec KeyParam) (d4 : Slice Std.U8)
    (hdes2 : sw_keyblob.deserialize_params d3 = ok (.Ok sw, d4))
    (hrest : d4.val.length < 8) :
    ∃ x, sw_keyblob.export_key data params = fail x

/-- info: 'Keystore2Verify.SwKeyblob.export_key_fail_rest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_fail_rest

recall export_key_fail_capacity (data : Slice Std.U8) (params : Slice KeyParam)
    (kb : sw_keyblob.KeyBlob) (hp : ParsesTo data params (ok (.Ok kb)))
    (hover : ¬ CombinedFits kb) :
    sw_keyblob.export_key data params = fail .panic

/-- info: 'Keystore2Verify.SwKeyblob.export_key_fail_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_fail_capacity

recall export_key_err_no_algorithm (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hclone : KeyParameterCloneLaw) (data : Slice Std.U8) (params : Slice KeyParam)
    (kb : sw_keyblob.KeyBlob) (hp : ParsesTo data params (ok (.Ok kb)))
    (comb : Slice KeyParam) (hcomb : CombinedOf kb comb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok none) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.export_key_err_no_algorithm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_err_no_algorithm

recall export_key_err_algorithm (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hclone : KeyParameterCloneLaw) (data : Slice Std.U8) (params : Slice KeyParam)
    (kb : sw_keyblob.KeyBlob) (hp : ParsesTo data params (ok (.Ok kb)))
    (comb : Slice KeyParam) (hcomb : CombinedOf kb comb)
    (v : ParamValue) (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some v))
    (hv : ¬ KnownAlgorithm v) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.export_key_err_algorithm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_err_algorithm

recall export_key_ok_raw (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb) (a : Algorithm.Algorithm)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV a)))
    (ha : RawAlgorithm a) :
    ∃ c, sw_keyblob.export_key data params
        = ok (.Ok (KeyFormat.KeyFormat.RAW, kb.key_material, c)) ∧ c.val = comb.val

/-- info: 'Keystore2Verify.SwKeyblob.export_key_ok_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_ok_raw

recall export_key_err_rsa (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hclone : KeyParameterCloneLaw) (data : Slice Std.U8) (params : Slice KeyParam)
    (kb : sw_keyblob.KeyBlob) (hp : ParsesTo data params (ok (.Ok kb)))
    (comb : Slice KeyParam) (hcomb : CombinedOf kb comb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algRSA))) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.export_key_err_rsa' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_err_rsa

recall export_key_err_no_curve (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hclone : KeyParameterCloneLaw) (data : Slice Std.U8) (params : Slice KeyParam)
    (kb : sw_keyblob.KeyBlob) (hp : ParsesTo data params (ok (.Ok kb)))
    (comb : Slice KeyParam) (hcomb : CombinedOf kb comb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = ok none) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.export_key_err_no_curve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_err_no_curve

recall export_key_fail_get_algorithm (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb) (x : Error)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = fail x) :
    sw_keyblob.export_key data params = fail x

/-- info: 'Keystore2Verify.SwKeyblob.export_key_fail_get_algorithm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_fail_get_algorithm

recall export_key_fail_get_curve (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb) (x : Error)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = fail x) :
    sw_keyblob.export_key data params = fail x

/-- info: 'Keystore2Verify.SwKeyblob.export_key_fail_get_curve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_fail_get_curve

recall export_key_err_curve (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hclone : KeyParameterCloneLaw) (data : Slice Std.U8) (params : Slice KeyParam)
    (kb : sw_keyblob.KeyBlob) (hp : ParsesTo data params (ok (.Ok kb)))
    (comb : Slice KeyParam) (hcomb : CombinedOf kb comb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (cv : ParamValue) (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = ok (some cv))
    (hcv : ¬ KnownCurve cv) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.export_key_err_curve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_err_curve

recall export_key_ok_curve25519 (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = ok (some (curveV curve25519))) :
    ∃ c, sw_keyblob.export_key data params
        = ok (.Ok (KeyFormat.KeyFormat.PKCS8, kb.key_material, c)) ∧ c.val = comb.val

/-- info: 'Keystore2Verify.SwKeyblob.export_key_ok_curve25519' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_ok_curve25519

recall export_key_ok_nist (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (c : EcCurve.EcCurve)
    (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = ok (some (curveV c)))
    (alg : Slice Std.U8) (hc : NistAlgId c alg)
    (hbody : (pkcs8Body (nums alg.val) (nums (Vec.deref kb.key_material).val)).length ≤ 0xffff) :
    ∃ w cs, sw_keyblob.export_key data params = ok (.Ok (KeyFormat.KeyFormat.PKCS8, w, cs)) ∧
      nums w.val = pkcs8Wrap (nums alg.val) (nums (Vec.deref kb.key_material).val) ∧
      cs.val = comb.val

/-- info: 'Keystore2Verify.SwKeyblob.export_key_ok_nist' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_ok_nist

recall export_key_err_nist_key_len (root : anyhow.Error → ErrRoot)
    (hlaw : BlobErrFmtLaws root) (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (c : EcCurve.EcCurve)
    (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = ok (some (curveV c)))
    (hc : NistCurve c) (hkey : 0xffff < (Vec.deref kb.key_material).val.length) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.export_key_err_nist_key_len' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_err_nist_key_len

recall export_key_err_nist_body_len (root : anyhow.Error → ErrRoot)
    (hlaw : BlobErrFmtLaws root) (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (hp : ParsesTo data params (ok (.Ok kb))) (comb : Slice KeyParam)
    (hcomb : CombinedOf kb comb)
    (hget : sw_keyblob.get_tag_value comb Tag.Tag.ALGORITHM = ok (some (algV algEC)))
    (c : EcCurve.EcCurve)
    (hcurve : sw_keyblob.get_tag_value comb Tag.Tag.EC_CURVE = ok (some (curveV c)))
    (alg : Slice Std.U8) (hc : NistAlgId c alg)
    (hkey : (Vec.deref kb.key_material).val.length ≤ 0xffff)
    (hbody : 0xffff < (pkcs8Body (nums alg.val) (nums (Vec.deref kb.key_material).val)).length) :
    ∃ e, sw_keyblob.export_key data params = ok (.Err e) ∧ IsBlobErr root e

/-- info: 'Keystore2Verify.SwKeyblob.export_key_err_nist_body_len' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_err_nist_body_len

recall export_key_ok_of_result (hclone : KeyParameterCloneLaw) (data : Slice Std.U8)
    (params : Slice KeyParam) (fmt : KeyFormat.KeyFormat) (key : Vec Std.U8) (cs : Vec KeyParam)
    (h : sw_keyblob.export_key data params = ok (.Ok (fmt, key, cs))) :
    ∃ kb, ParsesTo data params (ok (.Ok kb)) ∧ CombinedOf kb (Vec.deref cs) ∧
      ((∃ a, sw_keyblob.get_tag_value (Vec.deref cs) Tag.Tag.ALGORITHM = ok (some (algV a)) ∧
        RawAlgorithm a ∧ fmt = KeyFormat.KeyFormat.RAW ∧ key = kb.key_material) ∨
       (sw_keyblob.get_tag_value (Vec.deref cs) Tag.Tag.ALGORITHM = ok (some (algV algEC)) ∧
        fmt = KeyFormat.KeyFormat.PKCS8 ∧ ∃ c,
        sw_keyblob.get_tag_value (Vec.deref cs) Tag.Tag.EC_CURVE = ok (some (curveV c)) ∧
        ((c = curve25519 ∧ key = kb.key_material) ∨
         (∃ alg, NistAlgId c alg ∧
           sw_keyblob.pkcs8_wrap_nist_key (Vec.deref kb.key_material) c = ok (.Ok key) ∧
           nums key.val = pkcs8Wrap (nums alg.val) (nums kb.key_material.val)))))

/-- info: 'Keystore2Verify.SwKeyblob.export_key_ok_of_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 anyhow.Error,
 binder.ExceptionCode,
 binder.StatusCode,
 keystore2_crypto.hmac_sha256,
 sw_keyblob.deserialize_params,
 sw_keyblob.get_tag_value,
 sw_keyblob.hidden_params,
 sw_keyblob.serialize_params,
 alloc.fmt.format,
 core.mem.size_of,
 Shared0Slice.Insts.CoreCmpPartialEqVec.ne,
 Vec.truncate,
 anyhow.error.Error.context,
 anyhow.error.Error.new,
 core.fmt.Arguments.from_str_nonconst,
 core.num.U32.from_ne_bytes,
 core.slice.Slice.first,
 anyhow.Error.Insts.CoreConvertFrom.from,
 error.Error.Insts.CoreFmtDebug.fmt,
 error.Error.Insts.CoreFmtDisplay.fmt,
 alloc.string.String.Insts.CoreFmtDisplay.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
 keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
 EcCurve.EcCurve.Insts.CoreFmtDebug.fmt,
 KeyFormat.KeyFormat.Insts.CoreFmtDebug.fmt,
 KeyParameter.KeyParameter.Insts.CoreCloneClone.clone,
 KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms export_key_ok_of_result

end Keystore2Verify.SwKeyblob
