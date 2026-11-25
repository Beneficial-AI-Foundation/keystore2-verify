import Keystore2Verify.Proofs.EcCrypto.Generate
import Keystore2Verify.Proofs.EcCrypto.FromPrivateKey
import Keystore2Verify.Proofs.EcCrypto.PrivateKey
import Keystore2Verify.Proofs.EcCrypto.PublicKey
import Keystore2Verify.Proofs.EcCrypto.AgreeKey
import Keystore2Verify.Proofs.EcCrypto.EncryptMessage
import Keystore2Verify.Proofs.EcCrypto.DecryptMessage
import Keystore2Verify.Proofs.EcCrypto.Satisfiable

namespace Keystore2Verify.EcCrypto
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open alloc.vec
open ec_crypto.ECDHPrivateKey.decrypt_message
open closure.Insts.CoreOpsFunctionFnOnceTupleErrorResultZVecError renaming
  call_once → closureCallOnce

recall generate_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root ec_crypto.ECDHPrivateKey)
    (k : keystore2_crypto.ECKey)
    (hgen : keystore2_crypto.ec_key_generate_key = ok (.Ok k)) :
    ec_crypto.ECDHPrivateKey.generate = ok (.Ok k)

/-- info: 'Keystore2Verify.EcCrypto.generate_ok' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.ec_key_generate_key, alloc.fmt.format,
core.fmt.Arguments.from_str_nonconst, alloc.string.String.Insts.CoreFmtDisplay.fmt,
anyhow.context.ext.StdError.Blanket.ext_context, core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms generate_ok

recall generate_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root ec_crypto.ECDHPrivateKey)
    (e : keystore2_crypto.error.Error)
    (hgen : keystore2_crypto.ec_key_generate_key = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.generate = ok (.Err e') ∧ root e' = ErrRoot.crypto e

/-- info: 'Keystore2Verify.EcCrypto.generate_err' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.ec_key_generate_key, alloc.fmt.format,
core.fmt.Arguments.from_str_nonconst, alloc.string.String.Insts.CoreFmtDisplay.fmt,
anyhow.context.ext.StdError.Blanket.ext_context, core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms generate_err

recall generate_fail (x : Error)
    (hgen : keystore2_crypto.ec_key_generate_key = fail x) :
    ec_crypto.ECDHPrivateKey.generate = fail x

/-- info: 'Keystore2Verify.EcCrypto.generate_fail' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, keystore2_crypto.ECKey,
keystore2_crypto.ec_key_generate_key, alloc.fmt.format, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms generate_fail

recall from_private_key_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root ec_crypto.ECDHPrivateKey)
    (buf : Slice Std.U8) (k : keystore2_crypto.ECKey)
    (hparse : keystore2_crypto.ec_key_parse_private_key buf = ok (.Ok k)) :
    ec_crypto.ECDHPrivateKey.from_private_key buf = ok (.Ok k)

/-- info: 'Keystore2Verify.EcCrypto.from_private_key_ok' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.ec_key_parse_private_key, alloc.fmt.format,
core.fmt.Arguments.from_str_nonconst, alloc.string.String.Insts.CoreFmtDisplay.fmt,
anyhow.context.ext.StdError.Blanket.ext_context, core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms from_private_key_ok

recall from_private_key_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root ec_crypto.ECDHPrivateKey)
    (buf : Slice Std.U8) (e : keystore2_crypto.error.Error)
    (hparse : keystore2_crypto.ec_key_parse_private_key buf = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.from_private_key buf = ok (.Err e') ∧
      root e' = ErrRoot.crypto e

/-- info: 'Keystore2Verify.EcCrypto.from_private_key_err' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.ec_key_parse_private_key, alloc.fmt.format,
core.fmt.Arguments.from_str_nonconst, alloc.string.String.Insts.CoreFmtDisplay.fmt,
anyhow.context.ext.StdError.Blanket.ext_context, core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms from_private_key_err

recall from_private_key_fail (buf : Slice Std.U8) (x : Error)
    (hparse : keystore2_crypto.ec_key_parse_private_key buf = fail x) :
    ec_crypto.ECDHPrivateKey.from_private_key buf = fail x

/-- info: 'Keystore2Verify.EcCrypto.from_private_key_fail' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, keystore2_crypto.ECKey,
keystore2_crypto.ec_key_parse_private_key, alloc.fmt.format,
core.fmt.Arguments.from_str_nonconst, alloc.string.String.Insts.CoreFmtDisplay.fmt,
anyhow.context.ext.StdError.Blanket.ext_context, core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms from_private_key_fail

recall private_key_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (z : keystore2_crypto.zvec.ZVec)
    (hm : keystore2_crypto.ec_key_marshal_private_key self = ok (.Ok z)) :
    ec_crypto.ECDHPrivateKey.private_key self = ok (.Ok z)

/-- info: 'Keystore2Verify.EcCrypto.private_key_ok' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.ec_key_marshal_private_key, alloc.fmt.format,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms private_key_ok

recall private_key_ok_length (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hlen : EcKeyMarshalPrivateKeySpec)
    (self : ec_crypto.ECDHPrivateKey) (z : keystore2_crypto.zvec.ZVec)
    (hm : keystore2_crypto.ec_key_marshal_private_key self = ok (.Ok z)) :
    ec_crypto.ECDHPrivateKey.private_key self = ok (.Ok z) ∧
      ∃ s, zvecDeref z = ok s ∧ s.length = 73

/-- info: 'Keystore2Verify.EcCrypto.private_key_ok_length' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.ec_key_marshal_private_key, alloc.fmt.format,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms private_key_ok_length

recall private_key_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (e : keystore2_crypto.error.Error)
    (hm : keystore2_crypto.ec_key_marshal_private_key self = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.private_key self = ok (.Err e') ∧
      root e' = ErrRoot.crypto e

/-- info: 'Keystore2Verify.EcCrypto.private_key_err' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.ec_key_marshal_private_key, alloc.fmt.format,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms private_key_err

recall private_key_fail (self : ec_crypto.ECDHPrivateKey) (x : Error)
    (hm : keystore2_crypto.ec_key_marshal_private_key self = fail x) :
    ec_crypto.ECDHPrivateKey.private_key self = fail x

/-- info: 'Keystore2Verify.EcCrypto.private_key_fail' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, keystore2_crypto.ECKey,
keystore2_crypto.ec_key_marshal_private_key, alloc.fmt.format, keystore2_crypto.zvec.ZVec,
core.fmt.Arguments.from_str_nonconst, alloc.string.String.Insts.CoreFmtDisplay.fmt,
anyhow.context.ext.StdError.Blanket.ext_context, core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms private_key_fail

recall private_key_ok_length_of_result (root : anyhow.Error → ErrRoot)
    (hctx : CryptoCtxLaw root keystore2_crypto.zvec.ZVec) (hlen : EcKeyMarshalPrivateKeySpec)
    (self : ec_crypto.ECDHPrivateKey) (z : keystore2_crypto.zvec.ZVec)
    (h : ec_crypto.ECDHPrivateKey.private_key self = ok (.Ok z)) :
    ∃ s, zvecDeref z = ok s ∧ s.length = 73

/-- info: 'Keystore2Verify.EcCrypto.private_key_ok_length_of_result' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.ec_key_marshal_private_key, alloc.fmt.format,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms private_key_ok_length_of_result

recall public_key_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (self : ec_crypto.ECDHPrivateKey) (pt : keystore2_crypto.BorrowedECPoint)
    (eps : keystore2_crypto_bindgen.ec_point_st) (v : alloc.vec.Vec Std.U8)
    (hkey : keystore2_crypto.ec_key_get0_public_key self = ok pt)
    (hpt : keystore2_crypto.BorrowedECPoint.get_point pt = ok eps)
    (hoct : keystore2_crypto.ec_point_point_to_oct eps = ok (.Ok v)) :
    ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok v)

/-- info: 'Keystore2Verify.EcCrypto.public_key_ok' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_point_to_oct,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms public_key_ok

recall public_key_ok_length (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root (alloc.vec.Vec Std.U8)) (hlen : EcPointPointToOctSpec)
    (self : ec_crypto.ECDHPrivateKey) (pt : keystore2_crypto.BorrowedECPoint)
    (eps : keystore2_crypto_bindgen.ec_point_st) (v : alloc.vec.Vec Std.U8)
    (hkey : keystore2_crypto.ec_key_get0_public_key self = ok pt)
    (hpt : keystore2_crypto.BorrowedECPoint.get_point pt = ok eps)
    (hoct : keystore2_crypto.ec_point_point_to_oct eps = ok (.Ok v)) :
    ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok v) ∧
      1 ≤ v.val.length ∧ v.val.length ≤ 133

/-- info: 'Keystore2Verify.EcCrypto.public_key_ok_length' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_point_to_oct,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms public_key_ok_length

recall public_key_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (self : ec_crypto.ECDHPrivateKey) (pt : keystore2_crypto.BorrowedECPoint)
    (eps : keystore2_crypto_bindgen.ec_point_st) (e : keystore2_crypto.error.Error)
    (hkey : keystore2_crypto.ec_key_get0_public_key self = ok pt)
    (hpt : keystore2_crypto.BorrowedECPoint.get_point pt = ok eps)
    (hoct : keystore2_crypto.ec_point_point_to_oct eps = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.public_key self = ok (.Err e') ∧
      root e' = ErrRoot.crypto e

/-- info: 'Keystore2Verify.EcCrypto.public_key_err' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_point_to_oct,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms public_key_err

recall public_key_fail_get_point (self : ec_crypto.ECDHPrivateKey)
    (pt : keystore2_crypto.BorrowedECPoint) (x : Error)
    (hkey : keystore2_crypto.ec_key_get0_public_key self = ok pt)
    (hpt : keystore2_crypto.BorrowedECPoint.get_point pt = fail x) :
    ec_crypto.ECDHPrivateKey.public_key self = fail x

/-- info: 'Keystore2Verify.EcCrypto.public_key_fail_get_point' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, keystore2_crypto.BorrowedECPoint,
keystore2_crypto.ECKey, keystore2_crypto.ec_key_get0_public_key,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms public_key_fail_get_point

recall public_key_fail_get0_public_key (self : ec_crypto.ECDHPrivateKey) (x : Error)
    (hkey : keystore2_crypto.ec_key_get0_public_key self = fail x) :
    ec_crypto.ECDHPrivateKey.public_key self = fail x

/-- info: 'Keystore2Verify.EcCrypto.public_key_fail_get0_public_key' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, keystore2_crypto.BorrowedECPoint,
keystore2_crypto.ECKey, keystore2_crypto.ec_key_get0_public_key,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms public_key_fail_get0_public_key

recall public_key_fail_point_to_oct (self : ec_crypto.ECDHPrivateKey)
    (pt : keystore2_crypto.BorrowedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (x : Error)
    (hkey : keystore2_crypto.ec_key_get0_public_key self = ok pt)
    (hpt : keystore2_crypto.BorrowedECPoint.get_point pt = ok eps)
    (hoct : keystore2_crypto.ec_point_point_to_oct eps = fail x) :
    ec_crypto.ECDHPrivateKey.public_key self = fail x

/-- info: 'Keystore2Verify.EcCrypto.public_key_fail_point_to_oct' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, keystore2_crypto.BorrowedECPoint,
keystore2_crypto.ECKey, keystore2_crypto.ec_key_get0_public_key,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms public_key_fail_point_to_oct

recall public_key_ok_length_of_result (root : anyhow.Error → ErrRoot)
    (hctx : CryptoCtxLaw root (alloc.vec.Vec Std.U8)) (hlen : EcPointPointToOctSpec)
    (self : ec_crypto.ECDHPrivateKey) (v : alloc.vec.Vec Std.U8)
    (h : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok v)) :
    1 ≤ v.val.length ∧ v.val.length ≤ 133

/-- info: 'Keystore2Verify.EcCrypto.public_key_ok_length_of_result' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_point_to_oct,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax) in
#print axioms public_key_ok_length_of_result

recall agree_key_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (p : keystore2_crypto.OwnedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (sec : keystore2_crypto.zvec.ZVec)
    (ss s2 : Slice Std.U8) (k3 : keystore2_crypto.zvec.ZVec)
    (s3 : Slice Std.U8) (key : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = ok eps)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = ok (.Ok sec))
    (hds : zvecDeref sec = ok ss) (hd2 : zvecDeref k2 = ok s2)
    (hext3 : keystore2_crypto.hkdf_extract ss s2 = ok (.Ok k3))
    (hd3 : zvecDeref k3 = ok s3)
    (hexp : keystore2_crypto.hkdf_expand keystore2_crypto.AES_256_KEY_LENGTH s3 aesKeyInfo =
      ok (.Ok key)) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = ok (.Ok key)

/-- info: 'Keystore2Verify.EcCrypto.agree_key_ok' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_ok

recall agree_key_ok_length (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (hlen : KeystoreCryptoHkdfExpandSpec)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (p : keystore2_crypto.OwnedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (sec : keystore2_crypto.zvec.ZVec)
    (ss s2 : Slice Std.U8) (k3 : keystore2_crypto.zvec.ZVec)
    (s3 : Slice Std.U8) (key : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = ok eps)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = ok (.Ok sec))
    (hds : zvecDeref sec = ok ss) (hd2 : zvecDeref k2 = ok s2)
    (hext3 : keystore2_crypto.hkdf_extract ss s2 = ok (.Ok k3))
    (hd3 : zvecDeref k3 = ok s3)
    (hexp : keystore2_crypto.hkdf_expand keystore2_crypto.AES_256_KEY_LENGTH s3 aesKeyInfo =
      ok (.Ok key)) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = ok
    (.Ok key) ∧ ∃ s, zvecDeref key = ok s ∧ s.length = 32

/-- info: 'Keystore2Verify.EcCrypto.agree_key_ok_length' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_ok_length

recall agree_key_err_sender_extract (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (e : keystore2_crypto.error.Error)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = ok
    (.Err e') ∧
      root e' = ErrRoot.crypto e

/-- info: 'Keystore2Verify.EcCrypto.agree_key_err_sender_extract' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_err_sender_extract

recall agree_key_err_recipient_extract (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (e : keystore2_crypto.error.Error)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = ok
    (.Err e') ∧
      root e' = ErrRoot.crypto e

/-- info: 'Keystore2Verify.EcCrypto.agree_key_err_recipient_extract' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_err_recipient_extract

recall agree_key_err_oct_to_point (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (e : keystore2_crypto.error.Error)
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = ok
    (.Err e') ∧
      root e' = ErrRoot.crypto e

/-- info: 'Keystore2Verify.EcCrypto.agree_key_err_oct_to_point' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_err_oct_to_point

recall agree_key_err_ecdh (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (p : keystore2_crypto.OwnedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = ok eps)
    (e : keystore2_crypto.error.Error)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = ok
    (.Err e') ∧
      root e' = ErrRoot.crypto e

/-- info: 'Keystore2Verify.EcCrypto.agree_key_err_ecdh' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_err_ecdh

recall agree_key_err_secret_extract (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (p : keystore2_crypto.OwnedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (sec : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = ok eps)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = ok (.Ok sec))
    (e : keystore2_crypto.error.Error)
    (ss s2 : Slice Std.U8) (hds : zvecDeref sec = ok ss) (hd2 : zvecDeref k2 = ok s2)
    (hext3 : keystore2_crypto.hkdf_extract ss s2 = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = ok
    (.Err e') ∧
      root e' = ErrRoot.crypto e

/-- info: 'Keystore2Verify.EcCrypto.agree_key_err_secret_extract' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_err_secret_extract

recall agree_key_err_expand (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (p : keystore2_crypto.OwnedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (sec : keystore2_crypto.zvec.ZVec)
    (ss s2 : Slice Std.U8) (k3 : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = ok eps)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = ok (.Ok sec))
    (hds : zvecDeref sec = ok ss) (hd2 : zvecDeref k2 = ok s2)
    (hext3 : keystore2_crypto.hkdf_extract ss s2 = ok (.Ok k3))
    (e : keystore2_crypto.error.Error)
    (s3 : Slice Std.U8) (hd3 : zvecDeref k3 = ok s3)
    (hexp : keystore2_crypto.hkdf_expand keystore2_crypto.AES_256_KEY_LENGTH s3 aesKeyInfo =
      ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = ok
    (.Err e') ∧
      root e' = ErrRoot.crypto e

/-- info: 'Keystore2Verify.EcCrypto.agree_key_err_expand' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_err_expand

recall agree_key_fail_sender_extract (self : ec_crypto.ECDHPrivateKey)
    (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (x : Error)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x

/-- info: 'Keystore2Verify.EcCrypto.agree_key_fail_sender_extract' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, keystore2_crypto.ECKey,
keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_fail_sender_extract

recall agree_key_fail_deref_sender_extract (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (x : Error)
    (hd1 : zvecDeref k1 = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x

/-- info: 'Keystore2Verify.EcCrypto.agree_key_fail_deref_sender_extract' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_fail_deref_sender_extract

recall agree_key_fail_recipient_extract (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (x : Error)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x

/-- info: 'Keystore2Verify.EcCrypto.agree_key_fail_recipient_extract' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_fail_recipient_extract

recall agree_key_fail_oct_to_point (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (x : Error)
    (hoct : keystore2_crypto.ec_point_oct_to_point other = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x

/-- info: 'Keystore2Verify.EcCrypto.agree_key_fail_oct_to_point' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_fail_oct_to_point

recall agree_key_fail_get_point (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (p : keystore2_crypto.OwnedECPoint) (x : Error)
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x

/-- info: 'Keystore2Verify.EcCrypto.agree_key_fail_get_point' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_fail_get_point

recall agree_key_fail_ecdh (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (p : keystore2_crypto.OwnedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = ok eps)
    (x : Error)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x

/-- info: 'Keystore2Verify.EcCrypto.agree_key_fail_ecdh' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_fail_ecdh

recall agree_key_fail_deref_secret (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (p : keystore2_crypto.OwnedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (sec : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = ok eps)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = ok (.Ok sec))
    (x : Error)
    (hds : zvecDeref sec = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x

/-- info: 'Keystore2Verify.EcCrypto.agree_key_fail_deref_secret' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_fail_deref_secret

recall agree_key_fail_deref_recipient_prk (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (p : keystore2_crypto.OwnedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (sec : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = ok eps)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = ok (.Ok sec))
    (ss : Slice Std.U8) (x : Error)
    (hds : zvecDeref sec = ok ss) (hd2 : zvecDeref k2 = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x

/-- info: 'Keystore2Verify.EcCrypto.agree_key_fail_deref_recipient_prk' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_fail_deref_recipient_prk

recall agree_key_fail_secret_extract (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (p : keystore2_crypto.OwnedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (sec : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = ok eps)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = ok (.Ok sec))
    (ss s2 : Slice Std.U8) (x : Error)
    (hds : zvecDeref sec = ok ss) (hd2 : zvecDeref k2 = ok s2)
    (hext3 : keystore2_crypto.hkdf_extract ss s2 = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x

/-- info: 'Keystore2Verify.EcCrypto.agree_key_fail_secret_extract' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_fail_secret_extract

recall agree_key_fail_deref_prk (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (p : keystore2_crypto.OwnedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (sec : keystore2_crypto.zvec.ZVec)
    (ss s2 : Slice Std.U8) (k3 : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = ok eps)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = ok (.Ok sec))
    (hds : zvecDeref sec = ok ss) (hd2 : zvecDeref k2 = ok s2)
    (hext3 : keystore2_crypto.hkdf_extract ss s2 = ok (.Ok k3))
    (x : Error)
    (hd3 : zvecDeref k3 = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x

/-- info: 'Keystore2Verify.EcCrypto.agree_key_fail_deref_prk' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_fail_deref_prk

recall agree_key_fail_expand (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (p : keystore2_crypto.OwnedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (sec : keystore2_crypto.zvec.ZVec)
    (ss s2 : Slice Std.U8) (k3 : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = ok eps)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = ok (.Ok sec))
    (hds : zvecDeref sec = ok ss) (hd2 : zvecDeref k2 = ok s2)
    (hext3 : keystore2_crypto.hkdf_extract ss s2 = ok (.Ok k3))
    (s3 : Slice Std.U8) (x : Error)
    (hd3 : zvecDeref k3 = ok s3)
    (hexp : keystore2_crypto.hkdf_expand keystore2_crypto.AES_256_KEY_LENGTH s3 aesKeyInfo =
      fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x

/-- info: 'Keystore2Verify.EcCrypto.agree_key_fail_expand' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_fail_expand

recall agree_key_ok_length_of_result (root : anyhow.Error → ErrRoot)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec) (hlen : KeystoreCryptoHkdfExpandSpec)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion) (key : keystore2_crypto.zvec.ZVec)
    (h : ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version =
      ok (.Ok key)) : ∃ s, zvecDeref key = ok s ∧ s.length = 32

/-- info: 'Keystore2Verify.EcCrypto.agree_key_ok_length_of_result' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_key_ok_length_of_result

recall encrypt_message_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (hc84 : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (hc93 : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc95 : CryptoCtxLaw root
      (alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8))
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (spk : alloc.vec.Vec Std.U8)
    (salt : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8) (ct iv tag : alloc.vec.Vec Std.U8)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Ok spk))
    (hs : keystore2_crypto.generate_salt = ok (.Ok salt))
    (ha : ec_crypto.ECDHPrivateKey.agree_key k (Vec.deref salt) recipient
      (Vec.deref spk) recipient keystore2_crypto.EcdhComputeKeyVersion.Current =
      ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (he : keystore2_crypto.aes_gcm_encrypt message ks = ok (.Ok (ct, iv, tag))) :
    ec_crypto.ECDHPrivateKey.encrypt_message recipient message = ok
    (.Ok (spk, salt, iv, ct, tag))

/-- info: 'Keystore2Verify.EcCrypto.encrypt_message_ok' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_encrypt, keystore2_crypto.ec_key_generate_key,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto.ecdh_compute_key,
keystore2_crypto.generate_salt, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms encrypt_message_ok

recall encrypt_message_ok_lengths (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (hc84 : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (hc93 : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc95 : CryptoCtxLaw root
      (alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8))
    (recipient message : Slice Std.U8)
    (hsalt : KeystoreCryptoGenerateSaltSpec) (haes : AesGcmEncryptSpec)
    (k : ec_crypto.ECDHPrivateKey)
    (spk : alloc.vec.Vec Std.U8)
    (salt : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8) (ct iv tag : alloc.vec.Vec Std.U8)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Ok spk))
    (hs : keystore2_crypto.generate_salt = ok (.Ok salt))
    (ha : ec_crypto.ECDHPrivateKey.agree_key k (Vec.deref salt) recipient
      (Vec.deref spk) recipient keystore2_crypto.EcdhComputeKeyVersion.Current =
      ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (he : keystore2_crypto.aes_gcm_encrypt message ks = ok (.Ok (ct, iv, tag))) :
    ec_crypto.ECDHPrivateKey.encrypt_message recipient message =
      ok (.Ok (spk, salt, iv, ct, tag)) ∧
      salt.val.length = 16 ∧ iv.val.length = 12 ∧ tag.val.length = 16 ∧
      ct.val.length = message.length

/-- info: 'Keystore2Verify.EcCrypto.encrypt_message_ok_lengths' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_encrypt, keystore2_crypto.ec_key_generate_key,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto.ecdh_compute_key,
keystore2_crypto.generate_salt, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms encrypt_message_ok_lengths

recall encrypt_message_ok_lengths_of_result (root : anyhow.Error → ErrRoot)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (hc84 : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (hc95 : CryptoCtxLaw root
      (alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8))
    (hoct : EcPointPointToOctSpec) (hsalt : KeystoreCryptoGenerateSaltSpec)
    (haes : AesGcmEncryptSpec)
    (recipient message : Slice Std.U8)
    (spk salt iv ct tag : alloc.vec.Vec Std.U8)
    (h : ec_crypto.ECDHPrivateKey.encrypt_message recipient message =
      ok (.Ok (spk, salt, iv, ct, tag))) :
    (1 ≤ spk.val.length ∧ spk.val.length ≤ 133) ∧
      salt.val.length = 16 ∧ iv.val.length = 12 ∧ tag.val.length = 16 ∧
      ct.val.length = message.length

/-- info: 'Keystore2Verify.EcCrypto.encrypt_message_ok_lengths_of_result' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_encrypt, keystore2_crypto.ec_key_generate_key,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto.ecdh_compute_key,
keystore2_crypto.generate_salt, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms encrypt_message_ok_lengths_of_result

recall encrypt_message_err_generate (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (recipient message : Slice Std.U8)
    (e : anyhow.Error)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.encrypt_message recipient message = ok (.Err e') ∧
      root e' = root e

/-- info: 'Keystore2Verify.EcCrypto.encrypt_message_err_generate' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_encrypt, keystore2_crypto.ec_key_generate_key,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto.ecdh_compute_key,
keystore2_crypto.generate_salt, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms encrypt_message_err_generate

recall encrypt_message_err_public_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (e : anyhow.Error)
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.encrypt_message recipient message = ok (.Err e') ∧
      root e' = root e

/-- info: 'Keystore2Verify.EcCrypto.encrypt_message_err_public_key' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_encrypt, keystore2_crypto.ec_key_generate_key,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto.ecdh_compute_key,
keystore2_crypto.generate_salt, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms encrypt_message_err_public_key

recall encrypt_message_err_generate_salt (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (hc84 : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (spk : alloc.vec.Vec Std.U8)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Ok spk))
    (e : keystore2_crypto.error.Error)
    (hs : keystore2_crypto.generate_salt = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.encrypt_message recipient message = ok (.Err e') ∧
      root e' = ErrRoot.crypto e

/-- info: 'Keystore2Verify.EcCrypto.encrypt_message_err_generate_salt' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_encrypt, keystore2_crypto.ec_key_generate_key,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto.ecdh_compute_key,
keystore2_crypto.generate_salt, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms encrypt_message_err_generate_salt

recall encrypt_message_err_agree_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (hc84 : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (hc93 : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (spk : alloc.vec.Vec Std.U8)
    (salt : alloc.vec.Vec Std.U8)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Ok spk))
    (hs : keystore2_crypto.generate_salt = ok (.Ok salt))
    (e : anyhow.Error)
    (ha : ec_crypto.ECDHPrivateKey.agree_key k (Vec.deref salt) recipient
      (Vec.deref spk) recipient keystore2_crypto.EcdhComputeKeyVersion.Current =
      ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.encrypt_message recipient message = ok (.Err e') ∧
      root e' = root e

/-- info: 'Keystore2Verify.EcCrypto.encrypt_message_err_agree_key' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_encrypt, keystore2_crypto.ec_key_generate_key,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto.ecdh_compute_key,
keystore2_crypto.generate_salt, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms encrypt_message_err_agree_key

recall encrypt_message_err_aes_gcm_encrypt (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (hc84 : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (hc93 : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc95 : CryptoCtxLaw root
      (alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8))
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (spk : alloc.vec.Vec Std.U8)
    (salt : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Ok spk))
    (hs : keystore2_crypto.generate_salt = ok (.Ok salt))
    (ha : ec_crypto.ECDHPrivateKey.agree_key k (Vec.deref salt) recipient
      (Vec.deref spk) recipient keystore2_crypto.EcdhComputeKeyVersion.Current =
      ok (.Ok key))
    (e : keystore2_crypto.error.Error)
    (ks : Slice Std.U8)
    (hd : zvecDeref key = ok ks)
    (he : keystore2_crypto.aes_gcm_encrypt message ks = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.encrypt_message recipient message = ok (.Err e') ∧
      root e' = ErrRoot.crypto e

/-- info: 'Keystore2Verify.EcCrypto.encrypt_message_err_aes_gcm_encrypt' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_encrypt, keystore2_crypto.ec_key_generate_key,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto.ecdh_compute_key,
keystore2_crypto.generate_salt, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms encrypt_message_err_aes_gcm_encrypt

recall encrypt_message_fail_public_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (x : Error)
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = fail x) :
    ec_crypto.ECDHPrivateKey.encrypt_message recipient message = fail x

/-- info: 'Keystore2Verify.EcCrypto.encrypt_message_fail_public_key' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_encrypt, keystore2_crypto.ec_key_generate_key,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto.ecdh_compute_key,
keystore2_crypto.generate_salt, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms encrypt_message_fail_public_key

recall encrypt_message_fail_agree_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (hc84 : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (spk : alloc.vec.Vec Std.U8)
    (salt : alloc.vec.Vec Std.U8)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Ok spk))
    (hs : keystore2_crypto.generate_salt = ok (.Ok salt))
    (x : Error)
    (ha : ec_crypto.ECDHPrivateKey.agree_key k (Vec.deref salt) recipient
      (Vec.deref spk) recipient keystore2_crypto.EcdhComputeKeyVersion.Current =
      fail x) :
    ec_crypto.ECDHPrivateKey.encrypt_message recipient message = fail x

/-- info: 'Keystore2Verify.EcCrypto.encrypt_message_fail_agree_key' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_encrypt, keystore2_crypto.ec_key_generate_key,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto.ecdh_compute_key,
keystore2_crypto.generate_salt, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms encrypt_message_fail_agree_key

recall encrypt_message_fail_generate (recipient message : Slice Std.U8)
    (x : Error)
    (hg : ec_crypto.ECDHPrivateKey.generate = fail x) :
    ec_crypto.ECDHPrivateKey.encrypt_message recipient message = fail x

/-- info: 'Keystore2Verify.EcCrypto.encrypt_message_fail_generate' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, keystore2_crypto.BorrowedECPoint,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.aes_gcm_encrypt,
keystore2_crypto.ec_key_generate_key, keystore2_crypto.ec_key_get0_public_key,
keystore2_crypto.ec_point_oct_to_point, keystore2_crypto.ec_point_point_to_oct,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.generate_salt, keystore2_crypto.hkdf_expand,
keystore2_crypto.hkdf_extract, keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms encrypt_message_fail_generate

recall encrypt_message_fail_generate_salt (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (spk : alloc.vec.Vec Std.U8)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Ok spk))
    (x : Error)
    (hs : keystore2_crypto.generate_salt = fail x) :
    ec_crypto.ECDHPrivateKey.encrypt_message recipient message = fail x

/-- info: 'Keystore2Verify.EcCrypto.encrypt_message_fail_generate_salt' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_encrypt, keystore2_crypto.ec_key_generate_key,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto.ecdh_compute_key,
keystore2_crypto.generate_salt, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms encrypt_message_fail_generate_salt

recall encrypt_message_fail_deref_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (hc84 : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (hc93 : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (spk : alloc.vec.Vec Std.U8)
    (salt : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Ok spk))
    (hs : keystore2_crypto.generate_salt = ok (.Ok salt))
    (ha : ec_crypto.ECDHPrivateKey.agree_key k (Vec.deref salt) recipient
      (Vec.deref spk) recipient keystore2_crypto.EcdhComputeKeyVersion.Current =
      ok (.Ok key))
    (x : Error)
    (hd : zvecDeref key = fail x) :
    ec_crypto.ECDHPrivateKey.encrypt_message recipient message = fail x

/-- info: 'Keystore2Verify.EcCrypto.encrypt_message_fail_deref_key' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_encrypt, keystore2_crypto.ec_key_generate_key,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto.ecdh_compute_key,
keystore2_crypto.generate_salt, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms encrypt_message_fail_deref_key

recall encrypt_message_fail_aes_gcm_encrypt (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (hc84 : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (hc93 : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (spk : alloc.vec.Vec Std.U8)
    (salt : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Ok spk))
    (hs : keystore2_crypto.generate_salt = ok (.Ok salt))
    (ha : ec_crypto.ECDHPrivateKey.agree_key k (Vec.deref salt) recipient
      (Vec.deref spk) recipient keystore2_crypto.EcdhComputeKeyVersion.Current =
      ok (.Ok key))
    (ks : Slice Std.U8) (x : Error)
    (hd : zvecDeref key = ok ks)
    (he : keystore2_crypto.aes_gcm_encrypt message ks = fail x) :
    ec_crypto.ECDHPrivateKey.encrypt_message recipient message = fail x

/-- info: 'Keystore2Verify.EcCrypto.encrypt_message_fail_aes_gcm_encrypt' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_encrypt, keystore2_crypto.ec_key_generate_key,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto.ecdh_compute_key,
keystore2_crypto.generate_salt, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms encrypt_message_fail_aes_gcm_encrypt

recall decrypt_message_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (p : keystore2_crypto.zvec.ZVec)
    (hdec : keystore2_crypto.aes_gcm_decrypt ct iv tag ks = ok (.Ok p)) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = ok (.Ok p)

/-- info: 'Keystore2Verify.EcCrypto.decrypt_message_ok' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_decrypt, keystore2_crypto.ec_key_get0_public_key,
keystore2_crypto.ec_point_oct_to_point, keystore2_crypto.ec_point_point_to_oct,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypt_message_ok

recall decrypt_message_ok_length (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (hlen : AesGcmDecryptSpec)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (p : keystore2_crypto.zvec.ZVec)
    (hdec : keystore2_crypto.aes_gcm_decrypt ct iv tag ks = ok (.Ok p)) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = ok
    (.Ok p) ∧ ∃ s, zvecDeref p = ok s ∧ s.length = ct.length

/-- info: 'Keystore2Verify.EcCrypto.decrypt_message_ok_length' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_decrypt, keystore2_crypto.ec_key_get0_public_key,
keystore2_crypto.ec_point_oct_to_point, keystore2_crypto.ec_point_point_to_oct,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypt_message_ok_length

recall decrypt_message_ok_length_of_result (root : anyhow.Error → ErrRoot)
    (hc131 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hlen : AesGcmDecryptSpec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (p : keystore2_crypto.zvec.ZVec)
    (h : ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = ok (.Ok p)) :
    ∃ s, zvecDeref p = ok s ∧ s.length = ct.length

/-- info: 'Keystore2Verify.EcCrypto.decrypt_message_ok_length_of_result' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_decrypt, keystore2_crypto.ec_key_get0_public_key,
keystore2_crypto.ec_point_oct_to_point, keystore2_crypto.ec_point_point_to_oct,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypt_message_ok_length_of_result

recall decrypt_message_ok_legacy (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc131 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8)
    (e1 : keystore2_crypto.error.Error)
    (key2 : keystore2_crypto.zvec.ZVec)
    (ks2 : Slice Std.U8)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (hdec1 : keystore2_crypto.aes_gcm_decrypt ct iv tag ks = ok (.Err e1))
    (ha2 : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.LegacyTruncated = ok
      (.Ok key2))
    (hd2 : zvecDeref key2 = ok ks2)
    (p : keystore2_crypto.zvec.ZVec)
    (hdec2 : keystore2_crypto.aes_gcm_decrypt ct iv tag ks2 = ok (.Ok p)) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = ok (.Ok p)

/-- info: 'Keystore2Verify.EcCrypto.decrypt_message_ok_legacy' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_decrypt, keystore2_crypto.ec_key_get0_public_key,
keystore2_crypto.ec_point_oct_to_point, keystore2_crypto.ec_point_point_to_oct,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypt_message_ok_legacy

recall decrypt_message_err_public_key
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (e : anyhow.Error)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Err e)) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = ok (.Err e)

/-- info: 'Keystore2Verify.EcCrypto.decrypt_message_err_public_key' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, keystore2_crypto.BorrowedECPoint,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.aes_gcm_decrypt,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto.ecdh_compute_key,
keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract, keystore2_crypto_bindgen.ec_point_st,
alloc.fmt.format, keystore2_crypto.BorrowedECPoint.get_point,
keystore2_crypto.OwnedECPoint.get_point, keystore2_crypto.zvec.ZVec,
core.fmt.Arguments.from_str_nonconst, anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypt_message_err_public_key

recall decrypt_message_err_agree_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (e : anyhow.Error)
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = ok
    (.Err e') ∧ root e' = root e

/-- info: 'Keystore2Verify.EcCrypto.decrypt_message_err_agree_key' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_decrypt, keystore2_crypto.ec_key_get0_public_key,
keystore2_crypto.ec_point_oct_to_point, keystore2_crypto.ec_point_point_to_oct,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypt_message_err_agree_key

recall decrypt_message_err_legacy_agree_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8)
    (e1 : keystore2_crypto.error.Error)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (hdec1 : keystore2_crypto.aes_gcm_decrypt ct iv tag ks = ok (.Err e1))
    (e : anyhow.Error)
    (ha2 : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.LegacyTruncated = ok
      (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = ok
    (.Err e') ∧ root e' = root e

/-- info: 'Keystore2Verify.EcCrypto.decrypt_message_err_legacy_agree_key' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_decrypt, keystore2_crypto.ec_key_get0_public_key,
keystore2_crypto.ec_point_oct_to_point, keystore2_crypto.ec_point_point_to_oct,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypt_message_err_legacy_agree_key

recall decrypt_message_err_legacy_decrypt (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc131 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8)
    (e1 : keystore2_crypto.error.Error)
    (key2 : keystore2_crypto.zvec.ZVec)
    (ks2 : Slice Std.U8)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (hdec1 : keystore2_crypto.aes_gcm_decrypt ct iv tag ks = ok (.Err e1))
    (ha2 : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.LegacyTruncated = ok
      (.Ok key2))
    (hd2 : zvecDeref key2 = ok ks2)
    (e : keystore2_crypto.error.Error)
    (hdec2 : keystore2_crypto.aes_gcm_decrypt ct iv tag ks2 = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = ok
    (.Err e') ∧ root e' = ErrRoot.crypto e

/-- info: 'Keystore2Verify.EcCrypto.decrypt_message_err_legacy_decrypt' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_decrypt, keystore2_crypto.ec_key_get0_public_key,
keystore2_crypto.ec_point_oct_to_point, keystore2_crypto.ec_point_point_to_oct,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypt_message_err_legacy_decrypt

recall decrypt_message_fail_public_key (self : ec_crypto.ECDHPrivateKey)
    (sender salt iv ct tag : Slice Std.U8)
    (x : Error) (hpk : ec_crypto.ECDHPrivateKey.public_key self = fail x) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = fail x

/-- info: 'Keystore2Verify.EcCrypto.decrypt_message_fail_public_key' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, keystore2_crypto.BorrowedECPoint,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.aes_gcm_decrypt,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto.ecdh_compute_key,
keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract, keystore2_crypto_bindgen.ec_point_st,
alloc.fmt.format, keystore2_crypto.BorrowedECPoint.get_point,
keystore2_crypto.OwnedECPoint.get_point, keystore2_crypto.zvec.ZVec,
core.fmt.Arguments.from_str_nonconst, anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypt_message_fail_public_key

recall decrypt_message_fail_agree_key (self : ec_crypto.ECDHPrivateKey)
    (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8) (x : Error)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = fail x) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = fail x

/-- info: 'Keystore2Verify.EcCrypto.decrypt_message_fail_agree_key' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, keystore2_crypto.BorrowedECPoint,
keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint, keystore2_crypto.aes_gcm_decrypt,
keystore2_crypto.ec_key_get0_public_key, keystore2_crypto.ec_point_oct_to_point,
keystore2_crypto.ec_point_point_to_oct, keystore2_crypto.ecdh_compute_key,
keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract, keystore2_crypto_bindgen.ec_point_st,
alloc.fmt.format, keystore2_crypto.BorrowedECPoint.get_point,
keystore2_crypto.OwnedECPoint.get_point, keystore2_crypto.zvec.ZVec,
core.fmt.Arguments.from_str_nonconst, anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypt_message_fail_agree_key

recall decrypt_message_fail_legacy_agree_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8)
    (e1 : keystore2_crypto.error.Error)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (hdec1 : keystore2_crypto.aes_gcm_decrypt ct iv tag ks = ok (.Err e1))
    (x : Error)
    (ha2 : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.LegacyTruncated = fail x) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = fail x

/-- info: 'Keystore2Verify.EcCrypto.decrypt_message_fail_legacy_agree_key' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_decrypt, keystore2_crypto.ec_key_get0_public_key,
keystore2_crypto.ec_point_oct_to_point, keystore2_crypto.ec_point_point_to_oct,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypt_message_fail_legacy_agree_key

recall decrypt_message_closure_ignores_error
    (c : closure)
    (e1 e2 : keystore2_crypto.error.Error) :
    closureCallOnce c e1 = closureCallOnce c e2

/-- info: 'Keystore2Verify.EcCrypto.decrypt_message_closure_ignores_error' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, keystore2_crypto.ECKey,
keystore2_crypto.OwnedECPoint, keystore2_crypto.aes_gcm_decrypt,
keystore2_crypto.ec_point_oct_to_point, keystore2_crypto.ecdh_compute_key,
keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract, keystore2_crypto_bindgen.ec_point_st,
alloc.fmt.format, keystore2_crypto.OwnedECPoint.get_point, keystore2_crypto.zvec.ZVec,
core.fmt.Arguments.from_str_nonconst, anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypt_message_closure_ignores_error

recall decrypt_message_fail_deref_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (x : Error)
    (hd : zvecDeref key = fail x) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = fail x

/-- info: 'Keystore2Verify.EcCrypto.decrypt_message_fail_deref_key' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_decrypt, keystore2_crypto.ec_key_get0_public_key,
keystore2_crypto.ec_point_oct_to_point, keystore2_crypto.ec_point_point_to_oct,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypt_message_fail_deref_key

recall decrypt_message_fail_first_decrypt (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (x : Error)
    (hdec : keystore2_crypto.aes_gcm_decrypt ct iv tag ks = fail x) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = fail x

/-- info: 'Keystore2Verify.EcCrypto.decrypt_message_fail_first_decrypt' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_decrypt, keystore2_crypto.ec_key_get0_public_key,
keystore2_crypto.ec_point_oct_to_point, keystore2_crypto.ec_point_point_to_oct,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypt_message_fail_first_decrypt

recall decrypt_message_fail_deref_legacy_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8)
    (e1 : keystore2_crypto.error.Error)
    (key2 : keystore2_crypto.zvec.ZVec)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (hdec1 : keystore2_crypto.aes_gcm_decrypt ct iv tag ks = ok (.Err e1))
    (ha2 : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.LegacyTruncated = ok (.Ok key2))
    (x : Error)
    (hd2 : zvecDeref key2 = fail x) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = fail x

/-- info: 'Keystore2Verify.EcCrypto.decrypt_message_fail_deref_legacy_key' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_decrypt, keystore2_crypto.ec_key_get0_public_key,
keystore2_crypto.ec_point_oct_to_point, keystore2_crypto.ec_point_point_to_oct,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypt_message_fail_deref_legacy_key

recall decrypt_message_fail_legacy_decrypt (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8)
    (e1 : keystore2_crypto.error.Error)
    (key2 : keystore2_crypto.zvec.ZVec)
    (ks2 : Slice Std.U8)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (hdec1 : keystore2_crypto.aes_gcm_decrypt ct iv tag ks = ok (.Err e1))
    (ha2 : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.LegacyTruncated = ok (.Ok key2))
    (hd2 : zvecDeref key2 = ok ks2)
    (x : Error)
    (hdec2 : keystore2_crypto.aes_gcm_decrypt ct iv tag ks2 = fail x) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = fail x

/-- info: 'Keystore2Verify.EcCrypto.decrypt_message_fail_legacy_decrypt' depends on axioms:
[propext, Classical.choice, Quot.sound, anyhow.Error, binder.ExceptionCode, binder.StatusCode,
keystore2_crypto.BorrowedECPoint, keystore2_crypto.ECKey, keystore2_crypto.OwnedECPoint,
keystore2_crypto.aes_gcm_decrypt, keystore2_crypto.ec_key_get0_public_key,
keystore2_crypto.ec_point_oct_to_point, keystore2_crypto.ec_point_point_to_oct,
keystore2_crypto.ecdh_compute_key, keystore2_crypto.hkdf_expand, keystore2_crypto.hkdf_extract,
keystore2_crypto_bindgen.ec_point_st, alloc.fmt.format,
keystore2_crypto.BorrowedECPoint.get_point, keystore2_crypto.OwnedECPoint.get_point,
keystore2_crypto.zvec.ZVec, core.fmt.Arguments.from_str_nonconst,
anyhow.Error.Insts.AnyhowContextExtStdError.ext_context,
alloc.string.String.Insts.CoreFmtDisplay.fmt, anyhow.context.ext.StdError.Blanket.ext_context,
core.result.Result.Insts.AnyhowContext.context,
keystore2_crypto.error.Error.Insts.CoreFmtDebug.fmt,
keystore2_crypto.error.Error.Insts.CoreFmtDisplay.fmt,
keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8.deref] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypt_message_fail_legacy_decrypt

recall ec_crypto_laws_satisfiable :
    ∃ (Z : Type) (deref : Z → Result (Slice Std.U8))
      (expand : Std.Usize → Slice Std.U8 → Slice Std.U8 →
        Result (core.result.Result Z keystore2_crypto.error.Error))
      (extract : Slice Std.U8 → Slice Std.U8 →
        Result (core.result.Result Z keystore2_crypto.error.Error))
      (salt : Result (core.result.Result (alloc.vec.Vec Std.U8) keystore2_crypto.error.Error))
      (marshal : Unit →
        Result (core.result.Result Z keystore2_crypto.error.Error))
      (to_oct : Unit →
        Result (core.result.Result (alloc.vec.Vec Std.U8) keystore2_crypto.error.Error))
      (enc : Slice Std.U8 → Slice Std.U8 → Result (core.result.Result
        (alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8)
        keystore2_crypto.error.Error))
      (dec : Slice Std.U8 → Slice Std.U8 → Slice Std.U8 → Slice Std.U8 →
        Result (core.result.Result Z keystore2_crypto.error.Error)),
      TotalLaw deref ∧ HkdfExpandLenLaw deref expand ∧ HkdfExtractLenLaw deref extract ∧
      SaltLenLaw salt ∧ EcKeyMarshalLenLaw deref marshal ∧ PointToOctLenLaw to_oct ∧
      AesGcmEncryptLenLaw enc ∧ AesGcmDecryptLenLaw deref dec ∧
      (∃ n prk info z, expand n prk info = ok (.Ok z)) ∧
      (∃ secret salt' z, extract secret salt' = ok (.Ok z)) ∧
      (∃ s, salt = ok (.Ok s)) ∧
      (∀ key, ∃ z, marshal key = ok (.Ok z)) ∧
      (∀ pt, ∃ v, to_oct pt = ok (.Ok v)) ∧
      (∃ m k ct iv tag, enc m k = ok (.Ok (ct, iv, tag))) ∧
      (∃ data iv tag key p, dec data iv tag key = ok (.Ok p))

/-- info: 'Keystore2Verify.EcCrypto.ec_crypto_laws_satisfiable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ec_crypto_laws_satisfiable

end Keystore2Verify.EcCrypto
