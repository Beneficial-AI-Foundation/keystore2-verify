import Keystore2Verify.Proofs.KmCompat.KeyImportDataNew
import Keystore2Verify.Proofs.KmCompat.WrapKeyblob
import Keystore2Verify.Proofs.KmCompat.UnwrapKeyblob
import Keystore2Verify.Proofs.KmCompat.Detectors

namespace Keystore2Verify.KmCompat
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open keystore2.core.slice.Slice renaming starts_with → sliceStartsWith
open keystore2.Shared0Slice.Insts.CoreCmpPartialEqVec renaming eq → sliceVecEq
open km_compat renaming wrap_keyblob → wrapKeyblob, unwrap_keyblob → unwrapKeyblob

recall key_import_data_new_pkcs8 (key_data : Slice Std.U8) :
    km_compat.KeyImportData.new 1#i32 key_data = ok (.Ok (.Pkcs8 key_data))

recall key_import_data_new_raw (key_data : Slice Std.U8) :
    km_compat.KeyImportData.new 3#i32 key_data = ok (.Ok (.Raw key_data))

recall key_import_data_new_err (key_format : Std.I32) (key_data : Slice Std.U8)
    (ec : Std.I32) (s : binder.Status)
    (h1 : key_format ≠ 1#i32) (h3 : key_format ≠ 3#i32)
    (hec : ErrorCode.ErrorCode.UNSUPPORTED_KEY_FORMAT = ok ec)
    (hs : binder.Status.new_service_specific_error ec none = ok s) :
    km_compat.KeyImportData.new key_format key_data = ok (.Err s)

recall wrap_keyblob_ok (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (root : anyhow.Error → ErrRoot) (hctx : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (keyblob : Slice Std.U8) (n : Std.Usize)
    (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hcap : km_compat.KEYBLOB_PREFIX.length + keyblob.val.length + n.val ≤ Std.Usize.max)
    (tag : alloc.vec.Vec Std.U8)
    (hfit : km_compat.KEYBLOB_PREFIX.length + keyblob.val.length + tag.val.length
      ≤ Std.Usize.max)
    (hmac : keystore2_crypto.hmac_sha256 km_compat.KEYBLOB_HMAC_KEY keyblob = ok (.Ok tag)) :
    ∃ v, wrapKeyblob keyblob = ok (.Ok v) ∧
      v.val = km_compat.KEYBLOB_PREFIX.val ++ keyblob.val ++ tag.val

recall wrap_keyblob_err (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (root : anyhow.Error → ErrRoot) (hctx : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (keyblob : Slice Std.U8) (n : Std.Usize)
    (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hcap : km_compat.KEYBLOB_PREFIX.length + keyblob.val.length + n.val ≤ Std.Usize.max)
    (x : keystore2_crypto.error.Error)
    (hmac : keystore2_crypto.hmac_sha256 km_compat.KEYBLOB_HMAC_KEY keyblob = ok (.Err x)) :
    ∃ e, wrapKeyblob keyblob = ok (.Err e) ∧ root e = ErrRoot.crypto x

recall wrap_keyblob_fail_hmac (keyblob : Slice Std.U8) (n : Std.Usize) (x : Error)
    (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hcap : km_compat.KEYBLOB_PREFIX.length + keyblob.val.length + n.val ≤ Std.Usize.max)
    (hmac : keystore2_crypto.hmac_sha256 km_compat.KEYBLOB_HMAC_KEY keyblob = fail x) :
    wrapKeyblob keyblob = fail x

recall wrap_keyblob_fail_len_add (keyblob : Slice Std.U8)
    (hover : Std.Usize.max < km_compat.KEYBLOB_PREFIX.length + keyblob.val.length) :
    wrapKeyblob keyblob = fail .integerOverflow

recall wrap_keyblob_fail_cap_add (keyblob : Slice Std.U8) (n : Std.Usize)
    (hfit : km_compat.KEYBLOB_PREFIX.length + keyblob.val.length ≤ Std.Usize.max)
    (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hover : Std.Usize.max < km_compat.KEYBLOB_PREFIX.length + keyblob.val.length + n.val) :
    wrapKeyblob keyblob = fail .integerOverflow

recall wrap_keyblob_fail_hmac_len (keyblob : Slice Std.U8) (x : Error)
    (hfit : km_compat.KEYBLOB_PREFIX.length + keyblob.val.length ≤ Std.Usize.max)
    (hn : keystore2_crypto.HMAC_SHA256_LEN = fail x) :
    wrapKeyblob keyblob = fail x

recall wrap_keyblob_fail_append (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (root : anyhow.Error → ErrRoot) (hctx : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (keyblob : Slice Std.U8) (n : Std.Usize)
    (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hcap : km_compat.KEYBLOB_PREFIX.length + keyblob.val.length + n.val ≤ Std.Usize.max)
    (tag : alloc.vec.Vec Std.U8)
    (hover : Std.Usize.max <
      km_compat.KEYBLOB_PREFIX.length + keyblob.val.length + tag.val.length)
    (hmac : keystore2_crypto.hmac_sha256 km_compat.KEYBLOB_HMAC_KEY keyblob = ok (.Ok tag)) :
    wrapKeyblob keyblob = fail .panic

recall unwrap_keyblob_raw_no_prefix (hstart : CoreSliceStartsWithSpec)
    (keyblob : Slice Std.U8) (hpre : ¬ km_compat.KEYBLOB_PREFIX.val <+: keyblob.val) :
    unwrapKeyblob keyblob = ok (.Raw keyblob)

recall unwrap_keyblob_raw_short (hstart : CoreSliceStartsWithSpec) (keyblob : Slice Std.U8)
    (hpre : km_compat.KEYBLOB_PREFIX.val <+: keyblob.val)
    (n : Std.Usize) (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hshort : (unwrapRest keyblob).length < n.val) :
    unwrapKeyblob keyblob = ok (.Raw keyblob)

recall unwrap_keyblob_wrapped (hstart : CoreSliceStartsWithSpec) (keyblob : Slice Std.U8)
    (hpre : km_compat.KEYBLOB_PREFIX.val <+: keyblob.val)
    (n : Std.Usize) (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hlen : n.val ≤ (unwrapRest keyblob).length)
    (heq : Shared0SliceEqSpec) (inner want : Slice Std.U8) (tag : alloc.vec.Vec Std.U8)
    (hinner : inner.val = unwrapInner keyblob n.val)
    (hwant : want.val = unwrapTag keyblob n.val)
    (hmac : keystore2_crypto.hmac_sha256 km_compat.KEYBLOB_HMAC_KEY inner = ok (.Ok tag))
    (htag : want.val = tag.val) :
    unwrapKeyblob keyblob = ok (.Wrapped inner)

recall unwrap_keyblob_raw_tag_differs (hstart : CoreSliceStartsWithSpec) (keyblob : Slice Std.U8)
    (hpre : km_compat.KEYBLOB_PREFIX.val <+: keyblob.val)
    (n : Std.Usize) (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hlen : n.val ≤ (unwrapRest keyblob).length)
    (heq : Shared0SliceEqSpec) (inner want : Slice Std.U8) (tag : alloc.vec.Vec Std.U8)
    (hinner : inner.val = unwrapInner keyblob n.val)
    (hwant : want.val = unwrapTag keyblob n.val)
    (hmac : keystore2_crypto.hmac_sha256 km_compat.KEYBLOB_HMAC_KEY inner = ok (.Ok tag))
    (htag : want.val ≠ tag.val) :
    unwrapKeyblob keyblob = ok (.Raw keyblob)

recall unwrap_keyblob_raw_hmac_err (hstart : CoreSliceStartsWithSpec) (keyblob : Slice Std.U8)
    (hpre : km_compat.KEYBLOB_PREFIX.val <+: keyblob.val)
    (n : Std.Usize) (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hlen : n.val ≤ (unwrapRest keyblob).length)
    (hcmp : LogLevelPartialCmpSpec) (hmax : LogMaxLevelSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) (inner : Slice Std.U8)
    (x : keystore2_crypto.error.Error)
    (hinner : inner.val = unwrapInner keyblob n.val)
    (hmac : keystore2_crypto.hmac_sha256 km_compat.KEYBLOB_HMAC_KEY inner = ok (.Err x)) :
    unwrapKeyblob keyblob = ok (.Raw keyblob)

recall unwrap_keyblob_fail_hmac (hstart : CoreSliceStartsWithSpec) (keyblob : Slice Std.U8)
    (hpre : km_compat.KEYBLOB_PREFIX.val <+: keyblob.val)
    (n : Std.Usize) (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hlen : n.val ≤ (unwrapRest keyblob).length)
    (inner : Slice Std.U8) (x : Error)
    (hinner : inner.val = unwrapInner keyblob n.val)
    (hmac : keystore2_crypto.hmac_sha256 km_compat.KEYBLOB_HMAC_KEY inner = fail x) :
    unwrapKeyblob keyblob = fail x

recall unwrap_keyblob_fail_hmac_len (hstart : CoreSliceStartsWithSpec)
    (keyblob : Slice Std.U8) (hpre : km_compat.KEYBLOB_PREFIX.val <+: keyblob.val) (x : Error)
    (hn : keystore2_crypto.HMAC_SHA256_LEN = fail x) :
    unwrapKeyblob keyblob = fail x

recall key_mint_v1_new (sec_level : SecurityLevel.SecurityLevel) :
    km_compat.KeyMintV1.new sec_level = ok { sec_level := sec_level }

recall keymaster_new (sec_level : SecurityLevel.SecurityLevel) :
    km_compat.Keymaster.new sec_level = ok { v1 := { sec_level := sec_level } }

end Keystore2Verify.KmCompat
