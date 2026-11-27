import Keystore2Verify.Proofs.LegacyBlob.ErrorEq
import Keystore2Verify.Proofs.LegacyBlob.BlobValueEq
import Keystore2Verify.Proofs.LegacyBlob.LegacyKeyCharacteristics
import Keystore2Verify.Proofs.LegacyBlob.BlobEq
import Keystore2Verify.Proofs.LegacyBlob.BlobNew
import Keystore2Verify.Proofs.LegacyBlob.BlobGetFlags
import Keystore2Verify.Proofs.LegacyBlob.BlobIsFallback
import Keystore2Verify.Proofs.LegacyBlob.BlobIsEncrypted
import Keystore2Verify.Proofs.LegacyBlob.BlobIsCriticalToDeviceEncryption
import Keystore2Verify.Proofs.LegacyBlob.BlobIsStrongbox
import Keystore2Verify.Proofs.LegacyBlob.BlobValue
import Keystore2Verify.Proofs.LegacyBlob.BlobTakeValue
import Keystore2Verify.Proofs.LegacyBlob.LoaderNew
import Keystore2Verify.Proofs.LegacyBlob.DecodeAlias
import Keystore2Verify.Proofs.LegacyBlob.TagType
import Keystore2Verify.Proofs.LegacyBlob.ReadCharacteristicsFile
import Keystore2Verify.Proofs.LegacyBlob.ReadLegacyKeystoreEntry
import Keystore2Verify.Proofs.LegacyBlob.RemoveLegacyKeystoreEntry
import Keystore2Verify.Proofs.LegacyBlob.ExtractLegacyAlias
import Keystore2Verify.Proofs.LegacyBlob.MakeLegacyKeystoreEntryFilename
import Keystore2Verify.Proofs.LegacyBlob.MakeBlobFilename
import Keystore2Verify.Proofs.LegacyBlob.MakeChrFilename
import Keystore2Verify.Proofs.LegacyBlob.MakeSuperKeyFilename
import Keystore2Verify.Proofs.LegacyBlob.MakeUserPathName
import Keystore2Verify.Proofs.LegacyBlob.IsEmptyUser
import Keystore2Verify.Proofs.LegacyBlob.ListUser
import Keystore2Verify.Proofs.LegacyBlob.WithRetryInterrupted
import Keystore2Verify.Proofs.LegacyBlob.MoveKeystoreFileIfExists
import Keystore2Verify.Proofs.LegacyBlob.RemoveUserDirIfEmpty
import Keystore2Verify.Proofs.LegacyBlob.HasSuperKey
import Keystore2Verify.Proofs.LegacyBlob.LoadSuperKey
import Keystore2Verify.Proofs.LegacyBlob.RemoveSuperKey


namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

section ErrorEq
open legacy_blob.Error.Insts renaming CoreCmpPartialEqError.eq → errorEq

recall legacy_blob_error_eq (a b : legacy_blob.Error) :
    errorEq a b = ok (decide (errorIndex a = errorIndex b))

end ErrorEq

section BlobValueEq
open legacy_blob.BlobValue.Insts renaming CoreCmpPartialEqBlobValue.eq → blobValueEq
open keystore2_crypto.zvec.ZVec.Insts renaming CoreCmpPartialEqZVec.eq → zvecEq

recall blob_value_eq_variant_ne (a b : legacy_blob.BlobValue)
    (h : blobValueIndex a ≠ blobValueIndex b) : blobValueEq a b = ok false

recall blob_value_eq_generic (a b : alloc.vec.Vec Std.U8) :
    blobValueEq (.Generic a) (.Generic b) = ok (decide (a.val = b.val))

recall blob_value_eq_characteristics (a b : alloc.vec.Vec Std.U8) :
    blobValueEq (.Characteristics a) (.Characteristics b) = ok (decide (a.val = b.val))

recall blob_value_eq_characteristics_cache (a b : alloc.vec.Vec Std.U8) :
    blobValueEq (.CharacteristicsCache a) (.CharacteristicsCache b) =
      ok (decide (a.val = b.val))

recall blob_value_eq_encrypted_characteristics
    (iv tag data iv' tag' data' : alloc.vec.Vec Std.U8) :
    blobValueEq (.EncryptedCharacteristics iv tag data) (.EncryptedCharacteristics iv' tag' data') =
      ok (decide (iv.val = iv'.val ∧ tag.val = tag'.val ∧ data.val = data'.val))

recall blob_value_eq_pw_encrypted (iv tag data salt iv' tag' data' salt' : alloc.vec.Vec Std.U8)
    (n n' : Std.Usize) :
    blobValueEq (.PwEncrypted iv tag data salt n) (.PwEncrypted iv' tag' data' salt' n') =
      ok (decide (iv.val = iv'.val ∧ tag.val = tag'.val ∧ data.val = data'.val ∧
        salt.val = salt'.val ∧ n.val = n'.val))

recall blob_value_eq_encrypted (iv tag data iv' tag' data' : alloc.vec.Vec Std.U8) :
    blobValueEq (.Encrypted iv tag data) (.Encrypted iv' tag' data') =
      ok (decide (iv.val = iv'.val ∧ tag.val = tag'.val ∧ data.val = data'.val))

recall blob_value_eq_encrypted_generic (iv tag data iv' tag' data' : alloc.vec.Vec Std.U8) :
    blobValueEq (.EncryptedGeneric iv tag data) (.EncryptedGeneric iv' tag' data') =
      ok (decide (iv.val = iv'.val ∧ tag.val = tag'.val ∧ data.val = data'.val))

recall blob_value_eq_decrypted (a b : keystore2_crypto.zvec.ZVec) :
    blobValueEq (.Decrypted a) (.Decrypted b) = zvecEq a b

recall blob_value_eq_decrypted_content {α : Type} (view : keystore2_crypto.zvec.ZVec → α)
    (h : ZVecEqSpec view) (a b : keystore2_crypto.zvec.ZVec) :
    ∃ r, blobValueEq (.Decrypted a) (.Decrypted b) = ok r ∧ (r = true ↔ view a = view b)

end BlobValueEq

section LegacyKeyCharacteristics
open legacy_blob.LegacyKeyCharacteristics.Insts
open alloc.vec.CloneVec renaming clone → vecClone
open alloc.vec.partial_eq.PartialEqVec renaming eq → vecEq
open alloc.vec.Vec.Insts.CoreCmpOrd renaming cmp → vecCmp
open CoreCloneClone renaming clone → lkcClone
open CoreCmpPartialEqLegacyKeyCharacteristics renaming eq → lkcEq
open CoreCmpOrd renaming cmp → lkcCmp
open CoreCmpPartialOrdLegacyKeyCharacteristics renaming partial_cmp → lkcPartialCmp
open key_parameter.KeyParameter.Insts renaming CoreCloneClone.clone → kpClone
open key_parameter.KeyParameter.Insts renaming CoreCloneClone → kpCloneInst
open key_parameter.KeyParameter.Insts renaming CoreCmpOrd → kpOrdInst
open key_parameter.KeyParameter.Insts renaming CoreCmpPartialEqKeyParameter → kpEqInst

recall lkc_clone_cache (v : alloc.vec.Vec key_parameter.KeyParameter)
    (r : legacy_blob.LegacyKeyCharacteristics) :
    lkcClone (.Cache v) = ok r ↔ ∃ v', vecClone kpCloneInst v = ok v' ∧
      r = .Cache v'

recall lkc_clone_file (v : alloc.vec.Vec key_parameter.KeyParameter)
    (r : legacy_blob.LegacyKeyCharacteristics) :
    lkcClone (.File v) = ok r ↔ ∃ v', vecClone kpCloneInst v = ok v' ∧
      r = .File v'

recall lkc_clone_eq (hkp : ∀ x, kpClone x = ok x) (x : legacy_blob.LegacyKeyCharacteristics) :
    lkcClone x = ok x

recall lkc_eq_variant_ne (a b : legacy_blob.LegacyKeyCharacteristics)
    (h : characteristicsIndex a ≠ characteristicsIndex b) : lkcEq a b = ok false

recall lkc_eq_cache (a b : alloc.vec.Vec key_parameter.KeyParameter) :
    lkcEq (.Cache a) (.Cache b) =
      vecEq kpEqInst a b

recall lkc_eq_file (a b : alloc.vec.Vec key_parameter.KeyParameter) :
    lkcEq (.File a) (.File b) =
      vecEq kpEqInst a b

recall lkc_cmp_cache_file (a b : alloc.vec.Vec key_parameter.KeyParameter) :
    lkcCmp (.Cache a) (.File b) = ok Ordering.lt

recall lkc_cmp_file_cache (a b : alloc.vec.Vec key_parameter.KeyParameter) :
    lkcCmp (.File a) (.Cache b) = ok Ordering.gt

recall lkc_cmp_cache (a b : alloc.vec.Vec key_parameter.KeyParameter) :
    lkcCmp (.Cache a) (.Cache b) =
      vecCmp alloc.alloc.Global kpOrdInst a b

recall lkc_cmp_file (a b : alloc.vec.Vec key_parameter.KeyParameter) :
    lkcCmp (.File a) (.File b) =
      vecCmp alloc.alloc.Global kpOrdInst a b

recall lkc_partial_cmp (a b : legacy_blob.LegacyKeyCharacteristics)
    (r : Option Ordering) :
    lkcPartialCmp a b = ok r ↔ ∃ o, lkcCmp a b = ok o ∧ r = some o

recall lkc_eq_content
    (hkp : ∀ x y, ∃ r, kpEqInst.eq x y = ok r ∧ (r = true ↔ x = y))
    (a b : legacy_blob.LegacyKeyCharacteristics)
    (h : characteristicsIndex a = characteristicsIndex b) :
    ∃ r, lkcEq a b = ok r ∧ (r = true ↔ lkcList a = lkcList b)

recall lkc_cmp_order
    (c : key_parameter.KeyParameter → key_parameter.KeyParameter → Ordering)
    (hc : ∀ x y, kpOrdInst.cmp x y = ok (c x y)) (hv : VecCmpSpec c)
    (a b : legacy_blob.LegacyKeyCharacteristics) :
    lkcCmp a b = ok (lkcOrder c a b)

recall lkc_partial_cmp_order
    (c : key_parameter.KeyParameter → key_parameter.KeyParameter → Ordering)
    (hc : ∀ x y, kpOrdInst.cmp x y = ok (c x y)) (hv : VecCmpSpec c)
    (a b : legacy_blob.LegacyKeyCharacteristics) :
    lkcPartialCmp a b = ok (some (lkcOrder c a b))

end LegacyKeyCharacteristics

section BlobEq
open legacy_blob.Blob.Insts renaming CoreCmpPartialEqBlob.eq → blobEq
open legacy_blob.BlobValue.Insts renaming CoreCmpPartialEqBlobValue.eq → blobValueEq

recall blob_eq_flags_ne (a b : legacy_blob.Blob) (h : a.flags ≠ b.flags) :
    blobEq a b = ok false

recall blob_eq_flags_eq (a b : legacy_blob.Blob) (h : a.flags = b.flags) :
    blobEq a b = blobValueEq a.value b.value

end BlobEq

section BlobNew

recall blob_new (flags : Std.U8) (value : legacy_blob.BlobValue) :
    legacy_blob.Blob.new flags value = ok { flags := flags, value := value }

end BlobNew

section BlobGetFlags

recall blob_get_flags (b : legacy_blob.Blob) : legacy_blob.Blob.get_flags b = ok b.flags

end BlobGetFlags

section BlobIsFallback

recall blob_is_fallback (b : legacy_blob.Blob) :
    legacy_blob.Blob.is_fallback b = ok (flagSet b 1)

end BlobIsFallback

section BlobIsEncrypted

recall blob_is_encrypted (b : legacy_blob.Blob) :
    legacy_blob.Blob.is_encrypted b = ok (flagSet b 2 || flagSet b 0)

end BlobIsEncrypted

section BlobIsCriticalToDeviceEncryption

recall blob_is_critical_to_device_encryption (b : legacy_blob.Blob) :
    legacy_blob.Blob.is_critical_to_device_encryption b = ok (flagSet b 3)

end BlobIsCriticalToDeviceEncryption

section BlobIsStrongbox

recall blob_is_strongbox (b : legacy_blob.Blob) :
    legacy_blob.Blob.is_strongbox b = ok (flagSet b 4)

end BlobIsStrongbox

section BlobValue
open legacy_blob.Blob.impl renaming value → implValue

recall blob_value (b : legacy_blob.Blob) : implValue b = ok b.value

end BlobValue

section BlobTakeValue

recall blob_take_value (b : legacy_blob.Blob) : legacy_blob.Blob.take_value b = ok b.value

end BlobTakeValue

section LoaderNew
open legacy_blob.LegacyBlobLoader
open std.path.Path.Insts.AllocBorrowToOwnedPathBuf renaming to_owned → pathToOwned

recall legacy_blob_loader_new_ok (path : std.path.Path) (pb : std.path.PathBuf)
    (h : pathToOwned path = ok pb) :
    legacy_blob.LegacyBlobLoader.new path = ok { path := pb }

recall legacy_blob_loader_new_fail (path : std.path.Path) (x : Error)
    (h : pathToOwned path = fail x) :
    legacy_blob.LegacyBlobLoader.new path = fail x

end LoaderNew

section DecodeAlias
open legacy_blob.LegacyBlobLoader

recall decode_alias_bad_encoding (root : anyhow.Error → ErrRoot)
    (view : StrBytesIter → List Std.U8)
    (hbytes : StrBytesSpec view) (hnext : BytesNextSpec view) (hmsg : MessageSpecs)
    (hctx : LegacyErrCtxLaw root String) (nm : Str)
    (hbad : decodeNat none (nm.val.map (·.val)) [] = none) :
    ∃ e, decode_alias nm = ok (.Err e) ∧ root e = ErrRoot.other

recall decode_alias_ok (root : anyhow.Error → ErrRoot)
    (view : StrBytesIter → List Std.U8)
    (hbytes : StrBytesSpec view) (hnext : BytesNextSpec view) (hutf : StringFromUtf8Spec)
    (hmsg : MessageSpecs) (hctx : Utf8ErrCtxLaw root String) (nm : Str) (acc : List Nat)
    (hdec : decodeNat none (nm.val.map (·.val)) [] = some acc)
    (hvalid : ∃ s, (utf8Bytes s).map (·.val) = acc) :
    ∃ s, decode_alias nm = ok (.Ok s) ∧ (utf8Bytes s).map (·.val) = acc

recall decode_alias_invalid_utf8 (root : anyhow.Error → ErrRoot)
    (view : StrBytesIter → List Std.U8)
    (hbytes : StrBytesSpec view) (hnext : BytesNextSpec view) (hutf : StringFromUtf8Spec)
    (hmsg : MessageSpecs) (hctx : Utf8ErrCtxLaw root String) (nm : Str) (acc : List Nat)
    (hdec : decodeNat none (nm.val.map (·.val)) [] = some acc)
    (hvalid : ¬ ∃ s, (utf8Bytes s).map (·.val) = acc) :
    ∃ e, decode_alias nm = ok (.Err e) ∧ root e = ErrRoot.other

end DecodeAlias

section TagType
open legacy_blob.LegacyBlobLoader
open android_hardware_security_keymint.aidl.android.hardware.security.keymint

recall legacy_blob_tag_type
    (tag : Tag.Tag) :
    ∃ r, tag_type tag = ok r ∧ r.bv = tag.bv &&& 4278190080#32

end TagType

section ReadCharacteristicsFile
open legacy_blob.LegacyBlobLoader
open android_system_keystore2.aidl.android.system.keystore2.ResponseCode.ResponseCode
open android_hardware_security_keymint.aidl.android.hardware.security.keymint.SecurityLevel

recall read_characteristics_file_absent (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob)) (self : legacy_blob.LegacyBlobLoader)
    (uid : utils.AppUid) (pre al : Str) (hw : SecurityLevel) (sk : SuperKey)
    (pb : std.path.PathBuf) (p : std.path.Path)
    (hchr : make_chr_filename self uid al pre = ok pb)
    (hd : pathBufDeref pb = ok p)
    (hr : read_generic_blob p = ok (.Ok none)) :
    ∃ v, read_characteristics_file self uid pre al hw sk = ok (.Ok (.Cache v)) ∧
      v.val = []

recall read_characteristics_file_read_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob)) (self : legacy_blob.LegacyBlobLoader)
    (uid : utils.AppUid) (pre al : Str) (hw : SecurityLevel) (sk : SuperKey)
    (pb : std.path.PathBuf) (p : std.path.Path) (e : anyhow.Error)
    (hchr : make_chr_filename self uid al pre = ok pb)
    (hd : pathBufDeref pb = ok p)
    (hr : read_generic_blob p = ok (.Err e)) :
    ∃ e', read_characteristics_file self uid pre al hw sk = ok (.Err e') ∧
      root e' = root e

recall read_characteristics_file_decrypt_err (root : anyhow.Error → ErrRoot)
    (hmsg : MessageSpecs) (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hctx' : AnyCtxLaw root legacy_blob.Blob) (self : legacy_blob.LegacyBlobLoader)
    (uid : utils.AppUid) (pre al : Str) (hw : SecurityLevel) (sk : SuperKey)
    (pb : std.path.PathBuf) (p : std.path.Path) (blob : legacy_blob.Blob) (e : anyhow.Error)
    (hchr : make_chr_filename self uid al pre = ok pb)
    (hd : pathBufDeref pb = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hdec : decrypt_if_required sk blob = ok (.Err e)) :
    ∃ e', read_characteristics_file self uid pre al hw sk = ok (.Err e') ∧
      root e' = root e

recall read_characteristics_file_wrong_type (root : anyhow.Error → ErrRoot)
    (hmsg : MessageSpecs) (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hctx' : AnyCtxLaw root legacy_blob.Blob)
    (hks : KsErrCtxLaw root legacy_blob.LegacyKeyCharacteristics)
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (pre al : Str) (hw : SecurityLevel)
    (sk : SuperKey) (pb : std.path.PathBuf) (p : std.path.Path) (blob blob' : legacy_blob.Blob)
    (rc : Std.I32)
    (hchr : make_chr_filename self uid al pre = ok pb)
    (hd : pathBufDeref pb = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hdec : decrypt_if_required sk blob = ok (.Ok blob'))
    (hv : ¬ IsCharacteristics blob'.value) (hrc : VALUE_CORRUPTED = ok rc) :
    ∃ e', read_characteristics_file self uid pre al hw sk = ok (.Err e') ∧
      root e' = ErrRoot.ks (error.Error.Rc rc)

recall read_characteristics_file_file (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob)) (hctx' : AnyCtxLaw root legacy_blob.Blob)
    (hctx'' : AnyCtxLaw root (alloc.vec.Vec key_parameter.KeyParameterValue))
    (viewSw : SwMap → List key_parameter.KeyParameter) (viewOpt : HwOpt → List HwMap)
    (viewHw : HwMap → List key_parameter.KeyParameter)
    (viewFlat : HwFlat → List key_parameter.KeyParameter)
    (viewChain : ParamChain → List key_parameter.KeyParameter)
    (hsw : MapSwSpec viewSw) (hopt : OptionIntoIterSpec viewOpt)
    (hflat : FlattenSpec viewOpt viewHw viewFlat) (hchain : ChainSpec viewFlat viewSw viewChain)
    (hnext : ChainNextSpec viewChain)
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (pre al : Str) (hw : SecurityLevel)
    (sk : SuperKey) (pb : std.path.PathBuf) (p : std.path.Path) (blob blob' : legacy_blob.Blob)
    (data : alloc.vec.Vec Std.U8) (stream rest : Slice Std.U8)
    (vals : alloc.vec.Vec key_parameter.KeyParameterValue) (sl : SecurityLevel)
    (hchr : make_chr_filename self uid al pre = ok pb)
    (hd : pathBufDeref pb = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hdec : decrypt_if_required sk blob = ok (.Ok blob'))
    (hv : blob'.value = .Characteristics data) (hs : stream.val = data.val)
    (hrk : read_key_parameters stream = ok (.Ok vals, rest)) (hks : KEYSTORE = ok sl)
    (hlen : vals.val.length ≤ Std.Usize.max) :
    ∃ params, read_characteristics_file self uid pre al hw sk = ok (.Ok (.File params)) ∧
      params.val = vals.val.map fun v => mkKeyParameter v sl

recall read_characteristics_file_cache (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob)) (hctx' : AnyCtxLaw root legacy_blob.Blob)
    (hctx'' : AnyCtxLaw root (alloc.vec.Vec key_parameter.KeyParameterValue))
    (viewHw : HwMap → List key_parameter.KeyParameter)
    (viewSw : SwMap → List key_parameter.KeyParameter) (viewOpt : HwOpt → List HwMap)
    (viewFlat : HwFlat → List key_parameter.KeyParameter)
    (viewChain : ParamChain → List key_parameter.KeyParameter)
    (hhw : MapHwSpec viewHw) (hsw : MapSwSpec viewSw) (hopt : OptionIntoIterSpec viewOpt)
    (hflat : FlattenSpec viewOpt viewHw viewFlat) (hchain : ChainSpec viewFlat viewSw viewChain)
    (hnext : ChainNextSpec viewChain)
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (pre al : Str) (hw : SecurityLevel)
    (sk : SuperKey) (pb : std.path.PathBuf) (p : std.path.Path) (blob blob' : legacy_blob.Blob)
    (data : alloc.vec.Vec Std.U8) (stream stream1 rest : Slice Std.U8)
    (hwl swl : alloc.vec.Vec key_parameter.KeyParameterValue) (sl : SecurityLevel)
    (hchr : make_chr_filename self uid al pre = ok pb)
    (hd : pathBufDeref pb = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hdec : decrypt_if_required sk blob = ok (.Ok blob'))
    (hv : blob'.value = .CharacteristicsCache data) (hs : stream.val = data.val)
    (hrk1 : read_key_parameters stream = ok (.Ok hwl, stream1))
    (hrk2 : read_key_parameters stream1 = ok (.Ok swl, rest)) (hks : KEYSTORE = ok sl)
    (hlen : hwl.val.length + swl.val.length ≤ Std.Usize.max) :
    ∃ params, read_characteristics_file self uid pre al hw sk = ok (.Ok (.Cache params)) ∧
      params.val = (hwl.val.map fun v => mkKeyParameter v hw) ++
        (swl.val.map fun v => mkKeyParameter v sl)

recall read_characteristics_file_hw_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob)) (hctx' : AnyCtxLaw root legacy_blob.Blob)
    (hctx'' : AnyCtxLaw root (alloc.vec.Vec key_parameter.KeyParameterValue))
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (pre al : Str) (hw : SecurityLevel)
    (sk : SuperKey) (pb : std.path.PathBuf) (p : std.path.Path) (blob blob' : legacy_blob.Blob)
    (data : alloc.vec.Vec Std.U8) (stream stream1 : Slice Std.U8) (e : anyhow.Error)
    (hchr : make_chr_filename self uid al pre = ok pb)
    (hd : pathBufDeref pb = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hdec : decrypt_if_required sk blob = ok (.Ok blob'))
    (hv : blob'.value = .CharacteristicsCache data) (hs : stream.val = data.val)
    (hrk1 : read_key_parameters stream = ok (.Err e, stream1)) :
    ∃ e', read_characteristics_file self uid pre al hw sk = ok (.Err e') ∧
      root e' = root e

recall read_characteristics_file_sw_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob)) (hctx' : AnyCtxLaw root legacy_blob.Blob)
    (hctx'' : AnyCtxLaw root (alloc.vec.Vec key_parameter.KeyParameterValue))
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (pre al : Str) (hw : SecurityLevel)
    (sk : SuperKey) (pb : std.path.PathBuf) (p : std.path.Path) (blob blob' : legacy_blob.Blob)
    (data : alloc.vec.Vec Std.U8) (stream rest : Slice Std.U8) (e : anyhow.Error)
    (hchr : make_chr_filename self uid al pre = ok pb)
    (hd : pathBufDeref pb = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hdec : decrypt_if_required sk blob = ok (.Ok blob'))
    (hv : blob'.value = .Characteristics data) (hs : stream.val = data.val)
    (hrk : read_key_parameters stream = ok (.Err e, rest)) :
    ∃ e', read_characteristics_file self uid pre al hw sk = ok (.Err e') ∧
      root e' = root e

recall read_characteristics_file_cache_sw_err (root : anyhow.Error → ErrRoot)
    (hmsg : MessageSpecs) (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hctx' : AnyCtxLaw root legacy_blob.Blob)
    (hctx'' : AnyCtxLaw root (alloc.vec.Vec key_parameter.KeyParameterValue))
    (viewHw : HwMap → List key_parameter.KeyParameter) (hhw : MapHwSpec viewHw)
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (pre al : Str) (hw : SecurityLevel)
    (sk : SuperKey) (pb : std.path.PathBuf) (p : std.path.Path) (blob blob' : legacy_blob.Blob)
    (data : alloc.vec.Vec Std.U8) (stream stream1 rest : Slice Std.U8)
    (hwl : alloc.vec.Vec key_parameter.KeyParameterValue) (e : anyhow.Error)
    (hchr : make_chr_filename self uid al pre = ok pb)
    (hd : pathBufDeref pb = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hdec : decrypt_if_required sk blob = ok (.Ok blob'))
    (hv : blob'.value = .CharacteristicsCache data) (hs : stream.val = data.val)
    (hrk1 : read_key_parameters stream = ok (.Ok hwl, stream1))
    (hrk2 : read_key_parameters stream1 = ok (.Err e, rest)) :
    ∃ e', read_characteristics_file self uid pre al hw sk = ok (.Err e') ∧
      root e' = root e

end ReadCharacteristicsFile

section ReadLegacyKeystoreEntry
open legacy_blob.LegacyBlobLoader
open core.ops.function
open read_legacy_keystore_entry.closure.Insts renaming
  CoreOpsFunctionFnOnceTupleBlobOptionVecU8 → entryClosureInst

recall read_legacy_keystore_entry_prefixed {F : Type} (inst : DecryptInst F)
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al : Str) (decrypt : F)
    (hfn : make_legacy_keystore_entry_filename self uid al = ok none) :
    read_legacy_keystore_entry inst self uid al decrypt = ok (.Ok none)

recall read_legacy_keystore_entry_absent {F : Type} (inst : DecryptInst F)
    (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hand : OptionAndThenSpec
      (entryClosureInst inst))
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al : Str) (decrypt : F)
    (path : std.path.PathBuf) (p : std.path.Path)
    (hfn : make_legacy_keystore_entry_filename self uid al = ok (some path))
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob_decrypt_with inst p decrypt = ok (.Ok none)) :
    read_legacy_keystore_entry inst self uid al decrypt = ok (.Ok none)

recall read_legacy_keystore_entry_generic {F : Type} (inst : DecryptInst F)
    (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hand : OptionAndThenSpec
      (entryClosureInst inst))
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al : Str) (decrypt : F)
    (path : std.path.PathBuf) (p : std.path.Path) (blob : legacy_blob.Blob)
    (bytes : alloc.vec.Vec Std.U8)
    (hfn : make_legacy_keystore_entry_filename self uid al = ok (some path))
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob_decrypt_with inst p decrypt = ok (.Ok (some blob)))
    (hv : blob.value = .Generic bytes) :
    read_legacy_keystore_entry inst self uid al decrypt = ok (.Ok (some bytes))

recall read_legacy_keystore_entry_other {F : Type} (inst : DecryptInst F)
    (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs) (hlog : LogSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hand : OptionAndThenSpec
      (entryClosureInst inst))
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al : Str) (decrypt : F)
    (path : std.path.PathBuf) (p : std.path.Path) (blob : legacy_blob.Blob)
    (hfn : make_legacy_keystore_entry_filename self uid al = ok (some path))
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob_decrypt_with inst p decrypt = ok (.Ok (some blob)))
    (hv : ∀ bytes, blob.value ≠ .Generic bytes) :
    read_legacy_keystore_entry inst self uid al decrypt = ok (.Ok none)

recall read_legacy_keystore_entry_err {F : Type} (inst : DecryptInst F)
    (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al : Str) (decrypt : F)
    (path : std.path.PathBuf) (p : std.path.Path) (e : anyhow.Error)
    (hfn : make_legacy_keystore_entry_filename self uid al = ok (some path))
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob_decrypt_with inst p decrypt = ok (.Err e)) :
    ∃ e', read_legacy_keystore_entry inst self uid al decrypt = ok (.Err e') ∧
      root e' = root e

end ReadLegacyKeystoreEntry

section RemoveLegacyKeystoreEntry
open legacy_blob.LegacyBlobLoader
open std.path.PathBuf renaming as_path → pathBufAsPath

recall remove_legacy_keystore_entry_prefixed (self : legacy_blob.LegacyBlobLoader)
    (uid : utils.AppUid) (al : Str)
    (hfn : make_legacy_keystore_entry_filename self uid al = ok none) :
    remove_legacy_keystore_entry self uid al = ok (.Ok false)

recall remove_legacy_keystore_entry_removed (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hctx : AnyCtxLaw root Unit)
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al : Str)
    (path : std.path.PathBuf) (q : std.path.Path) (r : Unit) (user : utils.AndroidUserId)
    (hfn : make_legacy_keystore_entry_filename self uid al = ok (some path))
    (hasp : pathBufAsPath path = ok q) (hrm : removeFileCall q = ok (.Ok r))
    (hu : utils.AppUid.owning_user uid = ok user)
    (hdir : remove_user_dir_if_empty self user = ok (.Ok ())) :
    remove_legacy_keystore_entry self uid al = ok (.Ok true)

recall remove_legacy_keystore_entry_dir_err (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hctx : AnyCtxLaw root Unit)
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al : Str)
    (path : std.path.PathBuf) (q : std.path.Path) (r : Unit) (user : utils.AndroidUserId)
    (e : anyhow.Error)
    (hfn : make_legacy_keystore_entry_filename self uid al = ok (some path))
    (hasp : pathBufAsPath path = ok q) (hrm : removeFileCall q = ok (.Ok r))
    (hu : utils.AppUid.owning_user uid = ok user)
    (hdir : remove_user_dir_if_empty self user = ok (.Err e)) :
    ∃ e', remove_legacy_keystore_entry self uid al = ok (.Err e') ∧ root e' = root e

recall remove_legacy_keystore_entry_not_found (self : legacy_blob.LegacyBlobLoader)
    (uid : utils.AppUid) (al : Str) (path : std.path.PathBuf) (q : std.path.Path) (e : IoError)
    (hfn : make_legacy_keystore_entry_filename self uid al = ok (some path))
    (hasp : pathBufAsPath path = ok q) (hrm : removeFileCall q = ok (.Err e))
    (hk : ioErrorKind e = ok ioNotFound) :
    remove_legacy_keystore_entry self uid al = ok (.Ok false)

recall remove_legacy_keystore_entry_io_err (root : anyhow.Error → ErrRoot)
    (hmsg : MessageSpecs) (hctx : IoErrCtxLaw root Bool)
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al : Str)
    (path : std.path.PathBuf) (q : std.path.Path) (e : IoError)
    (k : IoErrorKind)
    (hfn : make_legacy_keystore_entry_filename self uid al = ok (some path))
    (hasp : pathBufAsPath path = ok q) (hrm : removeFileCall q = ok (.Err e))
    (hk : ioErrorKind e = ok k) (hne : k ≠ ioNotFound) (hni : k ≠ ioInterrupted) :
    ∃ e', remove_legacy_keystore_entry self uid al = ok (.Err e') ∧
      root e' = ErrRoot.other

end RemoveLegacyKeystoreEntry

section ExtractLegacyAlias
open legacy_blob.LegacyBlobLoader

recall extract_legacy_alias_prefixed (enc : Str) (his : is_keystore_alias enc = ok true) :
    extract_legacy_alias enc = ok none

recall extract_legacy_alias_decoded (enc : Str) (a : String)
    (his : is_keystore_alias enc = ok false) (hdec : decode_alias enc = ok (.Ok a)) :
    extract_legacy_alias enc = ok (some a)

recall extract_legacy_alias_undecodable (enc : Str) (e : anyhow.Error)
    (his : is_keystore_alias enc = ok false) (hdec : decode_alias enc = ok (.Err e)) :
    extract_legacy_alias enc = ok none

end ExtractLegacyAlias

section MakeLegacyKeystoreEntryFilename
open legacy_blob.LegacyBlobLoader

recall make_legacy_keystore_entry_filename_prefixed (hlog : LogSpecs)
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al : Str)
    (his : is_keystore_alias al = ok true) :
    make_legacy_keystore_entry_filename self uid al = ok none

recall make_legacy_keystore_entry_filename_path (view : std.path.PathBuf → List Std.U8)
    (hclone : PathBufCloneSpec view) (hpush : PathBufPushStringSpec view)
    (hfmt : AllocFmtFormatSpec) (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid)
    (al : Str) (user : utils.AndroidUserId) (enc : String)
    (his : is_keystore_alias al = ok false) (hu : utils.AppUid.owning_user uid = ok user)
    (hen : encode_alias al = ok enc) :
    ∃ p s1 s2, make_legacy_keystore_entry_filename self uid al = ok (some p) ∧
      view p = pathPush (pathPush (view self.path) (utf8Bytes s1)) (utf8Bytes s2)

end MakeLegacyKeystoreEntryFilename

section MakeBlobFilename
open legacy_blob.LegacyBlobLoader

recall make_blob_filename_ok (view : std.path.PathBuf → List Std.U8)
    (hpush : PathBufPushStringSpec view) (hfmt : AllocFmtFormatSpec)
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al pre : Str)
    (user : utils.AndroidUserId) (s1 : String) (s2 : Str) (enc : String) (p0 : std.path.PathBuf)
    (hu : utils.AppUid.owning_user uid = ok user)
    (hf : alloc.fmt.format () = ok s1) (hd : stringAsStr s1 = ok s2)
    (henc : encode_alias s2 = ok enc) (hp : make_user_path_name self user = ok p0) :
    ∃ p s, make_blob_filename self uid al pre = ok p ∧
      view p = pathPush (view p0) (utf8Bytes s)

end MakeBlobFilename

section MakeChrFilename
open legacy_blob.LegacyBlobLoader

recall make_chr_filename_ok (view : std.path.PathBuf → List Std.U8)
    (hpush : PathBufPushStringSpec view) (hfmt : AllocFmtFormatSpec)
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al pre : Str)
    (user : utils.AndroidUserId) (s1 : String) (s2 : Str) (enc : String) (p0 : std.path.PathBuf)
    (hu : utils.AppUid.owning_user uid = ok user)
    (hf : alloc.fmt.format () = ok s1) (hd : stringAsStr s1 = ok s2)
    (henc : encode_alias s2 = ok enc) (hp : make_user_path_name self user = ok p0) :
    ∃ p s, make_chr_filename self uid al pre = ok p ∧
      view p = pathPush (view p0) (utf8Bytes s)

end MakeChrFilename

section MakeSuperKeyFilename
open legacy_blob.LegacyBlobLoader

recall make_super_key_filename_ok (view : std.path.PathBuf → List Std.U8)
    (hpush : PathBufPushStrSpec view) (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (p0 : std.path.PathBuf)
    (hp : make_user_path_name self user = ok p0) :
    ∃ p, make_super_key_filename self user = ok p ∧
      view p = pathPush (view p0) (utf8Bytes ".masterkey")

end MakeSuperKeyFilename

section MakeUserPathName
open legacy_blob.LegacyBlobLoader

recall make_user_path_name_ok (view : std.path.PathBuf → List Std.U8)
    (hclone : PathBufCloneSpec view) (hpush : PathBufPushStringSpec view)
    (hfmt : AllocFmtFormatSpec) (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId) :
    ∃ p s, make_user_path_name self user = ok p ∧
      view p = pathPush (view self.path) (utf8Bytes s)

end MakeUserPathName

section IsEmptyUser
open legacy_blob.LegacyBlobLoader
open std.fs.ReadDir.Insts.CoreIterTraitsIteratorIteratorResultDirEntryError renaming
  next → readDirNextFn
open std.path.Path renaming is_dir → pathIsDir
open std.path.PathBuf renaming as_path → pathBufAsPath

recall is_empty_user_not_dir (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId)
    (p0 : std.path.PathBuf) (s : String) (up : std.path.PathBuf) (p : std.path.Path)
    (hc : pathBufCloneFn self.path = ok p0) (hf : alloc.fmt.format () = ok s)
    (hpush : pathPushString p0 s = ok up) (hasp : pathBufAsPath up = ok p)
    (hdir : pathIsDir p = ok false) :
    is_empty_user self user = ok (.Ok true)

recall is_empty_user_dir (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : IoErrCtxLaw root std.fs.ReadDir)
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId)
    (p0 : std.path.PathBuf) (s : String) (up : std.path.PathBuf) (p : std.path.Path)
    (hc : pathBufCloneFn self.path = ok p0) (hf : alloc.fmt.format () = ok s)
    (hpush : pathPushString p0 s = ok up) (hasp : pathBufAsPath up = ok p)
    (hdir : pathIsDir p = ok true) (pd : std.path.Path) (hdd : pathBufDeref up = ok pd)
    (dir : std.fs.ReadDir) (hrd : pathReadDirCall pd = ok (.Ok dir))
    (o : Option (core.result.Result std.fs.DirEntry IoError)) (dir' : std.fs.ReadDir)
    (hn : readDirNextFn dir = ok (o, dir')) :
    is_empty_user self user = ok (.Ok o.isNone)

recall is_empty_user_read_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : IoErrCtxLaw root std.fs.ReadDir)
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId)
    (p0 : std.path.PathBuf) (s : String) (up : std.path.PathBuf) (p : std.path.Path)
    (hc : pathBufCloneFn self.path = ok p0) (hf : alloc.fmt.format () = ok s)
    (hpush : pathPushString p0 s = ok up) (hasp : pathBufAsPath up = ok p)
    (hdir : pathIsDir p = ok true) (pd : std.path.Path) (hdd : pathBufDeref up = ok pd)
    (e : IoError) (hrd : pathReadDirCall pd = ok (.Err e)) (k : IoErrorKind)
    (hk : ioErrorKind e = ok k) (hni : k ≠ ioInterrupted) :
    ∃ e', is_empty_user self user = ok (.Err e') ∧ root e' = ErrRoot.other

end IsEmptyUser

section ListUser
open legacy_blob.LegacyBlobLoader
open std.path.PathBuf renaming as_path → pathBufAsPath
open std.fs.ReadDir.Insts renaming
  CoreIterTraitsIteratorIteratorResultDirEntryError.next → readDirNext

recall list_user_ok (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : IoErrCtxLaw root std.fs.DirEntry) (hts : StrToStringSpec) (hto : OsStrToStrSpec)
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId) (path : std.path.PathBuf)
    (hp : make_user_path_name self user = ok path) (dir : std.fs.ReadDir)
    (q : std.path.Path) (hasp : pathBufAsPath path = ok q)
    (hr : readDirCall q = ok (.Ok dir))
    (entries : List std.fs.DirEntry)
    (hrun : NextRun readDirNext dir (entries.map okEntry))
    (nm : std.fs.DirEntry → Option Str) (hnm : ∀ d ∈ entries, FileNameIs d (nm d))
    (hlen : (entries.filterMap nm).length ≤ Std.Usize.max) :
    ∃ v, list_user self user = ok (.Ok v) ∧
      v.val.map utf8Bytes = (entries.filterMap nm).map (·.val)

recall list_user_entry_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : IoErrCtxLaw root std.fs.DirEntry) (hts : StrToStringSpec) (hto : OsStrToStrSpec)
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId) (path : std.path.PathBuf)
    (hp : make_user_path_name self user = ok path) (dir : std.fs.ReadDir)
    (q : std.path.Path) (hasp : pathBufAsPath path = ok q)
    (hr : readDirCall q = ok (.Ok dir))
    (pre : List std.fs.DirEntry) (dir1 dir2 : std.fs.ReadDir) (e : IoError)
    (hpre : NextPrefix readDirNext dir (pre.map okEntry) dir1)
    (hn : readDirNext dir1 = ok (some (.Err e), dir2))
    (hnm : ∀ d ∈ pre, ∃ o, FileNameIs d o) (hlen : pre.length ≤ Std.Usize.max) :
    ∃ e', list_user self user = ok (.Err e') ∧ root e' = ErrRoot.other

recall list_user_not_found (hdef : VecStringDefaultSpec)
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId) (path : std.path.PathBuf)
    (hp : make_user_path_name self user = ok path) (e : IoError)
    (q : std.path.Path) (hasp : pathBufAsPath path = ok q)
    (hr : readDirCall q = ok (.Err e))
    (hk : ioErrorKind e = ok ioNotFound) :
    ∃ v, list_user self user = ok (.Ok v) ∧ v.val = []

recall list_user_open_err (root : anyhow.Error → ErrRoot) (hfmt : AllocFmtFormatSpec)
    (hctx : IoErrCtxLaw root (alloc.vec.Vec String))
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId) (path : std.path.PathBuf)
    (hp : make_user_path_name self user = ok path) (e : IoError)
    (q : std.path.Path) (hasp : pathBufAsPath path = ok q)
    (hr : readDirCall q = ok (.Err e))
    (k : IoErrorKind) (hk : ioErrorKind e = ok k)
    (hne : k ≠ ioNotFound) (hni : k ≠ ioInterrupted) :
    ∃ e', list_user self user = ok (.Err e') ∧ root e' = ErrRoot.other

end ListUser

section WithRetryInterrupted
open legacy_blob.LegacyBlobLoader

recall with_retry_interrupted_ok {F T : Type}
    (inst : RetryFn F T)
    (f : F) (v : T) (h : inst.call f () = ok (.Ok v)) :
    with_retry_interrupted inst f = ok (.Ok v)

recall with_retry_interrupted_err {F T : Type}
    (inst : RetryFn F T)
    (f : F) (e : IoError) (k : IoErrorKind)
    (h : inst.call f () = ok (.Err e)) (hk : ioErrorKind e = ok k)
    (hne : k ≠ ioInterrupted) :
    with_retry_interrupted inst f = ok (.Err e)

end WithRetryInterrupted

section MoveKeystoreFileIfExists
open legacy_blob.LegacyBlobLoader
open core.ops.function renaming Fn → functionFn

recall move_keystore_file_if_exists_ok {F : Type} (root : anyhow.Error → ErrRoot)
    (hmsg : MessageSpecs) (hctx : IoErrCtxLaw root Unit)
    (inst : functionFn F (utils.AppUid × Str × Str) std.path.PathBuf)
    (src_uid dest_uid : utils.AppUid) (src_alias dest_alias pre : Str) (mk : F)
    (src dest : std.path.PathBuf)
    (hsrc : inst.call mk (src_uid, src_alias, pre) = ok src)
    (hdest : inst.call mk (dest_uid, dest_alias, pre) = ok dest)
    (hr : renameCall src dest = ok (.Ok ())) :
    move_keystore_file_if_exists inst src_uid dest_uid src_alias dest_alias pre mk =
      ok (.Ok ())

recall move_keystore_file_if_exists_not_found {F : Type} (hkeq : IoKindEqSpec)
    (inst : functionFn F (utils.AppUid × Str × Str) std.path.PathBuf)
    (src_uid dest_uid : utils.AppUid) (src_alias dest_alias pre : Str) (mk : F)
    (src dest : std.path.PathBuf)
    (hsrc : inst.call mk (src_uid, src_alias, pre) = ok src)
    (hdest : inst.call mk (dest_uid, dest_alias, pre) = ok dest)
    (e : IoError) (hr : renameCall src dest = ok (.Err e))
    (hk : ioErrorKind e = ok ioNotFound) :
    move_keystore_file_if_exists inst src_uid dest_uid src_alias dest_alias pre mk =
      ok (.Ok ())

recall move_keystore_file_if_exists_err {F : Type} (root : anyhow.Error → ErrRoot)
    (hmsg : MessageSpecs) (hctx : IoErrCtxLaw root Unit) (hkeq : IoKindEqSpec)
    (inst : functionFn F (utils.AppUid × Str × Str) std.path.PathBuf)
    (src_uid dest_uid : utils.AppUid) (src_alias dest_alias pre : Str) (mk : F)
    (src dest : std.path.PathBuf)
    (hsrc : inst.call mk (src_uid, src_alias, pre) = ok src)
    (hdest : inst.call mk (dest_uid, dest_alias, pre) = ok dest)
    (e : IoError) (hr : renameCall src dest = ok (.Err e))
    (k : IoErrorKind) (hk : ioErrorKind e = ok k) (hne : k ≠ ioNotFound)
    (hni : k ≠ ioInterrupted) :
    ∃ e', move_keystore_file_if_exists inst src_uid dest_uid src_alias dest_alias pre mk =
      ok (.Err e') ∧ root e' = ErrRoot.other

end MoveKeystoreFileIfExists

section RemoveUserDirIfEmpty
open legacy_blob.LegacyBlobLoader
open std.path.PathBuf renaming as_path → pathBufAsPath

recall remove_user_dir_if_empty_empty (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root Bool) (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (his : is_empty_user self user = ok (.Ok true))
    (p : std.path.PathBuf) (hp : make_user_path_name self user = ok p) (q : std.path.Path)
    (hasp : pathBufAsPath p = ok q) (hr : CallReturns (removeDirCall q)) :
    remove_user_dir_if_empty self user = ok (.Ok ())

recall remove_user_dir_if_empty_not_empty (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root Bool) (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (his : is_empty_user self user = ok (.Ok false)) :
    remove_user_dir_if_empty self user = ok (.Ok ())

recall remove_user_dir_if_empty_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root Bool) (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (e : anyhow.Error)
    (his : is_empty_user self user = ok (.Err e)) :
    ∃ e', remove_user_dir_if_empty self user = ok (.Err e') ∧ root e' = root e

end RemoveUserDirIfEmpty

section HasSuperKey
open legacy_blob.LegacyBlobLoader
open std.path.Path renaming is_file → pathIsFile

recall has_super_key_ok (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId)
    (pb : std.path.PathBuf) (p : std.path.Path) (b : Bool)
    (hmk : make_super_key_filename self user = ok pb)
    (hd : pathBufDeref pb = ok p)
    (hf : pathIsFile p = ok b) :
    has_super_key self user = ok b

end HasSuperKey

section LoadSuperKey
open legacy_blob.LegacyBlobLoader
open android_system_keystore2.aidl.android.system.keystore2.ResponseCode.ResponseCode
open Aeneas.Std.alloc.vec.Vec renaming deref → vecDeref
open keystore2_crypto.zvec.ZVec.Insts.CoreConvertTryFromVecU8Error renaming try_from → tryFromVec
open keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8 renaming deref → zvecDerefFn

recall load_super_key_absent (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob)) (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (pw : keystore2_crypto.Password) (path : std.path.PathBuf)
    (p : std.path.Path) (hmk : make_super_key_filename self user = ok path)
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob p = ok (.Ok none)) :
    load_super_key self user pw = ok (.Ok none)

recall load_super_key_read_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob)) (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (pw : keystore2_crypto.Password) (path : std.path.PathBuf)
    (p : std.path.Path) (e : anyhow.Error)
    (hmk : make_super_key_filename self user = ok path)
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob p = ok (.Err e)) :
    ∃ e', load_super_key self user pw = ok (.Err e') ∧ root e' = root e

recall load_super_key_decrypted (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hcc : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId)
    (pw : keystore2_crypto.Password) (path : std.path.PathBuf) (p : std.path.Path)
    (blob : legacy_blob.Blob) (iv tag data salt : alloc.vec.Vec Std.U8) (n : Std.Usize)
    (key plain : keystore2_crypto.zvec.ZVec) (ks : Slice Std.U8)
    (hmk : make_super_key_filename self user = ok path)
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hv : blob.value = .PwEncrypted iv tag data salt n) (hfl : flagSet blob 0 = true)
    (hder : keystore2_crypto.Password.derive_key_pbkdf2 pw (vecDeref salt) n =
      ok (.Ok key))
    (hk : zvecDerefFn key = ok ks)
    (hdec : keystore2_crypto.aes_gcm_decrypt (vecDeref data) (vecDeref iv)
      (vecDeref tag) ks = ok (.Ok plain)) :
    load_super_key self user pw = ok (.Ok (some plain))

recall load_super_key_derive_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hcc : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId)
    (pw : keystore2_crypto.Password) (path : std.path.PathBuf) (p : std.path.Path)
    (blob : legacy_blob.Blob) (iv tag data salt : alloc.vec.Vec Std.U8) (n : Std.Usize)
    (e : keystore2_crypto.error.Error)
    (hmk : make_super_key_filename self user = ok path)
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hv : blob.value = .PwEncrypted iv tag data salt n) (hfl : flagSet blob 0 = true)
    (hder : keystore2_crypto.Password.derive_key_pbkdf2 pw (vecDeref salt) n =
      ok (.Err e)) :
    ∃ e', load_super_key self user pw = ok (.Err e') ∧ root e' = ErrRoot.crypto e

recall load_super_key_decrypt_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hcc : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId)
    (pw : keystore2_crypto.Password) (path : std.path.PathBuf) (p : std.path.Path)
    (blob : legacy_blob.Blob) (iv tag data salt : alloc.vec.Vec Std.U8) (n : Std.Usize)
    (key : keystore2_crypto.zvec.ZVec) (ks : Slice Std.U8) (e : keystore2_crypto.error.Error)
    (hmk : make_super_key_filename self user = ok path)
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hv : blob.value = .PwEncrypted iv tag data salt n) (hfl : flagSet blob 0 = true)
    (hder : keystore2_crypto.Password.derive_key_pbkdf2 pw (vecDeref salt) n =
      ok (.Ok key))
    (hk : zvecDerefFn key = ok ks)
    (hdec : keystore2_crypto.aes_gcm_decrypt (vecDeref data) (vecDeref iv)
      (vecDeref tag) ks = ok (.Err e)) :
    ∃ e', load_super_key self user pw = ok (.Err e') ∧ root e' = ErrRoot.crypto e

recall load_super_key_unencrypted (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hz : ZVecErrCtxLaw root keystore2_crypto.zvec.ZVec) (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (pw : keystore2_crypto.Password) (path : std.path.PathBuf)
    (p : std.path.Path) (blob : legacy_blob.Blob) (iv tag data salt : alloc.vec.Vec Std.U8)
    (n : Std.Usize) (z : keystore2_crypto.zvec.ZVec)
    (hmk : make_super_key_filename self user = ok path)
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hv : blob.value = .PwEncrypted iv tag data salt n) (hfl : flagSet blob 0 = false)
    (ht : tryFromVec data =
      ok (.Ok z)) :
    load_super_key self user pw = ok (.Ok (some z))

recall load_super_key_try_from_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hz : ZVecErrCtxLaw root keystore2_crypto.zvec.ZVec) (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (pw : keystore2_crypto.Password) (path : std.path.PathBuf)
    (p : std.path.Path) (blob : legacy_blob.Blob) (iv tag data salt : alloc.vec.Vec Std.U8)
    (n : Std.Usize) (e : keystore2_crypto.zvec.Error)
    (hmk : make_super_key_filename self user = ok path)
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hv : blob.value = .PwEncrypted iv tag data salt n) (hfl : flagSet blob 0 = false)
    (ht : tryFromVec data =
      ok (.Err e)) :
    ∃ e', load_super_key self user pw = ok (.Err e') ∧ root e' = ErrRoot.other

recall load_super_key_wrong_type (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hks : KsErrCtxLaw root (Option keystore2_crypto.zvec.ZVec))
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId)
    (pw : keystore2_crypto.Password) (path : std.path.PathBuf) (p : std.path.Path)
    (blob : legacy_blob.Blob) (rc : Std.I32)
    (hmk : make_super_key_filename self user = ok path)
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hv : ∀ iv tag data salt n, blob.value ≠ .PwEncrypted iv tag data salt n)
    (hrc : VALUE_CORRUPTED = ok rc) :
    ∃ e', load_super_key self user pw = ok (.Err e') ∧
      root e' = ErrRoot.ks (error.Error.Rc rc)

end LoadSuperKey

section RemoveSuperKey
open legacy_blob.LegacyBlobLoader
open std.path.PathBuf renaming as_path → pathBufAsPath

recall remove_super_key_empty (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId)
    (p1 p2 : std.path.PathBuf) (q1 q2 : std.path.Path)
    (hmk : make_super_key_filename self user = ok p1) (hasp1 : pathBufAsPath p1 = ok q1)
    (hr1 : CallReturns (removeFileCall q1))
    (his : is_empty_user self user = ok (.Ok true))
    (hup : make_user_path_name self user = ok p2) (hasp2 : pathBufAsPath p2 = ok q2)
    (hr2 : CallReturns (removeDirCall q2)) :
    remove_super_key self user = ok ()

recall remove_super_key_not_empty (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (p1 : std.path.PathBuf) (q1 : std.path.Path)
    (hmk : make_super_key_filename self user = ok p1) (hasp1 : pathBufAsPath p1 = ok q1)
    (hr1 : CallReturns (removeFileCall q1))
    (his : is_empty_user self user = ok (.Ok false)) :
    remove_super_key self user = ok ()

recall remove_super_key_empty_err (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (p1 : std.path.PathBuf) (q1 : std.path.Path) (e : anyhow.Error)
    (hmk : make_super_key_filename self user = ok p1) (hasp1 : pathBufAsPath p1 = ok q1)
    (hr1 : CallReturns (removeFileCall q1))
    (his : is_empty_user self user = ok (.Err e)) :
    remove_super_key self user = ok ()

end RemoveSuperKey

end Keystore2Verify.LegacyBlob
