import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open legacy_blob.LegacyBlobLoader
open android_system_keystore2.aidl.android.system.keystore2.ResponseCode.ResponseCode
open android_hardware_security_keymint.aidl.android.hardware.security.keymint.SecurityLevel

/-- The optional super key that `read_characteristics_file` passes to `decrypt_if_required`. -/
abbrev SuperKey : Type := Option (alloc.sync.Arc (Dyn (fun (_dyn : Type) => utils.AesGcm _dyn)))

/-! In each theorem the characteristics file is read as follows: `make_chr_filename` returns `pb`,
`deref` returns `p`, and `read_generic_blob` and `decrypt_if_required` (items the extraction could
not translate) and `read_key_parameters` (also untranslated) return the stated results. The
`stream` is the slice of the bytes of the blob value, as in `&data[..]`. -/

/-- conditional: if the characteristics file is absent, `read_characteristics_file` returns
`Ok (Cache v)` with `v` empty. The result is a `Cache` whatever the prefix. Hypotheses: the outcomes
of `make_chr_filename`, `deref` and `read_generic_blob`; the `context` assumption for an
`anyhow::Error`; and the message assumptions. -/
theorem read_characteristics_file_absent (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob)) (self : legacy_blob.LegacyBlobLoader)
    (uid : utils.AppUid) (pre al : Str) (hw : SecurityLevel) (sk : SuperKey)
    (pb : std.path.PathBuf) (p : std.path.Path)
    (hchr : make_chr_filename self uid al pre = ok pb)
    (hd : pathBufDeref pb = ok p)
    (hr : read_generic_blob p = ok (.Ok none)) :
    ∃ v, read_characteristics_file self uid pre al hw sk = ok (.Ok (.Cache v)) ∧
      v.val = [] := by
  sorry

/-- conditional: if reading the file returns an error `e`, `read_characteristics_file` returns an
error with the same root cause. Hypotheses: those of `read_characteristics_file_absent`, with the
outcome `Err e`. -/
theorem read_characteristics_file_read_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob)) (self : legacy_blob.LegacyBlobLoader)
    (uid : utils.AppUid) (pre al : Str) (hw : SecurityLevel) (sk : SuperKey)
    (pb : std.path.PathBuf) (p : std.path.Path) (e : anyhow.Error)
    (hchr : make_chr_filename self uid al pre = ok pb)
    (hd : pathBufDeref pb = ok p)
    (hr : read_generic_blob p = ok (.Err e)) :
    ∃ e', read_characteristics_file self uid pre al hw sk = ok (.Err e') ∧
      root e' = root e := by
  sorry

/-- conditional: if decrypting the blob returns an error `e`, `read_characteristics_file` returns an
error with the same root cause. Hypotheses: the outcomes of `make_chr_filename`, `deref`, of the
read (`Ok (Some blob)`) and of `decrypt_if_required`; the `context` assumption for an
`anyhow::Error` at both calls; and the message assumptions. -/
theorem read_characteristics_file_decrypt_err (root : anyhow.Error → ErrRoot)
    (hmsg : MessageSpecs) (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hctx' : AnyCtxLaw root legacy_blob.Blob) (self : legacy_blob.LegacyBlobLoader)
    (uid : utils.AppUid) (pre al : Str) (hw : SecurityLevel) (sk : SuperKey)
    (pb : std.path.PathBuf) (p : std.path.Path) (blob : legacy_blob.Blob) (e : anyhow.Error)
    (hchr : make_chr_filename self uid al pre = ok pb)
    (hd : pathBufDeref pb = ok p)
    (hr : read_generic_blob p = ok (.Ok (some blob)))
    (hdec : decrypt_if_required sk blob = ok (.Err e)) :
    ∃ e', read_characteristics_file self uid pre al hw sk = ok (.Err e') ∧
      root e' = root e := by
  sorry

/-- conditional: if the decrypted blob does not hold key characteristics,
`read_characteristics_file` returns an error whose root cause is `Rc VALUE_CORRUPTED` (class
`ks`). Hypotheses: the outcomes of `make_chr_filename`, `deref`, the read and
`decrypt_if_required` (the decrypted blob `blob'` has a value other than `Characteristics` or
`CharacteristicsCache`), and of the constant `VALUE_CORRUPTED`; the `context` assumptions for an
`anyhow::Error` and for a `keystore2::error::Error`; and the message assumptions. -/
theorem read_characteristics_file_wrong_type (root : anyhow.Error → ErrRoot)
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
      root e' = ErrRoot.ks (error.Error.Rc rc) := by
  sorry

/-- conditional: if the decrypted blob holds a `Characteristics` value with the bytes `data` and
`read_key_parameters` returns the values `vals` for them, `read_characteristics_file` returns
`Ok (File params)`, where `params` has one key parameter for each value, in order, with the
security level `SecurityLevel::KEYSTORE`. The bytes after the list are ignored. Hypotheses: the
outcomes of `make_chr_filename`, `deref`, the read, `decrypt_if_required`, `read_key_parameters` and
the constant `KEYSTORE`; the assumptions about the iterator adapters that build the result, with
the views `viewSw`, `viewOpt`, `viewFlat` and `viewChain`; the `context` assumptions for an
`anyhow::Error`; the message assumptions; and that the list has at most `Usize.max` parameters. -/
theorem read_characteristics_file_file (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
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
      params.val = vals.val.map fun v => mkKeyParameter v sl := by
  sorry

/-- conditional: if the decrypted blob holds a `CharacteristicsCache` value with the bytes
`data`, the first `read_key_parameters` returns the list `hwl` and the slice `stream1` that is left,
and the second, on `stream1`, returns the list `swl`, `read_characteristics_file` returns
`Ok (Cache params)`. The parameters are those of `hwl` with the security level `hw`, then those of
`swl` with the security level `SecurityLevel::KEYSTORE`. Hypotheses: those of
`read_characteristics_file_file`, with both reads and the assumption about the `map` adapter of
the hardware list; the list has at most `Usize.max` parameters. -/
theorem read_characteristics_file_cache (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
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
        (swl.val.map fun v => mkKeyParameter v sl) := by
  sorry

/-- conditional: if the decrypted blob holds a `CharacteristicsCache` value and the first
`read_key_parameters` returns an error `e`, `read_characteristics_file` returns an error with the
same root cause. In the Rust source this path returns before the second list is read. Hypotheses:
the outcomes of `make_chr_filename`, `deref`, the read, `decrypt_if_required` and the first
`read_key_parameters`; the `context` assumptions for an `anyhow::Error`; and the message
assumptions. -/
theorem read_characteristics_file_hw_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
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
      root e' = root e := by
  sorry

/-- conditional: if the decrypted blob holds a `Characteristics` value and `read_key_parameters`
returns an error `e`, `read_characteristics_file` returns an error with the same root cause.
Hypotheses: as for `read_characteristics_file_hw_err`, for a `Characteristics` value. -/
theorem read_characteristics_file_sw_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
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
      root e' = root e := by
  sorry

/-- conditional: if the decrypted blob holds a `CharacteristicsCache` value, the first
`read_key_parameters` returns the list `hwl` and the slice `stream1`, and the second, on `stream1`,
returns an error `e`, `read_characteristics_file` returns an error with the same root cause.
Hypotheses: as for `read_characteristics_file_hw_err`, with the first read returning `Ok hwl`, and
the assumption about the `map` adapter of the hardware list, which the translation builds before
the second read. -/
theorem read_characteristics_file_cache_sw_err (root : anyhow.Error → ErrRoot)
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
      root e' = root e := by
  sorry

end Keystore2Verify.LegacyBlob
