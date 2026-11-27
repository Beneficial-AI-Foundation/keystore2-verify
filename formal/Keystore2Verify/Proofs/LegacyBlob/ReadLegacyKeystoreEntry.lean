import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open legacy_blob.LegacyBlobLoader
open core.ops.function
open read_legacy_keystore_entry.closure.Insts renaming
  CoreOpsFunctionFnOnceTupleBlobOptionVecU8 → entryClosureInst

/-- The type of the decryption closure that `read_legacy_keystore_entry` takes. -/
abbrev DecryptInst (F : Type) : Type :=
  FnOnce F ((Slice Std.U8) × (Slice Std.U8) × (Slice Std.U8) ×
    (Option (Slice Std.U8)) × (Option Std.Usize))
    (core.result.Result keystore2_crypto.zvec.ZVec anyhow.Error)

/-- conditional: if the alias has a known keystore prefix, `read_legacy_keystore_entry` returns
`Ok None`. In the Rust source this path returns before any file is read. Hypothesis: the outcome of
`make_legacy_keystore_entry_filename`. -/
theorem read_legacy_keystore_entry_prefixed {F : Type} (inst : DecryptInst F)
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al : Str) (decrypt : F)
    (hfn : make_legacy_keystore_entry_filename self uid al = ok none) :
    read_legacy_keystore_entry inst self uid al decrypt = ok (.Ok none) := by
  sorry

/-- conditional: if the file is absent, `read_legacy_keystore_entry` returns `Ok None`. Hypotheses:
the outcome of `make_legacy_keystore_entry_filename`; the result `p` of `deref` on the path; the
outcome `Ok None` of `read_generic_blob_decrypt_with` (an item the extraction could not
translate); the assumption about `and_then`; the `context` assumption for an `anyhow::Error`;
and the message assumptions. -/
theorem read_legacy_keystore_entry_absent {F : Type} (inst : DecryptInst F)
    (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (hand : OptionAndThenSpec
      (entryClosureInst inst))
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al : Str) (decrypt : F)
    (path : std.path.PathBuf) (p : std.path.Path)
    (hfn : make_legacy_keystore_entry_filename self uid al = ok (some path))
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob_decrypt_with inst p decrypt = ok (.Ok none)) :
    read_legacy_keystore_entry inst self uid al decrypt = ok (.Ok none) := by
  sorry

/-- conditional: if the file holds a `Generic` blob, `read_legacy_keystore_entry` returns its bytes.
Hypotheses: those of `read_legacy_keystore_entry_absent`, with the outcome `Ok (Some blob)` of the
reader and `blob.value = Generic bytes`. -/
theorem read_legacy_keystore_entry_generic {F : Type} (inst : DecryptInst F)
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
    read_legacy_keystore_entry inst self uid al decrypt = ok (.Ok (some bytes)) := by
  sorry

/-- conditional: if the file holds a blob of another type, `read_legacy_keystore_entry` returns
`Ok None` (the Rust source logs a message). Hypotheses: those of
`read_legacy_keystore_entry_generic`, with `blob.value` not a `Generic` value, and the
assumptions about the logging calls. -/
theorem read_legacy_keystore_entry_other {F : Type} (inst : DecryptInst F)
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
    read_legacy_keystore_entry inst self uid al decrypt = ok (.Ok none) := by
  sorry

/-- conditional: if the reader returns an error `e`, `read_legacy_keystore_entry` returns an error
with the same root cause. Hypotheses: those of `read_legacy_keystore_entry_absent`, with the
outcome `Err e` of the reader. -/
theorem read_legacy_keystore_entry_err {F : Type} (inst : DecryptInst F)
    (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root (Option legacy_blob.Blob))
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al : Str) (decrypt : F)
    (path : std.path.PathBuf) (p : std.path.Path) (e : anyhow.Error)
    (hfn : make_legacy_keystore_entry_filename self uid al = ok (some path))
    (hd : pathBufDeref path = ok p)
    (hr : read_generic_blob_decrypt_with inst p decrypt = ok (.Err e)) :
    ∃ e', read_legacy_keystore_entry inst self uid al decrypt = ok (.Err e') ∧
      root e' = root e := by
  sorry

end Keystore2Verify.LegacyBlob
