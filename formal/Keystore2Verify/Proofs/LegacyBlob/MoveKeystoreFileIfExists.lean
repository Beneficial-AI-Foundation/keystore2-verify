import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open legacy_blob.LegacyBlobLoader
open core.ops.function renaming Fn → functionFn

/-- conditional: if the rename returns `Ok`, `move_keystore_file_if_exists` returns `Ok ()`. The
Rust source computes the source name first and then the destination name; the names are the
results `src` and `dest` of the closure `make_filename`. Hypotheses: the outcomes of the two
calls of `make_filename` and of the call `fs::rename` from the source to the destination, which
the retry loop makes and which returns `Ok` (the statement covers a run whose first call is not
interrupted); the `context` assumption for an `io::Error`; and the message assumptions. -/
theorem move_keystore_file_if_exists_ok {F : Type} (root : anyhow.Error → ErrRoot)
    (hmsg : MessageSpecs) (hctx : IoErrCtxLaw root Unit)
    (inst : functionFn F (utils.AppUid × Str × Str) std.path.PathBuf)
    (src_uid dest_uid : utils.AppUid) (src_alias dest_alias pre : Str) (mk : F)
    (src dest : std.path.PathBuf)
    (hsrc : inst.call mk (src_uid, src_alias, pre) = ok src)
    (hdest : inst.call mk (dest_uid, dest_alias, pre) = ok dest)
    (hr : renameCall src dest = ok (.Ok ())) :
    move_keystore_file_if_exists inst src_uid dest_uid src_alias dest_alias pre mk =
      ok (.Ok ()) := by
  sorry

/-- conditional: if the rename returns an error `e` of the kind `NotFound` (the source does not
exist), `move_keystore_file_if_exists` returns `Ok ()`. In the Rust source this path returns
before the error is wrapped. Hypotheses: the outcomes of the two calls of `make_filename`; the
call `fs::rename` from the source to the destination returns `Err e`; the kind of `e` is
`NotFound` (so the retry loop does not repeat the call); and the assumption about
`ErrorKind::eq`. -/
theorem move_keystore_file_if_exists_not_found {F : Type} (hkeq : IoKindEqSpec)
    (inst : functionFn F (utils.AppUid × Str × Str) std.path.PathBuf)
    (src_uid dest_uid : utils.AppUid) (src_alias dest_alias pre : Str) (mk : F)
    (src dest : std.path.PathBuf)
    (hsrc : inst.call mk (src_uid, src_alias, pre) = ok src)
    (hdest : inst.call mk (dest_uid, dest_alias, pre) = ok dest)
    (e : IoError) (hr : renameCall src dest = ok (.Err e))
    (hk : ioErrorKind e = ok ioNotFound) :
    move_keystore_file_if_exists inst src_uid dest_uid src_alias dest_alias pre mk =
      ok (.Ok ()) := by
  sorry

/-- conditional: if the rename returns an error `e` whose kind `k` is neither `NotFound` nor
`Interrupted`, `move_keystore_file_if_exists` returns an error whose root cause is an
`io::Error` (class `other`). Hypotheses: those of `move_keystore_file_if_exists_not_found`, with
the kind `k`; the `context` assumption for an `io::Error`; and the message assumptions. -/
theorem move_keystore_file_if_exists_err {F : Type} (root : anyhow.Error → ErrRoot)
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
      ok (.Err e') ∧ root e' = ErrRoot.other := by
  sorry

end Keystore2Verify.LegacyBlob
