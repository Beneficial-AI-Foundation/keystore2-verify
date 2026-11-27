import Keystore2Verify.Specs.Defs.Externals

/-!
# Definitions for the statements about `id_rotation.rs`

The `context` calls of `had_factory_reset_since_id_rotation`, the call chain that it shares on its
success paths, and the two new assumptions about external functions (`Option::context` and
`PathBuf::clone`). Nothing here is an axiom.
-/

namespace Keystore2Verify.IdRotation
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open core.result.Result.Insts.AnyhowContext
open anyhow.context.ext.StdError
open alloc.string.String.Insts renaming CoreFmtDisplay → StringDisplay

/-- The `context` assumption at the call `result.context(s)` where `result` holds an
`io::Error` and a value of type `T`, and `s` is a `String`. The model observes the root cause of
an `io::Error` only as `ErrRoot.other`.
Record `ks2-ext-core-result-result-insts-anyhowcontext-context`. -/
abbrev IoCtxAssumption (root : anyhow.Error → ErrRoot) (T : Type) : Prop :=
  ResultContextLaw (fun _ => ErrRoot.other) root
    (context (T := T) (Blanket core.io.error.Error.Insts.CoreErrorError) StringDisplay)

/-- The `context` assumption at the call `result.context(s)` where `result` holds a
`SystemTimeError` and a value of type `T`, and `s` is a `String`. The root cause is observed only
as `ErrRoot.other`.
Record `ks2-ext-core-result-result-insts-anyhowcontext-context`. -/
abbrev SystemTimeCtxAssumption (root : anyhow.Error → ErrRoot) (T : Type) : Prop :=
  ResultContextLaw (fun _ => ErrRoot.other) root
    (context (T := T) (Blanket std.time.SystemTimeError.Insts.CoreErrorError) StringDisplay)

/-- Assumption about an external function: `Option::context` with a `String` message (record
`ks2-ext-core-option-option-insts-anyhowcontexttnever-context`). Over the function `ctx`: `ctx`
never panics, it keeps a `Some v` as `Ok v`, and turns `None` into an error whose root cause is
`ErrRoot.other` (the error has only the message). Idealisation: allocation never fails.
Idealisation: destruction never panics (the message is dropped on `Some`). -/
def OptionContextAssumption {T C : Type} (root : anyhow.Error → ErrRoot)
    (ctx : Option T → C → Result (core.result.Result T anyhow.Error)) : Prop :=
  (∀ v c, ctx (some v) c = ok (.Ok v)) ∧
  (∀ c, ∃ e, ctx none c = ok (.Err e) ∧ root e = ErrRoot.other)

/-- The closed instance of `OptionContextAssumption` at the call of
`had_factory_reset_since_id_rotation`: `Option<SystemTime>` and a `String` message.
Record `ks2-ext-core-option-option-insts-anyhowcontexttnever-context`. -/
def OptionContextSpec (root : anyhow.Error → ErrRoot) : Prop :=
  OptionContextAssumption (T := std.time.SystemTime) root
    (core.option.Option.Insts.AnyhowContextTNever.context StringDisplay)

/-- The calls that the success path and the later error paths share. The epoch is `st`; the
creation time `creation` is `d` after it; `d` and the rotation period `p` are `i` and `i1`
milliseconds; the rotation period `p` is `Duration::from_secs(2592000)` (thirty days) and is
not zero. -/
def EpochOk (creation st : std.time.SystemTime) (d p : core.time.Duration)
    (i i1 : Std.U128) : Prop :=
  std.time.SystemTime.UNIX_EPOCH = ok st ∧
  std.time.SystemTime.duration_since creation st = ok (.Ok d) ∧
  core.time.Duration.as_millis d = ok i ∧
  core.time.Duration.from_secs 2592000#u64 = ok p ∧
  core.time.Duration.as_millis p = ok i1 ∧ i1.val ≠ 0

/-- The call `fs::metadata(timestamp_path)`. -/
noncomputable abbrev statTimestamp (self : id_rotation.IdRotationState) :=
  std.fs.metadata (Shared0T.Insts.CoreConvertAsRef std.path.PathBuf.Insts.CoreConvertAsRefPath)
    self.timestamp_path

/-- The call `File::create(timestamp_path)`. -/
noncomputable abbrev createTimestamp (self : id_rotation.IdRotationState) :=
  std.fs.File.create (Shared0T.Insts.CoreConvertAsRef std.path.PathBuf.Insts.CoreConvertAsRefPath)
    self.timestamp_path

/-- The outcomes of the external calls of the success path from the epoch up to `checked_add`:
the epoch is `st`; the creation time is `d` after it; `d` and the rotation period `p` are `i` and
`i1` milliseconds, and the period is not zero; `q` is the quotient `i / i1`; `try_from q` returns
`n32`; the period times `n32` is `d1`; and the epoch plus `d1` is `t`. The outcomes of the
metadata and of the modification time are separate hypotheses of the theorems. -/
def SuccessPath (creation st : std.time.SystemTime) (d p : core.time.Duration)
    (i i1 q : Std.U128) (n32 : Std.U32) (d1 : core.time.Duration) (t : std.time.SystemTime) :
    Prop :=
  EpochOk creation st d p i i1 ∧ q.val = i.val / i1.val ∧
  U32.Insts.CoreConvertTryFromU128TryFromIntError.try_from q = ok (.Ok n32) ∧
  core.time.Duration.Insts.CoreOpsArithMulU32Duration.mul p n32 = ok d1 ∧
  std.time.SystemTime.checked_add st d1 = ok (some t)

/-- Assumption about an external function, over the function `clone` and an observation `view` of
a path (for example its components): `clone p` never panics and returns a path with the same
observation. Idealisation: allocation never fails.
Record `ks2-ext-std-path-pathbuf-insts-corecloneclone-clone`. -/
def PathBufCloneAssumption {β : Type} (view : std.path.PathBuf → β)
    (clone : std.path.PathBuf → Result std.path.PathBuf) : Prop :=
  ∀ p, ∃ q, clone p = ok q ∧ view q = view p

/-- The closed instance of `PathBufCloneAssumption` for `PathBuf::clone` (record
`ks2-ext-std-path-pathbuf-insts-corecloneclone-clone`). -/
def PathBufCloneSpec {β : Type} (view : std.path.PathBuf → β) : Prop :=
  PathBufCloneAssumption view std.path.PathBuf.Insts.CoreCloneClone.clone

end Keystore2Verify.IdRotation
