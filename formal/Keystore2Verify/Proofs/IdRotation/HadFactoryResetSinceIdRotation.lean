import Keystore2Verify.Specs.Defs.IdRotation

namespace Keystore2Verify.IdRotation
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open id_rotation.IdRotationState renaming had_factory_reset_since_id_rotation → hadReset

/-- conditional: given the metadata and time-call outcomes below, the result is `Ok b`, where `b` is
the supplied outcome of comparing `t` and `m`. The value `t` is the `checked_add` outcome in
`SuccessPath`, and `m` is the supplied modification-time outcome. Hypotheses: the outcomes of
`fs::metadata`, of the clock and duration calls (listed in `SuccessPath`), of `Metadata::modified`
and of `SystemTime <=`; `format` and `from_str_nonconst` do not fail; the assumptions about
`context` for a `SystemTimeError`, an `io::Error`, an `anyhow::Error` and an `Option`. -/
theorem had_factory_reset_ok (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hst : SystemTimeCtxAssumption root core.time.Duration)
    (hopt : OptionContextSpec root) (hio : IoCtxAssumption root std.time.SystemTime)
    (hany : AnyCtxLaw root Bool)
    (self : id_rotation.IdRotationState) (creation : std.time.SystemTime)
    (md : std.fs.Metadata) (hmd : statTimestamp self = ok (.Ok md))
    (st : std.time.SystemTime) (d p : core.time.Duration) (i i1 q : Std.U128)
    (n32 : Std.U32) (d1 : core.time.Duration) (t : std.time.SystemTime)
    (hpath : SuccessPath creation st d p i i1 q n32 d1 t)
    (m : std.time.SystemTime) (hm : std.fs.Metadata.modified md = ok (.Ok m))
    (b : Bool)
    (hle : core.cmp.PartialOrd.le.trait_default
      std.time.SystemTime.Insts.CoreCmpPartialOrdSystemTime t m = ok b) :
    hadReset self creation = ok (.Ok b) := by
  sorry

/-- conditional: if the timestamp file exists and `creation_datetime` is before the epoch
(`duration_since` returns an error), the result is an error. Hypotheses: the outcomes of
`fs::metadata`, of `UNIX_EPOCH` and of `duration_since`; `format` and `from_str_nonconst` do not
fail; the assumption about `context` for a `SystemTimeError`. -/
theorem had_factory_reset_before_epoch (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hst : SystemTimeCtxAssumption root core.time.Duration)
    (self : id_rotation.IdRotationState) (creation : std.time.SystemTime)
    (md : std.fs.Metadata) (hmd : statTimestamp self = ok (.Ok md))
    (st : std.time.SystemTime) (hst0 : std.time.SystemTime.UNIX_EPOCH = ok st)
    (se : std.time.SystemTimeError)
    (hd : std.time.SystemTime.duration_since creation st = ok (.Err se)) :
    ∃ e, hadReset self creation = ok (.Err e) ∧ root e = ErrRoot.other := by
  sorry

/-- conditional: if the timestamp file exists and the number of periods since the epoch does not
fit in a `u32` (`try_from` returns an error), the result is an error converted from the
`TryFromIntError`, with no context. Hypotheses: the outcomes of `fs::metadata` and of the clock,
duration and `try_from` calls; `format` and `from_str_nonconst` do not fail; the assumptions
about `context` for a `SystemTimeError`, and for the conversion `From<TryFromIntError>`
(`ErrorFromLaw`). -/
theorem had_factory_reset_too_many_periods (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hst : SystemTimeCtxAssumption root core.time.Duration)
    (hfrom : ErrorFromLaw root (fun _ => ErrRoot.other)
      (anyhow.Error.Insts.CoreConvertFrom.from core.num.error.TryFromIntError.Insts.CoreErrorError))
    (self : id_rotation.IdRotationState) (creation : std.time.SystemTime)
    (md : std.fs.Metadata) (hmd : statTimestamp self = ok (.Ok md))
    (st : std.time.SystemTime) (d p : core.time.Duration) (i i1 q : Std.U128)
    (hepoch : EpochOk creation st d p i i1) (hq : q.val = i.val / i1.val)
    (te : core.num.error.TryFromIntError)
    (hconv : U32.Insts.CoreConvertTryFromU128TryFromIntError.try_from q = ok (.Err te)) :
    ∃ e, hadReset self creation = ok (.Err e) ∧ root e = ErrRoot.other := by
  sorry

/-- conditional: if the timestamp file exists and the rotation period is zero milliseconds, the
division fails: `had_factory_reset_since_id_rotation` returns `fail` (division by zero). The real
period is 2592000000 milliseconds, but `Duration::as_millis` is an external function.
Hypotheses: the outcomes of `fs::metadata`, of the clock and duration calls up to the division;
`format` and `from_str_nonconst` do not fail; the assumption about `context` for a
`SystemTimeError`. -/
theorem had_factory_reset_zero_period (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hst : SystemTimeCtxAssumption root core.time.Duration)
    (self : id_rotation.IdRotationState) (creation : std.time.SystemTime)
    (md : std.fs.Metadata) (hmd : statTimestamp self = ok (.Ok md))
    (st : std.time.SystemTime) (d p : core.time.Duration) (i i1 : Std.U128)
    (h1 : std.time.SystemTime.UNIX_EPOCH = ok st)
    (h2 : std.time.SystemTime.duration_since creation st = ok (.Ok d))
    (h3 : core.time.Duration.as_millis d = ok i)
    (h4 : core.time.Duration.from_secs 2592000#u64 = ok p)
    (h5 : core.time.Duration.as_millis p = ok i1) (h6 : i1.val = 0) :
    hadReset self creation = fail Error.divisionByZero := by
  sorry

/-- conditional: if the timestamp file exists and the start `t` of the period cannot be computed
(`checked_add` returns `None`), the result is an error. Hypotheses: the outcomes of `fs::metadata`
and of the clock and duration calls (listed in `SuccessPath`, with `checked_add` returning
`None`); `format` and `from_str_nonconst` do not fail; the assumptions about `context` for a
`SystemTimeError` and an `Option`. -/
theorem had_factory_reset_no_period_start (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hst : SystemTimeCtxAssumption root core.time.Duration)
    (hopt : OptionContextSpec root)
    (self : id_rotation.IdRotationState) (creation : std.time.SystemTime)
    (md : std.fs.Metadata) (hmd : statTimestamp self = ok (.Ok md))
    (st : std.time.SystemTime) (d p : core.time.Duration) (i i1 q : Std.U128)
    (n32 : Std.U32) (d1 : core.time.Duration)
    (hepoch : EpochOk creation st d p i i1) (hq : q.val = i.val / i1.val)
    (hconv : U32.Insts.CoreConvertTryFromU128TryFromIntError.try_from q = ok (.Ok n32))
    (hmul : core.time.Duration.Insts.CoreOpsArithMulU32Duration.mul p n32 = ok d1)
    (hadd : std.time.SystemTime.checked_add st d1 = ok none) :
    ∃ e, hadReset self creation = ok (.Err e) ∧ root e = ErrRoot.other := by
  sorry

/-- conditional: if the timestamp file exists but its modification time is not available
(`Metadata::modified` returns an error), the result is an error. Hypotheses: the outcomes of
`fs::metadata`, of the clock and duration calls (listed in `SuccessPath`) and of
`Metadata::modified`; `format` and `from_str_nonconst` do not fail; the assumptions about
`context` for a `SystemTimeError`, an `Option` and an `io::Error`. -/
theorem had_factory_reset_no_modified_time (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hst : SystemTimeCtxAssumption root core.time.Duration)
    (hopt : OptionContextSpec root) (hio : IoCtxAssumption root std.time.SystemTime)
    (self : id_rotation.IdRotationState) (creation : std.time.SystemTime)
    (md : std.fs.Metadata) (hmd : statTimestamp self = ok (.Ok md))
    (st : std.time.SystemTime) (d p : core.time.Duration) (i i1 q : Std.U128)
    (n32 : Std.U32) (d1 : core.time.Duration) (t : std.time.SystemTime)
    (hpath : SuccessPath creation st d p i i1 q n32 d1 t)
    (ie : core.io.error.Error) (hm : std.fs.Metadata.modified md = ok (.Err ie)) :
    ∃ e, hadReset self creation = ok (.Err e) ∧ root e = ErrRoot.other := by
  sorry

/-- conditional: if the stat fails with the kind `NotFound` and `File::create` succeeds, the result
is `Ok true`: the function reports a factory reset. Hypotheses: the outcomes of `fs::metadata`, of
`io::Error::kind` and of `File::create`; `format` and `from_str_nonconst` do not fail; the
assumptions about `context` for an `io::Error` and an `anyhow::Error`. -/
theorem had_factory_reset_created (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hio : IoCtxAssumption root std.fs.File) (hany : AnyCtxLaw root Bool)
    (self : id_rotation.IdRotationState) (creation : std.time.SystemTime)
    (e0 : core.io.error.Error) (hmd : statTimestamp self = ok (.Err e0))
    (hk : core.io.error.Error.kind e0 = ok core.io.error.ErrorKind.NotFound)
    (f : std.fs.File) (hc : createTimestamp self = ok (.Ok f)) :
    hadReset self creation = ok (.Ok true) := by
  sorry

/-- conditional: if the stat fails with the kind `NotFound` and `File::create` fails, the result is
an error. Hypotheses: the outcomes of `fs::metadata`, of `io::Error::kind` and of `File::create`;
`format` and `from_str_nonconst` do not fail; the assumption about `context` for an `io::Error`. -/
theorem had_factory_reset_create_failed (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hio : IoCtxAssumption root std.fs.File)
    (self : id_rotation.IdRotationState) (creation : std.time.SystemTime)
    (e0 : core.io.error.Error) (hmd : statTimestamp self = ok (.Err e0))
    (hk : core.io.error.Error.kind e0 = ok core.io.error.ErrorKind.NotFound)
    (ce : core.io.error.Error) (hc : createTimestamp self = ok (.Err ce)) :
    ∃ e, hadReset self creation = ok (.Err e) ∧ root e = ErrRoot.other := by
  sorry

/-- conditional: if the stat fails with any kind other than `NotFound`, the result is an error with
root class `ErrRoot.other`. In the Rust source this branch does not call `File::create`.
Hypotheses: the outcomes of `fs::metadata` and of `io::Error::kind`; `format` and
`from_str_nonconst` do not fail; the assumptions about `context` for an `io::Error` and an
`anyhow::Error`. -/
theorem had_factory_reset_stat_failed (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hio : IoCtxAssumption root Bool) (hany : AnyCtxLaw root Bool)
    (self : id_rotation.IdRotationState) (creation : std.time.SystemTime)
    (e0 : core.io.error.Error) (hmd : statTimestamp self = ok (.Err e0))
    (k : core.io.error.ErrorKind) (hk : core.io.error.Error.kind e0 = ok k)
    (hnf : k ≠ core.io.error.ErrorKind.NotFound) :
    ∃ e, hadReset self creation = ok (.Err e) ∧ root e = ErrRoot.other := by
  sorry
