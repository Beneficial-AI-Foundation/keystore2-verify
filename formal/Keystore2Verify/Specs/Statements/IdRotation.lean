import Keystore2Verify.Proofs.IdRotation.IdRotationState
import Keystore2Verify.Proofs.IdRotation.HadFactoryResetSinceIdRotation

namespace Keystore2Verify.IdRotation

section IdRotationState
open Aeneas Aeneas.Std Result keystore2
open id_rotation.IdRotationState.Insts.CoreCloneClone renaming clone → stateClone
open id_rotation.IdRotationState renaming new → stateNew

recall id_rotation_state_clone (self : id_rotation.IdRotationState) (pb : std.path.PathBuf)
    (h : std.path.PathBuf.Insts.CoreCloneClone.clone self.timestamp_path = ok pb) :
    stateClone self = ok { timestamp_path := pb }

recall id_rotation_state_new (keystore_db_path : std.path.Path) (p0 p1 : std.path.PathBuf)
    (h0 : std.path.Path.Insts.AllocBorrowToOwnedPathBuf.to_owned keystore_db_path = ok p0)
    (h1 : std.path.PathBuf.push (Shared0T.Insts.CoreConvertAsRef Str.Insts.CoreConvertAsRefPath)
      p0 (toStr "timestamp") = ok p1) :
    stateNew keystore_db_path = ok { timestamp_path := p1 }

recall id_rotation_state_clone_view {β : Type} (view : std.path.PathBuf → β)
    (hp : PathBufCloneSpec view) (self : id_rotation.IdRotationState) :
    ∃ y, stateClone self = ok y ∧ view y.timestamp_path = view self.timestamp_path

end IdRotationState

section HadFactoryResetSinceIdRotation
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open id_rotation.IdRotationState renaming had_factory_reset_since_id_rotation → hadReset

recall had_factory_reset_ok (root : anyhow.Error → ErrRoot)
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
    hadReset self creation = ok (.Ok b)

recall had_factory_reset_before_epoch (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hst : SystemTimeCtxAssumption root core.time.Duration)
    (self : id_rotation.IdRotationState) (creation : std.time.SystemTime)
    (md : std.fs.Metadata) (hmd : statTimestamp self = ok (.Ok md))
    (st : std.time.SystemTime) (hst0 : std.time.SystemTime.UNIX_EPOCH = ok st)
    (se : std.time.SystemTimeError)
    (hd : std.time.SystemTime.duration_since creation st = ok (.Err se)) :
    ∃ e, hadReset self creation = ok (.Err e) ∧ root e = ErrRoot.other

recall had_factory_reset_too_many_periods (root : anyhow.Error → ErrRoot)
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
    ∃ e, hadReset self creation = ok (.Err e) ∧ root e = ErrRoot.other

recall had_factory_reset_zero_period (root : anyhow.Error → ErrRoot)
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
    hadReset self creation = fail Error.divisionByZero

recall had_factory_reset_no_period_start (root : anyhow.Error → ErrRoot)
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
    ∃ e, hadReset self creation = ok (.Err e) ∧ root e = ErrRoot.other

recall had_factory_reset_no_modified_time (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hst : SystemTimeCtxAssumption root core.time.Duration)
    (hopt : OptionContextSpec root) (hio : IoCtxAssumption root std.time.SystemTime)
    (self : id_rotation.IdRotationState) (creation : std.time.SystemTime)
    (md : std.fs.Metadata) (hmd : statTimestamp self = ok (.Ok md))
    (st : std.time.SystemTime) (d p : core.time.Duration) (i i1 q : Std.U128)
    (n32 : Std.U32) (d1 : core.time.Duration) (t : std.time.SystemTime)
    (hpath : SuccessPath creation st d p i i1 q n32 d1 t)
    (ie : core.io.error.Error) (hm : std.fs.Metadata.modified md = ok (.Err ie)) :
    ∃ e, hadReset self creation = ok (.Err e) ∧ root e = ErrRoot.other

recall had_factory_reset_created (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hio : IoCtxAssumption root std.fs.File) (hany : AnyCtxLaw root Bool)
    (self : id_rotation.IdRotationState) (creation : std.time.SystemTime)
    (e0 : core.io.error.Error) (hmd : statTimestamp self = ok (.Err e0))
    (hk : core.io.error.Error.kind e0 = ok core.io.error.ErrorKind.NotFound)
    (f : std.fs.File) (hc : createTimestamp self = ok (.Ok f)) :
    hadReset self creation = ok (.Ok true)

recall had_factory_reset_create_failed (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hio : IoCtxAssumption root std.fs.File)
    (self : id_rotation.IdRotationState) (creation : std.time.SystemTime)
    (e0 : core.io.error.Error) (hmd : statTimestamp self = ok (.Err e0))
    (hk : core.io.error.Error.kind e0 = ok core.io.error.ErrorKind.NotFound)
    (ce : core.io.error.Error) (hc : createTimestamp self = ok (.Err ce)) :
    ∃ e, hadReset self creation = ok (.Err e) ∧ root e = ErrRoot.other

recall had_factory_reset_stat_failed (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hio : IoCtxAssumption root Bool) (hany : AnyCtxLaw root Bool)
    (self : id_rotation.IdRotationState) (creation : std.time.SystemTime)
    (e0 : core.io.error.Error) (hmd : statTimestamp self = ok (.Err e0))
    (k : core.io.error.ErrorKind) (hk : core.io.error.Error.kind e0 = ok k)
    (hnf : k ≠ core.io.error.ErrorKind.NotFound) :
    ∃ e, hadReset self creation = ok (.Err e) ∧ root e = ErrRoot.other

end HadFactoryResetSinceIdRotation

end Keystore2Verify.IdRotation
