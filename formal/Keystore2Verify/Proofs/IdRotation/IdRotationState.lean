import Keystore2Verify.Specs.Defs.IdRotation

namespace Keystore2Verify.IdRotation
open Aeneas Aeneas.Std Result keystore2
open id_rotation.IdRotationState.Insts.CoreCloneClone renaming clone → stateClone
open id_rotation.IdRotationState renaming new → stateNew

/-- conditional: if cloning the path `self.timestamp_path` returns `pb`, `clone self` returns the
state `{ timestamp_path := pb }`. Hypothesis: the outcome of `PathBuf::clone`; for a faithful
clone `pb` equals `self.timestamp_path`. -/
theorem id_rotation_state_clone (self : id_rotation.IdRotationState) (pb : std.path.PathBuf)
    (h : std.path.PathBuf.Insts.CoreCloneClone.clone self.timestamp_path = ok pb) :
    stateClone self = ok { timestamp_path := pb } := by
  sorry

/-- conditional: if `Path::to_owned` of the database path returns `p0`, and pushing the file name
`"timestamp"` (`TIMESTAMP_FILE_NAME`) onto `p0` returns `p1`, `new` returns the state
`{ timestamp_path := p1 }`. Hypotheses: the outcomes of `Path::to_owned` and `PathBuf::push`. No
other state is kept. -/
theorem id_rotation_state_new (keystore_db_path : std.path.Path) (p0 p1 : std.path.PathBuf)
    (h0 : std.path.Path.Insts.AllocBorrowToOwnedPathBuf.to_owned keystore_db_path = ok p0)
    (h1 : std.path.PathBuf.push (Shared0T.Insts.CoreConvertAsRef Str.Insts.CoreConvertAsRefPath)
      p0 (toStr "timestamp") = ok p1) :
    stateNew keystore_db_path = ok { timestamp_path := p1 } := by
  sorry

/-- conditional: `clone self` returns a state whose path has the same observation `view` as the
path of `self`. It never fails. Hypothesis: the assumption about `PathBuf::clone`
(`PathBufCloneSpec view`), for the observation `view` of paths that the model chooses. -/
theorem id_rotation_state_clone_view {β : Type} (view : std.path.PathBuf → β)
    (hp : PathBufCloneSpec view) (self : id_rotation.IdRotationState) :
    ∃ y, stateClone self = ok y ∧ view y.timestamp_path = view self.timestamp_path := by
  sorry
