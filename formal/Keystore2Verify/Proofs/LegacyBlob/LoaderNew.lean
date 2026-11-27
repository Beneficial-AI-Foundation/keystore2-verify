import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open legacy_blob.LegacyBlobLoader
open std.path.Path.Insts.AllocBorrowToOwnedPathBuf renaming to_owned → pathToOwned
/-- conditional: if `to_owned` returns the path buffer `pb`, `new` returns a loader that holds `pb`.
Hypothesis: the outcome of `Path::to_owned`. -/
theorem legacy_blob_loader_new_ok (path : std.path.Path) (pb : std.path.PathBuf)
    (h : pathToOwned path = ok pb) :
    legacy_blob.LegacyBlobLoader.new path = ok { path := pb } := by
  sorry

/-- conditional: if `to_owned` fails with `x`, `new` fails with the same `x`. Hypothesis: the
outcome of `Path::to_owned`. -/
theorem legacy_blob_loader_new_fail (path : std.path.Path) (x : Error)
    (h : pathToOwned path = fail x) :
    legacy_blob.LegacyBlobLoader.new path = fail x := by
  sorry

end Keystore2Verify.LegacyBlob
