import Keystore2Verify.Specs.Defs.LegacyImporter

namespace Keystore2Verify.LegacyImporter
open Aeneas Aeneas.Std Result keystore2
open legacy_importer.LegacyImporterState renaming check_empty → checkEmpty

/-- conditional: if the legacy blob loader reports that the database is empty
(`is_empty` returns `Ok true`), `check_empty` returns `STATE_EMPTY` (2). Hypotheses: the outcomes
of `Arc::deref` on the loader and of `LegacyBlobLoader::is_empty` (a file system read). -/
theorem check_empty_empty (self : legacy_importer.LegacyImporterState)
    (lbl : legacy_blob.LegacyBlobLoader)
    (hderef : alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref alloc.alloc.Global self.legacy_loader =
      ok lbl)
    (h : legacy_blob.LegacyBlobLoader.is_empty lbl = ok (.Ok true)) :
    checkEmpty self = ok legacy_importer.LegacyImporter.STATE_EMPTY ∧
      legacy_importer.LegacyImporter.STATE_EMPTY = 2#u8 := by
  sorry

/-- conditional: if the legacy blob loader reports that the database is not empty
(`Ok false`), or fails (`Err`), `check_empty` returns `STATE_READY` (1). The state
`STATE_UNINITIALIZED` is never returned. Hypotheses: the outcomes of `Arc::deref` on the loader
and of `LegacyBlobLoader::is_empty`. -/
theorem check_empty_ready (self : legacy_importer.LegacyImporterState)
    (lbl : legacy_blob.LegacyBlobLoader)
    (hderef : alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref alloc.alloc.Global self.legacy_loader =
      ok lbl)
    (r : core.result.Result Bool anyhow.Error)
    (h : legacy_blob.LegacyBlobLoader.is_empty lbl = ok r) (hr : r ≠ .Ok true) :
    checkEmpty self = ok legacy_importer.LegacyImporter.STATE_READY ∧
      legacy_importer.LegacyImporter.STATE_READY = 1#u8 := by
  sorry
