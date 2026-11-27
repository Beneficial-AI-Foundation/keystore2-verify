import Keystore2Verify.Proofs.LegacyImporter.RecentImport
import Keystore2Verify.Proofs.LegacyImporter.CheckEmpty
import Keystore2Verify.Proofs.LegacyImporter.AugmentLegacyCharacteristics

namespace Keystore2Verify.LegacyImporter

section RecentImport
open Aeneas Aeneas.Std Result keystore2
open legacy_importer.RecentImport.Insts

recall recent_import_clone (x : legacy_importer.RecentImport) (s : String)
    (h : alloc.string.String.Insts.CoreCloneClone.clone x.alias = ok s) :
    CoreCloneClone.clone x = ok { uid := x.uid, «alias» := s }

recall recent_import_eq_uid_differ (x y : legacy_importer.RecentImport) (h : x.uid ≠ y.uid) :
    CoreCmpPartialEqRecentImport.eq x y = ok false

recall recent_import_eq_uid_same (x y : legacy_importer.RecentImport) (h : x.uid = y.uid) :
    CoreCmpPartialEqRecentImport.eq x y =
      alloc.string.String.Insts.CoreCmpPartialEqString.eq x.alias y.alias

recall recent_import_cmp_lt (x y : legacy_importer.RecentImport) (h : x.uid.val < y.uid.val) :
    CoreCmpOrd.cmp x y = ok Ordering.lt

recall recent_import_cmp_gt (x y : legacy_importer.RecentImport) (h : y.uid.val < x.uid.val) :
    CoreCmpOrd.cmp x y = ok Ordering.gt

recall recent_import_cmp_uid_same (x y : legacy_importer.RecentImport) (h : x.uid = y.uid) :
    CoreCmpOrd.cmp x y = alloc.string.String.Insts.CoreCmpOrd.cmp x.alias y.alias

recall recent_import_partial_cmp (x y : legacy_importer.RecentImport) (o : Ordering)
    (h : CoreCmpOrd.cmp x y = ok o) :
    CoreCmpPartialOrdRecentImport.partial_cmp x y = ok (some o)

recall recent_import_clone_eq (hs : StringCloneSpec) (x : legacy_importer.RecentImport) :
    CoreCloneClone.clone x = ok x

recall recent_import_eq_iff (hs : StringEqSpec) (x y : legacy_importer.RecentImport) :
    ∃ b, CoreCmpPartialEqRecentImport.eq x y = ok b ∧
      (b = true ↔ x.uid = y.uid ∧ x.alias = y.alias)

recall recent_import_cmp_lex (hs : StringCmpSpec) (x y : legacy_importer.RecentImport) :
    CoreCmpOrd.cmp x y = ok (recentImportOrd x y)

recall recent_import_partial_cmp_lex (hs : StringCmpSpec) (x y : legacy_importer.RecentImport) :
    CoreCmpPartialOrdRecentImport.partial_cmp x y = ok (some (recentImportOrd x y))

end RecentImport

section CheckEmpty
open Aeneas Aeneas.Std Result keystore2
open legacy_importer.LegacyImporterState renaming check_empty → checkEmpty

recall check_empty_empty (self : legacy_importer.LegacyImporterState)
    (lbl : legacy_blob.LegacyBlobLoader)
    (hderef : alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref alloc.alloc.Global self.legacy_loader =
      ok lbl)
    (h : legacy_blob.LegacyBlobLoader.is_empty lbl = ok (.Ok true)) :
    checkEmpty self = ok legacy_importer.LegacyImporter.STATE_EMPTY ∧
      legacy_importer.LegacyImporter.STATE_EMPTY = 2#u8

recall check_empty_ready (self : legacy_importer.LegacyImporterState)
    (lbl : legacy_blob.LegacyBlobLoader)
    (hderef : alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref alloc.alloc.Global self.legacy_loader =
      ok lbl)
    (r : core.result.Result Bool anyhow.Error)
    (h : legacy_blob.LegacyBlobLoader.is_empty lbl = ok r) (hr : r ≠ .Ok true) :
    checkEmpty self = ok legacy_importer.LegacyImporter.STATE_READY ∧
      legacy_importer.LegacyImporter.STATE_READY = 1#u8

end CheckEmpty

section AugmentLegacyCharacteristics
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.RemoteProvisioning
open legacy_importer renaming
  augment_legacy_characteristics_file_with_key_characteristics → augmentLegacy
open key_parameter.KeyParameterValue.Insts
  renaming CoreCmpPartialEqKeyParameterValue → valueEqInst
open legacy_importer.augment_legacy_characteristics_file_with_key_characteristics.closure.Insts
  renaming CoreOpsFunctionFnMutTupleShared0KeyParameterBool → augClosure

recall augment_legacy_characteristics {T It : Type}
    (inst : core.iter.traits.collect.IntoIterator T key_parameter.KeyParameter It)
    (view : It → List key_parameter.KeyParameter)
    (eqv : key_parameter.KeyParameterValue → key_parameter.KeyParameterValue → Bool)
    (heq : ∀ a b, valueEqInst.eq a b = ok (eqv a b))
    (hany : CoreSliceIterAnySpec (augClosure inst))
    (from_km : alloc.vec.Vec key_parameter.KeyParameter) (legacy : T)
    (items : List key_parameter.KeyParameter) (hit : IteratesOver inst view legacy items)
    (hlen : (augmentList eqv from_km.val items).length ≤ Std.Usize.max) :
    ∃ v, augmentLegacy inst from_km legacy = ok v ∧
      v.val = augmentList eqv from_km.val items

recall augment_legacy_characteristics_overflow {T It : Type}
    (inst : core.iter.traits.collect.IntoIterator T key_parameter.KeyParameter It)
    (view : It → List key_parameter.KeyParameter)
    (eqv : key_parameter.KeyParameterValue → key_parameter.KeyParameterValue → Bool)
    (heq : ∀ a b, valueEqInst.eq a b = ok (eqv a b))
    (hany : CoreSliceIterAnySpec (augClosure inst))
    (from_km : alloc.vec.Vec key_parameter.KeyParameter) (legacy : T)
    (items : List key_parameter.KeyParameter) (hit : IteratesOver inst view legacy items)
    (hlen : Std.Usize.max < (augmentList eqv from_km.val items).length) :
    augmentLegacy inst from_km legacy = fail Error.maximumSizeExceeded

end AugmentLegacyCharacteristics

end Keystore2Verify.LegacyImporter
