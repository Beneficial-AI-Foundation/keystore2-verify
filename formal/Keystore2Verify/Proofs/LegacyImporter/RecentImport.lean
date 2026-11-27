import Keystore2Verify.Specs.Defs.LegacyImporter

namespace Keystore2Verify.LegacyImporter
open Aeneas Aeneas.Std Result keystore2
open legacy_importer.RecentImport.Insts

/-- conditional: if cloning the alias `x.alias` returns `s`, `clone x` returns the import with the
same `uid` and the alias `s`. Hypothesis: the outcome of `String::clone`; for a faithful clone `s`
equals `x.alias`. -/
theorem recent_import_clone (x : legacy_importer.RecentImport) (s : String)
    (h : alloc.string.String.Insts.CoreCloneClone.clone x.alias = ok s) :
    CoreCloneClone.clone x = ok { uid := x.uid, «alias» := s } := by
  sorry

/-- exact: if the two uids differ, `eq` returns `false`. In the Rust source the aliases are then
not compared. -/
theorem recent_import_eq_uid_differ (x y : legacy_importer.RecentImport) (h : x.uid ≠ y.uid) :
    CoreCmpPartialEqRecentImport.eq x y = ok false := by
  sorry

/-- exact: if the two uids are equal, `eq` returns what `String::eq` returns for the two
aliases. -/
theorem recent_import_eq_uid_same (x y : legacy_importer.RecentImport) (h : x.uid = y.uid) :
    CoreCmpPartialEqRecentImport.eq x y =
      alloc.string.String.Insts.CoreCmpPartialEqString.eq x.alias y.alias := by
  sorry

/-- exact: if the uid of `x` is less than the uid of `y`, `cmp x y` is `Less`. -/
theorem recent_import_cmp_lt (x y : legacy_importer.RecentImport) (h : x.uid.val < y.uid.val) :
    CoreCmpOrd.cmp x y = ok Ordering.lt := by
  sorry

/-- exact: if the uid of `x` is greater than the uid of `y`, `cmp x y` is `Greater`. -/
theorem recent_import_cmp_gt (x y : legacy_importer.RecentImport) (h : y.uid.val < x.uid.val) :
    CoreCmpOrd.cmp x y = ok Ordering.gt := by
  sorry

/-- exact: if the two uids are equal, `cmp` returns what `String::cmp` returns for the two
aliases. -/
theorem recent_import_cmp_uid_same (x y : legacy_importer.RecentImport) (h : x.uid = y.uid) :
    CoreCmpOrd.cmp x y = alloc.string.String.Insts.CoreCmpOrd.cmp x.alias y.alias := by
  sorry

/-- conditional: if `cmp x y` returns `o`, `partial_cmp x y` returns `Some o`. Hypothesis: the
outcome of `cmp`. If `cmp` fails, so does `partial_cmp`. -/
theorem recent_import_partial_cmp (x y : legacy_importer.RecentImport) (o : Ordering)
    (h : CoreCmpOrd.cmp x y = ok o) :
    CoreCmpPartialOrdRecentImport.partial_cmp x y = ok (some o) := by
  sorry

/-- conditional: `clone x` returns a copy of `x`: the same `uid` and the same `alias`. Hypothesis:
the assumption about `String::clone` (`StringCloneSpec`). -/
theorem recent_import_clone_eq (hs : StringCloneSpec) (x : legacy_importer.RecentImport) :
    CoreCloneClone.clone x = ok x := by
  sorry

/-- conditional: `eq x y` returns `true` exactly when the two `uid` are equal and the two `alias`
are equal. It never fails. Hypothesis: the assumption about `String::eq` (`StringEqSpec`). -/
theorem recent_import_eq_iff (hs : StringEqSpec) (x y : legacy_importer.RecentImport) :
    ∃ b, CoreCmpPartialEqRecentImport.eq x y = ok b ∧
      (b = true ↔ x.uid = y.uid ∧ x.alias = y.alias) := by
  sorry

/-- conditional: `cmp x y` is the lexicographic order of `(uid, alias)`: the order of the two `uid`,
and the order of the two `alias` if the `uid` are equal. It never fails. Hypothesis: the assumption
about `String::cmp` (`StringCmpSpec`). -/
theorem recent_import_cmp_lex (hs : StringCmpSpec) (x y : legacy_importer.RecentImport) :
    CoreCmpOrd.cmp x y = ok (recentImportOrd x y) := by
  sorry

/-- conditional: `partial_cmp x y` returns `Some` of the lexicographic order of `(uid, alias)`
(`recentImportOrd`). It never fails. Hypothesis: the assumption about `String::cmp`
(`StringCmpSpec`). -/
theorem recent_import_partial_cmp_lex (hs : StringCmpSpec) (x y : legacy_importer.RecentImport) :
    CoreCmpPartialOrdRecentImport.partial_cmp x y = ok (some (recentImportOrd x y)) := by
  sorry
