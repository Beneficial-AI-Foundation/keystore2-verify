import Keystore2Verify.Specs.Defs.Externals

namespace Keystore2Verify.DatabaseUtils
open Aeneas Aeneas.Std Result keystore2
open keystore2.rusqlite.row
open keystore2.database.utils
open rusqlite.types.from_sql

/-- exact: `new` never fails and returns the pair of the column index and the row. It does not
check that the index is a column of the row. -/
theorem sql_field_new (index : Std.Usize) (row : Row) :
    SqlField.new index row = ok (index, row) := by
  sorry

/-- exact: `get` returns what `Row::get` returns for the row and the column index of the field,
unchanged (`ok (Ok v)`, `ok (Err e)` or `fail`). It adds no context and converts no error. Which
value or which `rusqlite::Error` that call gives is not stated. -/
theorem sql_field_get {T : Type} (inst : FromSql T) (i : Std.Usize)
    (row : Row) :
    SqlField.get inst (i, row)
      = Row.get Usize.Insts.RusqliteRowRowIndex inst row i := by
  sorry

end Keystore2Verify.DatabaseUtils
