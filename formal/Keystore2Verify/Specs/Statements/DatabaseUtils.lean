import Keystore2Verify.Proofs.DatabaseUtils.SqlField

namespace Keystore2Verify.DatabaseUtils

section SqlField
open Aeneas Aeneas.Std Result keystore2
open keystore2.rusqlite.row
open keystore2.database.utils
open rusqlite.types.from_sql

recall sql_field_new (index : Std.Usize) (row : Row) :
    SqlField.new index row = ok (index, row)

recall sql_field_get {T : Type} (inst : FromSql T) (i : Std.Usize)
    (row : Row) :
    SqlField.get inst (i, row)
      = Row.get Usize.Insts.RusqliteRowRowIndex inst row i

end SqlField

end Keystore2Verify.DatabaseUtils
