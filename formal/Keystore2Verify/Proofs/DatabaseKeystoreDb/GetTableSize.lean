import Keystore2Verify.Specs.Defs.DatabaseKeystoreDb

namespace Keystore2Verify.DatabaseKeystoreDb
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

open android_security_metrics.aidl.android.security.metrics

/-- exact: the result, and the returned database, are those of `do_table_size_query` for the
storage type `storage_type`, the query on `dbstat` with the two parameters `schema` (`?1`) and
`table` (`?2`), in this order. Both strings are passed on unchanged, an empty one included. -/
theorem get_table_size_query (self : database.KeystoreDB) (storage_type : Storage.Storage)
    (schema table : Str) :
    database.KeystoreDB.get_table_size self storage_type schema table =
      database.KeystoreDB.do_table_size_query self storage_type (toStr
        "SELECT pgsize,unused FROM dbstat(?1)\n             WHERE name=?2 AND aggregate=TRUE;")
        (Array.to_slice (Array.make 2#usize [ schema, table ])) := by
  sorry
