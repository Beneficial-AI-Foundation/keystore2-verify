import Keystore2Verify.Specs.Defs.DatabaseKeystoreDb

namespace Keystore2Verify.DatabaseKeystoreDb
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

open android_security_metrics.aidl.android.security.metrics

/-- conditional: the constant `Storage::DATABASE` evaluates to `s`. The result, and the returned
database, are those of `do_table_size_query` for the storage type `s`, the query on
`page_count`, `page_size` and `freelist_count` of the `persistent` schema, and no parameters.
Nothing is said about the size values. -/
theorem get_total_size_query (self : database.KeystoreDB) (s : Storage.Storage)
    (hdb : Storage.Storage.DATABASE = ok s) :
    database.KeystoreDB.get_total_size self =
      database.KeystoreDB.do_table_size_query self s (toStr
        ("SELECT page_count * page_size, freelist_count * page_size\n" ++
         "             FROM pragma_page_count(\'persistent\'),\n" ++
         "                  pragma_page_size(\'persistent\'),\n" ++
         "                  persistent.pragma_freelist_count();"))
        (Array.to_slice (Std.Array.empty Str)) := by
  sorry
