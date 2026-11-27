import Keystore2Verify.Specs.Defs.Externals

namespace Keystore2Verify.Service
open Aeneas Aeneas.Std Result keystore2
open std.thread.local.LocalKey renaming «with» → localLocalKeywith
open Keystore2Verify.Externals
open android_system_keystore2.aidl.android.system.keystore2
open service.KeystoreService
open service.KeystoreService.count_num_entries.closure.Insts
  renaming CoreOpsFunctionFnOnceTupleShared2RefCellKeystoreDBResultI32Error → countClosure

/-- conditional: if the lookup of the key descriptor for `(domain, namespace)` returns the
descriptor `k`, `count_num_entries` returns what the closure on the thread-local database returns
for `(k.domain, k.nspace)` (the domain and namespace of the resolved descriptor): the number of
entries. Hypotheses: the outcomes of `get_key_descriptor_for_lookup` (an item of
keystore2 that the extraction could not translate), of `DB`, and of `LocalKey::with`. -/
theorem count_num_entries_ok (self : service.KeystoreService) (domain : Domain.Domain)
    (ns : Std.I64) (k : KeyDescriptor.KeyDescriptor)
    (hlook : get_key_descriptor_for_lookup self domain ns = ok (.Ok k))
    (lk : std.thread.local.LocalKey (core.cell.RefCell database.KeystoreDB))
    (hdb : globals.DB = ok lk) (v : Std.I32)
    (hwith : localLocalKeywith countClosure lk (k.domain, k.nspace) = ok (.Ok v)) :
    count_num_entries self domain ns = ok (.Ok v) := by
  sorry

/-- conditional: if the lookup and the call that the function forwards to have the outcomes
below and the final result is an error `e`, the function returns an error with the same root
cause (nothing is added). Hypotheses: the outcomes of `get_key_descriptor_for_lookup` (an item of
keystore2 that the extraction could not translate), of `DB`, and of `LocalKey::with`. -/
theorem count_num_entries_downstream_err (root : anyhow.Error → ErrRoot)
    (self : service.KeystoreService) (domain : Domain.Domain)
    (ns : Std.I64) (k : KeyDescriptor.KeyDescriptor)
    (hlook : get_key_descriptor_for_lookup self domain ns = ok (.Ok k))
    (lk : std.thread.local.LocalKey (core.cell.RefCell database.KeystoreDB))
    (hdb : globals.DB = ok lk) (e : anyhow.Error)
    (hwith : localLocalKeywith countClosure lk (k.domain, k.nspace) = ok (.Err e)) :
    ∃ e', count_num_entries self domain ns = ok (.Err e') ∧ root e' = root e := by
  sorry

/-- conditional: if the lookup of the key descriptor returns an error `e`, `count_num_entries`
returns an error with the same root cause (no context is added). In the Rust source the database
is not touched on this path. Hypothesis: the outcome of `get_key_descriptor_for_lookup`. -/
theorem count_num_entries_lookup_err (root : anyhow.Error → ErrRoot)
    (self : service.KeystoreService) (domain : Domain.Domain) (ns : Std.I64) (e : anyhow.Error)
    (hlook : get_key_descriptor_for_lookup self domain ns = ok (.Err e)) :
    ∃ e', count_num_entries self domain ns = ok (.Err e') ∧ root e' = root e := by
  sorry
