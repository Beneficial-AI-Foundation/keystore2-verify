import Keystore2Verify.Specs.Defs.Externals

namespace Keystore2Verify.Service
open Aeneas Aeneas.Std Result keystore2
open std.thread.local.LocalKey renaming «with» → localLocalKeywith
open Keystore2Verify.Externals
open android_system_keystore2.aidl.android.system.keystore2
open service.KeystoreService
open service.KeystoreService.list_entries.closure.Insts
  renaming
    CoreOpsFunctionFnOnceTupleShared2RefCellKeystoreDBResultVecKeyDescriptorError → listClosure
open service.KeystoreService.list_entries_batched.closure.Insts
  renaming
    CoreOpsFunctionFnOnceTupleShared4RefCellKeystoreDBResultVecKeyDescriptorError → batchClosure

/-- conditional: if the lookup of the key descriptor for `(domain, namespace)` returns the
descriptor `k`, `list_entries` returns what the closure on the thread-local database returns for
`(k.domain, k.nspace)` (the domain and namespace of the resolved descriptor, not the original
ones): the list of key descriptors. The closure lists the entries from the start
(no start alias). The database that it returns is dropped. Hypotheses: the outcomes of
`get_key_descriptor_for_lookup` (an item of keystore2 that the extraction could not translate),
of `DB`, and of `LocalKey::with`. -/
theorem list_entries_ok (self : service.KeystoreService) (domain : Domain.Domain)
    (ns : Std.I64) (k : KeyDescriptor.KeyDescriptor)
    (hlook : get_key_descriptor_for_lookup self domain ns = ok (.Ok k))
    (lk : std.thread.local.LocalKey (core.cell.RefCell database.KeystoreDB))
    (hdb : globals.DB = ok lk)
    (v : (alloc.vec.Vec KeyDescriptor.KeyDescriptor))
    (hwith : localLocalKeywith listClosure lk (k.domain, k.nspace) = ok (.Ok v)) :
    list_entries self domain ns = ok (.Ok v) := by
  sorry

/-- conditional: if the lookup and the call that the function forwards to have the outcomes
below and the final result is an error `e`, the function returns an error with the same root
cause (nothing is added). Hypotheses: the outcomes of
`get_key_descriptor_for_lookup` (an item of keystore2 that the extraction could not translate),
of `DB`, and of `LocalKey::with`. -/
theorem list_entries_downstream_err (root : anyhow.Error → ErrRoot)
    (self : service.KeystoreService) (domain : Domain.Domain)
    (ns : Std.I64) (k : KeyDescriptor.KeyDescriptor)
    (hlook : get_key_descriptor_for_lookup self domain ns = ok (.Ok k))
    (lk : std.thread.local.LocalKey (core.cell.RefCell database.KeystoreDB))
    (hdb : globals.DB = ok lk)
    (e : anyhow.Error)
    (hwith : localLocalKeywith listClosure lk (k.domain, k.nspace) = ok (.Err e)) :
    ∃ e', list_entries self domain ns = ok (.Err e') ∧ root e' = root e := by
  sorry

/-- conditional: if the lookup of the key descriptor returns an error `e`, `list_entries` returns
an error with the same root cause (no context is added). In the Rust source the database is not
touched on this path. Hypothesis: the outcome of `get_key_descriptor_for_lookup`. -/
theorem list_entries_lookup_err (root : anyhow.Error → ErrRoot) (self : service.KeystoreService)
    (domain : Domain.Domain) (ns : Std.I64) (e : anyhow.Error)
    (hlook : get_key_descriptor_for_lookup self domain ns = ok (.Err e)) :
    ∃ e', list_entries self domain ns = ok (.Err e') ∧ root e' = root e := by
  sorry

/-- conditional: as `list_entries_ok`, but the closure lists the entries that come after the alias
`start_past_alias`, if there is one. Hypotheses: the outcomes of `get_key_descriptor_for_lookup`,
of `DB`, and of `LocalKey::with`. -/
theorem list_entries_batched_ok (self : service.KeystoreService) (domain : Domain.Domain)
    (ns : Std.I64) (start_past_alias : Option Str) (k : KeyDescriptor.KeyDescriptor)
    (hlook : get_key_descriptor_for_lookup self domain ns = ok (.Ok k))
    (lk : std.thread.local.LocalKey (core.cell.RefCell database.KeystoreDB))
    (hdb : globals.DB = ok lk)
    (v : (alloc.vec.Vec KeyDescriptor.KeyDescriptor))
    (hwith : localLocalKeywith batchClosure lk
      (k.domain, k.nspace, start_past_alias) = ok (.Ok v)) :
    list_entries_batched self domain ns start_past_alias = ok (.Ok v) := by
  sorry

/-- conditional: if the lookup and the call that the function forwards to have the outcomes
below and the final result is an error `e`, the function returns an error with the same root
cause (nothing is added). Hypotheses: the outcomes of `get_key_descriptor_for_lookup`,
of `DB`, and of `LocalKey::with`. -/
theorem list_entries_batched_downstream_err (root : anyhow.Error → ErrRoot)
    (self : service.KeystoreService) (domain : Domain.Domain)
    (ns : Std.I64) (start_past_alias : Option Str) (k : KeyDescriptor.KeyDescriptor)
    (hlook : get_key_descriptor_for_lookup self domain ns = ok (.Ok k))
    (lk : std.thread.local.LocalKey (core.cell.RefCell database.KeystoreDB))
    (hdb : globals.DB = ok lk)
    (e : anyhow.Error)
    (hwith : localLocalKeywith batchClosure lk
      (k.domain, k.nspace, start_past_alias) = ok (.Err e)) :
    ∃ e', list_entries_batched self domain ns start_past_alias = ok (.Err e') ∧
      root e' = root e := by
  sorry

/-- conditional: if the lookup of the key descriptor returns an error `e`, `list_entries_batched`
returns an error with the same root cause (no context is added). Hypothesis: the outcome of
`get_key_descriptor_for_lookup`. -/
theorem list_entries_batched_lookup_err (root : anyhow.Error → ErrRoot)
    (self : service.KeystoreService) (domain : Domain.Domain) (ns : Std.I64)
    (start_past_alias : Option Str) (e : anyhow.Error)
    (hlook : get_key_descriptor_for_lookup self domain ns = ok (.Err e)) :
    ∃ e', list_entries_batched self domain ns start_past_alias = ok (.Err e') ∧
      root e' = root e := by
  sorry
