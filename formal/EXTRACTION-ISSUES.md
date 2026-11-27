# Extraction issues

This file lists every place where Charon, Aeneas or Lean could not take the `keystore2` crate as it is,
and how each was resolved. `formal/EXTRACTION.md` gives the tools and the exact arguments;
`METHODOLOGY.md` says how blockers were handled and how patches were reviewed.

Resolutions:

- **opaque**: the item's signature is translated and its body is not. In Lean it is an assumption about an
  external function (or, for a type, an opaque type).
- **excluded**: the item is not translated at all. Its callers are opaque.
- **body included**: an item of another crate whose body is translated (Charon keeps the bodies of other
  crates' items out by default).
- **patched**: a translation patch reshapes the code so the tools translate it; the item is translated with
  its body.
- **not started**: in nine modules (below), the translation starts from each free item and inherent method
  instead of the whole module. A trait impl there is translated only when translated code uses it.

## Blocker classes

| Class | Tool | Items | Known issue (all open at the pinned release unless said) |
|---|---|---:|---|
| `dyn` trait objects (types, casts, method calls) | Aeneas | 77 | 1343, 1500 |
| `LazyLock<_, fn() -> _>` statics and other arrow types | Aeneas | 46 | none found |
| Nested borrows | Aeneas | 50 | 1503, 1234, 1170 |
| Early returns, `?`, `break` or `continue` inside loops | Aeneas | 12 | 822 |
| Loop and borrow state that does not join | Aeneas | 19 | 930, 1282, 1349, 1266, 804, 1214 |
| Trait items: generic associated types, associated-type constraints | Aeneas | 8 | none found |
| Builds or reads a type Aeneas cannot declare | Aeneas | 14 | none found |
| Calls an excluded or failing item | Aeneas | 6 | none found |
| `format!` arguments are `()` in the Aeneas Lean library (`core::fmt::Arguments` is `Unit`) | Lean model | 9 | none found |
| Lean name clashes and name capture | Lean | 12 | 1554 |
| Generated Lean that does not elaborate | Lean | 29 | 1584 (fixed after the pinned release) |
| Other internal errors | Aeneas | 121 | none specific |
| Kept from the first stage, or for its frozen statements | - | 19 | - |

## The nine modules translated item by item

Charon puts every required method of a trait into the trait's Lean structure as soon as anything reaches
the trait, and Aeneas cannot give a Lean universe to `dyn` types inside a structure field (the same defect
as Aeneas issue 1584, fixed after the pinned release). keystore2 implements eight AIDL service traits and
`binder::Interface`, whose methods take or return `Strong<dyn ...>` and `&mut dyn Write`. In addition, the
serde derives in `key_parameter.rs` reach serde's `Serialize` and `Serializer`, which are mutually recursive;
Aeneas's Lean model does not support mutually recursive traits.

So in `apc`, `authorization`, `key_parameter`, `km_compat`, `maintenance`, `metrics`, `operation`,
`security_level` and `service`, the translation starts from each free item and inherent method instead of
the whole module, and these impls are left out:

- `apc.rs`: `IProtectedConfirmation` for `ApcManager` (line 328), `Interface` for `ApcManager` (line 176).
- `authorization.rs`: `IKeystoreAuthorization` for `AuthorizationManager` (line 326), `Interface` for `AuthorizationManager` (line 322).
- `key_parameter.rs`: `Deserialize` for `KeyParameterValue` (line 825), `Deserialize` for `KeyParameter` (line 1059), `Deserialize` for `Primitive` (line 196), `Serialize` for a serde helper type (line 1059), `Serialize` for a serde helper type (line 825), `Serialize` for `KeyParameterValue` (line 825), `Serialize` for `KeyParameter` (line 1059), `Serialize` for `Primitive` (line 196).
- `km_compat.rs`: `IKeyMintDevice` for `BacklevelKeyMintWrapper<T>` (line 175), `Interface` for `BacklevelKeyMintWrapper<T>` (line 173).
- `maintenance.rs`: `IKeystoreMaintenance` for `Maintenance` (line 578), `Interface` for `Maintenance` (line 556).
- `metrics.rs`: `IKeystoreMetrics` for `Metrics` (line 52), `Interface` for `Metrics` (line 50).
- `operation.rs`: `IKeystoreOperation` for `KeystoreOperation` (line 878), `Interface` for `KeystoreOperation` (line 876).
- `security_level.rs`: `IKeystoreSecurityLevel` for `KeystoreSecurityLevel` (line 1183), `Interface` for `KeystoreSecurityLevel` (line 1181).
- `service.rs`: `IKeystoreService` for `KeystoreService` (line 401), `Interface` for `KeystoreService` (line 397).

Charon cannot start from a method of a trait impl, so the other trait impls of these modules are translated
only when translated code uses them. Those not used are listed here:

- `apc.rs`: `Clone`, `Debug` x2, `Default`, `Display`, `Eq`, `Error`, `PartialEq`, `StructuralPartialEq`.
- `authorization.rs`: `Debug` x2, `Eq`, `PartialEq`, `StructuralPartialEq`.
- `key_parameter.rs`: `AssociatePrimitive` x13, `Clone` x2, `Debug`, `Display`, `Eq` x2, `Error`, `From` x4, `KpDefault` x2, `Ord` x2, `PartialEq`, `PartialOrd` x2, `StructuralPartialEq` x3, `ToSql`, `TryFrom` x3.
- `km_compat.rs`: `Debug` x4, `EmulationDetector` x2, `Eq` x2, `PartialEq` x2, `StructuralPartialEq` x2.
- `maintenance.rs`: `Debug`, `DecodeValue`, `DerOrd`, `EncodeValue`, `Eq`, `PartialEq`, `Sequence`, `StructuralPartialEq`.
- `operation.rs`: `Clone` x2, `Copy` x2, `Debug` x5, `Default` x2, `Drop`, `Eq`, `Ord`, `PartialEq`, `PartialOrd`, `StructuralPartialEq`.
- `service.rs`: `Default`.

Five inherent methods share their name with a method of a left-out impl (`Operation::{update, finish, abort}`,
`KeystoreService::{grant, ungrant}`) and are not started either; all five would be opaque.

## Translation patches

### `03-legacy-blob-result-ok`

Five uses of `Result::ok` in `legacy_blob.rs` are written without it, each on its own line, so that `extract_legacy_alias`, `remove_user_dir_if_empty` and `remove_super_key` are translated. Aeneas translates `Result::ok` to an axiom named `core.result.Result.ok`, which captures the Aeneas monad's `ok` inside the translation of `Result::or_else` (Aeneas issue 1554, open).

| Reviewer | Model | Score | Verdict |
|---|---|---|---|
| Claude Code | Claude Fable 5.2 (`claude-fable-5-2`, xhigh) | 9/10 | approve |
| Codex | GPT-6.2 Astra (`gpt-6.2-astra`, xhigh) | 10/10 | approve |
| Antigravity (`agy`) | Gemini Carbon (`gemini-4-carbon-high`) | 9.5/10 | approve |

Result: accepted, 3 of 3. Every reviewer found each rewritten line to have the same value, effects, order, error
paths and panics as the original. The other uses of `Result::ok` (`legacy_blob.rs` line 1005, `async_task.rs` lines 58
and 65) are in functions that stay opaque for other reasons.

### `04` to `11`: the `format!` sites

The Aeneas Lean library models the arguments of `format!` as `()`, so a translated `format!` gives one string for
every input. Each patch rewrites, on the same line, the `format!` calls of one function whose string reaches SQL, a
file path or a Binder service name. The new code builds the same `String` with `to_owned`, `push_str` and `to_string`,
which are translated as calls on their inputs. The diagnostic `format!` calls next to them are unchanged.

| Patch | Function | Lines | Claude Code, Fable 5.2 | Codex, GPT-6.2 Astra | Antigravity, Gemini Carbon | Result |
|---|---|---|---|---|---|---|
| `04` | `delete_received_grants` | `database.rs` 2488 | 9/10 approve | 7/10 reject | 10/10 approve | accepted, 2 of 3 |
| `05` | `pragma` | `database.rs` 3128 | 10/10 approve | 7/10 reject | 10/10 approve | accepted, 2 of 3 |
| `06` | `get_remotely_provisioned_component_name` | `globals.rs` 433, 441 | 10/10 approve | 10/10 approve | 10/10 approve | accepted, 3 of 3 |
| `07` | `make_legacy_keystore_entry_filename` | `legacy_blob.rs` 933, 934 | 9/10 approve | 7/10 reject | 10/10 approve | accepted, 2 of 3 |
| `08` | `make_blob_filename` | `legacy_blob.rs` 942, 944 | 9/10 approve | 7/10 reject | 10/10 approve | accepted, 2 of 3 |
| `09` | `make_chr_filename` | `legacy_blob.rs` 952, 954 | 9/10 approve | 7/10 reject | 10/10 approve | accepted, 2 of 3 |
| `10` | `make_user_path_name` | `legacy_blob.rs` 966 | 9/10 approve | 7/10 reject | 10/10 approve | accepted, 2 of 3 |
| `11` | `is_empty_user` | `legacy_blob.rs` 990 | 9/10 approve | 7/10 reject | 10/10 approve | accepted, 2 of 3 |

Each seat reviewed each patch separately. Checks besides the council: a differential test of the original and
patched code (2,501 comparisons, none differ), erasure probes in Lean (12 equalities of different inputs were
provable by `rfl` before the patches and none after), and the stage C build (see `METHODOLOGY.md`).

Dissent (Astra, on all but `06`): the patched code asks the allocator for different blocks than `format!` does (a
separate `String` for `to_string`, and a first reservation of another size). Both versions abort when an allocation
is refused, but under memory exhaustion one version can abort where the other goes on. Fable and Carbon judged
allocation requests to be outside the agreed observer set (return values, error results as callers distinguish them,
external effects, panic occurrence and the file and line it reports). For `06` the requests are the same as the
original's. Astra's alternative, a named helper that keeps the original `format!` and stays opaque, keeps the requests
exactly but leaves each string to an assumption about keystore2 code.

## Changes to the tools and the stand-ins

- `fvs-harness/models/watchdog_rs` (new) models the upstream `watchdog_rs` crate (`keystore2/watchdog`): its public
  API with opaque types and no bodies. With it, `keystore2` is built with the `watchdog` feature on, as Soong builds
  it, and the patch `02-watchdog-off-path-public`, which made the feature-off module compile, is no longer in the
  series. keystore2's global watchdog `WD` is excluded and the three helpers that read it are opaque (rows below).
- FVS's extraction engine accepts the standard library's own registry dependencies (`hashbrown 0.17.1`),
  checked against the toolchain's `library/Cargo.lock` and the cached archive. Without it the engine refused
  every extraction that uses `HashMap`.
- FVS's extraction engine lets an extraction pass Aeneas's `-filter-trait-methods`. Without it, every
  instance of `Iterator` and `core::error::Error` carried methods (`map`, `collect`, `source`, ...) that the
  Aeneas Lean library's model of the trait does not declare, and Lean rejected 68 instance fields.
- `fvs-harness/models/postprocessor_client` defines `PostProcessorError` and re-exports it as `Error`.
  Aeneas names a trait impl after the last segment of its type arguments, so keystore2's
  `From<rkpd_client::Error>` and `From<postprocessor_client::Error>` impls got one Lean name.
- `crate::error::_::fmt` (the `Debug` and `Display` impls of `keystore2::error::Error`) stay opaque: with their
  bodies translated, the axiom lists printed after the merged statements change.

## One row per argument

| Item | Where | Error | Resolution |
|---|---|---|---|
| `crate::apc::_::cancelPrompt` | `keystore2/src/apc.rs:342` | passes its module's `into_logged_binder` to `map_err` as a value; Charon makes one `FnOnce<(anyhow::Error,)>` impl per such function and Aeneas gives them all one Lean name (only `error.rs`'s family is kept) | opaque |
| `crate::apc::_::cancel_prompt` | `keystore2/src/apc.rs:301` | Dynamic trait types are not supported yet | opaque |
| `crate::apc::_::isSupported` | `keystore2/src/apc.rs:349` | passes its module's `into_logged_binder` to `map_err` as a value; Charon makes one `FnOnce<(anyhow::Error,)>` impl per such function and Aeneas gives them all one Lean name (only `error.rs`'s family is kept) | opaque |
| `crate::apc::_::new_native_binder` | `keystore2/src/apc.rs:180` | its signature returns `Strong<dyn IProtectedConfirmation>`; that trait's required methods take `dyn` types, which Lean cannot place in a universe | excluded |
| `crate::apc::_::presentPrompt` | `keystore2/src/apc.rs:329` | passes its module's `into_logged_binder` to `map_err` as a value; Charon makes one `FnOnce<(anyhow::Error,)>` impl per such function and Aeneas gives them all one Lean name (only `error.rs`'s family is kept) | opaque |
| `crate::apc::_::present_prompt` | `keystore2/src/apc.rs:242` | Dynamic trait types are not supported yet | opaque |
| `crate::apc::_::result` | `keystore2/src/apc.rs:224` | Nested borrows are not supported yet | opaque |
| `crate::apc::into_logged_binder` | `keystore2/src/apc.rs:88` | Could not match the contexts | opaque |
| `crate::async_task::AsyncTaskState` | `keystore2/src/async_task.rs:92` | Aeneas cannot translate this type's declaration (a field holds a `dyn` trait object), so the type is kept opaque | opaque |
| `crate::async_task::Shelf` | `keystore2/src/async_task.rs:42` | Aeneas cannot translate this type's declaration (a field holds a `dyn` trait object), so the type is kept opaque | opaque |
| `crate::async_task::_::add_idle` | `keystore2/src/async_task.rs:167` | Higher-ranked vtables are not supported | opaque |
| `crate::async_task::_::default` | `keystore2/src/async_task.rs:114` | builds or reads a field of a type whose declaration Aeneas cannot translate (Aeneas stops with `Not_found` in `PureTypeCheck.get_adt_field_types`) | opaque |
| `crate::async_task::_::fmt` |  | builds or reads a field of a type whose declaration Aeneas cannot translate (Aeneas stops with `Not_found` in `PureTypeCheck.get_adt_field_types`) | opaque |
| `crate::async_task::_::get_downcast_mut` | `keystore2/src/async_task.rs:53` | Can't end abstraction 6 as it is set as non-endable | opaque |
| `crate::async_task::_::get_downcast_ref` | `keystore2/src/async_task.rs:47` | Can't end abstraction 6 as it is set as non-endable | opaque |
| `crate::async_task::_::get_mut` | `keystore2/src/async_task.rs:73` | Dynamic trait types are not supported yet | opaque |
| `crate::async_task::_::get_or_put_with` | `keystore2/src/async_task.rs:86` | Dynamic trait types are not supported yet | opaque |
| `crate::async_task::_::new` | `keystore2/src/async_task.rs:121` | Unexpected bound region: '0_0 | opaque |
| `crate::async_task::_::put` | `keystore2/src/async_task.rs:65` | Dynamic trait types are not supported yet | opaque |
| `crate::async_task::_::queue_hi_if_running` | `keystore2/src/async_task.rs:216` | New value doesn't have the same type as its destination | opaque |
| `crate::async_task::_::queue_if` | `keystore2/src/async_task.rs:194` | Higher-ranked vtables are not supported | opaque |
| `crate::async_task::_::remove_downcast_ref` | `keystore2/src/async_task.rs:58` | Dynamic trait types are not supported yet | opaque |
| `crate::async_task::_::spawn_thread` | `keystore2/src/async_task.rs:241` | Dynamic trait types are not supported yet | opaque |
| `crate::attestation_key_utils::get_attest_key_info` | `keystore2/src/attestation_key_utils.rs:64` | Internal error, please file an issue | opaque |
| `crate::audit_log::log_key_event` | `keystore2/src/audit_log.rs:72` | Unimplemented | opaque |
| `crate::audit_log::log_key_integrity_violation` | `keystore2/src/audit_log.rs:63` | Unimplemented | opaque |
| `crate::authorization::_::addAuthToken` | `keystore2/src/authorization.rs:327` | Internal error: please file an issue | opaque |
| `crate::authorization::_::add_auth_token` | `keystore2/src/authorization.rs:267` | Nested borrows are not supported yet | opaque |
| `crate::authorization::_::getAuthTokensForCredStore` | `keystore2/src/authorization.rs:419` | passes its module's `into_logged_binder` to `map_err` as a value; Charon makes one `FnOnce<(anyhow::Error,)>` impl per such function and Aeneas gives them all one Lean name (only `error.rs`'s family is kept) | opaque |
| `crate::authorization::_::getLastAuthTime` | `keystore2/src/authorization.rs:436` | passes its module's `into_logged_binder` to `map_err` as a value; Charon makes one `FnOnce<(anyhow::Error,)>` impl per such function and Aeneas gives them all one Lean name (only `error.rs`'s family is kept) | opaque |
| `crate::authorization::_::get_auth_tokens_for_credstore` | `keystore2/src/authorization.rs:282` | Arrow types are not supported yet | opaque |
| `crate::authorization::_::get_last_auth_time` | `keystore2/src/authorization.rs:299` | Arrow types are not supported yet | opaque |
| `crate::authorization::_::new_native_binder` | `keystore2/src/authorization.rs:245` | Dynamic trait types are not supported yet | opaque |
| `crate::authorization::_::onDeviceLocked` | `keystore2/src/authorization.rs:357` | Internal error: please file an issue | opaque |
| `crate::authorization::_::onDeviceUnlocked` | `keystore2/src/authorization.rs:337` | passes its module's `into_logged_binder` to `map_err` as a value; Charon makes one `FnOnce<(anyhow::Error,)>` impl per such function and Aeneas gives them all one Lean name (only `error.rs`'s family is kept) | opaque |
| `crate::authorization::_::onNonLskfUnlockMethodsExpired` | `keystore2/src/authorization.rs:407` | passes its module's `into_logged_binder` to `map_err` as a value; Charon makes one `FnOnce<(anyhow::Error,)>` impl per such function and Aeneas gives them all one Lean name (only `error.rs`'s family is kept) | opaque |
| `crate::authorization::_::onUserStorageLocked` | `keystore2/src/authorization.rs:383` | passes its module's `into_logged_binder` to `map_err` as a value; Charon makes one `FnOnce<(anyhow::Error,)>` impl per such function and Aeneas gives them all one Lean name (only `error.rs`'s family is kept) | opaque |
| `crate::authorization::_::onWeakUnlockMethodsExpired` | `keystore2/src/authorization.rs:395` | passes its module's `into_logged_binder` to `map_err` as a value; Charon makes one `FnOnce<(anyhow::Error,)>` impl per such function and Aeneas gives them all one Lean name (only `error.rs`'s family is kept) | opaque |
| `crate::authorization::_::on_device_locked` | `keystore2/src/authorization.rs:186` | Nested borrows are not supported yet | opaque |
| `crate::authorization::_::on_device_unlocked` | `keystore2/src/authorization.rs:163` | Nested borrows are not supported yet | opaque |
| `crate::authorization::_::on_non_lskf_unlock_methods_expired` | `keystore2/src/authorization.rs:220` | Nested borrows are not supported yet | opaque |
| `crate::authorization::_::on_user_storage_locked` | `keystore2/src/authorization.rs:203` | Nested borrows are not supported yet | opaque |
| `crate::authorization::_::on_weak_unlock_methods_expired` | `keystore2/src/authorization.rs:211` | Nested borrows are not supported yet | opaque |
| `crate::authorization::_::update` | `keystore2/src/authorization.rs:146` | Internal error: please file an issue | opaque |
| `crate::authorization::_::update_lock_state` | `keystore2/src/authorization.rs:253` | Nested borrows are not supported yet | opaque |
| `crate::authorization::into_logged_binder` | `keystore2/src/authorization.rs:91` | Could not match the contexts | opaque |
| `crate::boot_level_keys::_::get_hkdf_key` | `keystore2/src/boot_level_keys.rs:226` | Unreachable | opaque |
| `crate::boot_level_keys::get_level_zero_key` | `keystore2/src/boot_level_keys.rs:120` | Nested borrows are not supported yet | opaque |
| `crate::boot_level_keys::lookup_level_zero_km_and_strategy` | `keystore2/src/boot_level_keys.rs:55` | Could not find: trait_impl_id: 516 | opaque |
| `crate::database::KEY_ID_LOCK` | `keystore2/src/database.rs:578` | Arrow types are not supported yet | excluded |
| `crate::database::_::UPGRADERS` | `keystore2/src/database.rs:930` | Arrow types are not supported yet | excluded |
| `crate::database::_::check_and_update_key_usage_count` | `keystore2/src/database.rs:2303` | Internal error: please file an issue | opaque |
| `crate::database::_::cleanup_leftovers` | `rusqlite-0.32.1/src/lib.rs:182` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::database::_::cleanup_unreferenced` | `rusqlite-0.32.1/src/lib.rs:182` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::database::_::column_result` | `keystore2/src/database.rs:309` | Internal error: please file an issue | opaque |
| `crate::database::_::count_keys` | `rusqlite-0.32.1/src/lib.rs:182` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::database::_::create_key_entry_internal` | `rusqlite-0.32.1/src/lib.rs:182` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::database::_::delete_received_grants` | `keystore2/src/database.rs:2485` | its `format!` arguments are `()` in the Aeneas Lean library (`core::fmt::Arguments` is `Unit`), so the DELETE query did not depend on `AID_USER_OFFSET` | patched (`04-grant-delete-sql-without-format`) |
| `crate::database::_::do_table_size_query` | `keystore2/src/database.rs:1213` | Internal error: please file an issue | opaque |
| `crate::database::_::drop` | `keystore2/src/database.rs:630` | Arrow types are not supported yet | opaque |
| `crate::database::_::fmt` | `keystore2/src/database.rs:129` | Internal error: please file an issue | opaque |
| `crate::database::_::from_0_to_1` | `rusqlite-0.32.1/src/lib.rs:182` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::database::_::from_1_to_2` | `rusqlite-0.32.1/src/lib.rs:179` | New value doesn't have the same type as its destination | opaque |
| `crate::database::_::get` | `keystore2/src/database.rs:601` | Internal error, please file an issue | opaque |
| `crate::database::_::get_app_uids_affected_by_sid` | `keystore2/src/database.rs:3060` | Internal error: please file an issue | opaque |
| `crate::database::_::grant` | `rusqlite-0.32.1/src/lib.rs:182` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::database::_::handle_next_superseded_blobs` | `keystore2/src/database.rs:1350` | Detected groups of mixed mutually recursive definitions (such as a type mutually recursive with a function, or a function mutually recursive with a trait implementation): | opaque |
| `crate::database::_::init_tables` | `keystore2/src/database.rs:1044` | Lean: the generated text does not parse ("unexpected identifier") | opaque |
| `crate::database::_::insert_keyparameter_internal` | `rusqlite-0.32.1/src/lib.rs:182` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::database::_::insert_with_retry` | `keystore2/src/database.rs:2995` | builds or reads a field of a type whose declaration Aeneas cannot translate (Aeneas stops with `Not_found` in `PureTypeCheck.get_adt_field_types`) | opaque |
| `crate::database::_::is_locked_error` | `keystore2/src/database.rs:1619` | Lean: "declaration contains universe level metavariables" (a `dyn` type whose universe Lean cannot infer) | opaque |
| `crate::database::_::key_exists` | `keystore2/src/database.rs:1471` | Lean: closure body refers to a missing `anyhow.Error` field | opaque |
| `crate::database::_::list_past_alias` | `rusqlite-0.32.1/src/lib.rs:182` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::database::_::load_access_tuple` | `rusqlite-0.32.1/src/lib.rs:182` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::database::_::load_blob_components` | `keystore2/src/database.rs:2216` | Internal error: please file an issue | opaque |
| `crate::database::_::load_from_db` | `keystore2/src/database.rs:165` | Internal error: please file an issue | opaque |
| `crate::database::_::load_key_entry_id` | `keystore2/src/database.rs:2082` | Unimplemented | opaque |
| `crate::database::_::load_key_entry_internal` | `keystore2/src/database.rs:2375` | Arrow types are not supported yet | opaque |
| `crate::database::_::load_key_parameters` | `keystore2/src/database.rs:2273` | Internal error: please file an issue | opaque |
| `crate::database::_::load_super_key` | `keystore2/src/database.rs:1545` | Internal error: please file an issue | opaque |
| `crate::database::_::make_connection` | `keystore2/src/database.rs:1183` | Early returns inside of loops are not supported yet | opaque |
| `crate::database::_::migrate_key_namespace` | `rusqlite-0.32.1/src/lib.rs:182` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::database::_::name` | `keystore2/src/database.rs:123` | Unreachable | opaque |
| `crate::database::_::new` | `keystore2/src/database.rs:949` | Unimplemented: found an occurrence of a lifetime constraint relating | opaque |
| `crate::database::_::per_uid_counts` | `keystore2/src/database.rs:1313` | Internal error: please file an issue | opaque |
| `crate::database::_::pragma` | `keystore2/src/database.rs:3126` | its `format!` arguments are `()` in the Aeneas Lean library (`core::fmt::Arguments` is `Unit`), so the query was the same for every PRAGMA name | patched (`05-pragma-sql-without-format`) |
| `crate::database::_::rebind_alias` | `rusqlite-0.32.1/src/lib.rs:182` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::database::_::remove_key_rows` | `rusqlite-0.32.1/src/lib.rs:182` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::database::_::set_blob` | `keystore2/src/database.rs:1668` | Internal error: please file an issue | opaque |
| `crate::database::_::set_blob_internal` | `rusqlite-0.32.1/src/lib.rs:182` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::database::_::source` | `keystore2/src/database.rs:400` | Internal error: please file an issue | opaque |
| `crate::database::_::store_in_db` | `rusqlite-0.32.1/src/lib.rs:182` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::database::_::store_super_key` | `keystore2/src/database.rs:1497` | Internal error: please file an issue | opaque |
| `crate::database::_::to_sql` | `keystore2/src/database.rs:299` | builds `rusqlite::types::Value`, kept opaque (an `f64` field gives universe metavariables in Lean) | opaque |
| `crate::database::_::unbind_auth_bound_keys_for_user` | `keystore2/src/database.rs:2720` | Early returns inside of loops are not supported yet | opaque |
| `crate::database::_::unbind_keys_for_namespace` | `rusqlite-0.32.1/src/lib.rs:182` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::database::_::unbind_keys_for_user` | `keystore2/src/database.rs:2648` | Internal error: please file an issue | opaque |
| `crate::database::_::ungrant` | `rusqlite-0.32.1/src/lib.rs:182` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::database::_::with_transaction` | `keystore2/src/database.rs:1591` | Can't end abstraction 4 as it is set as non-endable | opaque |
| `crate::database::perboot::PERBOOT_DB` | `keystore2/src/database/perboot.rs:76` | Arrow types are not supported yet | excluded |
| `crate::database::perboot::_::find_auth_token_entry` | `keystore2/src/database/perboot.rs:97` | There should be no bottoms in the value | opaque |
| `crate::database::utils::with_rows_extract_all` | `keystore2/src/database/utils.rs:40` | Unimplemented: found an occurrence of a lifetime constraint relating | excluded |
| `crate::database::utils::with_rows_extract_one` | `keystore2/src/database/utils.rs:25` | Unimplemented: found an occurrence of a lifetime constraint relating | excluded |
| `crate::database::versioning::create_or_get_version` | `keystore2/src/database/versioning.rs:42` | Could not match the contexts | opaque |
| `crate::database::versioning::upgrade_database` | `keystore2/src/database/versioning.rs:86` | Nested borrows are not supported yet | opaque |
| `crate::enforcements::_::add_auth_token` | `keystore2/src/enforcements.rs:220` | Nested borrows are not supported yet | opaque |
| `crate::enforcements::_::add_receiver` | `keystore2/src/enforcements.rs:189` | Lean: closure `FnOnce` instance, type mismatch | opaque |
| `crate::enforcements::_::authorize_create` | `keystore2/src/enforcements.rs:409` | its LLBC is 780 MB, over the engine's 512 MB JSON limit (Charon's `--no-code-duplication` is not allowed by the engine); it also has early returns inside loops (Aeneas issue 822) | opaque |
| `crate::enforcements::_::before_finish` | `keystore2/src/enforcements.rs:304` | Nested borrows are not supported yet | opaque |
| `crate::enforcements::_::finalize_create_authorization` | `keystore2/src/enforcements.rs:252` | Arrow types are not supported yet | opaque |
| `crate::enforcements::_::install_lock_state_task` | `keystore2/src/enforcements.rs:683` | Nested borrows are not supported yet | opaque |
| `crate::enforcements::_::is_device_locked` | `keystore2/src/enforcements.rs:705` | Nested borrows are not supported yet | opaque |
| `crate::enforcements::get_timestamp_token` | `keystore2/src/enforcements.rs:239` | Dynamic trait types are not supported yet | opaque |
| `crate::entropy::register_feeder` | `keystore2/src/entropy.rs:38` | Arrow types are not supported yet | opaque |
| `crate::error::Error` | `keystore2/src/error.rs:62` | Internal error: please file an issue | body included |
| `crate::error::_::fmt` | `keystore2/src/error.rs` | keeps stage C frozen: with these `Debug`/`Display` bodies translated, the `#print axioms` guards of the merged stage C statement files print a different axiom list | opaque |
| `crate::error::_::sys` | `keystore2/src/error.rs:90` | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `crate::error::anyhow_error_to_cstring` | `keystore2/src/error.rs:234` | its result is the `format!` rendering of the error, and the Aeneas Lean library models `format!` arguments as `()`, so the translated body ignored the error | opaque |
| `crate::error::anyhow_error_to_serialized_error` | `keystore2/src/error.rs:277` | Lean: "declaration contains universe level metavariables" (a `dyn` type whose universe Lean cannot infer) | opaque |
| `crate::error::get_log_level` | `keystore2/src/error.rs:115` | Lean: "declaration contains universe level metavariables" (a `dyn` type whose universe Lean cannot infer) | opaque |
| `crate::error::into_logged_binder` | `keystore2/src/error.rs:225` | Error when registering the name for id: keystore2::error::{impl core::ops::function::FnOnce<(anyhow::Error,), binder::Status> for keystore2::error::into_logged_binder}::call_once: | opaque |
| `crate::error::map_binder_status` | `keystore2/src/error.rs:205` | Unexpected error | opaque |
| `crate::error::map_km_error` | `keystore2/src/error.rs:181` | Unexpected error | opaque |
| `crate::error::wrapped_rkpd_error_to_ks_error` | `keystore2/src/error.rs:123` | the only user of `From<rkpd_client::Error>`, opaque while that impl clashed by name with `From<postprocessor_client::Error>` (kept, harmless) | opaque |
| `crate::gc::GcInternal` | `keystore2/src/gc.rs:87` | Aeneas cannot translate this type's declaration (a field holds a `dyn` trait object), so the type is kept opaque | opaque |
| `crate::gc::_::new_init_with` | `keystore2/src/gc.rs:48` | Dynamic trait types are not supported yet | excluded |
| `crate::gc::_::notify_gc` | `keystore2/src/gc.rs:80` | Lean: closure over `&mut Shelf`, "expected a product type" | opaque |
| `crate::gc::_::process_one_key` | `keystore2/src/gc.rs:104` | Internal error: please file an issue | opaque |
| `crate::gc::_::step` | `keystore2/src/gc.rs:152` | Nested borrows are not supported yet | opaque |
| `crate::globals::ASYNC_TASK` | `keystore2/src/globals.rs:160` | Arrow types are not supported yet | excluded |
| `crate::globals::DB` | `std: std/src/thread/local.rs:292` | Internal error: please file an issue | opaque |
| `crate::globals::DB_PATH` | `keystore2/src/globals.rs:149` | Arrow types are not supported yet | excluded |
| `crate::globals::ENFORCEMENTS` | `keystore2/src/globals.rs:162` | Arrow types are not supported yet | excluded |
| `crate::globals::GC` | `keystore2/src/globals.rs:178` | Arrow types are not supported yet | excluded |
| `crate::globals::KEY_MINT_DEVICES` | `keystore2/src/globals.rs:154` | Arrow types are not supported yet | excluded |
| `crate::globals::LEGACY_BLOB_LOADER` | `keystore2/src/globals.rs:165` | Arrow types are not supported yet | excluded |
| `crate::globals::LEGACY_IMPORTER` | `keystore2/src/globals.rs:171` | Arrow types are not supported yet | excluded |
| `crate::globals::LOGS_HANDLER` | `keystore2/src/globals.rs:174` | Arrow types are not supported yet | excluded |
| `crate::globals::SUPER_KEY` | `keystore2/src/globals.rs:152` | Arrow types are not supported yet | excluded |
| `crate::globals::await_boot_completed` | `keystore2/src/globals.rs:471` | Nested borrows are not supported yet | opaque |
| `crate::globals::connect_keymint` | `keystore2/src/globals.rs:303` | Nested borrows are not supported yet | opaque |
| `crate::globals::connect_secureclock` | `keystore2/src/globals.rs:401` | Unexpected error | opaque |
| `crate::globals::create_thread_local_db` | `keystore2/src/globals.rs:75` | Nested borrows are not supported yet | opaque |
| `crate::globals::get_keymint_dev_by_uuid` | `keystore2/src/globals.rs:360` | Arrow types are not supported yet | opaque |
| `crate::globals::get_keymint_device` | `keystore2/src/globals.rs:341` | Arrow types are not supported yet | opaque |
| `crate::globals::get_keymint_devices` | `keystore2/src/globals.rs:372` | Arrow types are not supported yet | opaque |
| `crate::globals::get_remotely_provisioned_component_name` | `keystore2/src/globals.rs:427` | its `format!` arguments are `()` in the Aeneas Lean library (`core::fmt::Arguments` is `Unit`), so both security levels got the same service name | patched (`06-rkp-instance-name-without-format`) |
| `crate::globals::get_timestamp_service` | `keystore2/src/globals.rs:415` | Could not find: trait_impl_id: 555 | opaque |
| `crate::globals::keymint_service_name` | `keystore2/src/globals.rs:200` | Internal error: please file an issue | opaque |
| `crate::key_parameter::_::_::deserialize` | `keystore2/src/key_parameter.rs:825` | Inconsistent projection: | opaque |
| `crate::key_parameter::_::from` | `keystore2/src/key_parameter.rs:1053` | Could not lookup the translated function, probably because of an error which happened before | opaque |
| `crate::key_parameter::_::new_from_sql` | `keystore2/src/key_parameter.rs:490` | Lean: pattern matching on an opaque enum is stuck | opaque |
| `crate::key_parameter::_::new_from_tag_primitive_pair` | `keystore2/src/key_parameter.rs:310` | Lean: pattern matching on an opaque enum is stuck | opaque |
| `crate::key_parameter::deserialize_primitive` | `keystore2/src/key_parameter.rs:273` | Lean: universe constraint cannot be solved; serde bounds | excluded |
| `crate::key_parameter::serialize_primitive` | `keystore2/src/key_parameter.rs:264` | its serde bounds reach `Serializer`, which is mutually recursive with `Serialize` (unsupported in Aeneas's Lean model) | excluded |
| `crate::km_compat::BacklevelKeyMintWrapper` | `keystore2/src/km_compat.rs:129` | Aeneas cannot translate this type's declaration (a field holds a `dyn` trait object), so the type is kept opaque | opaque |
| `crate::km_compat::_::addRngEntropy` | `keystore2/src/km_compat.rs:184` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::begin` | `keystore2/src/km_compat.rs:305` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::convertStorageKeyToEphemeral` | `keystore2/src/km_compat.rs:328` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::deleteAllKeys` | `keystore2/src/km_compat.rs:187` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::deleteKey` | `keystore2/src/km_compat.rs:295` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::destroyAttestationIds` | `keystore2/src/km_compat.rs:190` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::deviceLocked` | `keystore2/src/km_compat.rs:193` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::earlyBootEnded` | `keystore2/src/km_compat.rs:203` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::emulation_required` | `keystore2/src/km_compat.rs:347` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::eq` | `std: core/src/cmp.rs:2461` | Unreachable | opaque |
| `crate::km_compat::_::fmt` | `keystore2/src/km_compat.rs:74` | Could not find the shared loan for borrow 3 (dangling shared borrow) | opaque |
| `crate::km_compat::_::generateKey` | `keystore2/src/km_compat.rs:229` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::getHardwareInfo` | `keystore2/src/km_compat.rs:181` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::getKeyCharacteristics` | `keystore2/src/km_compat.rs:317` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::getRootOfTrust` | `keystore2/src/km_compat.rs:212` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::getRootOfTrustChallenge` | `keystore2/src/km_compat.rs:209` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::importKey` | `keystore2/src/km_compat.rs:242` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::importWrappedKey` | `keystore2/src/km_compat.rs:258` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::sendRootOfTrust` | `keystore2/src/km_compat.rs:215` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::setAdditionalAttestationInfo` | `keystore2/src/km_compat.rs:218` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::upgradeKey` | `keystore2/src/km_compat.rs:281` | Internal error: please file an issue | opaque |
| `crate::km_compat::_::wrap` | `keystore2/src/km_compat.rs:158` | Unexpected error | opaque |
| `crate::legacy_blob::_::decrypt_if_required` | `keystore2/src/legacy_blob.rs:644` | Function pointers are not supported yet | opaque |
| `crate::legacy_blob::_::encode_alias` | `keystore2/src/legacy_blob.rs:321` | Unreachable | opaque |
| `crate::legacy_blob::_::extract_keystore_alias` | `keystore2/src/legacy_blob.rs:1000` | Internal error: please file an issue | opaque |
| `crate::legacy_blob::_::extract_legacy_alias` | `keystore2/src/legacy_blob.rs:884` | calls `Result::ok`; that axiom captures the `ok` of the Aeneas monad inside `core.result.Result.or_else`, which stage C needs (Aeneas issue 1554) | patched (`03-legacy-blob-result-ok`) |
| `crate::legacy_blob::_::is_empty` | `keystore2/src/legacy_blob.rs:972` | Early returns inside of loops are not supported yet | opaque |
| `crate::legacy_blob::_::is_empty_user` | `keystore2/src/legacy_blob.rs:988` | its `format!` arguments are `()` in the Aeneas Lean library (`core::fmt::Arguments` is `Unit`), so the directory tested was the same for every user | patched (`11-is-empty-user-without-format`) |
| `crate::legacy_blob::_::is_keystore_alias` | `keystore2/src/legacy_blob.rs:756` | Could not find: trait_impl_id: 1275 | opaque |
| `crate::legacy_blob::_::list_keystore_entries_for_uid` | `keystore2/src/legacy_blob.rs:876` | passes a `&String` as a string pattern (`impl Pattern for &String`, which needs the excluded `Pattern`) | opaque |
| `crate::legacy_blob::_::list_keystore_entries_for_user` | `keystore2/src/legacy_blob.rs:1037` | Internal error: please file an issue | opaque |
| `crate::legacy_blob::_::list_legacy_keystore_entries_for_uid` | `keystore2/src/legacy_blob.rs:876` | passes a `&String` as a string pattern (`impl Pattern for &String`, which needs the excluded `Pattern`) | opaque |
| `crate::legacy_blob::_::list_legacy_keystore_entries_for_user` | `keystore2/src/legacy_blob.rs:895` | Internal error: please file an issue | opaque |
| `crate::legacy_blob::_::load_by_uid_alias` | `keystore2/src/legacy_blob.rs:1258` | Could not match the contexts | opaque |
| `crate::legacy_blob::_::make_blob_filename` | `keystore2/src/legacy_blob.rs:940` | its `format!` arguments are `()` in the Aeneas Lean library (`core::fmt::Arguments` is `Unit`), so the file name was the same for every prefix, alias and uid | patched (`08-blob-filename-without-format`) |
| `crate::legacy_blob::_::make_chr_filename` | `keystore2/src/legacy_blob.rs:950` | its `format!` arguments are `()` in the Aeneas Lean library (`core::fmt::Arguments` is `Unit`), so the file name was the same for every prefix, alias and uid | patched (`09-chr-filename-without-format`) |
| `crate::legacy_blob::_::make_legacy_keystore_entry_filename` | `keystore2/src/legacy_blob.rs:921` | its `format!` arguments are `()` in the Aeneas Lean library (`core::fmt::Arguments` is `Unit`), so the path was the same for every user, uid and alias | patched (`07-legacy-entry-filename-without-format`) |
| `crate::legacy_blob::_::make_user_path_name` | `keystore2/src/legacy_blob.rs:964` | its `format!` arguments are `()` in the Aeneas Lean library (`core::fmt::Arguments` is `Unit`), so the directory was the same for every user | patched (`10-user-path-name-without-format`) |
| `crate::legacy_blob::_::move_keystore_entry` | `keystore2/src/legacy_blob.rs:1178` | Breaks to outer loops are not supported yet | opaque |
| `crate::legacy_blob::_::new_from_stream` | `keystore2/src/legacy_blob.rs:366` | Dynamic trait types are not supported yet | opaque |
| `crate::legacy_blob::_::new_from_stream_decrypt_with` | `keystore2/src/legacy_blob.rs:489` | Unsupported cast to a dynamic trait | opaque |
| `crate::legacy_blob::_::read_generic_blob` | `keystore2/src/legacy_blob.rs:787` | Unsupported cast to a dynamic trait | opaque |
| `crate::legacy_blob::_::read_generic_blob_decrypt_with` | `keystore2/src/legacy_blob.rs:790` | Lean: "expected a product type" | opaque |
| `crate::legacy_blob::_::read_key_parameters` | `keystore2/src/legacy_blob.rs:547` | Early returns inside of loops are not supported yet | opaque |
| `crate::legacy_blob::_::read_km_blob_file` | `keystore2/src/legacy_blob.rs:762` | Nested borrows are not supported yet | opaque |
| `crate::legacy_blob::_::remove_keystore_entry` | `keystore2/src/legacy_blob.rs:1111` | Unreachable | opaque |
| `crate::legacy_blob::_::remove_super_key` | `keystore2/src/legacy_blob.rs:1347` | calls `Result::ok` (Aeneas issue 1554, see `extract_legacy_alias`) | patched (`03-legacy-blob-result-ok`) |
| `crate::legacy_blob::_::remove_user_dir_if_empty` | `keystore2/src/legacy_blob.rs:1230` | calls `Result::ok` (Aeneas issue 1554, see `extract_legacy_alias`) | patched (`03-legacy-blob-result-ok`) |
| `crate::legacy_blob::read_bool` | `keystore2/src/legacy_blob.rs:194` | Dynamic trait types are not supported yet | opaque |
| `crate::legacy_blob::read_ne_i32` | `keystore2/src/legacy_blob.rs:206` | Dynamic trait types are not supported yet | opaque |
| `crate::legacy_blob::read_ne_i64` | `keystore2/src/legacy_blob.rs:212` | Dynamic trait types are not supported yet | opaque |
| `crate::legacy_blob::read_ne_u32` | `keystore2/src/legacy_blob.rs:200` | Dynamic trait types are not supported yet | opaque |
| `crate::legacy_importer::LegacyImporter` | `keystore2/src/legacy_importer.rs:45` | Aeneas cannot translate this type's declaration (a field holds a `dyn` trait object), so the type is kept opaque | opaque |
| `crate::legacy_importer::_::bulk_delete` | `keystore2/src/legacy_importer.rs:747` | Early returns inside of loops are not supported yet | opaque |
| `crate::legacy_importer::_::bulk_delete_uid` | `keystore2/src/legacy_importer.rs:382` | Lean: closure `FnOnce` instance over `&mut` state, type mismatch | opaque |
| `crate::legacy_importer::_::bulk_delete_user` | `keystore2/src/legacy_importer.rs:401` | Lean: closure `FnOnce` instance over `&mut` state, type mismatch | opaque |
| `crate::legacy_importer::_::characteristics_file_to_cache` | `keystore2/src/legacy_importer.rs:502` | Function pointers are not supported yet | opaque |
| `crate::legacy_importer::_::check_and_import` | `keystore2/src/legacy_importer.rs:671` | Can't end abstraction 8 as it is set as non-endable | opaque |
| `crate::legacy_importer::_::check_and_import_super_key` | `keystore2/src/legacy_importer.rs:714` | Lean: closure `FnOnce` instance over `&mut` state, type mismatch | opaque |
| `crate::legacy_importer::_::check_state` | `keystore2/src/legacy_importer.rs:143` | Internal error: please file an issue | opaque |
| `crate::legacy_importer::_::deref` | `keystore2/src/legacy_importer.rs:885` | Unreachable | opaque |
| `crate::legacy_importer::_::do_serialized` | `keystore2/src/legacy_importer.rs:268` | Found bottom while reading a place | opaque |
| `crate::legacy_importer::_::get_km_uuid` | `keystore2/src/legacy_importer.rs:423` | Lean: closure refers to a missing `Error` field | opaque |
| `crate::legacy_importer::_::get_super_key_id_check_unlockable_or_delete` | `keystore2/src/legacy_importer.rs:443` | Internal error: please file an issue | opaque |
| `crate::legacy_importer::_::has_super_key` | `keystore2/src/legacy_importer.rs:416` | Lean: closure `FnOnce` instance over `&mut` state, type mismatch | opaque |
| `crate::legacy_importer::_::list_uid` | `keystore2/src/legacy_importer.rs:205` | Lean: closure `FnOnce` instance over `&mut` state, type mismatch | opaque |
| `crate::legacy_importer::_::new` | `keystore2/src/legacy_importer.rs:70` | Internal error: please file an issue | opaque |
| `crate::legacy_importer::_::set_init` | `keystore2/src/legacy_importer.rs:115` | Internal error: please file an issue | opaque |
| `crate::legacy_importer::_::with_try_import` | `keystore2/src/legacy_importer.rs:293` | Internal error: please file an issue | opaque |
| `crate::legacy_importer::_::with_try_import_super_key` | `keystore2/src/legacy_importer.rs:350` | Lean: closure over `&mut LegacyImporterState`: its `FnOnce` instance returns the state too (type mismatch) | opaque |
| `crate::legacy_importer::get_key_characteristics_without_app_data` | `keystore2/src/legacy_importer.rs:925` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::maintenance::Maintenance` | `keystore2/src/maintenance.rs:96` | Aeneas cannot translate this type's declaration (a field holds a `dyn` trait object), so the type is kept opaque | opaque |
| `crate::maintenance::_::add_or_remove_user` | `keystore2/src/maintenance.rs:120` | Function pointers are not supported yet | opaque |
| `crate::maintenance::_::call_on_all_security_levels` | `keystore2/src/maintenance.rs:217` | Dynamic trait types are not supported yet | excluded |
| `crate::maintenance::_::call_with_watchdog` | `log-0.4.29/src/macros.rs:137` | Dynamic trait types are not supported yet | excluded |
| `crate::maintenance::_::check_send_module_info` | `keystore2/src/maintenance.rs:265` | Nested borrows are not supported yet | opaque |
| `crate::maintenance::_::clearNamespace` | `keystore2/src/maintenance.rs:613` | Nested borrows are not supported yet | opaque |
| `crate::maintenance::_::clear_namespace` | `keystore2/src/maintenance.rs:169` | Function pointers are not supported yet | opaque |
| `crate::maintenance::_::decode_value` | `keystore2/src/maintenance.rs:68` | Internal error: please file an issue | opaque |
| `crate::maintenance::_::deleteAllKeys` | `keystore2/src/maintenance.rs:635` | Nested borrows are not supported yet | opaque |
| `crate::maintenance::_::delete_all_keys` | `keystore2/src/maintenance.rs:386` | Nested borrows are not supported yet | opaque |
| `crate::maintenance::_::dump_state` | `keystore2/src/maintenance.rs:403` | Early returns inside of loops are not supported yet | opaque |
| `crate::maintenance::_::earlyBootEnded` | `keystore2/src/maintenance.rs:619` | Nested borrows are not supported yet | opaque |
| `crate::maintenance::_::early_boot_ended` | `keystore2/src/maintenance.rs:235` | Nested borrows are not supported yet | opaque |
| `crate::maintenance::_::encode_module_info` | `keystore2/src/maintenance.rs:551` | the only user of `der::Encode`, whose default method `to_der` `impl_def` cannot unfold | opaque |
| `crate::maintenance::_::getAppUidsAffectedBySid` | `keystore2/src/maintenance.rs:647` | Nested borrows are not supported yet | opaque |
| `crate::maintenance::_::initUserSuperKeys` | `keystore2/src/maintenance.rs:593` | Nested borrows are not supported yet | opaque |
| `crate::maintenance::_::init_user_super_keys` | `keystore2/src/maintenance.rs:125` | Arrow types are not supported yet | opaque |
| `crate::maintenance::_::migrateKeyNamespace` | `keystore2/src/maintenance.rs:629` | Nested borrows are not supported yet | opaque |
| `crate::maintenance::_::migrate_key_namespace` | `keystore2/src/maintenance.rs:358` | Dynamic trait types are not supported yet | opaque |
| `crate::maintenance::_::new_native_binder` | `keystore2/src/maintenance.rs:102` | Internal error: please file an issue | opaque |
| `crate::maintenance::_::onUserAdded` | `keystore2/src/maintenance.rs:581` | Nested borrows are not supported yet | opaque |
| `crate::maintenance::_::onUserLskfRemoved` | `keystore2/src/maintenance.rs:607` | Nested borrows are not supported yet | opaque |
| `crate::maintenance::_::onUserRemoved` | `keystore2/src/maintenance.rs:600` | Nested borrows are not supported yet | opaque |
| `crate::maintenance::_::on_user_lskf_removed` | `keystore2/src/maintenance.rs:148` | Arrow types are not supported yet | opaque |
| `crate::maintenance::_::read_and_set_module_info` | `keystore2/src/maintenance.rs:309` | Nested borrows are not supported yet | opaque |
| `crate::maintenance::_::read_apex_info` | `keystore2/src/maintenance.rs:326` | Nested borrows are not supported yet | opaque |
| `crate::maintenance::_::set_module_info` | `keystore2/src/maintenance.rs:521` | Nested borrows are not supported yet | opaque |
| `crate::maintenance::_::value_len` | `keystore2/src/maintenance.rs:68` | Internal error: please file an issue | opaque |
| `crate::maintenance::_::watch_apex_info` | `keystore2/src/maintenance.rs:277` | Nested borrows are not supported yet | opaque |
| `crate::metrics::_::new_native_binder` | `keystore2/src/metrics.rs:39` | Dynamic trait types are not supported yet | opaque |
| `crate::metrics::_::pullMetrics` | `keystore2/src/metrics.rs:53` | Internal error: please file an issue | opaque |
| `crate::metrics::_::pull_metrics` | `keystore2/src/metrics.rs:42` | Arrow types are not supported yet | opaque |
| `crate::metrics_store::METRICS_STORE` | `keystore2/src/metrics_store.rs:82` | Arrow types are not supported yet | excluded |
| `crate::metrics_store::_::fmt` | `keystore2/src/metrics_store.rs:100` | Continue to outer loops are not supported yet | opaque |
| `crate::metrics_store::_::show` | `keystore2/src/metrics_store.rs:1051` | Function pointers are not supported yet | opaque |
| `crate::metrics_store::log_key_creation_event_stats` | `keystore2/src/metrics_store.rs:211` | Arrow types are not supported yet | opaque |
| `crate::metrics_store::log_key_operation_event_stats` | `keystore2/src/metrics_store.rs:372` | Arrow types are not supported yet | opaque |
| `crate::metrics_store::log_key_operation_streaming_stats` | `keystore2/src/metrics_store.rs:747` | Arrow types are not supported yet | opaque |
| `crate::metrics_store::log_operation_latency` | `keystore2/src/metrics_store.rs:712` | Arrow types are not supported yet | opaque |
| `crate::metrics_store::log_rkp_error_stats` | `keystore2/src/metrics_store.rs:805` | Arrow types are not supported yet | opaque |
| `crate::metrics_store::parse_key_parameters` | `keystore2/src/metrics_store.rs:655` | Internal error: please file an issue | opaque |
| `crate::metrics_store::process_key_creation_event_stats` | `keystore2/src/metrics_store.rs:240` | Internal error: please file an issue | opaque |
| `crate::metrics_store::process_key_operation_event_stats` | `keystore2/src/metrics_store.rs:408` | Internal error: please file an issue | opaque |
| `crate::metrics_store::pull_keys_per_uid` | `keystore2/src/metrics_store.rs:638` | Nested borrows are not supported yet | opaque |
| `crate::metrics_store::pull_storage_stats` | `keystore2/src/metrics_store.rs:601` | Internal error: please file an issue | opaque |
| `crate::metrics_store::read_keystore_crash_count` | `keystore2/src/metrics_store.rs:850` | Lean: passes `Some`/`Into::into` as a value; Aeneas prints the shim axiom type without parentheses | opaque |
| `crate::operation::Operation` | `keystore2/src/operation.rs:180` | Aeneas cannot translate this type's declaration (a field holds a `dyn` trait object), so the type is kept opaque | opaque |
| `crate::operation::_::abort` | `keystore2/src/operation.rs:920` | Could not match the contexts | opaque |
| `crate::operation::_::check_active` | `keystore2/src/operation.rs:345` | Internal error: please file an issue | opaque |
| `crate::operation::_::create_operation` | `keystore2/src/operation.rs:550` | Internal error: please file an issue | opaque |
| `crate::operation::_::drop` | `keystore2/src/operation.rs:508` | Internal error: please file an issue | opaque |
| `crate::operation::_::finish` | `keystore2/src/operation.rs:426` | Internal error: please file an issue | opaque |
| `crate::operation::_::fmt` | `keystore2/src/operation.rs:161` | Internal error: please file an issue | opaque |
| `crate::operation::_::get_pruning_info` | `keystore2/src/operation.rs:263` | Internal error: please file an issue | opaque |
| `crate::operation::_::log_metrics` | `keystore2/src/operation.rs:487` | Internal error: please file an issue | opaque |
| `crate::operation::_::new` | `keystore2/src/operation.rs:213` | Internal error: please file an issue | opaque |
| `crate::operation::_::new_native_binder` | `keystore2/src/operation.rs:830` | Lean: builds `Arc<KeystoreOperation>` with `{...}` notation, "expected type is not known" | opaque |
| `crate::operation::_::prune` | `keystore2/src/operation.rs:697` | Could not match the contexts | opaque |
| `crate::operation::_::touch` | `keystore2/src/operation.rs:366` | Internal error: please file an issue | opaque |
| `crate::operation::_::update` | `keystore2/src/operation.rs:398` | Internal error: please file an issue | opaque |
| `crate::operation::_::updateAad` | `keystore2/src/operation.rs:879` | passes its module's `into_logged_binder` to `map_err` as a value; Charon makes one `FnOnce<(anyhow::Error,)>` impl per such function and Aeneas gives them all one Lean name (only `error.rs`'s family is kept) | opaque |
| `crate::operation::_::update_aad` | `keystore2/src/operation.rs:375` | Internal error: please file an issue | opaque |
| `crate::operation::_::update_metrics` | `keystore2/src/operation.rs:479` | Internal error: please file an issue | opaque |
| `crate::operation::_::watch` | `keystore2/src/operation.rs:258` | Internal error: please file an issue | opaque |
| `crate::operation::_::with_locked_operation` | `keystore2/src/operation.rs:840` | Internal error: please file an issue | opaque |
| `crate::permission::KEYSTORE2_KEY_LABEL_BACKEND` | `keystore2/src/permission.rs:47` | Arrow types are not supported yet | excluded |
| `crate::permission::lookup_keystore2_key_context` | `keystore2/src/permission.rs:50` | Arrow types are not supported yet | opaque |
| `crate::raw_device::KeyMintDevice` | `keystore2/src/raw_device.rs:50` | Aeneas cannot translate this type's declaration (a field holds a `dyn` trait object), so the type is kept opaque | opaque |
| `crate::raw_device::_::create_and_store_key` | `keystore2/src/raw_device.rs:106` | Dynamic trait types are not supported yet | excluded |
| `crate::raw_device::_::get` | `keystore2/src/raw_device.rs:70` | Internal error: please file an issue | opaque |
| `crate::raw_device::_::get_or_none` | `keystore2/src/raw_device.rs:84` | Lean: "declaration contains universe level metavariables" (a `dyn` type whose universe Lean cannot infer) | opaque |
| `crate::raw_device::_::lookup_or_generate_key` | `keystore2/src/raw_device.rs:175` | Internal error: please file an issue | opaque |
| `crate::raw_device::_::not_found_is_none` | `keystore2/src/raw_device.rs:161` | Lean: "declaration contains universe level metavariables" (a `dyn` type whose universe Lean cannot infer) | opaque |
| `crate::raw_device::_::security_level` | `keystore2/src/raw_device.rs:101` | Internal error: please file an issue | opaque |
| `crate::raw_device::_::upgrade_keyblob_if_required_with` | `keystore2/src/raw_device.rs:264` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::raw_device::_::use_key_in_one_step` | `keystore2/src/raw_device.rs:293` | Internal error: please file an issue | opaque |
| `crate::raw_device::_::version` | `keystore2/src/raw_device.rs:94` | Internal error: please file an issue | opaque |
| `crate::remote_provisioning::_::get_rkpd_attestation_key_and_certs` | `keystore2/src/remote_provisioning.rs:117` | Nested borrows are not supported yet | opaque |
| `crate::security_level::KeystoreSecurityLevel` | `keystore2/src/security_level.rs:85` | Aeneas cannot translate this type's declaration (a field holds a `dyn` trait object), so the type is kept opaque | opaque |
| `crate::security_level::_::add_required_parameters` | `keystore2/src/security_level.rs:514` | Could not match the contexts | opaque |
| `crate::security_level::_::check_key_counts` | `keystore2/src/security_level.rs:602` | Nested borrows are not supported yet | opaque |
| `crate::security_level::_::convertStorageKeyToEphemeral` | `keystore2/src/security_level.rs:1297` | Internal error: please file an issue | opaque |
| `crate::security_level::_::convert_storage_key_to_ephemeral` | `keystore2/src/security_level.rs:1104` | Internal error: please file an issue | opaque |
| `crate::security_level::_::createOperation` | `keystore2/src/security_level.rs:1184` | Internal error: please file an issue | opaque |
| `crate::security_level::_::create_operation` | `keystore2/src/security_level.rs:239` | Internal error: please file an issue | opaque |
| `crate::security_level::_::deleteKey` | `keystore2/src/security_level.rs:1305` | Internal error: please file an issue | opaque |
| `crate::security_level::_::delete_key` | `keystore2/src/security_level.rs:1157` | Internal error: please file an issue | opaque |
| `crate::security_level::_::generateKey` | `keystore2/src/security_level.rs:1203` | Internal error: please file an issue | opaque |
| `crate::security_level::_::generate_key` | `keystore2/src/security_level.rs:684` | Internal error: please file an issue | opaque |
| `crate::security_level::_::generate_key_and_retry_on_att_id_mismatch` | `keystore2/src/security_level.rs:623` | Internal error: please file an issue | opaque |
| `crate::security_level::_::importKey` | `keystore2/src/security_level.rs:1234` | Internal error: please file an issue | opaque |
| `crate::security_level::_::importWrappedKey` | `keystore2/src/security_level.rs:1263` | Internal error: please file an issue | opaque |
| `crate::security_level::_::import_key` | `keystore2/src/security_level.rs:817` | Internal error: please file an issue | opaque |
| `crate::security_level::_::import_wrapped_key` | `keystore2/src/security_level.rs:878` | Internal error: please file an issue | opaque |
| `crate::security_level::_::new_native_binder` | `keystore2/src/security_level.rs:103` | Internal error: please file an issue | opaque |
| `crate::security_level::_::store_new_key` | `keystore2/src/security_level.rs:167` | Can't end abstraction 10 as it is set as non-endable | opaque |
| `crate::security_level::_::store_upgraded_keyblob` | `keystore2/src/security_level.rs:1014` | Could not match the contexts | opaque |
| `crate::security_level::_::upgrade_keyblob_if_required_with` | `keystore2/src/security_level.rs:1042` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::security_level::_::upgrade_rkpd_keyblob_if_required_with` | `keystore2/src/security_level.rs:1084` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::security_level::_::watch` | `keystore2/src/security_level.rs:129` | Internal error: please file an issue | opaque |
| `crate::security_level::_::watch_millis` | `keystore2/src/security_level.rs:124` | Internal error: please file an issue | opaque |
| `crate::security_level_manager::OPERATION_PERFORMED` | `keystore2/src/security_level_manager.rs:23` | Arrow types are not supported yet | excluded |
| `crate::security_level_manager::notify_operation_performed` | `keystore2/src/security_level_manager.rs:28` | Arrow types are not supported yet | opaque |
| `crate::security_level_manager::reset` | `keystore2/src/security_level_manager.rs:39` | Arrow types are not supported yet | opaque |
| `crate::security_level_manager::was_operation_performed` | `keystore2/src/security_level_manager.rs:34` | Arrow types are not supported yet | opaque |
| `crate::service::KeystoreService` | `keystore2/src/service.rs:59` | Aeneas cannot translate this type's declaration (a field holds a `dyn` trait object), so the type is kept opaque | opaque |
| `crate::service::_::default` | `keystore2/src/service.rs:58` | Internal error: please file an issue | opaque |
| `crate::service::_::delete_key` | `keystore2/src/service.rs:353` | Dynamic trait types are not supported yet | opaque |
| `crate::service::_::getKeyEntry` | `keystore2/src/service.rs:409` | passes its module's `into_logged_binder` to `map_err` as a value; Charon makes one `FnOnce<(anyhow::Error,)>` impl per such function and Aeneas gives them all one Lean name (only `error.rs`'s family is kept) | opaque |
| `crate::service::_::getSecurityLevel` | `keystore2/src/service.rs:402` | Arrow types are not supported yet | opaque |
| `crate::service::_::get_i_sec_level_by_uuid` | `keystore2/src/service.rs:114` | Internal error: please file an issue | opaque |
| `crate::service::_::get_key_descriptor_for_lookup` | `keystore2/src/service.rs:270` | Lean: pattern variable type contains metavariables | opaque |
| `crate::service::_::get_key_entry` | `keystore2/src/service.rs:147` | Dynamic trait types are not supported yet | opaque |
| `crate::service::_::get_security_level` | `keystore2/src/service.rs:129` | Can't end abstraction 20 as it is set as non-endable | opaque |
| `crate::service::_::grant` | `keystore2/src/service.rs:365` | Internal error: please file an issue | opaque |
| `crate::service::_::new_native_binder` | `keystore2/src/service.rs:66` | its signature returns `Strong<dyn IKeystoreService>`; that trait's required methods return `dyn` types, which Lean cannot place in a universe | excluded |
| `crate::service::_::ungrant` | `keystore2/src/service.rs:387` | Lean: depends on a failing binder instance | opaque |
| `crate::service::_::update_subcomponent` | `keystore2/src/service.rs:213` | Could not match the contexts | opaque |
| `crate::service::_::uuid_to_sec_level` | `keystore2/src/service.rs:106` | Internal error: please file an issue | opaque |
| `crate::shared_secret_negotiation::connect_participants` | `keystore2/src/shared_secret_negotiation.rs:158` | Could not compute a loop fixed point in 2 iterations | opaque |
| `crate::shared_secret_negotiation::filter_map_legacy_km_instances` | `keystore2/src/shared_secret_negotiation.rs:102` | Nested borrows are not supported yet | opaque |
| `crate::shared_secret_negotiation::list_participants` | `keystore2/src/shared_secret_negotiation.rs:123` | Unreachable | opaque |
| `crate::shared_secret_negotiation::negotiate_shared_secret` | `keystore2/src/shared_secret_negotiation.rs:230` | Internal error: please file an issue | opaque |
| `crate::shared_secret_negotiation::perform_shared_secret_negotiation` | `keystore2/src/shared_secret_negotiation.rs:49` | Nested borrows are not supported yet | opaque |
| `crate::shared_secret_negotiation::transfer_root_of_trust` | `keystore2/src/shared_secret_negotiation.rs:322` | Nested borrows are not supported yet | opaque |
| `crate::super_key::SuperKey` | `keystore2/src/super_key.rs:169` | Lean: a nested `Option` that is not strictly positive in the inductive type | opaque |
| `crate::super_key::_::add_key_to_key_index` | `keystore2/src/super_key.rs:292` | Lean: pattern on an opaque enum; reads `SuperKey` fields | opaque |
| `crate::super_key::_::create_super_key` | `keystore2/src/super_key.rs:762` | Nested borrows are not supported yet | opaque |
| `crate::super_key::_::decrypt` | `keystore2/src/super_key.rs:182` | reads `SuperKey` fields (opaque type) | opaque |
| `crate::super_key::_::deref` | `keystore2/src/super_key.rs:1261` | Unreachable | opaque |
| `crate::super_key::_::encrypt` | `keystore2/src/super_key.rs:190` | reads `SuperKey` fields (opaque type) | opaque |
| `crate::super_key::_::encrypt_with_aes_super_key` | `keystore2/src/super_key.rs:610` | reads `SuperKey` fields (opaque type) | opaque |
| `crate::super_key::_::encrypt_with_hybrid_super_key` | `keystore2/src/super_key.rs:636` | Arrow types are not supported yet | opaque |
| `crate::super_key::_::extract_super_key_from_key_entry` | `keystore2/src/super_key.rs:534` | Lean: implicit arguments cannot be synthesized; builds `SuperKey` | opaque |
| `crate::super_key::_::force_reencrypt` | `keystore2/src/super_key.rs:1244` | Lean: pattern on an opaque enum | opaque |
| `crate::super_key::_::forget_all_keys_for_user` | `keystore2/src/super_key.rs:375` | Lean: field access on a failing structure | opaque |
| `crate::super_key::_::get_credential_encrypted_key_by_user_id` | `keystore2/src/super_key.rs:422` | Unsupported cast to a dynamic trait | opaque |
| `crate::super_key::_::get_user_state` | `keystore2/src/super_key.rs:1083` | Lean: field access through `Arc<UserState>` fails | opaque |
| `crate::super_key::_::handle_super_encryption_on_key_init` | `keystore2/src/super_key.rs:713` | Can't end abstraction 4 as it is set as non-endable | opaque |
| `crate::super_key::_::initialize_user` | `keystore2/src/super_key.rs:1139` | Nested borrows are not supported yet | opaque |
| `crate::super_key::_::install_credential_encrypted_key_for_user` | `keystore2/src/super_key.rs:379` | Lean: "expected a product type" | opaque |
| `crate::super_key::_::lock_unlocked_device_required_keys` | `keystore2/src/super_key.rs:921` | Joining region abstractions containing shared loans whose shared value contains borrows is not supported yet | opaque |
| `crate::super_key::_::lookup_key` | `keystore2/src/super_key.rs:391` | Lean: placeholder cannot be synthesized; builds `SuperKey` | opaque |
| `crate::super_key::_::new` | `keystore2/src/super_key.rs:209` | builds `SuperKey` (opaque type); the pattern also covers the other `new` methods of `super_key.rs` | opaque |
| `crate::super_key::_::reencrypt_if_required` | `keystore2/src/super_key.rs:739` | Lean: pattern on an opaque enum | opaque |
| `crate::super_key::_::remove_user` | `keystore2/src/super_key.rs:1114` | Nested borrows are not supported yet | opaque |
| `crate::super_key::_::set_up_boot_level_cache` | `keystore2/src/super_key.rs:318` | Nested borrows are not supported yet | opaque |
| `crate::super_key::_::super_key_exists_in_db_for_user` | `keystore2/src/super_key.rs:496` | Internal error: please file an issue | opaque |
| `crate::super_key::_::try_unlock_user_with_biometric` | `keystore2/src/super_key.rs:1001` | Early returns inside of loops are not supported yet | opaque |
| `crate::super_key::_::unlock_unlocked_device_required_keys` | `keystore2/src/super_key.rs:821` | Internal error: please file an issue | opaque |
| `crate::super_key::_::unlock_user` | `keystore2/src/super_key.rs:1175` | Nested borrows are not supported yet | opaque |
| `crate::super_key::_::unwrap_key_if_required` | `keystore2/src/super_key.rs:434` | reads `SuperKey` fields (opaque type) | opaque |
| `crate::super_key::_::unwrap_key_with_key` | `keystore2/src/super_key.rs:457` | reads `SuperKey` fields (opaque type) | opaque |
| `crate::super_key::_::watch_boot_level` | `keystore2/src/super_key.rs:329` | Early returns inside of loops are not supported yet | opaque |
| `crate::super_key::_::wipe_unlocked_device_required_keys` | `keystore2/src/super_key.rs:962` | Lean: field access on a failing structure | opaque |
| `crate::super_key::_::wipe_unlocked_device_required_keys_internal` | `keystore2/src/super_key.rs:971` | Lean: field access on a failing structure | opaque |
| `crate::sw_keyblob::deserialize_params` | `keystore2/src/sw_keyblob.rs:397` | Early returns inside of loops are not supported yet | opaque |
| `crate::sw_keyblob::get_tag_value` | `keystore2/src/sw_keyblob.rs:46` | Can't end abstraction 14 as it is set as non-endable | opaque |
| `crate::sw_keyblob::hidden_params` | `keystore2/src/sw_keyblob.rs:279` | Internal error: please file an issue | opaque |
| `crate::sw_keyblob::serialize_params` | `keystore2/src/sw_keyblob.rs:486` | Returns inside of nested loops are not supported yet | opaque |
| `crate::utils::AppUid` | `keystore2/src/utils.rs:79` | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `crate::utils::app_info_for_uid` | `keystore2/src/utils.rs:794` | Nested borrows are not supported yet | opaque |
| `crate::utils::check_android_permission` | `keystore2/src/utils.rs:225` | Dynamic trait types are not supported yet | opaque |
| `crate::utils::check_grant_permission` | `keystore2/src/utils.rs:135` | Arrow types are not supported yet | opaque |
| `crate::utils::check_key_permission` | `keystore2/src/utils.rs:150` | calls an item that is excluded (Aeneas stops with `Not_found` in `FunsAnalysis`) | opaque |
| `crate::utils::check_keystore_permission` | `keystore2/src/utils.rs:121` | Arrow types are not supported yet | opaque |
| `crate::utils::count_key_entries` | `keystore2/src/utils.rs:665` | Arrow types are not supported yet | opaque |
| `crate::utils::errno_clear` | `keystore2/src/utils.rs:825` | Aeneas does not yet support dereferencing raw pointers. | opaque |
| `crate::utils::errno_read` | `keystore2/src/utils.rs:831` | Aeneas does not yet support dereferencing raw pointers. | opaque |
| `crate::utils::estimate_safe_amount_to_return` | `keystore2/src/utils.rs:600` | Found a case of unsupported nested borrows | opaque |
| `crate::utils::get_current_time_in_milliseconds` | `keystore2/src/utils.rs:519` | Unsupported operation: &raw mut (*_4) | opaque |
| `crate::utils::import_keyblob_and_perform_op` | `keystore2/src/utils.rs:276` | Nested borrows are not supported yet | opaque |
| `crate::utils::is_device_id_attestation_tag` | `keystore2/src/utils.rs:169` | Lean: pattern matching is stuck | opaque |
| `crate::utils::list_key_entries` | `keystore2/src/utils.rs:633` | Arrow types are not supported yet | opaque |
| `crate::utils::log_security_safe_params` | `keystore2/src/utils.rs:676` | Internal error: please file an issue | opaque |
| `crate::utils::merge_and_filter_key_entry_lists` | `keystore2/src/utils.rs:562` | Internal error: please file an issue | opaque |
| `crate::utils::retry_get_interface` | `keystore2/src/utils.rs:732` | Nested borrows are not supported yet | opaque |
| `crate::utils::self_renice` | `keystore2/src/utils.rs:876` | Nested borrows are not supported yet | opaque |
| `crate::utils::upgrade_keyblob_and_perform_op` | `keystore2/src/utils.rs:372` | Dynamic trait types are not supported yet | opaque |
| `crate::utils::upgrade_keyblob_if_required_with` | `keystore2/src/utils.rs:418` | Unsized cast between dynamic traits: unimplemented case | opaque |
| `crate::watchdog_helper::watchdog::WD` | `keystore2/src/watchdog_helper.rs:31` | Arrow types are not supported yet (`LazyLock<Arc<Watchdog>>`, whose second type parameter defaults to `fn() -> Arc<Watchdog>`) | excluded |
| `crate::watchdog_helper::watchdog::watch` | `keystore2/src/watchdog_helper.rs:39` | reads the global watchdog `WD`, which is excluded (Aeneas: "Arrow types are not supported yet") | opaque |
| `crate::watchdog_helper::watchdog::watch_millis` | `keystore2/src/watchdog_helper.rs:34` | reads the global watchdog `WD`, which is excluded (Aeneas: "Arrow types are not supported yet") | opaque |
| `crate::watchdog_helper::watchdog::watch_millis_with` | `keystore2/src/watchdog_helper.rs:45` | reads the global watchdog `WD`, which is excluded (Aeneas: "Arrow types are not supported yet") | opaque |
| `alloc::vec::into_iter::_::try_fold` | `std: core/src/iter/traits/iterator.rs:42` | a where-clause that fixes an associated type (`trait_type_constraints`), which Aeneas rejects in trait method signatures (fatal sanity check) | excluded |
| `android_hardware_security_keymint::aidl::android::hardware::security::keymint::BeginResult::BeginResult` |  | Aeneas cannot translate this type's declaration (a field holds a `dyn` trait object), so the type is kept opaque | opaque |
| `android_hardware_security_keymint::aidl::android::hardware::security::keymint::EcCurve::_::P_224` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_hardware_security_keymint::aidl::android::hardware::security::keymint::EcCurve::_::P_256` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_hardware_security_keymint::aidl::android::hardware::security::keymint::EcCurve::_::P_384` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_hardware_security_keymint::aidl::android::hardware::security::keymint::EcCurve::_::P_521` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_hardware_security_keymint::aidl::android::hardware::security::keymint::ErrorCode::_::INVALID_KEY_BLOB` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_hardware_security_keymint::aidl::android::hardware::security::keymint::KeyFormat::_::PKCS8` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_hardware_security_keymint::aidl::android::hardware::security::keymint::KeyFormat::_::RAW` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_hardware_security_keymint::aidl::android::hardware::security::keymint::Tag::_::ALGORITHM` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_hardware_security_keymint::aidl::android::hardware::security::keymint::Tag::_::EC_CURVE` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_hardware_security_rkp::aidl::android::hardware::security::keymint::IRemotelyProvisionedComponent::IRemotelyProvisionedComponent::get_descriptor` |  | a trait default method whose body must be visible: `impl_def` cannot unfold an axiom default ("could not resolve recursive fields"); the body is a constant | body included |
| `android_hardware_security_sharedsecret::aidl::android::hardware::security::sharedsecret::ISharedSecret::ISharedSecret::get_descriptor` |  | a trait default method whose body must be visible: `impl_def` cannot unfold an axiom default ("could not resolve recursive fields"); the body is a constant | body included |
| `android_system_keystore2::aidl::android::system::keystore2::CreateOperationResponse::CreateOperationResponse` |  | Aeneas cannot translate this type's declaration (a field holds a `dyn` trait object), so the type is kept opaque | opaque |
| `android_system_keystore2::aidl::android::system::keystore2::KeyEntryResponse::KeyEntryResponse` |  | Aeneas cannot translate this type's declaration (a field holds a `dyn` trait object), so the type is kept opaque | opaque |
| `android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::CONVERT_STORAGE_KEY_TO_EPHEMERAL` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::DELETE` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::GEN_UNIQUE_ID` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::GET_INFO` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::GRANT` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::MANAGE_BLOB` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::REBIND` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::REQ_FORCED_OP` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::UPDATE` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::USE` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::USE_DEV_ID` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_system_keystore2::aidl::android::system::keystore2::ResponseCode::_::INVALID_ARGUMENT` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `android_system_keystore2::aidl::android::system::keystore2::ResponseCode::_::SYSTEM_ERROR` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `anyhow::kind::AdhocKind::anyhow_kind` |  | a trait default method whose body must be visible: `impl_def` cannot unfold an axiom default ("could not resolve recursive fields"); the body is a constant | body included |
| `anyhow::kind::TraitKind::anyhow_kind` |  | a trait default method whose body must be visible: `impl_def` cannot unfold an axiom default ("could not resolve recursive fields"); the body is a constant | body included |
| `binder::ExceptionCode` | `fvs-harness/binder/src/lib.rs` | kept from stage C: negative enum discriminants, which the Aeneas Lean library's `discriminant` syntax cannot parse (`Aeneas/Data/Discriminant.lean:147`) | opaque |
| `binder::StatusCode` | `fvs-harness/binder/src/lib.rs` | kept from stage C: negative enum discriminants, which the Aeneas Lean library's `discriminant` syntax cannot parse (`Aeneas/Data/Discriminant.lean:147`) | opaque |
| `core::array::iter::_::try_fold` | `std: core/src/iter/traits/iterator.rs:42` | a where-clause that fixes an associated type (`trait_type_constraints`), which Aeneas rejects in trait method signatures (fatal sanity check) | excluded |
| `core::hint::must_use` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `core::iter::adapters::_::_::try_fold` | `std: core/src/iter/traits/iterator.rs:42` | a where-clause that fixes an associated type (`trait_type_constraints`), which Aeneas rejects in trait method signatures (fatal sanity check) | excluded |
| `core::iter::range::_::try_fold` | `std: core/src/iter/traits/iterator.rs:42` | a where-clause that fixes an associated type (`trait_type_constraints`), which Aeneas rejects in trait method signatures (fatal sanity check) | excluded |
| `core::iter::traits::iterator::Iterator::cloned` | `std: core/src/iter/traits/iterator.rs:42` | a where-clause that fixes an associated type (`trait_type_constraints`), which Aeneas rejects in trait method signatures (fatal sanity check) | excluded |
| `core::iter::traits::iterator::Iterator::copied` | `std: core/src/iter/traits/iterator.rs:42` | a where-clause that fixes an associated type (`trait_type_constraints`), which Aeneas rejects in trait method signatures (fatal sanity check) | excluded |
| `core::iter::traits::iterator::Iterator::try_fold` | `std: core/src/iter/traits/iterator.rs:42` | a where-clause that fixes an associated type (`trait_type_constraints`), which Aeneas rejects in trait method signatures (fatal sanity check) | excluded |
| `core::option::_::ok_or_else` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `core::option::_::transpose` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `core::result::_::or_else` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `core::str::pattern` | `std: core/src/str/pattern.rs:99` | the trait `Pattern` has a generic associated type (`Searcher<'a>`), which Aeneas does not implement (`[Error] Unimplemented`, fatal); excluded with its impls | excluded |
| `keystore2_crypto::AES_256_KEY_LENGTH` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `keystore2_selinux::_::perm` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `log::STATIC_MAX_LEVEL` |  | kept from stage C: a constant or small library function that stage C's statements and proofs need with its body | body included |
| `rusqlite::error::Error` |  | Aeneas cannot translate this type's declaration (a field holds a `dyn` trait object), so the type is kept opaque | opaque |
| `rusqlite::types::from_sql::FromSqlError` |  | Aeneas cannot translate this type's declaration (a field holds a `dyn` trait object), so the type is kept opaque | opaque |
| `rusqlite::types::value::Value` |  | Lean: the `f64` field gives universe level metavariables | opaque |
| `rusqlite::types::value_ref::ValueRef` |  | Lean: the `f64` field gives universe level metavariables | opaque |
