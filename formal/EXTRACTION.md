# How the Lean translation was made

`formal/Keystore2Verify/Extraction/Keystore2.lean` is generated. Do not edit it: regenerate it.

It translates the whole `keystore2` crate (the module tree of `keystore2/src/lib.rs`), except the items
listed in [`EXTRACTION-ISSUES.md`](EXTRACTION-ISSUES.md). [`../METHODOLOGY.md`](../METHODOLOGY.md) says
how it was made and how the translation patches were reviewed.

## Tools

| Tool | Version |
|---|---|
| Aeneas | release `nightly-2026.11.09-5a392f4` |
| Charon | 0.1.315 (same release) |
| Rust | `nightly-2026-09-17` |
| Lean | `v4.35.0` (Mathlib `v4.35.0`) |
| FVS | 3.0.0-rc3, with two local changes to its extraction engine (below) |

**Regenerating needs the changed engine.** FVS 3.0.0-rc3's extraction engine, unchanged, refuses this
extraction in two places:

- it refuses the source files of the standard library's own registry dependencies (`hashbrown 0.17.1`, which
  Charon lists whenever the crate uses `HashMap`). The changed engine accepts such a file only when its
  package is in the toolchain's `library/Cargo.lock` and the cached archive matches that lock's checksum, and
  it compares the file byte for byte with the archive, as it does for the project's own dependencies;
- it runs Aeneas with a fixed argument list. The changed engine also accepts `-filter-trait-methods` (and
  nothing else) in the extraction spec's `aeneasArgs`.

With the unchanged engine and the same spec, the earlier extraction (the four files of the first stage) is
byte-identical.

## Input

The extraction applies the patches in `translation-patches/series` to a copy of the tree and selects the
`keystore2` crate. Cargo arguments: `--locked --lib --package keystore2 --no-default-features --features watchdog`.

## Build configuration

- **Features.** Soong builds `libkeystore2` with the `watchdog` feature (`keystore2/Android.bp`, lines 77-79), so
  the translation follows that build: `--no-default-features --features watchdog`. The other feature,
  `keystore2_blob_test_utils`, is for tests and is off. Charon runs Cargo itself (`charon cargo`) and receives the
  same Cargo arguments, so Cargo and Charon see the same feature selection.
- **The watchdog.** `watchdog_rs` is the model in [`fvs-harness/models/watchdog_rs`](../fvs-harness/models/watchdog_rs):
  the public API of `keystore2/watchdog` (`Watchdog::new`, `Watchdog::watch`, `Watchdog::watch_with` and the
  `WatchPoint` guard, which is neither `Send` nor `Sync`), with opaque types and no bodies. keystore2's global
  watchdog `watchdog_helper::watchdog::WD` (a `LazyLock<Arc<Watchdog>>`) is excluded, because Aeneas cannot
  translate its `fn() -> _` type, so the three helpers that read it (`watch`, `watch_millis`, `watch_millis_with`)
  are opaque. In Lean they return `Option watchdog_rs.WatchPoint`, and nothing more is known about them.
- **Target.** The host, `aarch64-unknown-linux-gnu`; no Cargo configuration file or environment variable selects
  another target, and the [macOS-only clock patch](../fvs-harness/host-patches/macos-clock-boottime.patch) was not
  applied. `rustc +nightly-2026-09-17 -vV` printed `rustc 1.100.0-nightly (923c95cdf 2026-09-16)`, commit
  `923c95cdf5ba65cea505aa2ea829f578e1506ed8`, LLVM 23.1.1.
- **Tools.** Aeneas `nightly-2026.11.09-5a392f4`, Charon 0.1.315, Rust `nightly-2026-09-17` and FVS 3.0.0-rc3 (table
  above).

To regenerate on another host, record the same facts and compare both output hashes with
`Extraction/.fvs-publication.json`.

## `format!` arguments

The Aeneas Lean library models `core::fmt::Arguments` as `Unit`, so `format!(..)` translates to
`alloc.fmt.format ()`, whose result cannot depend on the values being formatted. Where such a string reaches SQL, a
file path or a Binder service name, the translation would give one result for inputs that Rust tells apart.

- **Patched.** The 12 calls of this kind in translated functions are rewritten by the translation patches `04` to
  `11` (one per function: `KeystoreDB::delete_received_grants` and `KeystoreDB::pragma` in `database.rs`,
  `get_remotely_provisioned_component_name` in `globals.rs`, and `make_legacy_keystore_entry_filename`,
  `make_blob_filename`, `make_chr_filename`, `make_user_path_name` and `is_empty_user` in `legacy_blob.rs`). Each
  builds the same string with `to_owned`, `push_str` and `to_string`, which translate as calls on their inputs.
- **Inside opaque functions.** The same kind of call at `database.rs` lines 2657, 2722, 2816 and 3069 (SQL),
  `legacy_blob.rs` lines 856 and 1066 (path prefixes), `globals.rs` lines 207, 214 and 386 and
  `shared_secret_negotiation.rs` line 165 (service names), and `super_key.rs` line 904 (a key descriptor) is in a
  function that is opaque for another reason, so no erased string reaches a Lean definition from there.
- **`error::anyhow_error_to_cstring`** (`error.rs` lines 234-235) is opaque: its result is the formatted error, and
  the translated body ignored the error.
- **Diagnostics.** Every other `format!` builds text for logs, error contexts or metrics output. In the translation
  that text does not depend on its arguments.

## Charon arguments

The start points: every module of the crate, except that nine modules are started item by item (each free
item and inherent method), so that their `binder` and AIDL service impls and the serde derives are not
translated ([why](EXTRACTION-ISSUES.md#the-nine-modules-translated-item-by-item)). Then the opaque, excluded
and included items; each one has a row in [`EXTRACTION-ISSUES.md`](EXTRACTION-ISSUES.md).

```
--preset=aeneas
--include crate::utils::AppUid
--include crate::error::Error
--opaque binder::StatusCode
--opaque binder::ExceptionCode
--include android_hardware_security_keymint::aidl::android::hardware::security::keymint::EcCurve::_::P_224
--include android_hardware_security_keymint::aidl::android::hardware::security::keymint::EcCurve::_::P_256
--include android_hardware_security_keymint::aidl::android::hardware::security::keymint::EcCurve::_::P_384
--include android_hardware_security_keymint::aidl::android::hardware::security::keymint::EcCurve::_::P_521
--include android_hardware_security_keymint::aidl::android::hardware::security::keymint::ErrorCode::_::INVALID_KEY_BLOB
--include android_hardware_security_keymint::aidl::android::hardware::security::keymint::KeyFormat::_::PKCS8
--include android_hardware_security_keymint::aidl::android::hardware::security::keymint::KeyFormat::_::RAW
--include android_hardware_security_keymint::aidl::android::hardware::security::keymint::Tag::_::ALGORITHM
--include android_hardware_security_keymint::aidl::android::hardware::security::keymint::Tag::_::EC_CURVE
--include android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::CONVERT_STORAGE_KEY_TO_EPHEMERAL
--include android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::DELETE
--include android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::GEN_UNIQUE_ID
--include android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::GET_INFO
--include android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::GRANT
--include android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::MANAGE_BLOB
--include android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::REBIND
--include android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::REQ_FORCED_OP
--include android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::UPDATE
--include android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::USE
--include android_system_keystore2::aidl::android::system::keystore2::KeyPermission::_::USE_DEV_ID
--include android_system_keystore2::aidl::android::system::keystore2::ResponseCode::_::INVALID_ARGUMENT
--include keystore2_crypto::AES_256_KEY_LENGTH
--include log::STATIC_MAX_LEVEL
--include core::option::_::ok_or_else
--include core::result::_::or_else
--include core::option::_::transpose
--include keystore2_selinux::_::perm
--include crate::error::_::sys
--include android_system_keystore2::aidl::android::system::keystore2::ResponseCode::_::SYSTEM_ERROR
--include core::hint::must_use
--opaque crate::enforcements::_::authorize_create
--start-from crate::async_task
--start-from crate::boot_level_keys
--start-from crate::database
--start-from crate::ec_crypto
--start-from crate::enforcements
--start-from crate::entropy
--start-from crate::error
--start-from crate::globals
--start-from crate::id_rotation
--start-from crate::legacy_blob
--start-from crate::legacy_importer
--start-from crate::metrics_store
--start-from crate::permission
--start-from crate::raw_device
--start-from crate::remote_provisioning
--start-from crate::security_level_manager
--start-from crate::shared_secret_negotiation
--start-from crate::utils
--start-from crate::attestation_key_utils
--start-from crate::audit_log
--start-from crate::gc
--start-from crate::super_key
--start-from crate::sw_keyblob
--start-from crate::watchdog_helper
--start-from crate::apc::ApcManager
--start-from crate::apc::ApcSessionState
--start-from crate::apc::ApcState
--start-from crate::apc::Error
--start-from crate::apc::RateInfo
--start-from crate::apc::_::ONE_DAY
--start-from crate::apc::_::cancel_prompt
--start-from crate::apc::_::get_remaining_back_off
--start-from crate::apc::_::ignored
--start-from crate::apc::_::is_supported
--start-from crate::apc::_::new
--start-from crate::apc::_::new_native_binder
--start-from crate::apc::_::pending
--start-from crate::apc::_::present_prompt
--start-from crate::apc::_::result
--start-from crate::apc::_::sys
--start-from crate::apc::_::unimplemented
--start-from crate::apc::into_logged_binder
--start-from crate::authorization::AuthorizationManager
--start-from crate::authorization::DeviceLockState
--start-from crate::authorization::Error
--start-from crate::authorization::LockState
--start-from crate::authorization::LockStateNotification
--start-from crate::authorization::_::add_auth_token
--start-from crate::authorization::_::get_auth_tokens_for_credstore
--start-from crate::authorization::_::get_last_auth_time
--start-from crate::authorization::_::new_native_binder
--start-from crate::authorization::_::on_device_locked
--start-from crate::authorization::_::on_device_unlocked
--start-from crate::authorization::_::on_non_lskf_unlock_methods_expired
--start-from crate::authorization::_::on_user_storage_locked
--start-from crate::authorization::_::on_weak_unlock_methods_expired
--start-from crate::authorization::_::update
--start-from crate::authorization::_::update_lock_state
--start-from crate::authorization::into_logged_binder
--start-from crate::key_parameter::AssociatePrimitive
--start-from crate::key_parameter::KeyParameter
--start-from crate::key_parameter::KeyParameterValue
--start-from crate::key_parameter::KpDefault
--start-from crate::key_parameter::Primitive
--start-from crate::key_parameter::PrimitiveError
--start-from crate::key_parameter::_::get_tag
--start-from crate::key_parameter::_::into_authorization
--start-from crate::key_parameter::_::into_key_parameter
--start-from crate::key_parameter::_::key_parameter_value
--start-from crate::key_parameter::_::new
--start-from crate::key_parameter::_::new_from_sql
--start-from crate::key_parameter::_::new_from_tag_primitive_pair
--start-from crate::key_parameter::_::security_level
--start-from crate::km_compat::BacklevelKeyMintWrapper
--start-from crate::km_compat::EmulationDetector
--start-from crate::km_compat::KEYBLOB_HMAC_KEY
--start-from crate::km_compat::KEYBLOB_PREFIX
--start-from crate::km_compat::KEYMASTER_BLOB_HW_PREFIX
--start-from crate::km_compat::KEYMASTER_BLOB_SW_PREFIX
--start-from crate::km_compat::KeyBlob
--start-from crate::km_compat::KeyImportData
--start-from crate::km_compat::KeyMintV1
--start-from crate::km_compat::Keymaster
--start-from crate::km_compat::_::new
--start-from crate::km_compat::_::wrap
--start-from crate::km_compat::unwrap_keyblob
--start-from crate::km_compat::wrap_keyblob
--start-from crate::maintenance::DeleteListener
--start-from crate::maintenance::KEYMINT_V4
--start-from crate::maintenance::Maintenance
--start-from crate::maintenance::ModuleInfo
--start-from crate::maintenance::_::add_or_remove_user
--start-from crate::maintenance::_::check_send_module_info
--start-from crate::maintenance::_::clear_namespace
--start-from crate::maintenance::_::delete_all_keys
--start-from crate::maintenance::_::dump_state
--start-from crate::maintenance::_::early_boot_ended
--start-from crate::maintenance::_::encode_module_info
--start-from crate::maintenance::_::get_app_uids_affected_by_sid
--start-from crate::maintenance::_::init_user_super_keys
--start-from crate::maintenance::_::migrate_key_namespace
--start-from crate::maintenance::_::new_native_binder
--start-from crate::maintenance::_::on_user_lskf_removed
--start-from crate::maintenance::_::read_and_set_module_info
--start-from crate::maintenance::_::read_apex_info
--start-from crate::maintenance::_::set_module_info
--start-from crate::maintenance::_::watch_apex_info
--start-from crate::metrics::Metrics
--start-from crate::metrics::_::new_native_binder
--start-from crate::metrics::_::pull_metrics
--start-from crate::operation::KeystoreOperation
--start-from crate::operation::LoggingInfo
--start-from crate::operation::MAX_RECEIVE_DATA
--start-from crate::operation::Operation
--start-from crate::operation::OperationDb
--start-from crate::operation::OperationMetrics
--start-from crate::operation::Outcome
--start-from crate::operation::PruningInfo
--start-from crate::operation::_::check_active
--start-from crate::operation::_::check_input_length
--start-from crate::operation::_::create_operation
--start-from crate::operation::_::get
--start-from crate::operation::_::get_pruning_info
--start-from crate::operation::_::log_metrics
--start-from crate::operation::_::new
--start-from crate::operation::_::new_native_binder
--start-from crate::operation::_::prune
--start-from crate::operation::_::touch
--start-from crate::operation::_::update_aad
--start-from crate::operation::_::update_metrics
--start-from crate::operation::_::update_outcome
--start-from crate::operation::_::watch
--start-from crate::operation::_::with_locked_operation
--start-from crate::security_level::API_37_PER_UID_KEY_LIMIT
--start-from crate::security_level::DEFAULT_PER_UID_KEY_LIMIT
--start-from crate::security_level::KeystoreSecurityLevel
--start-from crate::security_level::ZERO_BLOB_32
--start-from crate::security_level::_::add_required_parameters
--start-from crate::security_level::_::check_key_counts
--start-from crate::security_level::_::convert_storage_key_to_ephemeral
--start-from crate::security_level::_::create_operation
--start-from crate::security_level::_::delete_key
--start-from crate::security_level::_::generate_key
--start-from crate::security_level::_::generate_key_and_retry_on_att_id_mismatch
--start-from crate::security_level::_::import_key
--start-from crate::security_level::_::import_wrapped_key
--start-from crate::security_level::_::new_native_binder
--start-from crate::security_level::_::store_new_key
--start-from crate::security_level::_::store_upgraded_keyblob
--start-from crate::security_level::_::upgrade_keyblob_if_required_with
--start-from crate::security_level::_::upgrade_rkpd_keyblob_if_required_with
--start-from crate::security_level::_::watch
--start-from crate::security_level::_::watch_millis
--start-from crate::service::KeystoreService
--start-from crate::service::_::count_num_entries
--start-from crate::service::_::delete_key
--start-from crate::service::_::get_i_sec_level_by_uuid
--start-from crate::service::_::get_key_descriptor_for_lookup
--start-from crate::service::_::get_key_entry
--start-from crate::service::_::get_security_level
--start-from crate::service::_::get_supplementary_attestation_info
--start-from crate::service::_::list_entries
--start-from crate::service::_::list_entries_batched
--start-from crate::service::_::new_native_binder
--start-from crate::service::_::update_subcomponent
--start-from crate::service::_::uuid_to_sec_level
--exclude core::str::pattern
--opaque crate::legacy_blob::_::list_legacy_keystore_entries_for_uid
--opaque crate::legacy_blob::_::list_keystore_entries_for_uid
--exclude core::iter::traits::iterator::Iterator::try_fold
--exclude core::iter::traits::iterator::Iterator::copied
--exclude core::iter::traits::iterator::Iterator::cloned
--exclude core::iter::adapters::_::_::try_fold
--exclude core::iter::range::_::try_fold
--exclude alloc::vec::into_iter::_::try_fold
--exclude core::array::iter::_::try_fold
--opaque crate::async_task::_::default
--opaque crate::async_task::_::new
--opaque crate::raw_device::_::get
--opaque crate::database::_::column_result
--opaque crate::km_compat::_::wrap
--opaque crate::legacy_importer::_::new
--opaque crate::maintenance::_::new_native_binder
--opaque crate::operation::_::new
--opaque crate::security_level::_::new_native_binder
--opaque crate::security_level::_::create_operation
--opaque crate::service::_::default
--opaque crate::service::_::get_key_entry
--opaque crate::legacy_importer::get_key_characteristics_without_app_data
--opaque crate::legacy_importer::_::with_try_import
--opaque crate::maintenance::_::migrate_key_namespace
--opaque crate::maintenance::_::dump_state
--opaque crate::security_level::_::import_wrapped_key
--opaque crate::service::_::update_subcomponent
--opaque crate::service::_::delete_key
--opaque crate::service::_::grant
--opaque crate::async_task::_::spawn_thread
--opaque android_hardware_security_keymint::aidl::android::hardware::security::keymint::BeginResult::BeginResult
--opaque android_system_keystore2::aidl::android::system::keystore2::CreateOperationResponse::CreateOperationResponse
--opaque android_system_keystore2::aidl::android::system::keystore2::KeyEntryResponse::KeyEntryResponse
--opaque crate::async_task::AsyncTaskState
--opaque crate::async_task::Shelf
--opaque crate::gc::GcInternal
--opaque crate::km_compat::BacklevelKeyMintWrapper
--opaque crate::legacy_importer::LegacyImporter
--opaque crate::maintenance::Maintenance
--opaque crate::operation::Operation
--opaque crate::raw_device::KeyMintDevice
--opaque crate::security_level::KeystoreSecurityLevel
--opaque crate::service::KeystoreService
--opaque rusqlite::error::Error
--opaque rusqlite::types::from_sql::FromSqlError
--opaque crate::async_task::_::fmt
--opaque crate::async_task::_::get_downcast_ref
--opaque crate::async_task::_::get_downcast_mut
--opaque crate::async_task::_::remove_downcast_ref
--opaque crate::async_task::_::put
--opaque crate::async_task::_::get_mut
--opaque crate::async_task::_::get_or_put_with
--opaque crate::async_task::_::add_idle
--opaque crate::async_task::_::queue_if
--opaque crate::raw_device::_::version
--opaque crate::raw_device::_::security_level
--opaque crate::raw_device::_::use_key_in_one_step
--opaque crate::database::_::insert_with_retry
--opaque crate::legacy_importer::_::set_init
--opaque crate::legacy_importer::_::check_state
--opaque crate::legacy_importer::_::do_serialized
--opaque crate::maintenance::_::add_or_remove_user
--opaque crate::maintenance::_::clear_namespace
--opaque crate::operation::_::fmt
--opaque crate::operation::_::watch
--opaque crate::operation::_::get_pruning_info
--opaque crate::operation::_::prune
--opaque crate::operation::_::check_active
--opaque crate::operation::_::touch
--opaque crate::operation::_::update_aad
--opaque crate::operation::_::update
--opaque crate::operation::_::finish
--opaque crate::operation::_::abort
--opaque crate::operation::_::update_metrics
--opaque crate::operation::_::log_metrics
--opaque crate::operation::_::drop
--opaque crate::raw_device::_::upgrade_keyblob_if_required_with
--opaque crate::security_level::_::watch_millis
--opaque crate::security_level::_::watch
--opaque crate::security_level::_::store_new_key
--opaque crate::security_level::_::add_required_parameters
--opaque crate::security_level::_::generate_key_and_retry_on_att_id_mismatch
--opaque crate::security_level::_::import_key
--opaque crate::security_level::_::upgrade_keyblob_if_required_with
--opaque crate::security_level::_::upgrade_rkpd_keyblob_if_required_with
--opaque crate::security_level::_::convert_storage_key_to_ephemeral
--opaque crate::security_level::_::delete_key
--opaque crate::security_level::_::createOperation
--opaque crate::security_level::_::generateKey
--opaque crate::security_level::_::importKey
--opaque crate::security_level::_::importWrappedKey
--opaque crate::security_level::_::convertStorageKeyToEphemeral
--opaque crate::security_level::_::deleteKey
--opaque crate::service::_::uuid_to_sec_level
--opaque crate::service::_::get_i_sec_level_by_uuid
--opaque crate::service::_::get_security_level
--opaque crate::gc::_::process_one_key
--opaque crate::gc::_::step
--opaque crate::km_compat::_::getHardwareInfo
--opaque crate::km_compat::_::addRngEntropy
--opaque crate::km_compat::_::generateKey
--opaque crate::km_compat::_::importKey
--opaque crate::km_compat::_::importWrappedKey
--opaque crate::km_compat::_::upgradeKey
--opaque crate::km_compat::_::deleteKey
--opaque crate::km_compat::_::deleteAllKeys
--opaque crate::km_compat::_::destroyAttestationIds
--opaque crate::km_compat::_::begin
--opaque crate::km_compat::_::deviceLocked
--opaque crate::km_compat::_::earlyBootEnded
--opaque crate::km_compat::_::convertStorageKeyToEphemeral
--opaque crate::km_compat::_::getKeyCharacteristics
--opaque crate::km_compat::_::getRootOfTrustChallenge
--opaque crate::km_compat::_::getRootOfTrust
--opaque crate::km_compat::_::sendRootOfTrust
--opaque crate::km_compat::_::setAdditionalAttestationInfo
--opaque crate::async_task::_::queue_hi_if_running
--opaque crate::raw_device::_::lookup_or_generate_key
--opaque crate::security_level::_::generate_key
--exclude crate::database::KEY_ID_LOCK
--exclude crate::globals::DB_PATH
--exclude crate::globals::SUPER_KEY
--exclude crate::globals::KEY_MINT_DEVICES
--exclude crate::globals::ASYNC_TASK
--exclude crate::globals::ENFORCEMENTS
--exclude crate::globals::LEGACY_BLOB_LOADER
--exclude crate::globals::LEGACY_IMPORTER
--exclude crate::globals::LOGS_HANDLER
--exclude crate::globals::GC
--exclude crate::metrics_store::METRICS_STORE
--exclude crate::permission::KEYSTORE2_KEY_LABEL_BACKEND
--exclude crate::security_level_manager::OPERATION_PERFORMED
--exclude crate::database::perboot::PERBOOT_DB
--exclude crate::database::_::UPGRADERS
--exclude crate::maintenance::_::call_with_watchdog
--exclude crate::maintenance::_::call_on_all_security_levels
--exclude crate::database::utils::with_rows_extract_one
--exclude crate::database::utils::with_rows_extract_all
--exclude crate::raw_device::_::create_and_store_key
--exclude crate::gc::_::new_init_with
--opaque crate::entropy::register_feeder
--opaque crate::metrics_store::process_key_creation_event_stats
--opaque crate::key_parameter::_::from
--opaque crate::operation::_::create_operation
--opaque crate::audit_log::log_key_integrity_violation
--opaque crate::authorization::_::update
--opaque crate::database::_::new
--opaque crate::watchdog_helper::watchdog::watch
--opaque crate::key_parameter::_::_::deserialize
--opaque crate::legacy_importer::_::bulk_delete
--opaque crate::database::_::make_connection
--opaque crate::database::_::from_1_to_2
--opaque crate::legacy_importer::_::characteristics_file_to_cache
--opaque crate::super_key::_::unlock_user
--opaque crate::super_key::_::initialize_user
--opaque crate::super_key::_::unlock_unlocked_device_required_keys
--opaque crate::super_key::_::handle_super_encryption_on_key_init
--opaque crate::legacy_importer::_::check_and_import_super_key
--opaque crate::legacy_importer::_::get_super_key_id_check_unlockable_or_delete
--opaque crate::globals::connect_keymint
--opaque crate::globals::DB
--opaque crate::utils::app_info_for_uid
--opaque crate::utils::errno_read
--opaque crate::database::_::grant
--opaque crate::database::_::store_super_key
--opaque crate::legacy_blob::_::load_by_uid_alias
--opaque crate::database::_::list_past_alias
--opaque crate::database::_::set_blob
--opaque crate::database::_::create_key_entry_internal
--opaque crate::database::_::do_table_size_query
--opaque crate::database::_::cleanup_unreferenced
--opaque crate::utils::errno_clear
--opaque crate::database::_::name
--opaque crate::database::_::cleanup_leftovers
--opaque crate::database::_::handle_next_superseded_blobs
--opaque crate::super_key::_::decrypt
--opaque crate::attestation_key_utils::get_attest_key_info
--opaque crate::globals::connect_secureclock
--opaque crate::globals::keymint_service_name
--opaque crate::legacy_importer::_::check_and_import
--opaque crate::legacy_blob::_::is_keystore_alias
--opaque crate::database::_::from_0_to_1
--opaque crate::sw_keyblob::get_tag_value
--opaque crate::utils::get_current_time_in_milliseconds
--opaque crate::super_key::_::get_credential_encrypted_key_by_user_id
--opaque crate::super_key::_::create_super_key
--opaque crate::legacy_importer::_::deref
--opaque crate::super_key::_::deref
--opaque crate::km_compat::_::fmt
--opaque crate::km_compat::_::emulation_required
--opaque crate::utils::log_security_safe_params
--opaque crate::database::_::fmt
--opaque crate::shared_secret_negotiation::transfer_root_of_trust
--opaque crate::boot_level_keys::get_level_zero_key
--opaque crate::database::_::with_transaction
--opaque crate::database::_::load_key_entry_id
--opaque crate::legacy_blob::_::extract_keystore_alias
--opaque crate::error::map_binder_status
--opaque crate::utils::upgrade_keyblob_if_required_with
--opaque crate::audit_log::log_key_event
--opaque crate::km_compat::_::eq
--opaque crate::utils::import_keyblob_and_perform_op
--opaque crate::error::map_km_error
--opaque crate::metrics_store::_::show
--opaque crate::shared_secret_negotiation::connect_participants
--opaque crate::apc::_::result
--opaque crate::database::_::unbind_keys_for_user
--opaque crate::legacy_blob::_::decrypt_if_required
--opaque crate::remote_provisioning::_::get_rkpd_attestation_key_and_certs
--opaque crate::maintenance::_::deleteAllKeys
--opaque crate::maintenance::_::earlyBootEnded
--opaque crate::super_key::_::lock_unlocked_device_required_keys
--opaque crate::authorization::_::on_device_unlocked
--opaque crate::database::_::get
--opaque crate::database::_::load_access_tuple
--opaque crate::apc::into_logged_binder
--opaque crate::maintenance::_::onUserLskfRemoved
--opaque crate::authorization::_::onDeviceLocked
--opaque crate::maintenance::_::onUserRemoved
--opaque crate::maintenance::_::onUserAdded
--opaque crate::legacy_blob::_::remove_keystore_entry
--opaque crate::maintenance::_::set_module_info
--opaque crate::legacy_blob::_::new_from_stream_decrypt_with
--opaque crate::maintenance::_::migrateKeyNamespace
--opaque crate::maintenance::_::clearNamespace
--opaque crate::utils::self_renice
--opaque crate::metrics_store::pull_keys_per_uid
--opaque crate::database::_::count_keys
--opaque crate::maintenance::_::initUserSuperKeys
--opaque crate::maintenance::_::watch_apex_info
--opaque crate::database::_::unbind_keys_for_namespace
--opaque crate::database::_::get_app_uids_affected_by_sid
--opaque crate::globals::create_thread_local_db
--opaque crate::shared_secret_negotiation::filter_map_legacy_km_instances
--opaque crate::utils::retry_get_interface
--opaque crate::database::_::load_blob_components
--opaque crate::database::_::set_blob_internal
--opaque crate::super_key::_::set_up_boot_level_cache
--opaque crate::enforcements::_::is_device_locked
--opaque crate::enforcements::_::add_auth_token
--opaque crate::database::_::per_uid_counts
--opaque crate::database::_::rebind_alias
--opaque crate::operation::_::with_locked_operation
--opaque crate::database::_::remove_key_rows
--opaque crate::security_level::_::check_key_counts
--opaque crate::maintenance::_::early_boot_ended
--opaque crate::database::versioning::upgrade_database
--opaque crate::database::_::check_and_update_key_usage_count
--opaque crate::globals::await_boot_completed
--opaque crate::database::_::ungrant
--opaque crate::enforcements::_::before_finish
--opaque crate::security_level::_::store_upgraded_keyblob
--opaque crate::database::_::migrate_key_namespace
--opaque crate::database::versioning::create_or_get_version
--opaque crate::metrics_store::parse_key_parameters
--opaque crate::super_key::_::remove_user
--opaque crate::maintenance::_::read_apex_info
--opaque crate::legacy_blob::_::read_generic_blob
--opaque crate::legacy_blob::_::read_km_blob_file
--opaque crate::database::_::insert_keyparameter_internal
--opaque crate::metrics_store::pull_storage_stats
--opaque crate::database::_::store_in_db
--opaque crate::boot_level_keys::_::get_hkdf_key
--opaque crate::utils::estimate_safe_amount_to_return
--opaque crate::maintenance::_::getAppUidsAffectedBySid
--opaque crate::authorization::into_logged_binder
--opaque crate::authorization::_::add_auth_token
--opaque crate::maintenance::_::read_and_set_module_info
--opaque crate::maintenance::_::check_send_module_info
--opaque crate::enforcements::_::install_lock_state_task
--opaque crate::shared_secret_negotiation::perform_shared_secret_negotiation
--opaque crate::maintenance::_::delete_all_keys
--opaque crate::authorization::_::on_device_locked
--opaque crate::metrics_store::process_key_operation_event_stats
--opaque crate::authorization::_::update_lock_state
--opaque crate::super_key::_::super_key_exists_in_db_for_user
--opaque crate::authorization::_::on_weak_unlock_methods_expired
--opaque crate::authorization::_::on_non_lskf_unlock_methods_expired
--opaque crate::authorization::_::on_user_storage_locked
--opaque crate::sw_keyblob::hidden_params
--opaque crate::database::perboot::_::find_auth_token_entry
--opaque crate::enforcements::get_timestamp_token
--opaque crate::utils::check_android_permission
--opaque crate::authorization::_::new_native_binder
--opaque crate::metrics::_::new_native_binder
--opaque crate::globals::get_keymint_device
--opaque crate::globals::get_keymint_dev_by_uuid
--opaque crate::globals::get_keymint_devices
--opaque crate::metrics_store::log_key_creation_event_stats
--opaque crate::metrics_store::log_key_operation_event_stats
--opaque crate::metrics_store::log_operation_latency
--opaque crate::metrics_store::log_key_operation_streaming_stats
--opaque crate::metrics_store::log_rkp_error_stats
--opaque crate::permission::lookup_keystore2_key_context
--opaque crate::security_level_manager::notify_operation_performed
--opaque crate::security_level_manager::was_operation_performed
--opaque crate::security_level_manager::reset
--opaque crate::shared_secret_negotiation::negotiate_shared_secret
--opaque crate::utils::merge_and_filter_key_entry_lists
--opaque crate::utils::list_key_entries
--opaque crate::utils::count_key_entries
--opaque crate::authorization::_::get_auth_tokens_for_credstore
--opaque crate::authorization::_::get_last_auth_time
--opaque crate::database::_::load_from_db
--opaque crate::database::_::drop
--opaque crate::database::_::load_key_parameters
--opaque crate::database::_::load_key_entry_internal
--opaque crate::enforcements::_::finalize_create_authorization
--opaque crate::maintenance::_::value_len
--opaque crate::maintenance::_::init_user_super_keys
--opaque crate::maintenance::_::on_user_lskf_removed
--opaque crate::metrics::_::pull_metrics
--opaque crate::database::_::load_super_key
--opaque crate::database::_::unbind_auth_bound_keys_for_user
--opaque crate::apc::_::present_prompt
--opaque crate::globals::get_timestamp_service
--opaque crate::sw_keyblob::deserialize_params
--opaque crate::sw_keyblob::serialize_params
--opaque crate::legacy_blob::_::read_key_parameters
--opaque crate::legacy_blob::_::is_empty
--opaque crate::legacy_blob::_::move_keystore_entry
--opaque crate::metrics_store::_::fmt
--opaque crate::super_key::_::watch_boot_level
--opaque crate::super_key::_::try_unlock_user_with_biometric
--opaque crate::legacy_blob::_::new_from_stream
--opaque crate::service::_::getSecurityLevel
--opaque crate::database::_::source
--opaque crate::legacy_blob::read_ne_i64
--opaque crate::legacy_blob::read_ne_i32
--opaque crate::legacy_blob::read_ne_u32
--opaque crate::legacy_blob::read_bool
--opaque crate::super_key::_::encrypt_with_hybrid_super_key
--opaque crate::shared_secret_negotiation::list_participants
--opaque crate::utils::check_keystore_permission
--opaque crate::utils::check_grant_permission
--opaque crate::utils::check_key_permission
--opaque crate::maintenance::_::decode_value
--opaque crate::utils::upgrade_keyblob_and_perform_op
--opaque crate::apc::_::cancel_prompt
--opaque crate::authorization::_::addAuthToken
--opaque crate::metrics::_::pullMetrics
--opaque crate::error::into_logged_binder
--opaque crate::boot_level_keys::lookup_level_zero_km_and_strategy
--opaque crate::legacy_blob::_::encode_alias
--opaque crate::legacy_blob::_::list_legacy_keystore_entries_for_user
--opaque crate::legacy_blob::_::list_keystore_entries_for_user
--opaque crate::authorization::_::onDeviceUnlocked
--opaque crate::operation::_::updateAad
--opaque crate::error::wrapped_rkpd_error_to_ks_error
--opaque crate::authorization::_::onUserStorageLocked
--opaque crate::service::_::getKeyEntry
--opaque crate::authorization::_::onWeakUnlockMethodsExpired
--opaque crate::authorization::_::onNonLskfUnlockMethodsExpired
--opaque crate::authorization::_::getAuthTokensForCredStore
--opaque crate::authorization::_::getLastAuthTime
--opaque crate::apc::_::cancelPrompt
--opaque crate::apc::_::isSupported
--opaque crate::apc::_::presentPrompt
--opaque crate::database::_::init_tables
--opaque crate::database::_::key_exists
--opaque crate::database::_::is_locked_error
--opaque crate::error::get_log_level
--opaque crate::error::anyhow_error_to_serialized_error
--opaque crate::raw_device::_::not_found_is_none
--opaque crate::raw_device::_::get_or_none
--opaque crate::enforcements::_::add_receiver
--opaque crate::gc::_::notify_gc
--opaque crate::key_parameter::_::new_from_sql
--opaque crate::key_parameter::_::new_from_tag_primitive_pair
--opaque crate::legacy_blob::_::read_generic_blob_decrypt_with
--opaque crate::legacy_importer::_::bulk_delete_uid
--opaque crate::legacy_importer::_::bulk_delete_user
--opaque crate::legacy_importer::_::has_super_key
--opaque crate::legacy_importer::_::list_uid
--opaque crate::legacy_importer::_::get_km_uuid
--opaque crate::operation::_::new_native_binder
--opaque crate::service::_::ungrant
--opaque crate::service::_::get_key_descriptor_for_lookup
--opaque crate::super_key::_::extract_super_key_from_key_entry
--opaque crate::super_key::_::forget_all_keys_for_user
--opaque crate::super_key::_::install_credential_encrypted_key_for_user
--opaque crate::super_key::_::lookup_key
--opaque crate::super_key::_::reencrypt_if_required
--opaque crate::super_key::_::wipe_unlocked_device_required_keys
--opaque crate::super_key::_::wipe_unlocked_device_required_keys_internal
--opaque crate::super_key::_::add_key_to_key_index
--opaque crate::super_key::_::force_reencrypt
--opaque crate::utils::is_device_id_attestation_tag
--opaque crate::metrics_store::read_keystore_crash_count
--include anyhow::kind::AdhocKind::anyhow_kind
--include anyhow::kind::TraitKind::anyhow_kind
--include android_hardware_security_sharedsecret::aidl::android::hardware::security::sharedsecret::ISharedSecret::ISharedSecret::get_descriptor
--opaque crate::maintenance::_::encode_module_info
--opaque rusqlite::types::value::Value
--opaque rusqlite::types::value_ref::ValueRef
--opaque crate::database::_::to_sql
--opaque crate::super_key::SuperKey
--opaque crate::super_key::_::encrypt
--opaque crate::super_key::_::new
--opaque crate::super_key::_::unwrap_key_if_required
--opaque crate::super_key::_::unwrap_key_with_key
--opaque crate::super_key::_::encrypt_with_aes_super_key
--include android_hardware_security_rkp::aidl::android::hardware::security::keymint::IRemotelyProvisionedComponent::IRemotelyProvisionedComponent::get_descriptor
--opaque crate::super_key::_::get_user_state
--exclude crate::apc::_::new_native_binder
--exclude crate::service::_::new_native_binder
--opaque crate::legacy_importer::_::with_try_import_super_key
--exclude crate::key_parameter::serialize_primitive
--exclude crate::key_parameter::deserialize_primitive
--opaque crate::error::_::fmt
--opaque crate::error::anyhow_error_to_cstring
--exclude crate::watchdog_helper::watchdog::WD
--opaque crate::watchdog_helper::watchdog::watch_millis
--opaque crate::watchdog_helper::watchdog::watch_millis_with
```

Aeneas arguments: `-backend lean -emit-json -filter-trait-methods`.

## Items of other crates that are translated with their bodies

Charon keeps the body of an item of another crate opaque unless `--include` names it. The
`--include` arguments above name plain constants (the AIDL values such as `KeyFormat::RAW`,
`ErrorCode::INVALID_KEY_BLOB` and the `KeyPermission` bits, `keystore2_crypto::AES_256_KEY_LENGTH`,
`log::STATIC_MAX_LEVEL`), six small functions (`Option::ok_or_else`, `Result::or_else`,
`Option::transpose`, `core::hint::must_use`, `keystore2_selinux::Error::perm`, and
`keystore2::error::Error::sys`), and four trait default methods whose bodies are constants
(`anyhow`'s `AdhocKind::anyhow_kind` and `TraitKind::anyhow_kind`, and `get_descriptor` of the
`ISharedSecret` and `IRemotelyProvisionedComponent` stand-ins), so the translation holds their real values
and bodies and no statement has to assume them.

## Opaque and excluded items

An opaque item has a signature in the translation and no body: Lean knows its type and nothing else. An
excluded item is not in the translation at all. Every opaque, excluded and left-out item, with the error
that made it so, is listed in [`EXTRACTION-ISSUES.md`](EXTRACTION-ISSUES.md). The items of the first stage
are opaque for the same reasons as before:

| Item | Why |
|---|---|
| `boot_level_keys::lookup_level_zero_km_and_strategy` | Its body uses a trait impl that is not translated (Aeneas: "Could not find: trait_impl_id", `boot_level_keys.rs` line 55). |
| `boot_level_keys::get_level_zero_key` | Aeneas: "Nested borrows are not supported yet" (`boot_level_keys.rs` line 120). `get_level_zero_key_km_and_strategy`, opaque in the first stage, is now translated with its body. |
| `permission::lookup_keystore2_key_context`, and the excluded static `KEYSTORE2_KEY_LABEL_BACKEND` | The static has type `LazyLock<_, fn() -> _>`. Aeneas stops with "Arrow types are not supported yet" (`permission.rs` lines 47-52). |
| `boot_level_keys::BootLevelKeyCache::get_hkdf_key` | Aeneas fails on the body with "Unreachable" (`boot_level_keys.rs` lines 226-237). |
| `sw_keyblob::get_tag_value` | Aeneas fails on its closure with "Can't end abstraction 14 as it is set as non-endable" (`sw_keyblob.rs` line 46). |
| `sw_keyblob::hidden_params` | Aeneas fails on the body with "Internal error, please file an issue" (`sw_keyblob.rs` lines 281-283). |
| `sw_keyblob::deserialize_params` | Aeneas: "Early returns inside of loops are not supported yet" (`sw_keyblob.rs` lines 397-463). |
| `sw_keyblob::serialize_params` | Aeneas: "Returns inside of nested loops are not supported yet" (`sw_keyblob.rs` lines 486-561). |
| `binder::StatusCode`, `binder::ExceptionCode` | Enums with negative discriminants. Aeneas writes them into a `discriminant` attribute that the Aeneas Lean library reads as natural numbers only, so Lean rejects the file. |
| the `Debug` and `Display` impls of `keystore2::error::Error` | Kept opaque so that the axiom lists printed after the statements of the first stage stay as they were merged. |

Items of the standard library and of the other crates that have no Lean model are axioms in the
generated file as well: 932 axioms in all. A statement that depends on one of them says so.

An external call is a Lean function application. Equal arguments (including any explicit state) give
the same result; policy, randomness or resource outcomes that change between identical calls are not
represented. This is a limit of the model, not a determinism claim about a running Android system.

## What the statement milestone leaves open

* Boot advancement splits the cache returned by the opaque `get_hkdf_key`. No law relates that
  queue to the *input* cache, identifies its entries with a derivation history, or equates the
  retained entry to the returned key. The suffix statements refer to the post-lookup queue only.
* Successful export identifies its returned bytes, format and ordered parameter lists relative to
  the observed parse and tag lookups. The parameter decoder is opaque: its values and remaining
  slices are call results, not a specification of which values particular bytes encode. The
  lookup is not specified to return the first matching tag. No independent DER decoder is modeled.
* The EC length and wiring statements do not imply a round trip. A current-version round trip
  through the recipient's serialized private key needs marshal/parse and public-point agreement,
  equal derived key bytes at the sender and recipient, and inverse AES operations on those bytes.
  The present length contracts supply none of these identities.

The theorem origins are proved. Building the recalls checks that each restatement is the proved
statement, and the guard after each recall pins the axioms its proof rests on. Neither checks that
the external hypotheses hold on Android.

`Extraction/translation.json` maps each Rust item to its Lean name. `Extraction/.fvs-publication.json`
records the hashes of the published files.
