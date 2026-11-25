# How the Lean translation was made

`formal/Keystore2Verify/Extraction/Keystore2.lean` is generated. Do not edit it: regenerate it.

## Tools

| Tool | Version |
|---|---|
| Aeneas | release `nightly-2026.11.09-5a392f4` |
| Charon | 0.1.315 (same release) |
| Rust | `nightly-2026-09-17` |
| Lean | `v4.35.0` (Mathlib `v4.35.0`) |

## Input

The crate `keystore2` of this workspace, with the two patches of `translation-patches/series` applied
to a copy of the tree (the checkout is never edited). Cargo arguments:
`--locked --lib --package keystore2 --no-default-features`.

## Charon arguments

```
--preset=aeneas
--start-from crate::permission
--start-from crate::boot_level_keys
--start-from crate::sw_keyblob
--start-from crate::ec_crypto
--opaque crate::database
--opaque crate::globals
--opaque crate::utils
--opaque crate::raw_device
--opaque crate::error
--include crate::utils::AppUid
--include crate::error::Error
--opaque crate::boot_level_keys::lookup_level_zero_km_and_strategy
--opaque crate::boot_level_keys::get_level_zero_key_km_and_strategy
--opaque crate::boot_level_keys::get_level_zero_key
--opaque crate::permission::lookup_keystore2_key_context
--exclude crate::permission::KEYSTORE2_KEY_LABEL_BACKEND
--opaque crate::sw_keyblob::deserialize_params
--opaque crate::sw_keyblob::serialize_params
--opaque crate::sw_keyblob::get_tag_value
--opaque crate::boot_level_keys::_::get_hkdf_key
--opaque crate::sw_keyblob::hidden_params
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
```

Aeneas arguments: `-backend lean -emit-json`.

## Items of other crates that are translated with their bodies

Charon keeps the body of an item of another crate opaque unless `--include` names it. The
`--include` arguments above name plain constants (the AIDL values such as `KeyFormat::RAW`,
`ErrorCode::INVALID_KEY_BLOB` and the `KeyPermission` bits, `keystore2_crypto::AES_256_KEY_LENGTH`,
`log::STATIC_MAX_LEVEL`) and six small functions (`Option::ok_or_else`, `Result::or_else`,
`Option::transpose`, `core::hint::must_use`, `keystore2_selinux::Error::perm`, and
`keystore2::error::Error::sys`), so the translation holds their real values and bodies and no
statement has to assume them.

## Why some items are opaque

An opaque item has a signature in the translation and no body: Lean knows its type and nothing else.

| Item | Why |
|---|---|
| modules `database`, `globals`, `utils`, `raw_device`, `error` (except `utils::AppUid` and `error::Error`) | Outside the first stage of the verification. |
| `boot_level_keys::lookup_level_zero_km_and_strategy`, `get_level_zero_key_km_and_strategy`, `get_level_zero_key` | They talk to KeyMint and read system properties; outside the first stage. |
| `permission::lookup_keystore2_key_context`, and the excluded static `KEYSTORE2_KEY_LABEL_BACKEND` | The static has type `LazyLock<_, fn() -> _>`. Aeneas stops with "Arrow types are not supported yet" (`permission.rs` lines 47-52). |
| `boot_level_keys::BootLevelKeyCache::get_hkdf_key` | Aeneas fails on the body with "Unreachable" (`boot_level_keys.rs` lines 226-237). |
| `sw_keyblob::get_tag_value` | Aeneas fails on its closure with "Can't end abstraction 14 as it is set as non-endable" (`sw_keyblob.rs` line 46). |
| `sw_keyblob::hidden_params` | Aeneas fails on the body with "Internal error, please file an issue" (`sw_keyblob.rs` lines 281-283). |
| `sw_keyblob::deserialize_params` | Aeneas: "Early returns inside of loops are not supported yet" (`sw_keyblob.rs` lines 397-463). |
| `sw_keyblob::serialize_params` | Aeneas: "Returns inside of nested loops are not supported yet" (`sw_keyblob.rs` lines 486-561). |
| `binder::StatusCode`, `binder::ExceptionCode` | Enums with negative discriminants. Aeneas writes them into a `discriminant` attribute that the Aeneas Lean library reads as natural numbers only, so Lean rejects the file. |

Items of the standard library and of the other crates that have no Lean model are axioms in the
generated file as well: 91 axioms in all. A statement that depends on one of them says so.

An external call is a Lean function application. Equal arguments (including any explicit state) give
the same result; policy, randomness or resource outcomes that change between identical calls are not
represented. This is a limit of the model, not a determinism claim about a running Android system.

`Extraction/translation.json` maps each Rust item to its Lean name. `Extraction/.fvs-publication.json`
records the hashes of the published files.
