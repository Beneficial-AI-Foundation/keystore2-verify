# fvs-harness

This directory makes `keystore2` build with Cargo on a Linux or macOS host. The upstream tree is
built by Soong, has no Cargo manifests, and depends on Android code that exists only on a device
or in other repositories. Everything here is added: no upstream file is edited on this branch.

The aim is verification work (Charon, Aeneas, Lean) on a subset of `keystore2`, not a working
daemon. Every stand-in has the right signatures and no behaviour.

## Build

The stand-in crates use `#![feature(register_tool)]`, so a nightly toolchain is required. The
branch was built with `nightly-2026-09-17`.

```sh
RUSTUP_TOOLCHAIN=nightly-2026-09-17 cargo check --locked --lib -p keystore2 --no-default-features
```

That command succeeds only after the translation patches are applied to a copy of the tree (next
section). Do not apply them to the checkout. From the repository root:

```sh
cp -R . "${COPY}"            # any new, empty directory outside the checkout
cd "${COPY}"
for p in $(cat translation-patches/series); do patch -p1 < "translation-patches/${p}"; done
patch -p1 < fvs-harness/host-patches/macos-clock-boottime.patch    # macOS only
```

`Cargo.lock` is committed and every build uses `--locked`. The direct registry dependencies are
pinned with `=` to the versions of the `android-17` branch of the GrapheneOS mirror of
`external/rust/android-crates-io`. That branch is close to the tag, not guaranteed equal to it. The
transitive versions are those Cargo resolved when the lock was made.

## Patches

Upstream files stay as they are. Six lines in two files do not compile outside Android, so they
are kept as patches against a copy.

| Patch | File | Why | Where |
|---|---|---|---|
| `translation-patches/01-errno-platform-accessor.patch` | `keystore2/src/utils.rs` | `libc` defines `__errno` only for Android and the NetBSD family. The patch picks the platform's errno accessor by `cfg` and leaves the Android code as it was. | every host |
| `translation-patches/02-watchdog-off-path-public.patch` | `keystore2/src/watchdog_helper.rs` | The module used when the `watchdog` feature is off keeps `watch` and `watch_millis` private and has no `DEFAULT_TIMEOUT_MS`. Soong always builds with the feature on, so this path was never compiled. | every host |
| `fvs-harness/host-patches/macos-clock-boottime.patch` | `keystore2/src/utils.rs` | `libc` has no `CLOCK_BOOTTIME` for macOS. The patch reads `CLOCK_MONOTONIC` there. It is not in the series because a Linux host does not need it, and it changes what the function reads (classification B). | macOS only |

The host patch has the header of a translation patch. The patch engine applies only `series`, so
to use the engine on a macOS host, copy the file into `translation-patches/` of a working copy,
append its name to `series` there, and give it the equivalence-gate packet that a B patch needs.
The engine's `check` accepts the three patches together.

Each patch keeps the line count of every hunk, so line numbers in later reports still point at
the upstream lines. Without the patches the check fails with 100 errors on macOS; with the two
series patches only, the one remaining error on macOS is `CLOCK_BOOTTIME` at `utils.rs:519`, and
`--target x86_64-unknown-linux-gnu` and `--target aarch64-unknown-linux-gnu` pass.

The `watchdog` feature stays off: `keystore2/Cargo.toml` declares it empty and the `watchdog_rs`
crate is not in the workspace. Turning it on needs that crate as a dependency.

## Layout

```
Cargo.toml, Cargo.lock           workspace of 31 members; hals, mls and prng_seeder/test are excluded
keystore2/                       the core crate; Cargo.toml added next to the sources
keystore2/selinux, message_macro,
keystore2/src/crypto, km_compat  upstream helper crates reused unchanged; one Cargo.toml each
translation-patches/             the patch series (see above)
fvs-harness/
  tools/fetch_aidl_inputs.py     fetches the .aidl inputs from AOSP at the pinned tag
  tools/aidl_stub_gen.py         writes the 14 AIDL crates from the .aidl files
  aidl-src/                      the fetched .aidl files and SOURCES.tsv
  aidl/                          14 generated crates, committed, never edited by hand
  binder/                        stand-in for the Android binder crate
  util/                          rustutils, keystore2_flags, structured_log, bssl_crypto
  bindgen/                       selinux_bindgen, keystore2_crypto_bindgen
  models/                        keystore2_aaid, keystore2_apc_compat, keystore2_hal_names,
                                 rkpd_client, postprocessor_client
  host-patches/                  patches for one host only
```

The crate under verification is `keystore2`. The other 30 members are support: four reused
upstream crates, 14 AIDL stand-ins, `binder`, four util stand-ins, two bindgen stand-ins and five
models. The `watchdog_rs`, `legacykeystore`, `test_utils`, `tests/`, fuzzers and the daemon `main`
are not in the workspace.

## How the stand-ins work

- **AIDL crates.** Soong generates one Rust crate per `aidl_interface`. `aidl_stub_gen.py` writes
  the same item paths, field types, derives, enum representation and trait signatures from the
  `.aidl` files, following the AOSP generator at the tag. A parcelable is a struct with public
  fields, a union is an enum, an enum is a newtype over its backing integer, an interface is a
  trait with `BnFoo` and `BpFoo`. Method bodies panic. `python3 fvs-harness/tools/aidl_stub_gen.py
  --check` fails when a committed crate differs from the generator output; fix the generator, not
  the crate.
- **Oracles.** The hand-written util and model crates mark functions that stand for system
  behaviour (property reads, flags, digests, calls to other services) with `#[charon::opaque]`.
  Charon then emits a signature and no body, and Aeneas an axiom, instead of a function that
  always panics. `cfg(charon)` is not set by `charon cargo`, so the attribute is unconditional:
  each such crate starts with `#![feature(register_tool)]` and `#![register_tool(charon)]`.
  This was checked on a small crate that carried the attribute itself. Whether a function of a
  dependency crate is treated the same when another crate reaches it is not tested: in the first
  Charon run, functions of `keystore2_selinux`, `android_system_keystore2` and `anyhow` came out
  opaque with no attribute, and the AIDL crates carry no attribute.
- **Flags.** `keystore2_flags` has the six flags keystore2 reads. Each is opaque, not fixed to
  its production value.
- **Models.** The five model crates copy the public API of the upstream crate: `Error` enums,
  constants and signatures are exact, bodies are missing.

## Provenance

Source: AOSP, tag `android-17.0.0_r1`, read from `https://android.googlesource.com` (public, no
credentials). `SOURCES.tsv` in `aidl-src/` lists every file with repository, tag, commit, path
and sha256. Re-run `python3 fvs-harness/tools/fetch_aidl_inputs.py` to check: the result must be
identical.

| Module (Soong name, version) | Repository | Commit | Files |
|---|---|---|--:|
| `android.hardware.security.keymint-V5` | `platform/hardware/interfaces` | `0162af698935100a590b7359581ac8b1b80693e5` | 25 |
| `android.hardware.security.rkp-V3` | `platform/hardware/interfaces` | `0162af698935100a590b7359581ac8b1b80693e5` | 5 |
| `android.hardware.security.secureclock-V1` | `platform/hardware/interfaces` | `0162af698935100a590b7359581ac8b1b80693e5` | 3 |
| `android.hardware.security.sharedsecret-V1` | `platform/hardware/interfaces` | `0162af698935100a590b7359581ac8b1b80693e5` | 2 |
| `android.system.keystore2-V6` | `platform/system/hardware/interfaces` | `9c3469aa3d4aeec5b2bc8e8ae8fdb4437dab4edb` | 15 |
| `android.security.rkp_aidl` | `platform/frameworks/base` | `94b4c163b7dfe5ce3607f7bb8456f9573f7de57d` | 6 |
| `android.os.permissions_aidl` | `platform/frameworks/base` | `94b4c163b7dfe5ce3607f7bb8456f9573f7de57d` | 1 |
| `apex_aidl_interface` | `platform/system/apex` | `ce2bb9f710183c864040401d859874b5723e44d8` | 7 |
| `packagemanager_aidl` | reconstructed | none | 2 |

The versioned modules use the frozen snapshots (`aidl_api/<module>/<version>`), which is what
Soong feeds the Rust generator. The five `android.security.*` crates for apc, authorization,
compat, maintenance and metrics are generated from the `.aidl` files already in this tree
(`keystore2/aidl`).

### Written by hand, not taken from a source

- **`packagemanager_aidl`.** The `.aidl` files of `IPackageManagerNative` and `PackageInfo` were
  not located at the tag. The two files in `aidl-src/packagemanager_aidl/` carry a banner and hold
  only what keystore2 calls: three constants and three methods of `IPackageManagerNative`, and the
  `packageName` field of `PackageInfo`. Replace them when the originals are found.
- **`binder`, `rustutils`, `structured_log`, `bssl_crypto`.** Written from the call sites in
  `keystore2` and from the public binder sources. Only what keystore2 uses exists. The values of
  `AID_SYSTEM`, `AID_KEYSTORE`, `AID_USER_OFFSET` and `LOG_ID_SECURITY` follow Android's headers,
  and only the first three matter to the code.
- **`selinux_bindgen`, `keystore2_crypto_bindgen`.** Declarations of the libselinux items that
  `keystore2_selinux` uses and the 18 functions, two types and one constant of the bindgen
  allowlist of `keystore2/src/crypto/Android.bp`. Nothing is linked.

## For the verification workflow

- Every in-repo library crate is declared in the root `Cargo.toml`: a crate that is missing there
  is not seen by the workflow and a crate that is present is a target unless declared otherwise.
  Declare the 30 support crates as non-targets.
- `keystore2/src/crypto` and `keystore2/src/km_compat` sit inside `keystore2/`. Their manifests
  use `[lib] path = "lib.rs"`. File ownership follows the longest directory prefix.
- `rustfmt.toml` at the repository root is a symbolic link into the Android build tree and dangles
  here. Keep it out of the extraction inputs.
- The patch paths are relative to the repository root, so a copy used for extraction must carry
  the root `Cargo.toml` and `Cargo.lock`.
- Per-run files such as `.formalising/` are created by the workflow and are not committed here.
