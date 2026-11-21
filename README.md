# keystore2-verify

Formal verification of the functional correctness (FC) of the core source of Keystore2, the Android key store daemon written in Rust.

## What this fork is

A fork of AOSP platform/system/security, taken from the mirror aosp-mirror-neo/platform_system_security at tag android-17.0.0_r1 (commit cbb2ef1617a94d6cdf2dc2ccb7a545575dbb20cb), the revision GrapheneOS builds for Android 17. Keystore2 is in keystore2/. The upstream license (Apache-2.0) applies to the upstream files.

## Why it exists

Android builds Keystore2 with Soong, so the source has no Cargo manifests and the verification tools cannot read it. This fork adds what they need, and nothing else:
- a Cargo workspace and a lock file, so the Rust code builds with Cargo on a host;
- fvs-harness/: stand-in crates for the Android-only parts (binder, the generated AIDL interfaces, SELinux and crypto bindings), generated from the AIDL sources at the same tag;
- the specifications and proofs, once they exist.
Upstream source files are not edited. Any change the extraction needs is kept as a separate, reviewable patch.

## What we verify

The core source in keystore2/src (37 files, about 20,000 lines). We go in stages, starting with the access-control logic (permission.rs) and the pure parts next to it. The daemon entry point, tests, fuzzers and the C and C++ helper crates are out of scope. So are the Android pieces behind the stand-ins: their behaviour is stated as explicit assumptions, not proved.

## How

Rust is translated to Lean 4 with Charon and Aeneas. Specifications are written for the public functions and proved in Lean. The work is run with the Formal Verification Skills (FVS) plugin for coding agents, from Beneficial AI Foundation, and every proof is checked by Lean.

## Status

Work in progress. Nothing here claims that Keystore2 is verified as a whole. See the branches and pull requests for what has been proved so far.

This is not an official Android or GrapheneOS project.
