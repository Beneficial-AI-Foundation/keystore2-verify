# Methodology

This file says how the Lean translation of the `keystore2` crate in `formal/` was made, and how the
changes made to let the tools translate it were checked.

## What is translated

The target is the `keystore2` crate: the module tree of `keystore2/src/lib.rs`, 37 files, without
test modules and test files. Everything else in the repository is either a dependency or one of the
stand-ins in `fvs-harness/` that let the crate build outside Android (AIDL interfaces, `binder`,
bindgen output and a few small service models).

The translation is made in two steps:

1. Charon compiles the crate and writes its LLBC, a
   simplified form of Rust's MIR.
2. Aeneas turns the LLBC into a pure Lean model:
   `formal/Keystore2Verify/Extraction/Keystore2.lean`.

The crate is built as Soong builds it, with the `watchdog` feature on (`--no-default-features --features
watchdog`); `formal/EXTRACTION.md` records the feature set, the target and the tool versions.

Both run through the extraction engine of FVS 3.0.0-rc3, which prepares a copy of the tree, applies
the translation patches, runs the tools under a pinned toolchain and records the hashes of every
input and output. `formal/EXTRACTION.md` lists the tool versions, the arguments and how to
regenerate the file.

## The extraction loop

The crate is translated from every module. Each run lists what Charon or Aeneas rejects, or what the
generated Lean fails to elaborate, and each blocker is resolved in one of these ways:

- **A blocker in another crate** (the standard library, a dependency, a stand-in): the item is made
  opaque, excluded, or, when its body is small and needed, included with its body.
- **A blocker in `keystore2` itself:** first a search for a known fix in Aeneas's open issues and
  merged pull requests, and for a Charon or Aeneas option. If none exists, the smallest translation
  patch that is semantically equivalent (the same behaviour, only reshaped for the tools) is written.
  When no such patch exists, the item is made opaque: its signature is translated and its body is
  not.

An opaque function is an assumption about an external function in the Lean model: Lean knows its type
and nothing else. `formal/EXTRACTION-ISSUES.md` has one row per blocker, with the item, the place in
the source, the error and the resolution.

The run kept the statements and proofs that were already merged unchanged. After every change to the
translation, the whole Lean project was built with `lake build --wfail`, which also checks the axiom
lists printed after each statement.

## Translation patches

Translation patches live in `translation-patches/` and are listed in `translation-patches/series`.
They are applied to a copy of the tree when the translation is made. The upstream source files are
never edited. Every patch keeps the line count of each hunk, so the source lines the translation
cites stay the same.

Each new patch was assessed by a council run with the `tstack-council` skill: three reviewers from
three providers, each working read-only and independently, each asked whether the patched code is
equivalent to the original and asked to work FVS's equivalence checklist. The seats were:

- Claude Code with Claude Fable 5.2 (`claude-fable-5-2`, reasoning effort xhigh);
- Codex with GPT-6.2 Astra (`gpt-6.2-astra`, reasoning effort xhigh);
- Antigravity (`agy`) with Gemini Carbon (`gemini-4-carbon-high`, the highest effort Carbon offers).

**A patch is accepted when at least 2 of the 3 seats approve it.** Otherwise the item stays opaque.
Each seat's verdict and score is listed with the patch in `formal/EXTRACTION-ISSUES.md`; the full
reports are kept with the project's run records.

The first patch (`01-errno-platform-accessor`) only makes the crate compile on the build host and was
accepted by the repository owner. A second one (`02-watchdog-off-path-public`) made the module for a build
without the `watchdog` feature compile; it was removed when the translation moved to the Android build, with the
feature on.

### Patches for `format!`

The Aeneas Lean library models the arguments of `format!` as `()`, so a translated `format!` gives the same
string for every input. Patches `04` to `11` rewrite the 12 such calls whose string reaches SQL, a file path or a
Binder service name (`formal/EXTRACTION.md`, "`format!` arguments"). Besides the council, each was checked in
three ways:

- **A differential test.** A generated Rust program runs the original and the patched code of the eight functions,
  copied byte for byte from the two source trees, on the same inputs: users and uids at the edges of their types,
  empty and escaped aliases and prefixes, reserved prefixes, several PRAGMA names, every security level, and a real
  directory for `is_empty_user`. All 2,501 comparisons agree, and the strings for contrasting inputs are the ones
  the format strings describe.
- **Erasure probes.** For each parameter of the patched functions, of `make_super_key_filename` (which builds on
  `make_user_path_name`) and of `anyhow_error_to_cstring`, a Lean `example` claims by `rfl` that the function gives
  the same result when only that parameter changes (26 claims, three of them on literal inputs). Before this
  change, 12 of them were provable, although Rust tells the inputs apart; now none is.
- **The stage C check.** `lake build --wfail` builds the merged statements and proofs unchanged.

## Changes to the tools

Two local changes to FVS's extraction engine were needed. Each was reviewed by the same three-seat
council before use, and each leaves every earlier extraction byte-identical:

- the engine accepts source files of the standard library's own registry dependencies (such as
  `hashbrown`), checked against the toolchain's `library/Cargo.lock` and the cached archive;
- the engine lets an extraction pass Aeneas's `-filter-trait-methods` option, so that instances of
  traits the Aeneas Lean library models (`Iterator`, `core::error::Error`) carry only the methods
  that model declares.

`fvs-harness/models/watchdog_rs` was added: a model of the `keystore2/watchdog` crate with its public API and
no bodies, so that the crate builds with the `watchdog` feature on.

One stand-in was changed: `fvs-harness/models/postprocessor_client` defines its error type as
`PostProcessorError` and re-exports it as `Error`, because Aeneas names a trait impl after the last
segment of its type arguments and two `From<..::Error>` impls of `keystore2` would otherwise get one
Lean name.
