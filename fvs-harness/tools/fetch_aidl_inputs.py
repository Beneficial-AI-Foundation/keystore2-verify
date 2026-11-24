#!/usr/bin/env python3
"""Fetch the .aidl inputs of the Rust stand-in crates from AOSP at the pinned tag.

Python standard library only. Reads from https://android.googlesource.com (public, no credentials).
Writes, under fvs-harness/aidl-src/:
  <module>/<package path>/<Name>.aidl   one tree per Soong aidl_interface module
  SOURCES.tsv                           module, repo, tag, commit, path in repo, sha256 of the file

Usage:  python3 fvs-harness/tools/fetch_aidl_inputs.py [--out fvs-harness/aidl-src]

The files that the keystore2 checkout already holds (keystore2/aidl) are not fetched: the generator
reads them in place. One input is not fetched either: packagemanager_aidl is reconstructed by hand
(see fvs-harness/README.md); it is listed in SOURCES.tsv with the repo "(reconstructed)".
"""
import argparse
import base64
import hashlib
import json
import pathlib
import sys
import time
import urllib.error
import urllib.request

BASE = "https://android.googlesource.com"
TAG = "android-17.0.0_r1"
REF = f"refs/tags/{TAG}"

# (Soong module with the version the keystore2 build uses, repo, directory that holds the package
#  tree, [package directories, or explicit .aidl files], explicit?)
# Versions come from the Soong files at the tag: keymint-V5, secureclock-V1, sharedsecret-V1, rkp-V3
# and android.system.keystore2-V6 are the frozen API snapshots (aidl_api/<module>/<n>), which is what
# Soong feeds the Rust generator for the -V<n>-rust crates.
MODULES = [
    ("android.hardware.security.keymint-V5", "platform/hardware/interfaces",
     "security/keymint/aidl/aidl_api/android.hardware.security.keymint/5",
     ["android/hardware/security/keymint"], False),
    ("android.hardware.security.secureclock-V1", "platform/hardware/interfaces",
     "security/secureclock/aidl/aidl_api/android.hardware.security.secureclock/1",
     ["android/hardware/security/secureclock"], False),
    ("android.hardware.security.sharedsecret-V1", "platform/hardware/interfaces",
     "security/sharedsecret/aidl/aidl_api/android.hardware.security.sharedsecret/1",
     ["android/hardware/security/sharedsecret"], False),
    ("android.hardware.security.rkp-V3", "platform/hardware/interfaces",
     "security/rkp/aidl/aidl_api/android.hardware.security.rkp/3",
     ["android/hardware/security/keymint"], False),
    ("android.system.keystore2-V6", "platform/system/hardware/interfaces",
     "keystore2/aidl/aidl_api/android.system.keystore2/6",
     ["android/system/keystore2"], False),
    ("android.security.rkp_aidl", "platform/frameworks/base", "core/java",
     ["android/security/rkp"], False),
    ("android.os.permissions_aidl", "platform/frameworks/base", "core/java",
     ["android/os/IPermissionController.aidl"], True),
    ("apex_aidl_interface", "platform/system/apex", "apexd/aidl",
     ["android/apex/ApexInfo.aidl", "android/apex/ApexInfoList.aidl",
      "android/apex/ApexSessionInfo.aidl", "android/apex/ApexSessionParams.aidl",
      "android/apex/CompressedApexInfo.aidl", "android/apex/CompressedApexInfoList.aidl",
      "android/apex/IApexService.aidl"], True),
]


def get(url):
    # Gitiles answers 429 when requests come too fast: pause between requests, back off on 429/5xx.
    for attempt in range(6):
        time.sleep(0.4)
        try:
            with urllib.request.urlopen(url, timeout=60) as r:
                return r.read()
        except urllib.error.HTTPError as e:
            if e.code != 429 and e.code < 500 or attempt == 5:
                raise
            time.sleep(5 * 2 ** attempt)


def commit_of(repo):
    j = json.loads(get(f"{BASE}/{repo}/+/{REF}?format=JSON").split(b"\n", 1)[1])
    return j["commit"]


def listing(repo, path):
    j = json.loads(get(f"{BASE}/{repo}/+/{REF}/{path}?format=JSON").split(b"\n", 1)[1])
    return [e["name"] for e in j["entries"] if e["type"] == "blob" and e["name"].endswith(".aidl")]


def cat(repo, path):
    return base64.b64decode(get(f"{BASE}/{repo}/+/{REF}/{path}?format=TEXT"))


def main():
    here = pathlib.Path(__file__).resolve().parent.parent
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(here / "aidl-src"))
    out = pathlib.Path(ap.parse_args().out)
    rows = []
    commits = {}
    for module, repo, root, parts, explicit in MODULES:
        commit = commits.setdefault(repo, commit_of(repo))
        files = []
        for part in parts:
            if explicit:
                files.append(part)
            else:
                files += [f"{part}/{n}" for n in listing(repo, f"{root}/{part}")]
        for rel in sorted(files):
            data = cat(repo, f"{root}/{rel}")
            dest = out / module / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(data)
            rows.append((module, repo, TAG, commit, f"{root}/{rel}", hashlib.sha256(data).hexdigest()))
            print(f"{module}: {rel}", file=sys.stderr)
    for name in ("IPackageManagerNative", "PackageInfo"):
        kept = out / "packagemanager_aidl" / "android" / "content" / "pm" / f"{name}.aidl"
        rows.append(("packagemanager_aidl", "(reconstructed)", TAG, "-",
                     f"android/content/pm/{name}.aidl",
                     hashlib.sha256(kept.read_bytes()).hexdigest() if kept.exists() else "-"))
    with open(out / "SOURCES.tsv", "w") as f:
        f.write("module\trepo\ttag\tcommit\tpath_in_repo\tsha256\n")
        for r in rows:
            f.write("\t".join(r) + "\n")
    print(f"{len(rows)} files, {len(commits)} repositories", file=sys.stderr)


if __name__ == "__main__":
    main()
