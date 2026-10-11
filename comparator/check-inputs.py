#!/usr/bin/env python3
"""Check the pinned inputs without compiling any Lean proof."""

import argparse
import hashlib
import json
import subprocess
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt-dir", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent

    def git(*arguments):
        return subprocess.check_output(["git", "-C", str(root), *arguments])

    def require(condition, message):
        if not condition:
            raise SystemExit(message)

    pins = json.loads((root / "comparator/pins.json").read_text())
    config = json.loads((root / "lean/comparator.json").read_text())
    targets = [
        "BapatLal.qPermanentMonotonicity",
        "BapatLal.qPermanentHalfLineMonotonicity",
    ]
    require(config["theorem_names"] == targets, "Both FC targets must be checked")
    require(config["challenge_module"] == "Challenge", "Unexpected challenge module")
    require(config["solution_module"] == "Bapat", "Unexpected solution module")
    require(sorted(config["permitted_axioms"]) == sorted([
        "propext", "Quot.sound", "Classical.choice"
    ]), "Unexpected permitted axioms")

    challenge = (root / "lean/Challenge.lean").read_bytes()
    require(hashlib.sha256(challenge).hexdigest() == pins["challenge_sha256"],
            "Challenge is not the exact downloaded FC target file")
    require((root / "lean/lean-toolchain").read_text().strip() == pins["lean_toolchain"],
            "Proof toolchain changed")

    protected = ["lean/Bapat.lean", "lean/Bapat", "lean/lean-toolchain", "lean/lake-manifest.json"]
    proof_paths = git("ls-tree", "-r", "--name-only", "-z", pins["proof_commit"],
                      "--", *protected).decode().rstrip("\0").split("\0")
    require(all(proof_paths), "Pinned proof files are missing from Git history")
    hashes = {}
    for name in proof_paths:
        original = git("show", pins["proof_commit"] + ":" + name)
        require((root / name).is_file(), "Missing pinned file: " + name)
        current = (root / name).read_bytes()
        require(current == original, "Pinned proof file changed: " + name)
        hashes[name] = hashlib.sha256(current).hexdigest()
    expected_sources = {name for name in proof_paths if name.endswith(".lean")}
    actual_sources = {"lean/Bapat.lean"} | {
        p.relative_to(root).as_posix() for p in (root / "lean/Bapat").rglob("*.lean")
    }
    require(actual_sources == expected_sources, "Extra or missing proof sources")

    manifest = json.loads((root / "lean/lake-manifest.json").read_text())
    dependencies = {item["name"]: item["rev"] for item in manifest["packages"]}
    require(dependencies["formal_conjectures"] == pins["fc_dependency_commit"],
            "FC dependency changed")
    require(dependencies["mathlib"] == pins["mathlib_commit"], "Mathlib dependency changed")

    result = {
        "input_check": "passed",
        "verification_commit": git("rev-parse", "HEAD").decode().strip(),
        "pins": pins,
        "config": config,
        "unchanged_proof_file_sha256": hashes,
        "note": "This checks input provenance; Comparator must still verify the proofs.",
    }
    if args.receipt_dir:
        args.receipt_dir.mkdir(parents=True, exist_ok=True)
        (args.receipt_dir / "input-check.json").write_text(json.dumps(result, indent=2) + "\n")
        (args.receipt_dir / "Challenge.lean").write_bytes(challenge)
    print(f"Input check passed: both targets, exact FC copy, {len(hashes)} unchanged pinned files.")


if __name__ == "__main__":
    main()
