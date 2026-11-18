#!/usr/bin/env python3
"""Verify the current research package, without rerunning numerical experiments.

Checks import completeness, the recorded executable/evidence hashes, numerical
SDP residual fields, Python syntax, and repository-local documentation links.
This is an integrity and finite-evidence check, not a proof verifier.
"""
from __future__ import annotations

import argparse
import ast
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
import re
from urllib.parse import unquote, urlparse

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit("FAIL: " + message)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record-integrity", action="store_true", help="Record package hashes after checking the replay hashes and evidence.")
    args = parser.parse_args()
    record_path = ROOT / "validation.json"
    record = json.loads(record_path.read_text())
    require(record["status"] == "passed", "No successful replay record")
    require(set(record["studies"]) == {"screening", "code-aware"}, "Incomplete replay record")
    require(record["reproduction_driver_sha256"] == digest(ROOT / "reproduce.py"), "Reproduction driver changed since replay")
    for study, data in record["studies"].items():
        require(data["status"] == "passed", f"Failed study: {study}")
        require(all(row["returncode"] == 0 for row in data["runs"]), f"Failed script: {study}")
        for category in ("source_sha256", "evidence_sha256"):
            for relative, expected in data[category].items():
                path = ROOT / relative
                require(path.is_file() and digest(path) == expected, f"Replay hash mismatch: {relative}")
        expected_outputs = set(data["evidence_sha256"])
        actual_outputs = {str(p.relative_to(ROOT)) for p in (ROOT / study / "evidence").iterdir() if p.is_file()}
        require(actual_outputs == expected_outputs, f"Untracked or missing evidence: {study}")

    provenance = json.loads((ROOT / "provenance.json").read_text())
    require(len(provenance["files"]) == 54, "Unexpected import inventory")
    for item in provenance["files"]:
        relative = item["destination"]
        if relative is None:
            continue
        path = ROOT / relative
        require(path.is_file(), f"Missing imported file: {relative}")
        if item["original_name"].endswith(".py"):
            require(digest(path) == item["original_sha256"], f"Imported executable changed: {relative}")

    python_files = sorted(ROOT.rglob("*.py"))
    for path in python_files:
        ast.parse(path.read_text(), filename=str(path))

    # Additional explicit numerical checks: the original runner records these
    # residual fields, but does not assert all of them. These are floating-point
    # checks on recorded output, not rational/interval feasibility certificates.
    rows = json.loads((ROOT / "code-aware/evidence/decoder_optimized_results.json").read_text())
    require(len(rows) == 8, "Expected eight optimized configurations")
    brackets = [row[key] for row in rows for key in ("serial_AB", "serial_BA", "switch_coherent")]
    for i, bracket in enumerate(brackets):
        require(all(math.isfinite(float(value)) for value in bracket.values()), f"Nonfinite SDP record {i}")
        gap = bracket["upper"] - bracket["lower"]
        require(-1e-10 <= gap <= 2.1e-6, f"SDP gap {i}: {gap}")
        require(abs(gap - bracket["gap"]) < 1e-10, f"SDP gap bookkeeping {i}")
        require(bracket["dual_min_eig"] >= -1e-10, f"SDP dual residual {i}")
        require(bracket["tp_error"] <= 1e-10, f"SDP TP residual {i}")
    for i, row in enumerate(rows):
        gap = row["switch_flagged_upper"] - row["switch_flagged_lower"]
        require(-1e-10 <= gap <= 2.1e-6, f"Flagged SDP gap {i}")

    links = 0
    docs = [REPO / "README.md", *sorted(ROOT.rglob("*.md"))]
    for path in docs:
        text = path.read_text()
        require("/mnt/data/" not in text and "/workspace/scratch/" not in text, f"Local scratch path in {path}")
        # Operator expressions such as S[A,B](rho) are not Markdown links.
        prose = re.sub(r"\$\$[\s\S]*?\$\$", "", text)
        prose = re.sub(r"(?<!\\)\$[^\n]*?(?<!\\)\$", "", prose)
        prose = re.sub(r"```[\s\S]*?```", "", prose)
        prose = re.sub(r"`[^`]*`", "", prose)
        for raw in re.findall(r"\[[^\]]*\]\(([^\s)]+)\)", prose):
            if urlparse(raw).scheme:
                continue
            url, _, anchor = raw.partition("#")
            target = path.parent / unquote(url) if url else path
            require(target.exists(), f"Broken local link in {path.relative_to(REPO)}: {raw}")
            if anchor.startswith("section-") and target.suffix == ".md":
                require(f'id="{anchor}"' in target.read_text(), f"Missing explicit section anchor: {raw}")
            links += 1

    files = sorted(p for p in ROOT.rglob("*") if p.is_file() and p != record_path and "__pycache__" not in p.parts)
    package_hashes = {str(p.relative_to(ROOT)): digest(p) for p in files}
    summary = {
        "python_files_parsed": len(python_files),
        "local_links_checked": links,
        "import_entries_checked": len(provenance["files"]),
        "SDP_brackets_with_recorded_feasibility_fields": len(brackets),
        "flagged_SDP_brackets": len(rows),
        "max_SDP_gap": max(x["gap"] for x in brackets),
        "max_SDP_TP_residual": max(x["tp_error"] for x in brackets),
        "min_SDP_dual_eigenvalue": min(x["dual_min_eig"] for x in brackets),
        "scope": "Integrity, links, syntax and floating-point residual checks; not a mathematical proof or exact SDP certificate.",
    }
    if args.record_integrity:
        record["integration_checks"] = {"checked_utc": datetime.now(timezone.utc).isoformat(), "status": "passed", **summary}
        record["package_sha256"] = package_hashes
        record_path.write_text(json.dumps(record, indent=2) + "\n")
    elif "package_sha256" in record:
        require(record["package_sha256"] == package_hashes, "Package content changed since recorded integration check")
    else:
        raise SystemExit("Missing package integrity record; run --record-integrity after reviewing the import")
    print(json.dumps({"status": "passed", **summary}, indent=2))


if __name__ == "__main__":
    main()
