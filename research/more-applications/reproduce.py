#!/usr/bin/env python3
"""Replay the two imported studies in clean build directories.

The original experiment scripts remain unchanged. A shared, byte-identical
core.py is staged beside each study's scripts so their original imports work.
No downloaded data or precomputed result is supplied to an experiment.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
STUDIES = ("screening", "code-aware")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--study", choices=("all",) + STUDIES, default="all")
    parser.add_argument(
        "--refresh-evidence", action="store_true",
        help="After both studies pass, replace the tracked current evidence and validation record.",
    )
    args = parser.parse_args()
    if args.refresh_evidence and args.study != "all":
        parser.error("--refresh-evidence requires --study all for a single complete validation record")
    chosen = STUDIES if args.study == "all" else (args.study,)
    build = REPO / "_build" / "more-applications"
    build.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="replay-", dir=build))
    print(f"Replay directory: {work}", flush=True)
    env = dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1")
    records = {}
    for study in chosen:
        source = ROOT / study / "experiments"
        stage = work / study
        stage.mkdir()
        for path in sorted(source.glob("*.py")):
            shutil.copyfile(path, stage / path.name)
        shutil.copyfile(ROOT / "common" / "core.py", stage / "core.py")
        start = time.monotonic()
        print(f"\nRunning {study}", flush=True)
        process = subprocess.run([sys.executable, "run_all.py"], cwd=stage, env=env)
        if process.returncode:
            raise SystemExit(f"FAILED: {study}; inspect {stage / '_build'}")
        old_record = json.loads((stage / "validation.json").read_text())
        outputs = sorted(
            p for p in stage.iterdir()
            if p.suffix in {".json", ".csv"} and p.name != "validation.json"
        )
        expected = sorted(p.name for p in (ROOT / study / "evidence").iterdir() if p.is_file())
        actual = [p.name for p in outputs]
        if actual != expected:
            raise SystemExit(f"Evidence inventory mismatch for {study}: expected {expected}, produced {actual}")
        records[study] = {
            "status": old_record["status"],
            "seconds": round(time.monotonic() - start, 3),
            "runs": old_record.get("runs", old_record.get("checks")),
            "scope": old_record["scope"],
            "source_sha256": {
                str(p.relative_to(ROOT)): digest(p)
                for p in sorted(source.glob("*.py"))
            } | {"common/core.py": digest(ROOT / "common" / "core.py")},
            "evidence_sha256": {f"{study}/evidence/{p.name}": digest(p) for p in outputs},
        }
    record = {
        "schema_version": 1,
        "checked_utc": datetime.now(timezone.utc).isoformat(),
        "status": "passed",
        "python": platform.python_version(),
        "platform": platform.platform(),
        "packages": {name: importlib.metadata.version(name) for name in ("numpy", "scipy", "sympy", "mpmath")},
        "command": "python research/more-applications/reproduce.py" + ("" if args.study == "all" else f" --study {args.study}"),
        "reproduction_driver_sha256": digest(Path(__file__)),
        "studies": records,
        "scope": (
            "Clean replay of finite symbolic, combinatorial, matrix, quadrature and numerical SDP experiments. "
            "Analytical proofs are in the reports; numerical regressions do not replace them. "
            "No new Lean audit, exact SDP certificate, literature-priority certification, hardware validation, "
            "or unrestricted practitioner application separation is claimed."
        ),
    }
    (work / "validation.json").write_text(json.dumps(record, indent=2) + "\n")
    if args.refresh_evidence:
        # Every study has succeeded before any tracked evidence is changed.
        for study in chosen:
            for path in sorted((work / study).iterdir()):
                if path.suffix in {".json", ".csv"} and path.name != "validation.json":
                    shutil.copyfile(path, ROOT / study / "evidence" / path.name)
        (ROOT / "validation.json").write_text(json.dumps(record, indent=2) + "\n")
        print("Updated the single current validation record and evidence files.", flush=True)
    print(f"PASS: {len(records)} studies; replay record {work / 'validation.json'}", flush=True)


if __name__ == "__main__":
    main()
