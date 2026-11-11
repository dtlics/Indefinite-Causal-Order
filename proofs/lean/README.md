# Lean proofs

This is the canonical source tree for the formal results accompanying the
[paper](../../paper/main.tex). Start with [THEOREMS.txt](THEOREMS.txt) for precise
statements, hypotheses, metric conventions, and stable paper labels.
[DEPENDENCIES.txt](DEPENDENCIES.txt) records upstream versions and provenance.

The selected proof closure contains 1,611 project modules in `ICO/` and 48
unchanged Lean-QIT modules in `vendor/Lean-QIT/QIT/` (1,659 local modules total across 28 root imports). `ICO.lean` selects the
endpoints; `Audit.lean` prints their types and transitive axiom dependencies.
The independent finite-arithmetic companion is kept once, in
[certificates/](certificates/README.md).

## Reproduce

Install the pinned Lean toolchain through elan. From this directory:

```sh
lake exe cache get
```

The toolchain is Lean 4.30.0 (`commit d024af099ca4bf2c86f649261ebf59565dc8c622`). The lockfile pins Mathlib to
`c5ea00351c28e24afc9f0f84379aa41082b1188f` and its transitive dependencies.
The vendored QIT source is the required import closure of Lean-QIT commit
`c1d59b133b56e3d79efb11ee46a728d290f761f5`. Preserve the lockfile unless changing
the dependency baseline deliberately. Fetching the cache requires Git and
internet access; no dependency caches or compiled proof objects are committed.

To inspect the current selected source closure offline, without fetching
dependencies or running Lean:

```sh
python prepare_verification.py
```

It follows local imports from both `ICO.lean` and `Audit.lean`, rejects missing
local sources and cycles, and writes the current source hashes, order, and audit
endpoint list into `_build/verification/`. External Lean/Mathlib imports are
resolved by the pinned Lake environment when Lean runs. This preparation is a
source inventory, not proof verification.

To elaborate that complete source closure and run the kernel/axiom audit:

```powershell
powershell -ExecutionPolicy Bypass -File verify.ps1
# Optional after an interrupted run:
powershell -ExecutionPolicy Bypass -File verify.ps1 -Resume
```

On a POSIX shell:

```sh
sh verify.sh
```

Both wrappers regenerate the current closure automatically. They use Python 3.10+
(`python` by default in PowerShell; `python3` in POSIX, configurable with
`-Python` or the `PYTHON` environment variable respectively). The rebuild uses
one worker and a larger stack for exact certificates. It can
take substantial time. Logs and the resume ledger are written to
`_build/verification/`, without replacing the current verification record until checks are complete.
`lake build` is also available, but the explicit scripts run the final audit:

```sh
lake env lean -t0 -j1 -s524288 Audit.lean
```

## What the evidence establishes

The [recorded audit](audit/README.md) reports a
successful trust-level-zero kernel check of 124 selected endpoints, after
cleanly elaborating all 1,659 local proof modules (`1,611` `ICO` and `48` `QIT`)
from `.lean` source from an empty `QIT`/`ICO` `.olean` directory on Windows
under Lean 4.30.0 (`commit d024af099ca4bf2c86f649261ebf59565dc8c622`) before
running the single-threaded `-t0` kernel audit of `ICO.lean` and `Audit.lean`.
It reports only `propext`, `Classical.choice`, and `Quot.sound` as transitive
axioms. The exact output is [final-kernel-audit.log](audit/final-kernel-audit.log).

Windows was exercised for the complete clean build from scratch and single-threaded
`-t0` kernel audit; a separate Unix build was not run. A source hash match or
successful Python replay does not replace the Lean kernel audit.

The keyed-family transfer retains two explicit security assumptions. It does
not formalize an efficient PRU construction or asymptotic cryptographic security.
Both the fixed-plus-control exact impossibility endpoint and the arbitrary-control
full-switch theorems (`ICO/PolarizationOrderedArbitraryControl.lean`), both the
`215/10000` and `212/10000` C6 scalar bounds (`ICO/C6BonusInventory.lean`), and
both the kernel-checked `d=4` rational dual certificate (`ICO/TwoCallCertificate.lean`)
and its unconditional operational two-call strategy bound (`ICO/TwoCallOperational.lean`)
are included in the audited closure.

## Updating in place

Edit the existing module or add a required module to this tree. Keep `ICO.lean`,
`Audit.lean`, and `THEOREMS.txt` synchronized with the selected endpoints.

`verify_integrity.py` compares source with the currently recorded verification
state. An intentional proof edit should change this result until new verification
is complete. The rebuild wrappers derive the current import closure rather than
depending on the previous fingerprint set.

After a successful build and endpoint audit, replace the corresponding current
source fingerprints and verification reports in `audit/`. Keep exactly one
selected state; Git records previous versions. A hash update or offline closure
generation alone is not proof verification.

## Attribution

Lean-QIT's license and citation are retained under `vendor/Lean-QIT/`; upstream
Lean and Mathlib licenses are under `licenses/`. Those notices apply to the
respective dependencies. The imported handoff did not select a license for the
new ICO research sources.
