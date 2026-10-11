# Lean proofs

This is the canonical source tree for the formal results accompanying the
[paper](../../paper/main.tex). Start with [THEOREMS.txt](THEOREMS.txt) for precise
statements, hypotheses, metric conventions, and stable paper labels.
[DEPENDENCIES.txt](DEPENDENCIES.txt) records upstream versions and provenance.

The selected proof closure contains 1,603 project modules in `ICO/` and 48
unchanged Lean-QIT modules in `vendor/Lean-QIT/QIT/`. `ICO.lean` selects the
endpoints; `Audit.lean` prints their types and transitive axiom dependencies.
The independent finite-arithmetic companion is kept once, in
[certificates/](certificates/README.md).

## Reproduce

Install the pinned Lean toolchain through elan. From this directory:

```sh
lake exe cache get
```

The toolchain is Lean 4.30.0. The lockfile pins Mathlib to
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

The [recorded audit](audit/README.md), dated 3 October 2026, reports a
successful trust-level-zero kernel check of 32 selected endpoints, using the
working project's compiled objects matched to these sources. It reports only
`propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. These are
imported results, not a new Lean run performed during repository organization.
The exact output is [final-kernel-audit.log](audit/final-kernel-audit.log).

The release separately records individual source elaborations and a 16-module
isolated-layout check. It explicitly does **not** claim a second clean build of
all 1,651 modules. Windows was exercised; a complete Unix build was not. A source
hash match or successful Python replay does not replace the Lean kernel audit.

The keyed-family transfer retains two explicit security assumptions. It does
not formalize an efficient PRU construction or asymptotic cryptographic security.
The theorem map also distinguishes the fixed-plus-control exact impossibility
endpoint from its full-control corollary, and the formal `215/10000` scalar
allowance from the paper's sharper `212/10000` estimate.

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
