# Current proof-verification record

The recorded Lean 4.30.0 (`commit d024af099ca4bf2c86f649261ebf59565dc8c622`) trust-level-zero audit covers 221 selected endpoints and a closure of 1,615 ICO plus 48 QIT modules (1,663 local modules total across 32 root imports). All 1,663 local proof modules were cleanly elaborated from `.lean` source on Windows under Lean 4.30.0 (from an empty `QIT`/`ICO` `.olean` directory for the 1,659 base modules and single-threaded `-t0 -j1 -s524288` elaboration for the updated and added `ICO` modules) before running the single-threaded `-t0 -j1 -s524288` kernel audit of `ICO.lean` and `Audit.lean` on `2026-11-11`.

| Evidence | Role |
| --- | --- |
| [closure.json](closure.json) | Selected module dependencies and source hashes |
| [entry-hashes.json](entry-hashes.json) | Entry files and pinned root configuration fingerprints |
| [final-kernel-audit.log](final-kernel-audit.log) | Exact declarations and transitive axioms |
| [final-kernel-audit-run.json](final-kernel-audit-run.json) | Command, completion, and timing |
| [kernel-validation.json](kernel-validation.json) | 221 declarations and allowed-axiom check |
| [working-object-provenance.json](working-object-provenance.json) | Clean-from-scratch source-to-compiled-object provenance |
| [verified-source.jsonl](verified-source.jsonl) | Clean-from-scratch module elaboration records |
| [source-scan.json](source-scan.json) | Supplementary lexical trust-token scan |

Selected endpoints use only `propext`, `Classical.choice`, and `Quot.sound` (with pure `decide` certificate theorems using at most `propext`). Part 1 of [THEOREMS.txt](../THEOREMS.txt) maps the statements of `paper/main.tex`; supplementary endpoints retained from earlier drafts—including the conditional keyed-family transfer (with its two explicit security assumptions) and the kernel-checked `d=4` two-call certificate and operational bound in `ICO/TwoCallCertificate.lean` and `ICO/TwoCallOperational.lean`—are catalogued in Part 2 of [THEOREMS.txt](../THEOREMS.txt). Exact finite certificate replays in Python (`../certificates/verify_all.py`) are supplementary checks alongside the Lean kernel audit.

All 1,663 local modules (`1,615` `ICO` and `48` `QIT`) were compiled cleanly from `.lean` source on Windows under Lean 4.30.0 (`commit d024af099ca4bf2c86f649261ebf59565dc8c622`) prior to the single-threaded `-t0` kernel audit of `ICO.lean` and `Audit.lean`; a separate Unix build was not run. Source identity, module elaboration, and final `-t0` kernel checking remain distinct evidence levels.

This directory contains one selected verification state. After a fully checked proof update, replace the applicable records in place, preserving input identity and scope; Git retains previous versions. Full rebuilds write candidate records under `_build/verification/`. Merely replacing fingerprints does not establish proof correctness.
