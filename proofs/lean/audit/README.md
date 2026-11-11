# Current proof-verification record

The recorded Lean 4.30.0 trust-level-zero audit covers 104 selected endpoints and a closure of 1,610 ICO plus 48 QIT modules (1,658 modules total). It completed successfully using `Audit.lean` and compiled objects matched to these sources, after freshly elaborating all repaired and newly added `ICO` modules under Lean 4.30.0 (`-t0 -j1 -s524288`).

| Evidence | Role |
| --- | --- |
| [closure.json](closure.json) | Selected module dependencies and source hashes |
| [entry-hashes.json](entry-hashes.json) | Entry files and pinned root configuration fingerprints |
| [final-kernel-audit.log](final-kernel-audit.log) | Exact declarations and transitive axioms |
| [final-kernel-audit-run.json](final-kernel-audit-run.json) | Command, completion, and timing |
| [kernel-validation.json](kernel-validation.json) | 104 declarations and allowed-axiom check |
| [working-object-provenance.json](working-object-provenance.json) | Source-to-compiled-object identity evidence |
| [verified-source.jsonl](verified-source.jsonl) | Representative isolated-layout source checks |
| [source-scan.json](source-scan.json) | Supplementary lexical trust-token scan |

Selected endpoints use only `propext`, `Classical.choice`, and `Quot.sound` (with pure `decide` certificate theorems using at most `propext`). The keyed-family transfer retains its two explicit security assumptions. Exact finite certificate replays in Python are supplementary checks alongside the kernel-checked Lean `decide` certificate in `ICO/TwoCallCertificate.lean`.

Every included new or repaired dependency and endpoint was individually elaborated with Lean 4.30.0 (`-t0 -j1 -s524288`) before the recorded combined 104-endpoint audit. A separate isolated-layout check covered 16 representative modules. A second clean elaboration of all 1,658 modules from scratch was not performed; nor was a complete Unix build. Source identity, individual elaboration, the representative check, and kernel checking are different evidence levels.

This directory contains one selected verification state. After a fully checked proof update, replace the applicable records in place, preserving input identity and scope; Git retains previous versions. Full rebuilds write candidate records under `_build/verification/`. Merely replacing fingerprints does not establish proof correctness.
