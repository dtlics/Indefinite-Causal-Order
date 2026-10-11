# Current proof-verification record

The recorded Lean 4.30.0 trust-level-zero audit covers 32 selected endpoints and a closure of 1,603 ICO plus 48 QIT modules. It completed successfully on 3 October 2026 using staged `Audit.lean` and compiled objects matched to these sources. This is the verification record supplied with the current proofs, not a new kernel run performed during repository organization.

| Evidence | Role |
| --- | --- |
| [closure.json](closure.json) | Selected module dependencies and source hashes |
| [entry-hashes.json](entry-hashes.json) | Entry files and pinned root configuration fingerprints |
| [final-kernel-audit.log](final-kernel-audit.log) | Exact declarations and transitive axioms |
| [final-kernel-audit-run.json](final-kernel-audit-run.json) | Command, completion, and timing |
| [kernel-validation.json](kernel-validation.json) | 32 declarations and allowed-axiom check |
| [working-object-provenance.json](working-object-provenance.json) | Source-to-compiled-object identity evidence |
| [verified-source.jsonl](verified-source.jsonl) | Representative isolated-layout source checks |
| [source-scan.json](source-scan.json) | Supplementary lexical trust-token scan |

Selected endpoints use only `propext`, `Classical.choice`, and `Quot.sound`. The keyed-family transfer retains its two explicit security assumptions. Exact finite certificate replays are supplementary checks, not premises of Lean theorems.

Every included new dependency and endpoint was individually elaborated before the recorded combined audit. A separate isolated-layout check covered 16 representative modules. A second clean elaboration of all 1,651 modules was not performed; nor was a complete Unix build. Source identity, individual elaboration, the representative check, and kernel checking are different evidence levels.

This directory contains one selected verification state. After a fully checked proof update, replace the applicable records in place, preserving input identity and scope; Git retains previous versions. Full rebuilds write candidate records under `_build/verification/`. Merely replacing fingerprints does not establish proof correctness.
