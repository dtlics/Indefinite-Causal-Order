# Verification scope

Repository organization preserves the distinction between mathematical claims, exact finite checks, computational diagnostics, and a formal proof audit.

| Component | Current evidence and reproducibility |
| --- | --- |
| Research ownership | `python scripts/validate_repo.py` checks canonical result owners, generated indexes, and local links |
| Paper | `python scripts/build_paper.py` compiles the selected source in two pdfLaTeX passes to 19 pages, with no undefined references or overfull/underfull boxes; all pages were rendered and visually reviewed, with full-page checks of pages 3, 5, 16, 17, 18, and 19 |
| Overleaf export | `python scripts/package_overleaf.py` deterministically packages the exact `paper/main.tex` bytes |
| Visual guide | `docs/guide.html` was refined with the research HTML guide skill and checked in Chrome at widths of 320, 390, 768, and 1,440 pixels. Checks passed for 84 probability states, 12 task/access states, four presets, four qubit/coherence states, the transfer to the four-use calculation, and keyboard selection. Ten editable diagrams have accessible labels. No script errors, external resource requests, page overflow, duplicate IDs, or broken internal anchors were found. The expanded 19-page print preview was inspected. Scientific review checked the control-state calculation, cross-order term, common-reference proof, and prior-work attribution against the manuscript and checked primary sources. This is explanation review, not a new proof audit. |
| Selected Lean source | `python proofs/lean/verify_integrity.py` compares 1,651 modules and entry/configuration files to the recorded verification fingerprints |
| Lean rebuild and kernel audit | See [current proof-verification record](../proofs/lean/audit/README.md) and [rebuild instructions](../proofs/lean/README.md) |
| Exact P3 certificates | `python proofs/lean/certificates/verify_all.py` replays the independent support and sparse separation identities using exact arithmetic |
| P1 | The consolidated proof compiles; exact rational matrix generation and the source manifest check pass. The arbitrary-ancilla claim is analytical, not established by finite sampling |
| P2 | `verify_p2.py --all` passes four certificate replays and eleven exact structural checks; these do not settle the unrestricted optimum or finite attainment |
| RG | The source package documents integrity and certificate tiers, including [supporting helpers absent from the supplied material](../research/topics/rg-routed-graph/source/REPRODUCIBILITY.md) |
| C6 scalar checks | The exact-arithmetic replay checks both the paper's `212/10000` estimate and the formal `215/10000` allowance; it does not replace the shared-Haar proof |

The current paper build and visual review took place on 18 October 2026 with MiKTeX 25.12. Shell escape was disabled; its related warning and an update reminder do not affect the required build. All 19 pages were rendered with Poppler at 115 dpi and checked in contact sheets. The six listed pages were also inspected at full render size, including both diagrams, dense equations, and the bibliography. No clipping, overlap, missing glyphs, or broken layout was found. This review checks rendering; it is not a new mathematical proof audit or an online Overleaf run. The source checksum is `7aafc806fa3573757f3e3a73ffb3476a770ca1928aac17fb2371829f2a43a33a`. The saved output is [the compiled paper PDF](../dist/quantum-switch-paper.pdf). The ignored `dist/paper-build.json` file records the local compiler and input/output hashes; the `paper-pdf` workflow artifact also includes it.

The selected proof-verification record reports 32 endpoints checked with Lean 4.30.0 at trust level zero, using compiled objects matched to the selected sources. It does not claim a second clean elaboration of every module. A new full Lean rebuild or kernel audit was not performed as part of repository consolidation. Source fingerprints and finite Python replays do not replace that audit.

`prepare_verification.py` derives the current import closure and endpoint list offline. It rejects missing local modules and dependency cycles; the wrappers also check endpoint identities and allowed axioms. Their offline checks are separate from running Lean.

Current evidence belongs with the claim it supports. When source changes, rerun relevant checks and update the corresponding record in place after success. Keep temporary output under `_build/`; normal Git history preserves prior versions. Do not preserve intermediate build logs or repeated checkpoint reports as alternate research records.
