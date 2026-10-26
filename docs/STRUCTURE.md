# One owner for each result

| Information | Owner |
| --- | --- |
| Result identity and location | `research/results.json`; `research/RESULTS.md` is generated navigation |
| Mathematical statement, proof, assumptions, limits | The canonical source linked from that index |
| Topic-level current status | `research/status.json`; `research/README.md` has a generated table |
| Open question or next research target | The owning topic README |
| Selected paper exposition and bibliography | `paper/main.tex` |
| Visual teaching guide (explanation, not a theorem owner) | `docs/guide.html` |
| Paper-to-formal correspondence | `proofs/lean/THEOREMS.txt` |
| Selected formal implementation | `proofs/lean/ICO/` and required `vendor/Lean-QIT/QIT/` |
| Finite exact P3 data and replay | `proofs/lean/certificates/` |
| Noisy-recovery proofs and required exact replay | `research/topics/nr-noisy-recovery/`; `checks/validation.json` records current checked inputs |
| Current verification and scope | Each source package's validation record and `docs/VALIDATION.md` |

The eight topic IDs RG, P1, P2, P3, C4, C5, C6, and NR are stable. A new version of the same result updates the same files. Result dependencies and distinct model assumptions explain legitimate relationships between results; repeating a theorem in several checkpoint files does not create a new result.

A canonical result can have a manuscript presentation, formal implementation, and executable certificate. These serve different roles and are linked to one result identity. Navigation may mention a result's title and scope without duplicating its proof.

The initialization contains current knowledge, including useful scoped negative findings and unresolved gaps. No imported history archive, chronological checkpoint ledger, or redundant audit narrative is maintained. Future Git commits provide the natural revision history.
