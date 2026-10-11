# P2 — Unrestricted bipartite GYNI

[Research index](../../README.md) · [Current status](../../status.json)

The target is the supremum of `(1/4) sum_xy p(a=y,b=x|x,y)` over every finite-dimensional valid bipartite process and arbitrary local binary instruments. The supremum does not presume attainment. No port-dimension, support, angle, or Kraus restriction is imposed.

Each row below has one owner. Update that proof or experiment in place; navigation pages and audit reports are not alternative versions of the result.

| Knowledge | Canonical owner |
| --- | --- |
| Exact certified interval and metadata | [CERTIFIED_BOUNDS.json](source/CERTIFIED_BOUNDS.json) |
| P2-R01/R02: reduced physical cone, all-charge lift, finite-size algebraic exhaustion | [physical-process/reduced_process_theorem.md](source/support/physical-process/reduced_process_theorem.md) |
| P2-R03: quantitative Jordan-grid reduction | [foundations/jordan_grid_reduction.md](source/support/foundations/jordan_grid_reduction.md) |
| P2-R04: universal word certificates and exact repair | [foundations/uniform_word_channel_theorem.md](source/support/foundations/uniform_word_channel_theorem.md) |
| P2-R05: complete hierarchy and centered-path convergence | [word-kernels/hierarchy_completeness.md](source/support/word-kernels/hierarchy_completeness.md) |
| P2-R06: universal rational-kernel upper certificate | [word-kernels/rational_kernel_ansatz.md](source/support/word-kernels/rational_kernel_ansatz.md) |
| P2-R07/R26: six-angle physical lower and exclusion of one fixed five-angle support | [objective/strict_support_separation.md](source/support/objective/strict_support_separation.md) |
| P2-R08/R09: output dephasing and Jacobi/coset normal form | [output dephasing](source/support/objective/output_eigenvalue_reduction.md), [coset form](source/support/objective/jacobi_coset_kernel_form.md) |
| P2-R10: finite-Kraus local factorization | [local-factorization/finite_rank_local_factorization.md](source/support/local-factorization/finite_rank_local_factorization.md) |
| P2-R11/R12: rook scalar reduction and normalized clique gap | [local-factorization/rook_support/rook_rank_one_reduction.md](source/support/local-factorization/rook_support/rook_rank_one_reduction.md) |
| P2-R13/R14: spectral-ideal saturation and conditional tester realization | [finite-realization/flat_tester_realization.md](source/support/finite-realization/flat_tester_realization.md) |
| P2-R15–R21/R25: complementary-face criterion, strict slack, local-rank and tail obstructions, weighted-tail criterion, positive-lift and convex-average obstructions | [complementarity-and-tails/complementary_support_and_tail_gap.md](source/support/complementarity-and-tails/complementary_support_and_tail_gap.md) |
| P2-R22/R23: operator-system and coherent-Choi compression obstructions | [compression-obstructions/finite_span_obstructions.md](source/support/compression-obstructions/finite_span_obstructions.md) |
| P2-R24: uncertified L10 search and exact reconstruction limits | [NUMERICAL_DIAGNOSTICS.md](source/NUMERICAL_DIAGNOSTICS.md) |
| Commands and dependencies | [REPRODUCIBILITY.md](source/REPRODUCIBILITY.md) |
| Primary-source modelling assumptions | [LITERATURE.md](source/LITERATURE.md) |

The current frontier is owned by the final “missing step” section of the [complementarity/tail proof](source/support/complementarity-and-tails/complementary_support_and_tail_gap.md#8-precise-outcome-and-next-genuinely-missing-step). Distinct scoped obstructions remain useful; none is a nonattainment theorem.

Verification has different scopes. The upper certificate has a separately written standard-library checker; the physical lower and fixed-support upper have supplied exact arithmetic replay. Structural proofs are analytical, with exact finite examples and some separate symbolic checks. Neither the navigation inventory nor those checks creates independent peer review of every general claim. Default `verify_p2.py` checks integrity and exact metadata; `--core` reconstructs bounds; `--all` also runs the supported exact structural checks in a temporary copy.
