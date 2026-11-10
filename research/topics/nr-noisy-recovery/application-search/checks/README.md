# Reproduce the application-search checks

[Research handoff](../README.md)

Python 3.10+ and NumPy, SciPy, SymPy and threadpoolctl are required. Package versions are recorded in the current validation record. No external data or network service is needed for these checks.

```sh
python -m pip install numpy scipy sympy threadpoolctl
python research/topics/nr-noisy-recovery/application-search/checks/run.py
python scripts/validate_repo.py
```

Use `--group model`, `finite-query`, `baselines`, `finite-games`, `network`, `algebra` or `orders` for a subset. A complete successful run with `--record` replaces the single current `validation.json`; failures never replace a passing record. The runner copies each group to `_build/application-search/` before running it. Generated logs, scans and optimizer arrays stay out of the source tree.

## Evidence boundaries

| Group | What is checked | What is not established by the check |
| --- | --- | --- |
| model | Seeded model/fidelity/distance identities, susceptibility, known-arm compiler | All-instance proofs from sampling or the adaptive-query lower bound |
| finite-query | Exact Haar fourth moment and rational dual positivity | Larger query budgets, numerical optimality or physical feasibility |
| baselines | Choi filtering and candidate-projector identities; local-noise comparator | A new proof of the published threshold-search theorem or efficient candidate enumeration |
| finite-games | Exact finite-parameter inequalities | An independent C4/C5 proof or efficient referee |
| network | Exact ledgers, entropy intervals and five-qubit-code enumeration | Network-cut assumptions or an analytic LOCC converse from finite testing |
| algebra | Symbolic polynomial search and seeded channel examples | General multiqubit or arbitrary-protocol lower bounds |
| orders | Rational order matrices, restricted optimum/recursion and delivery probabilities | A same-apparatus advantage or generic query lower bound |

The optional `finite-query/two_call_diagnostic.py` can regenerate numerical candidates; it additionally requires CVXPY and should be run only in an ignored build copy. The default exact verifier uses the supplied `two_call_exact_certificate.json` and does not require the old floating optimizer NPZ. The optional `orders/explore_orders.py` generates discovery scans; exact certificates, not floating eigenvalues, support the finite-order statements.

[SOURCES.json](SOURCES.json) maps imported files to their supplied attachment hashes. [validation.json](validation.json) records commands, versions, source hashes and outcomes. These are scoped replay records, not a new Lean build, independent external proof audit, novelty search or hardware demonstration.
