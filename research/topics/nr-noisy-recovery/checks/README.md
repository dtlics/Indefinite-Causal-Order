# Exact replay

Run from the repository root with Python 3.10 or newer; no third-party packages are needed:

```sh
python -S research/topics/nr-noisy-recovery/checks/run_all.py
```

Use `--record` to replace the single current [validation record](validation.json) after a successful run. It records relative input hashes, command, environment, outcome and scope. The inputs include the topic's canonical Markdown proofs and the required checker/certificate files. A normal run checks the saved fingerprints without changing them and fails if the record is missing or stale. Recorded environment metadata is informative; another operating system or Python version does not invalidate matching inputs and scope. Assertions are proof checks: the runner and verifiers reject `-O`.

The runner copies executable inputs into `_build/noisy-recovery/stage/` and runs each job in a fresh `python -S -B` process. Reports, logs, bytecode and other generated files stay under `_build/noisy-recovery/`; tracked checker sources remain unchanged. Run individual verifiers from the staged copy if their detailed output is needed, because some save a report beside their source.

| Directory / job | Proof obligations replayed |
| --- | --- |
| `algebra/brauer_objective.py --validate` | Independent sparse physical Choi contractions: every diagram at dimension 2, selected diagrams at dimension 4, both device labels and fidelity/probability objectives. Gaussian integers and fractions only. |
| `algebra/brauer_gate_product_exact_check.py` with the deterministic-tree JSON | Dimension-8 global-noise ordinary converse. Rebuilds all objective Gram equations, causal slacks and exact diagram sums of squares. |
| `recovery/expected_cost_D8.py` | Replays the full heralded dimension-8 certificate through the same checker, then checks its homogeneous intercept, expected-cost elimination and Bell/private-state payoffs. A second standalone heralded replay would duplicate this job. |
| `recovery/finite_ensemble_D8.py` | Constructs all 72 projectors in nine mutually unbiased bases using Gaussian integers, verifies their first and second moments and every overlap, then checks the finite-input recovery payoff reductions. The full D8 source certificate is replayed by the preceding job. |
| `acceptance/acceptance_correct_sharp_stdlib_replay.py` | Correct four-port adaptive acceptance dual for all dimensions at least 8. Rebuilds 72 symbolic Gram equations, all 108 principal minors, 16 cup-free characters and the directed causal prefix equalities. Supplied Boolean flags and expression strings are not trusted. |
| `local/verify_structural.py` | Formal cup/Pauli contractions, invariant-component normalization, all adjoint contractions, one-cup weights and exact rook-graph overlap identities. |
| `local/verify_dimensions.py` | All mixed `(3,3)` Weyl dimension identities, multiplicities, physical/commutant dimension sums and polynomial lower bounds. |
| `recovery/scalable_global.py` | Exact global-noise scalar and polynomial corollaries for qubit dimensions `8,16,…`, including expected-query reward and conservative design loss. |
| `recovery/local_recovery.py` | Frozen local-noise intercept, stopping coefficients, approximate-design loss, recovery reward and 97% control-visibility margin for at least eight qubits. |
| `architecture/verify_fault_simulation.py` | Finite exact orthogonal-process and full switched-output examples for the calibrated classical-fault baseline NR-R06. |
| `architecture/verify_reuse.py` | Rational threshold, spectral-gap, recovered-score and training/rejection crossover arithmetic for NR-R07. The collective learning algorithm and its asymptotic constants are cited inputs, not computed by this replay. |
| `architecture/verify_measurements.py` | Small exact Lüders PVM examples, Choi overlaps, recorded return probabilities, binary trace-filter identities and syndrome-sector scaling constants for NR-R08. |
| `architecture/verify_communication.py` | Full Choi equalities for six absorbing-vacuum examples, sixteen rank-one-channel/noisy-qubit-wire factorizations, four rank-two protected-factor factorizations and four tight qubit-activation examples, plus an elastic-node instrument and a bus-mixing counterexample. The general entanglement, finite-mean and capacity proofs are analytic. |
| `architecture/verify_native_checks.py` | Exact finite known-Clifford Pauli-check and classical-bit-oracle comparisons with non-Pauli noise; no fitted helper-gate or hardware-runtime model. |
| `architecture/verify_dispatch.py` | Thirty-six reference-complete flagged counter/data Choi examples at data dimensions 2 and 3, the fully dephased indexed-unitary identity, and three-call/parallel four-call dummy factorizations for NR-R12. The exact universal query obstruction uses the cited analytic no-go theorem. |

The five modules in `algebra/` form the shared exact engine. `brauer_exact_replay.py` derives diagram multiplication, adjoints, traces and identity insertions directly from pairings. `brauer_objective.py` constructs canonical Gaussian-integer objectives; `brauer_weingarten.py` inverts their permutation Gram system over fractions. `brauer_sos_certificate.py` checks the actual tensor-operator sum-of-squares residual and its norm margin. The main checker independently verifies every objective Gram equation and reconstructs every certificate slack. Both dimension-8 certificate JSONs are required inputs; search diagnostics and cached slacks cannot substitute for a successful replay.

These checks complement the canonical mathematical proofs. Their finite or polynomial identities do not independently prove representation-sector completeness, stopping-time reductions, physical access assumptions, or approximate-design norm transfer. Those arguments remain in the linked method notes and theorem. This package performs no solver search, floating-point feasibility test, hardware experiment or new Lean kernel audit. Numerical discovery scripts, repeated audit narratives and search caches are intentionally absent.

The architecture jobs support the [ordinary baselines](../architecture-baselines.md),
and [communication bounds](../communication.md), not a positive application claim.
Their examples do not prove the
all-input simulation by sampling, implement Threshold Search, or establish
a useful native-device cost advantage. The general proofs and interface
conditions remain in that canonical note. The
[application assessment](../architecture.md) states the remaining gaps
and concrete next tests.

The communication and native-check replays share Gaussian-rational matrix
helpers with `verify_fault_simulation.py`; all those inputs are copied and
hashed together. Full matrix identities cover the tested reference-complete
channels. Finite examples do not establish the all-history entropy ledger,
Schmidt-number theorem, a general loss convention or a native noise budget.

The [dispatch proof](../dispatch.md) distinguishes a hard worst-case exact
query count from fidelity, expected cost, parallel latency and reuse.
Its replay does not establish a quantitative ordinary approximation gap
or a valid coherent-use interface for a physical processor.
