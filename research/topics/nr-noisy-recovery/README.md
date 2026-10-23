# NR — Noisy physical state recovery

[Research map](../../README.md) · [Result index](../../RESULTS.md) · [Validation scope](../../../docs/VALIDATION.md)

This topic owns recovery through two opaque related modules, with the
ordinary comparison charged for every invocation, including calibration
and rejected histories. It is distinct from universal switch simulation
and from learning a scalar channel property.

## Canonical results

| ID | Result | Source of truth |
| --- | --- | --- |
| NR-R01 | Local-output-noise recovery against arbitrary ordinary mean-query receivers | [Theorem and proof](theorem.md#nr-r01) |
| NR-R02 | Global replacement-noise gate-product recovery and exact finite certificates | [Global-noise result](global-noise.md#nr-r02) |
| NR-R03 | Obstruction to a uniform-frame local-noise guarantee | [Scoped counterexample](obstructions.md#nr-r03) |
| NR-R04 | Exact unknown-unitary implementation is impossible from full-support noisy queries | [Support argument](obstructions.md#nr-r04) |
| NR-R05 | Destructive rejection and finite offline-program limits | [Failure and retrieval boundaries](obstructions.md#nr-r05) |
| NR-R06 | Exact ordinary simulation of calibrated orthogonal-unitary fault trajectories | [Fault simulation](architecture-baselines.md#nr-r06) |
| NR-R07 | Polynomial-query calibration of the reused finite-frame family | [Reuse baseline](architecture-baselines.md#nr-r07) |
| NR-R08 | Accessible measurement records and syndrome-sector baselines | [Measurement baselines](architecture-baselines.md#nr-r08) |
| NR-R09 | Absorbing optical loss is serial erasure plus a receiver-preparable flag | [Loss equivalence](communication.md#nr-r09) |
| NR-R10 | Entanglement-breaking slot, control-quality wire simulation and stopping bounds | [Communication resource bounds](communication.md#nr-r10) |
| NR-R11 | Elastic local-node instruments have no extra order syndrome | [Cavity-instrument screen](communication.md#nr-r11) |
| NR-R12 | Exact coherent dispatch with a dephased counter and bounded-query boundary | [Conditional dispatch result](dispatch.md#nr-r12) |

The main result has a fixed-Bell-test formulation and a secret-state
variant. They share one frontier and one result identity. Its analytic
methods are the [local converse](methods/local-converse.md),
[causal acceptance bound](methods/acceptance.md), and
[finite-design transfer](methods/design-transfer.md).

## Reproduce the exact checks

From the repository root, with Python 3.10+ and no third-party packages:

```sh
python -S research/topics/nr-noisy-recovery/checks/run_all.py
```

The [check map](checks/README.md) distinguishes executable identities from
the mathematical arguments and cited representation/design inputs.
Generated reports stay under `_build/noisy-recovery/`; one
[current validation record](checks/validation.json) identifies the
checked sources. The recovery theorems have not been formalized in Lean
or externally peer reviewed. The existing selected Lean endpoints and
manuscript remain separately indexed.

## Interpretation and open questions

Use the canonical statements for numerical constants and noise laws.
The local theorem is an average over fresh private frames, with a local
noise layer after each complete module and per-qubit rate of order
`1/n`. It compares an explicitly declared pass/fail/reject utility under
an expected oracle-call budget. Its order-control tolerance concerns
the specified scalar dephasing model. It supplies a physical output,
without a deployed-runtime or communication-capacity claim.

The [architecture assessment](architecture.md) owns the application
requirements and next-test protocol. A significant architecture benefit
has not been established. In particular, the fresh-frame converse does
not extend to reused devices after calibration; the ordinary reuse
baseline is in NR-R07. Calibrated classical Pauli faults and recorded
Lüders measurements have the ordinary baselines in NR-R06 and NR-R08.

The next application questions concern a physical unmonitored multimode
workload, retained inelastic scattering in a matter-photon link, and a
native coherent-dispatch interface. First establish each instrument,
available records and controls, and the best ordinary method; then
compare useful task outputs at matched time, memory, calls and routing
cost. The [communication note](communication.md) identifies why pure
loss and the documented elastic cavity model do not suffice. The
assessment gives explicit go/no-go tests and source-specific gaps.
The dispatch result is an exact universal query statement with a known
correction mechanism. Native slot realization, approximation, expected
cost, parallel execution, compilation and calibration reuse still need
an architecture comparison; its query count alone is not a runtime gain.
Other open directions include noise throughout compiled gates, protected
encodings at fixed site error rates, and sharper query frontiers. These
are open questions, not consequences of the present theorem.

The [literature comparison](references.md) credits the existing filtering
and recovery mechanisms. The bounded primary-source check does not
establish priority.

## Updating this topic

Update each result in its owning file. Methods and certificates are
representations or proof components, not additional result identities.
Do not import checkpoint archives, repeated audit narratives or source
ZIPs. After changing checked inputs, rerun the relevant verification and
refresh the current evidence only after success, as documented in the
check map.
