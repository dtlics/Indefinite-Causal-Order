# P3 — Exact universal quantum-switch simulation

[Research map](../../README.md) · [Status registry](../../status.json) · [Formal statements](../../../proofs/lean/THEOREMS.txt)

## Canonical results

| ID | Result or component | Source of truth |
| --- | --- | --- |
| P3-R01 | Universal finite-budget exact-simulation obstruction | [Theorem map](../../../proofs/lean/THEOREMS.txt), “Exact universal simulation (P3)”; [paper](../../../paper/main.tex), labels `thm:exact-simulation`, `sec:exact` |
| P3-R02 | Finite qubit support and separating certificate | [Certificate source and replay guide](../../../proofs/lean/certificates/README.md); [paper](../../../paper/main.tex), `lem:exact-obstruction`, `sec:certificate` |

The finite certificate is a component of P3-R01. The actual all-query and all-dimension reductions belong to the selected [Lean source](../../../proofs/lean/ICO/BoundedSwitchObstruction.lean). A matrix-rank replay alone does not certify the physical endpoint.

## Model boundaries

The result concerns deterministic universal simulation of the full retained control-target output, with a finite worst-case total call budget and arbitrary finite private memory. Its fixed-plus-control endpoint and the arbitrary-control corollary are distinguished in the theorem map.

Postselection, a unitary-only promise, accessible dilations or Kraus labels, control-only output, approximation, correlated-memory oracles, and unbounded stopping time with finite expected cost are different models. Their status does not follow from P3-R01.

## Limits of possible shortcuts

**Full CPTP access is essential twice.** Mixtures of CPTP channels justify polarization, and the full CPTP Choi span justifies the gauge projection. The unitary-channel set is not convex. A unitary-only identity cannot be inserted into the mixture argument, even if it holds for every unitary.

**Support needs positivity and a characteristic-zero rank argument.** The tensor-defined columns must satisfy the support constraint universally; a finite gate collection then provides an upper bound on its dimension. A modular calculation requires nonzero reduced pivots and denominators to lift to characteristic zero. Finite sampling alone is not a universal support proof.

**First-order choice can depend on the input.** Ordered Choi components obey homogeneous comb equations with input effects. Separately normalizing them as an input-independent probabilistic mixture would narrow the allowed model.

**An inaccurate SDP outcome is inconclusive.** The discovery calculation at dilution 0.1 produced a nearly feasible matrix with a negative eigenvalue. This supplies neither a feasible simulator nor an impossibility proof. P3-R02 is the exact evidence used instead.

## Updating this topic

Change the existing paper, proof, or certificate for the same result. Keep this page as navigation and model/method guidance; do not paste a second theorem statement or dated checkpoint here.
