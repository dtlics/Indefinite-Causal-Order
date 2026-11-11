# Indefinite causal order

## Natural-black-box application-search handoff

The [current application investigation](research/topics/nr-noisy-recovery/application-search/README.md) organizes the model-validation results, ordinary baselines, exact certificates and secondary recovery/order-geometry work. The original goal remains a substantial advantage in a natural black-box quantum-computing or QEC workload; that application is not claimed complete. See the handoff before resuming exploration.

The current research on quantum-switch advantages, causal structure, and the limits of ordinary quantum queries. The repository contains the paper **Infinite or indefinite: the query cost of simulating the quantum switch**, its proof code, and the results, limitations, and open problems from eight research directions.

| Read or change… | Canonical location |
| --- | --- |
| Paper and Overleaf export | [paper/](paper/README.md) |
| Research directions and current status | [Research map](research/README.md) |
| A particular result, obstruction, or conditional theorem | [Result index](research/RESULTS.md) |
| Noisy physical recovery and its expected-query comparison | [Recovery topic](research/topics/nr-noisy-recovery/README.md) |
| Architecture applications, strongest ordinary baselines, and next tests | [Application assessment](research/topics/nr-noisy-recovery/architecture.md) |
| Persistent versus refreshed noise, universal capacity and finite-block obstruction | [Temporal-noise qualification](research/topics/nr-noisy-recovery/noise-model-selection.md#nr-r22) |
| Memory-capacity qualification, hidden-basis query separation and channel-entropy certificates | [Memory qualification](research/topics/nr-noisy-recovery/memory-qualification.md) |
| Communication cuts, optical loss and control-resource bounds | [Communication results](research/topics/nr-noisy-recovery/communication.md) |
| Coherent dispatch, ordinary recovery and microscopic temporal models | [Dispatch result](research/topics/nr-noisy-recovery/dispatch.md) |
| Bath backaction, calibration transfer and ordinary memory controls | [Shared-bath screen](research/topics/nr-noisy-recovery/backaction.md) |
| Unknown odd couplers, exact correction and expected-query fidelity limits | [Coupler benchmark](research/topics/nr-noisy-recovery/backaction.md#nr-r19) |
| Noisy phase calibration, finite-query precision and native memory costs | [Metrology benchmark](research/topics/nr-noisy-recovery/metrology.md) |
| Displacement calibration, energy bookkeeping and ordinary optical loops | [Geometric calibration](research/topics/nr-noisy-recovery/geometric-calibration.md) |
| Braided magic and physical coherent-trajectory resources | [Braided-magic screen](research/topics/nr-noisy-recovery/braided-magic.md) |
| Unknown anticommuting pulse gates, adaptive exact-call bound and ordinary timing | [Pulse-gate comparison](research/topics/nr-noisy-recovery/unknown-pulse-gates.md) |
| Drifting measurement alignment, exact two-query limits and calibrated reuse | [Alignment benchmark](research/topics/nr-noisy-recovery/alignment.md) |
| Selected formal theorem statements and hypotheses | [Theorem map](proofs/lean/THEOREMS.txt) |
| Lean proofs and exact finite certificates | [Proof project](proofs/lean/README.md) |
| Literature context and access-model distinctions | [References](references/README.md) |
| Verification scope | [Validation](docs/VALIDATION.md) |
| Where future edits belong | [Contribution guide](CONTRIBUTING.md) |

## Organization

```text
paper/          The single editable manuscript
research/       Current results, scoped negative findings, and open questions
proofs/lean/    Selected formal proof source, certificates, and verification evidence
references/     Literature context; paper citations remain in the manuscript
docs/           Structure, validation scope, and attribution
scripts/        Consistency checks and generated indexes/exports
```

Each result has one canonical owner. The result index and topic READMEs provide navigation; they do not maintain alternate theorem statements. Stronger results incorporate superseded checkpoints where their assumptions permit it. Distinct restrictions, counterexamples, conditional criteria, and unresolved gaps remain explicit. The same result's manuscript exposition, formal implementation, and certificate are linked as representations of that result.

The manuscript also connects its query lower bound to theoretical noise characterization and QEC: a constant-query switch diagnostic distinguishes positive from zero unassisted quantum capacity in an explicit hidden-memory promise. The positive-capacity model has a basis-independent code sequence; the same lower bound forces a long code block. The canonical application is [NR-R22](research/topics/nr-noisy-recovery/noise-model-selection.md#nr-r22).

The recovery topic contains an analytic physical-output theorem, its exact replay dependencies, and scoped obstructions. It is separate from the manuscript's existing simulation and decision results and has not been formalized in Lean.

Its architecture assessment distinguishes fresh-oracle theorems from persistent calibration and real device interfaces. Memory qualification connects the hidden-dephasing lower bound to positive quantum capacity and gives a Choi-entropy certificate for all unital channels, with an explicit nonunitality correction for general channels. Separate proofs bound unitary-error realization entropy and decoder-bootstrap costs. Local probes, structural calibration and native control/noise screens delimit that application. The unknown-coupler benchmark includes certified expected-query fidelity limits; calibrated Pauli/qutrit recovery, finite-energy bosonic controls, spin-loss and entanglement-first comparisons, measurement records and device reuse supply strong ordinary baselines. A [charged noisy H/S magic source](research/topics/nr-noisy-recovery/braided-magic.md#nr-r17-noisy-factory) now supplies standard distillation inputs in a declared regime where the specified ordinary noisy-T supply cannot generate magic. Its exact ordinary noisy-CS boundary is explicit. The [measured Trotter-depth certificate](research/topics/nr-noisy-recovery/methods/workload-commutators.md#nr-r06-average-case-trotter) is a direct scalar-meter use case in average-case Hamiltonian simulation, with explicit calibration costs and ordinary/classical alternatives. A [restricted one-step accuracy decision](research/topics/nr-noisy-recovery/methods/workload-commutators.md#nr-r06-trotter-query-advantage) has a theoretical two-versus-three exact-contact advantage under its stated opaque-generator interfaces. Substantial matched-device advantages and optimal general simulation remain open.

Checkpoint collections, repeated reviews, old drafts, and packaging history are not part of the repository. Revisions belong in ordinary Git commits to the canonical files.

## Use

Python 3.10+ is sufficient for repository checks, packaging, and the standalone exact-certificate replay. Lean, LaTeX, and topic-specific computations have their own documented requirements.

```sh
python scripts/validate_repo.py
python -S research/topics/nr-noisy-recovery/checks/run_all.py
python scripts/package_overleaf.py
```

Upload generated `dist/overleaf.zip` to Overleaf and compile `main.tex` with pdfLaTeX. GitHub Actions also saves an `overleaf` download from each successful check run. Generated files stay under ignored `_build/` or `dist/`.

The scientific statuses reflect the supplied research and its verification record. Repository checks do not constitute a new proof of every mathematical assertion. See [validation scope](docs/VALIDATION.md) and [rights and attribution](docs/RIGHTS.md).
