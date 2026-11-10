# Natural-black-box quantum-computing application search

[Research map](../../../README.md) · [Result owners](../../../RESULTS.md) · [NR topic](../README.md) · [Application assessment](../architecture.md)

## Research objective and present status

The objective is a substantial quantum-switch advantage for a quantum-computing workload, including QEC, QEM, compilation, or characterization, in which the black-box access follows naturally from the practitioner's problem. The result must specify the useful output or decision, the allowed device interfaces, the strongest ordinary competitor, a finite accuracy/confidence target, and all relevant calls, failed attempts, calibration, and reuse.

A hardware runtime demonstration is not a prerequisite. However, an arbitrary Haar oracle renamed as a practical noise model, a small two-versus-two success gap, a large numerical substitution into an existing bound, or an assumed extra coherent communication interface does not by itself solve this objective.

**The objective remains open.** The later communication, superswitch recovery, and order-geometry investigations are retained as secondary results and scoped boundaries; they are not the new center of this project. The user's latest direction is to return to naturally occurring black boxes in quantum computing/QEC before developing more general order-only communication theory. This synchronization does not continue the investigation or promote the imported claims into the manuscript or Lean tree.

## Where the current results belong

| Owner | Canonical source | Role in the original objective |
| --- | --- | --- |
| NR-R23 | [Matched-fidelity model validation](model-validation.md#nr-r23) | Conditional application candidate. Useful model-mismatch and finite-depth identities; large query gap still inherits the existing hidden-basis theorem. No realistic local-noise advantage established. |
| NR-R24 | [Two-call discrimination certificate](finite-query.md#nr-r24) | Independently checkable finite result, but too weak to be the desired application headline. Does not bound eight-call or unrestricted-budget learners. |
| NR-R25 | [Ordinary finite-family and local-noise baselines](ordinary-baselines.md#nr-r25) | Essential negative evidence: a short known candidate family can be sample-efficient with expensive processing; product-local noise has a strong ordinary Choi test. |
| NR-R26 | [Spectral sensitivity and OTOC screens](spectral-sensitivity.md#nr-r26) | A physical interpretation and derivation, not yet a switch advantage for ordinary Hamiltonian/echo workloads. |
| NR-R27 | [Finite Bell-pair service](network-service.md#nr-r27) | Secondary communication detour. Large finite ratio holds under the declared network cut; not a theorem against all ordinary uses of the same apparatus. |
| NR-R28 | [Algebraic qubit recovery](algebraic-recovery.md#nr-r28) | Secondary constructive result, with prior superswitch mechanism, pure-fixed-state boundary, unknown-measurement specialization, and ordinary-code counterexamples. |
| NR-R29 | [Order geometry and modular delivery](order-geometry.md#nr-r29) | Secondary order-only algebra/certificates and conditional ledgers. Explicitly not a completed natural-black-box computing application. |
| NR-R30 | [Finite games](finite-games.md#nr-r30) | Numerical/game corollaries of existing bounds. They do not become new applications by making the dimension enormous. |

Existing [noise-memory qualification](../noise-model-selection.md#nr-r22), [memory-capacity qualification](../memory-qualification.md#nr-r20), [mixing/rewrite certification](../../c6-hidden-dephasing/applications.md#c6-r08), and [workload-commutator comparisons](../methods/workload-commutators.md) keep their current owners. This directory contains the additional derivations and baselines, not copies of those canonical proofs.

## Corrections that future work must retain

* A hidden Haar basis is sampled once and reused. Fresh channel environments do not mean a fresh basis. Entanglement fidelity to identity is a fixed Bell-return probability; average gate fidelity averages input states, not device choices. Equal fidelity scalars do not make channels equal.
* A known instance can admit an easy instance-dependent test while learning that test from unknown-channel calls is hard. This distinction does not make all structured unknown channels hard.
* The sampled-noise-model prediction may be classically easy while the actual-device statistic is hard. A short white-box circuit is not automatically classically simulable; available ordinary quantum computation must also be counted fairly.
* POVM effects specify probabilities, instruments specify state updates, and the target NCOM concerns the summed channel. Classical labels, a known description, a controllable dilation, and a replayable noise trajectory are different resources.
* Scalar estimation, full-switch simulation, exactness, finite-error approximation, and useful quantum-output tasks are separate endpoints. The no-finite exact universal theorem does not imply a constant gap at unlimited query budget.
* Known-arm/dilation compilers, unitary repeated-query constructions, outcome-readable projective ABA tests, Pauli/Bell sampling, finite-family threshold search, ordinary codes, coherent-probe resetting, and gate-based error filtration must be admitted when their interfaces are available.
* Haar information-theoretic hardness does not automatically survive a polynomial-length keyed/structured family. The ordinary threshold-search baseline is sample-efficient but may use exponential computation; cryptographic claims concern efficient learners instead.
* A capacity certificate is not an encoder or decoder. A cheap supplied code with a measurable constant performance gap is itself an ordinary discriminator.
* Near-entanglement-breaking network activation and bare order-geometry results have different comparators from unrestricted local characterization. Do not quietly substitute one for the other.

## Resume from the practitioner, not the primitive

Before expanding a candidate, specify a named workload, the natural opaque operation it exposes, and the action changed by the proposed switch measurement or retained output. Grant the ordinary competitor the actual preparation, memory, control, records, calibration, and repeatability available in that workload. Identify an actionable task-error/resource quantity, not only an ABAB-shaped expression. Test direct ordinary experiments and the baseline list above before a large search.

Retain failed candidates as precisely scoped counterexamples. In particular, replayable random unitaries, public probes, product-local axes, and short candidate lists can erase the proposed query advantage. Exact conditional recovery alone is irrelevant when a free local bypass already supplies identity. A change to a network cut or an encoded-interface assumption must be motivated by the workload, not selected solely to rescue a separation.

No claimed hardware crossover, broad novelty conclusion, or independent audit of the manuscript's adaptive lower bound is supplied by this handoff.

## Reproduction and provenance

Run from the repository root:

```sh
python research/topics/nr-noisy-recovery/application-search/checks/run.py
python scripts/validate_repo.py
```

The first command runs finite rational/symbolic certificates and seeded numerical checks in `_build/application-search/`. See [check instructions](checks/README.md) and the single [current validation record](checks/validation.json). The source-attachment map is [SOURCES.json](checks/SOURCES.json). A full successful replay can replace the record with `--record`; failures never overwrite a passing record.

The supplied notes, mathematical arguments, source attributions, exact certificate input, and executable dependencies were retained. Duplicate archive manifests/logs, regenerable scan output, and optimizer intermediates were not imported as research snapshots. The optimization script can regenerate its numerical candidate; the exact finite-query verifier does not depend on that candidate. No changes were made to `paper/main.tex` or `proofs/lean/` in this sync.
