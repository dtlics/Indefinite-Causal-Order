# Literature context

The [paper](../paper/main.tex) owns the bibliography for its claims. The distinctions below summarize the source study that informs the current research; they do not claim an exhaustive priority review. Download attempts, presentation checkpoints, downloaded source trees, and duplicate literature summaries are not maintained.

The physical recovery topic owns its distinct [literature comparison](../research/topics/nr-noisy-recovery/references.md), including parity filtering, unknown-process filtration, local output noise, and finite random-circuit frames. Its expected-query result is separate from the paper's commuting-channel decision theorem.

## Oracle models and prior switch advantages

| Work | What it contributes here | Boundary to preserve |
| --- | --- | --- |
| [Gao, Li et al., measurement incompatibility with a switch](https://arxiv.org/abs/2208.06210v4) | The known interference statistic, SAME/MUB extrema, and switch estimator | Credit the experiment; the current research's added claim is the ordinary adaptive lower bound |
| [Araújo, Costa, Brukner, computational advantage](https://arxiv.org/abs/1401.8127v5) | Unitary-order promise problem and n-switch query comparison | An older comparison to the best known ordinary algorithm is not a proved quadratic lower bound |
| [Allard Guérin et al., exponential communication advantage](https://arxiv.org/abs/1605.07372v2) | A bounded-error communication separation | One-way communication, even with prior entanglement, differs from arbitrary repeated channel queries; two-way communication changes that separation |
| [Ebler, Salek, Chiribella, noisy-channel communication](https://arxiv.org/abs/1711.10165v2) | Target/control correlations survive switching depolarizing channels | This gives channel intuition, not the present query lower bound; the switch does not grant access to a hidden Kraus label |
| [Renner and Brukner, query complexity of Fourier promises](https://arxiv.org/abs/2102.11293v1) | Ordinary algorithms can solve a task more cheaply than simulating its switch implementation | Keep task learning and full-output simulation distinct |
| [Abbott, Mhalla, Pocreau, quantum query complexity](https://arxiv.org/abs/2307.10285v3) | Fixed-order replacement when every slot receives the same unknown unitary; broader supermap analysis | The replacement statement does not extend to arbitrary nonunitary channels; general supermaps are broader than the switch |
| [Abbott, Mhalla, Pocreau, Boolean-query separations](https://arxiv.org/abs/2506.05187v2) | Query separations for general causally indefinite processes | Keep the process resource and Boolean oracle model distinct from hidden dephasing channels |
| [Bavaresco et al., hardness of switch simulation](https://arxiv.org/abs/2409.18202v2) | Closest full-switch simulation comparison | Match quantifiers, error metric, allowed circuits, and output systems before comparing bounds |

## Recording theorem and the usable interface

[Ma–Huang, *How to Construct Random Unitaries*, v3](https://arxiv.org/abs/2410.10116v3) is the selected source version. The examined statements of Theorem 8 and Claim 22 agree with v2; this does not make the complete versions identical.

- Theorem 8, Eq. (9.5), physical PDF page 39, compares Haar and recording-oracle visible outputs in half trace distance. It permits forward/inverse queries with a fixed sign sequence and known interleavings. A dephasing query uses the fixed inverse/forward pair; adaptive choice belongs to the known middle operation.
- Claim 22, Eq. (10.25), physical PDF page 49, concerns full multiset total-length sectors. An injective-record-only replacement would omit needed states.
- Creation includes multiplicity factors. Restriction and adjoint do not commute freely: input-sector annihilation uses the preceding creation grade. The current proof's implementation must respect these interfaces.

The mathematical statements and constants used by this project are owned by its [formal map](../proofs/lean/THEOREMS.txt) and [current C6 sources](../research/topics/c6-hidden-dephasing/README.md), rather than repeated here.

## OTOCs, operator algebras, and cryptographic access

| Work | Relevant connection | What does not follow |
| --- | --- | --- |
| [Zanardi, mutual averaged noncommutativity](https://arxiv.org/abs/2312.14019v2) | The maximal-abelian-algebra expression identifies the complement of the measurement visibility; projection-channel/Choi protocols give another estimator | Existence of an estimator with a shrinking signal does not establish dimension-independent ordinary query cost |
| [Cotler, Schuster, Mohseni, OTOC hardness](https://arxiv.org/abs/2208.02256v1) | A forward versus inverse unitary-access separation | Its external-ancilla restriction and reversible unitary access differ from this project's arbitrary-memory irreversible-channel model |
| [Roberts and Yoshida, chaos and designs](https://arxiv.org/abs/1610.04903v2) | Complete Pauli-probe averages relate generalized OTOCs to frame potentials | A single phase-averaged scalar does not certify a unitary design, dynamical scrambling, or cryptographic security |
| [Ji, Liu, Song, pseudorandom states and unitaries](https://arxiv.org/abs/1711.00385v1) | Forward-oracle PRU definition and foundational motivation | Forward-only security is insufficient for a reduction that implements a dephaser using both U and its inverse |
| [Ma–Huang](https://arxiv.org/abs/2410.10116v3) | The inverse-query access needed by the conditional keyed reduction | Efficiency and cryptographic assumptions remain explicit; they are not proved by the Haar lower bound |
| [Schuster et al., strong random unitaries](https://arxiv.org/abs/2509.26310v1) | Stronger access sets and depth-efficient constructions | “Strong” must name its access set; extra assumptions are not automatically required for the basic conditional corollary |

The OTOC interpretation is a consequence of the SAME/MUB comparison and an exact identity, not another independent lower-bound method. The current [C6 result ownership](../research/topics/c6-hidden-dephasing/README.md) preserves that dependency. The keyed transfer is conditional and does not transfer an unbounded Haar-query claim to a finite keyed ensemble.

## Local records and memory qualification

[Gulácsi, Kattemölle and Burkard](https://doi.org/10.1103/k2lx-vfqp)
provide correlated-noise diagnostics using product preparation and local
operations. [Huang, Kueng and Preskill](https://doi.org/10.1038/s41567-020-0932-7)
provide randomized-measurement prediction of many local observables.
The [owning NR-R14 comparison](../research/topics/nr-noisy-recovery/backaction.md#nr-r14-pair-qualification)
states the dedicated-pair and stronger parallel classical-phase memory
tasks, prior attribution and calibration-transfer limits. A coarse parity
aggregate must not replace the full labelled ordinary records.

The same [NR-R14 owner](../research/topics/nr-noisy-recovery/backaction.md#nr-r14-loss-memory)
connects measured dark-state controls, retained-control amplitude-damping
literature and the established parity-check sandwich to loss-memory
qualification. It keeps physical photon absorption, simulated optical
thermalization and a separate surviving control distinct. The
encoding-specific endpoint comparison is not a universal switch no-go.

## Exposition conventions

The manuscript presents the task, access model, output, and resource accounting before the lower bound. Proofs separate correctness from query cost, identify which random objects stay fixed, and state the conditioning needed before averaging. Diagrams identify an operational experiment or proof step; they do not replace the reduction. Conditional claims and model restrictions stay adjacent to their statements. These conventions are maintained in the one paper source rather than in successive style-review documents.
