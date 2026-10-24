# Literature context

The [local-noise theorem](theorem.md) owns the mathematical statement, proof, access model, and limitations. The [global-noise result](global-noise.md) has a distinct noise model and finite certificate. This page records the closest primary literature and the contribution being positioned; it is a bounded source check, not an exhaustive novelty or priority claim.

## Contribution and task boundary

The proposed contribution is a physical Bell-frame restoration task with a reward advantage over every ordinary receiver at the same **expected total module-query cost**. The receiver must return a quantum register or reject; correct accepted outputs, incorrect accepted outputs, and rejections all contribute to the expectation. The ordinary comparison includes quantum memory, codes, entangled probes, repeated choices of either module, and rare arbitrarily long learning histories. The local-noise instance uses fresh hidden related modules, efficiently sampled approximate-design frames, and the stated control-dephasing model.

The supplied state is already maximally entangled. The task restores a **specified standard Bell alignment** while the reference remains passive and inaccessible, and verification uses a fixed Bell projector. It is not entanglement creation, generic entanglement distribution, or a capacity theorem. Allowing a frame-dependent correction on the reference, changing the verification frame, or substituting a classical Pauli-frame record for the required physical output changes the task. These interface restrictions are essential to the [theorem](theorem.md).

## Filtering and noisy unknown operations

| Primary work | Closest connection | Distinction to preserve |
| --- | --- | --- |
| [Xiong, Chandra, Ng, and Hanzo, *Circuit Symmetry Verification Mitigates Quantum-Domain Impairments*](https://arxiv.org/html/2112.13904v2), IEEE TSP **71** (2023), Proposition 1 and Eqs. (11)–(13) | A switch separates Kraus commutator and anticommutator branches, permitting symmetry-based error filtering on physical quantum data. | This is the direct filtering-mechanism precedent. Applying it to an anticommuting pair or local Pauli errors does not establish a new filter or the present ordinary-receiver optimum. |
| [Guo et al., *Physica Scripta* **101**, 375105 (2026)](https://doi.org/10.1088/1402-4896/aea388), publisher-deposited abstract | Explicit commutation-syndrome filtering and optimized qubit recovery. | The accessible abstract specifies memoryless intermediate operations for its solvable depolarizing/axis-flip pair, and receiver-side processing for general Pauli pairs. Its precise side-system qualification and full proof were not accessible in this audit. |
| [Lee et al., *Error Suppression for Arbitrary-Size Black Box Quantum Operations*](https://arxiv.org/html/2210.10733v2), PRL **131**, 190601 (2023), Fig. 1 | Ordinary controlled-routing filtration improves the physical action of unknown noisy black-box operations. | The basic construction repeats the same complete process. Two copies of a composed $AB$ process consume four primitive module calls. Its constructive filtration theorem is not the expected-cost converse for distinct correlated modules. |
| [Miguel-Ramiro et al., *Enhancing Quantum Computation via Superposition of Quantum Gates*](https://arxiv.org/html/2304.08529v2), PRA **108**, 062604 (2023), companion to [*Superposed Quantum Error Mitigation*](https://arxiv.org/abs/2304.08528) | Generic SQEM can operate without knowing the unitary. Section II.2.1 and Section IV.3.1 explicitly treat tensor-product output depolarization and physical purification; other sections study outcome recovery and noisy auxiliary gates. | Local module-output noise and physical unknown-operation filtration are established prior. Optimal auxiliary projections can require extra knowledge or resources. Repeating the complete computation and comparing with its unprotected version does not optimize all ordinary receivers under the present mean budget. |
| [Niwa, Yoshida, and Murao, *Asymptotically optimal purification of noisy unitary channels in any dimension*](https://arxiv.org/html/2608.26061v1) (2026), Eqs. (4)–(5) | An arbitrary-sequential-strategy converse and an achievable construction for noisy unknown-unitary purification. | All slots contain the same noisy unitary, the noise is global depolarization, and the optimum is deterministic and asymptotic. This does not directly give the distinct-product, local-noise, variable-length recovery bound. |
| [Zhao et al., *Distilling Qubit Unitary Operations: A No-Go Theorem and Minimal Realization*](https://arxiv.org/html/2604.01048v3) (2026) | Deterministic purification of repeated copies of the same noisy qubit unitary; restricted gate sets already exhibit numerical two-slot ICO gaps. | Neither physical purification nor a generic two-slot indefinite-order advantage is a first claim here. The present target, dimension, rejection reward, and expected-resource comparison differ. |

A four-call ordinary filter is **not excluded** by a mean-two-query budget: it can be run on occasional rounds and combined with rejection or other strategies. The cost-sensitive converse must cover such mixtures and adaptive continuations. Fixed call counts explain the constructions' resources; they do not by themselves prove the new comparison. Ordinary postselection and coherent routing must likewise remain allowed.

The Guo comparison above uses the publisher's
[official deposited abstract](https://api.crossref.org/works/10.1088/1402-4896/aea388),
which dates online publication to 17 September 2026. The article/PDF
endpoint did not provide full text in this audit. Its side-system condition
must not be silently read as either a marginal-only or a throughout-protocol
restriction. A memory-assisted ordinary fidelity baseline need not reproduce
the original flagged channel; conversely, a full-instrument memory bound
does not establish a better recovery score or contradict a theorem for a
smaller competitor class. The commutation-syndrome mechanism is prior work.

## Fault-parity controller memory

The [controller-memory component](methods/binary-fault-controller.md)
owns the response-uniform measured-instrument task and its proofs.
The controlled-Pauli check is established background; a bounded primary
screen located no identical full-payload memory statement, without
establishing priority.

| Primary work | Closest connection | Scope to preserve |
| --- | --- | --- |
| [Bisio et al., *Memory cost of quantum protocols*, arXiv:1112.3853](https://arxiv.org/pdf/1112.3853), Definition 3, Proposition 3 and Theorem 3 | Quantum memory accounting with classical records permitted. | A closed unitary controller can overcount memory needed when intermediate measurements are allowed; the two models require separate bounds. |
| [Nayak, *Optimal lower bounds for quantum automata and random access codes*, quant-ph/9904093v3](https://arxiv.org/pdf/quant-ph/9904093v3), Theorem 2.3 and Section 4.4 | Information lower bounds for recovering selected bits. | The total carrier includes the payload. The component separately proves its reversible-source rank/entropy bound before extracting a helper-memory requirement. |
| [Chen and Gong, *Efficient Pauli channel estimation with logarithmic quantum memory*, arXiv:2309.14326v5](https://arxiv.org/html/2309.14326v5), Sections 4, 5.1.1 and 7 | Small-memory learning and purification with concatenated calls. | Those learners may consume probes and many invocations. Their learning bounds do not establish the one-call-per-layer full-payload instrument optimum. |
| [Bavaresco et al., *Simulating the quantum switch with quantum circuits is computationally hard*, arXiv:2409.18202v2](https://arxiv.org/pdf/2409.18202v2), Theorems 1–3 | Ordinary query cost of universal full-SWITCH simulation. | The fault-parity component instead fixes known cross-dual Pauli supports and measures the control; its resource is memory at specified query cuts and input-arrival times. |

## Depolarizing-noise search and restart accounting

The [search proof component](methods/noisy-search.md) owns the full
ordinary compiler, measurement-timing comparison and counted restarts.

| Primary work | Closest connection | Scope to preserve |
| --- | --- | --- |
| [Srivastava et al., *Using Quantum Switches to Mitigate Noise in Grover's Search Algorithm*, arXiv:2401.05866v2, May 2025](https://arxiv.org/pdf/2401.05866v2), Sections IV.1–IV.2 and Eqs. (57)–(58) | Balanced depolarizing switches and immediate versus deferred postselection. | The canonical comparison treats the stated fresh controls, untouched old controls and terminal product-all-plus readout. Conditional success is distinct from all-attempt cost. |
| [Vrana, Reeb, Reitzner and Wolf, *Fault-ignorant Quantum Search*](https://arxiv.org/pdf/1307.0771), Sections II.C–II.D | Noisy Grover restarts, explicit verification and noise-ignorant schedules. | Reliable candidate checking and its query cost are part of the interface. Their restricted lower bounds are not imported as all-SWITCH lower bounds. |
| [Rosmanis, *Quantum Search with Noisy Oracle*](https://arxiv.org/abs/2309.14944) | Strong query bounds for depolarizing/dephasing noise, including an error-flag setting. | The oracle/register and verification ports differ between models; this is context, not a native-router or unrestricted physical-noise theorem. |

## Recovery, inversion, and verification

- [Quintino et al., *Reversing Unknown Quantum Transformations*](https://arxiv.org/abs/1810.06944), PRL **123**, 210502 (2019), gives heralded physical inversion of an unknown unitary and analyzes adaptive strategies and indefinite-order advantages. [Dong et al., *Success-or-Draw*](https://arxiv.org/abs/2011.01055), PRL **126**, 150504 (2021), develops retries whose draw branch preserves the input. Heralding alone does not give the present noisy filter that preservation property.
- [Trillo, Dive, and Navascués, *A universal quantum rewinding protocol with an arbitrarily high probability of success*](https://arxiv.org/abs/2205.01131), PRL **130**, 110201 (2023), uses unknown repeatable qubit operations and switch parity branches for adaptive physical recovery. Almost-sure finite stopping is distinct from a finite expected query budget. These results preclude a broad first-recovery or first-rewinding claim.
- [Salek, Ebler, and Chiribella, *Quantum communication in a superposition of causal orders*](https://arxiv.org/abs/1809.06655) (2018), already gives a heralded error-free physical transmission branch. Its communication task and comparison do not establish restoration of the specified Bell alignment against the present ordinary receivers.
- [Bai and Chiribella, *Test one to test many: a unified approach to quantum benchmarks*](https://arxiv.org/abs/1711.10240), PRL **120**, 150502 (2018), and [Barizien et al., *Quantifying the fidelity of a quantum memory*](https://arxiv.org/html/2610.08445) (2026), provide channel-test and probabilistic-fidelity context. A Bell overlap and an explicit rejection reward are standard operational tools; the task-specific expected-cost separation is the contribution.

## Efficient frames and representation input

[Brandão, Harrow, and Horodecki, *Local random quantum circuits are approximate polynomial-designs*](https://arxiv.org/html/1208.0692v4), CMP **346**, 397–434 (2016), corrected v4, supplies the efficient frame construction. Definition 2 uses relative CP-order approximation; Lemma 3 bounds its additive twirl diamond error by twice that parameter. Corollary 7 permits a fixed finite inverse-closed universal algebraic gate alphabet. At fixed order six, the gate count is $O_G(n[n+\log(1/\varepsilon)])$, hence polynomial even for the exponentially small additive accuracy required in the [theorem](theorem.md). This is an **approximate** design construction with an unspecified gate-set constant, not an exact-design or practically small-depth claim.

The design substitution controls the proof's explicit bounded-degree moment contractions after the stopping argument reduces to finite prefixes. It does not assert that sixth moments fool every unbounded-query decoder. Because the manufactured modules contain both $U$ and $U^\dagger$, a generic statement about forward queries alone cannot replace that contraction argument. Fresh private circuit sampling is an access convention, not a cryptographic pseudorandom-unitary assumption.

[Grinko and Ozols, *Linear Programming with Unitary-Equivariant Constraints*](https://doi.org/10.1007/s00220-024-05108-1), CMP (2024), Theorem 3.8 and Remark 3.10, states mixed Schur–Weyl duality for tensor powers of $U$ and its complex conjugate, including the stable-range decomposition. Its original mixed-tensor reference is [Benkart et al., *Journal of Algebra* **166**, 529–567 (1994)](https://doi.org/10.1006/jabr.1994.1166). These are the standard representation-theory inputs. The specialized sector analysis, remainder estimate, and causal cost bound are proved in this topic's own method, not asserted by those references.

## Scope of the local-noise instance

The calibrated independent local noise acts once **after each entire module**. Its per-qubit rate decreases as the register grows, keeping the module's total no-Pauli-error weight fixed. This does not establish a fixed-rate threshold for faults throughout every elementary gate in the compiled frame. The visibility calculation covers the declared scalar order-control dephasing, rather than arbitrary routing loss or hardware faults. Fresh frames prevent calibration from being amortized across challenges; persistent-device workloads require a different comparison. The physical theorem establishes the stated average one-shot restoration reward, not unrestricted throughput, cryptographic privacy, or a reusable gate program.
