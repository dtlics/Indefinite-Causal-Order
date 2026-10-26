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
| [Zhao et al., *Distilling Qubit Unitary Operations: A No-Go Theorem and Minimal Realization*](https://arxiv.org/html/2604.01048v3) (2026), Sections II-B--IV and Appendix C | For identical unknown qubit unitaries with independent equal-strength post-unitary depolarization and ideal auxiliary operations, two-use universal deterministic purification gives no improvement even with general ICO. An ordinary three-use parallel encoder/decoder with one protected memory qubit attains the three-use ICO optimum. | This ordinary code is a required gate-purification comparator. Restricted six-gate ICO gaps are numerical general-process results, not an exhibited physical SWITCH. Correlated clock/bath histories, noisy memory, postselection and calibration reuse need their own instruments and costs. The present distinct-product target, local noise, rejection reward and expected-resource comparison differ. |

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

## Microscopic contact interference

The [thermal-contact component](architecture-baselines.md#nr-r06-thermal-contact-history)
distinguishes a controlled physical contact schedule from an abstract
SWITCH of reduced channels. Its temporal bath-copy comparison uses
established Gaussian correlation methods; it does not claim a new general
stability technique or a demonstrated memory advantage.
Its [required-gate component](architecture-baselines.md#nr-r06-required-bcs-gate)
keeps the source's virtual Cooper-pair process separate from an explicitly
hypothetical common-amplitude stress test. Its pulse witnesses establish
achievable comparisons with that declared retry protocol, without a new
gate-synthesis or composite-control priority claim.

| Primary work | Input used | Scope to preserve |
| --- | --- | --- |
| [Bhattacharyya and van Heck, *Dynamics of Majorana tetron qubits under quasiparticle poisoning*, arXiv:2608.18042v1](https://arxiv.org/html/2608.18042v1), Sections II, V--VI and Appendices B--C | Island Hamiltonian, thermal lead correlations, charging-energy protection and split-energy dynamics. | The source supplies neither two coherently orderable contact families nor their controlled bath cross map. The exact isotropic specialization and the split-energy case require different comparisons. |
| [Huang, Zhu, Park and Lin, *Unified error bounds for perturbations of non-Markovian open quantum systems in Gaussian environments*, arXiv:2411.08741v2](https://arxiv.org/html/2411.08741v2), Theorem 2.9, Lemmas 2.10--2.11 and Appendix B | Correlation-perturbation resummation for bosonic and fermionic environments. | The contact proof adapts the insertion argument to piecewise controlled unitary propagators and a localized two-time covariance change. Its reference-complete code-input bound is an application with explicit parity and continuum assumptions. |
| [Mascherpa et al., *Open systems with error bounds: spin-boson model with spectral density variations*, PRL **118**, 100401 (2017), arXiv:1611.03377v4](https://arxiv.org/html/1611.03377v4), Eqs. (6)--(9) | Earlier non-Markovian observable bounds from changes in bath correlations. | This is a bosonic spin-boson precedent, rather than the fermionic controlled-contact statement. Gaussian influence and correlation-error bounds are established background. |
| [Schrade and Fu, *Majorana Superconducting Qubit*, arXiv:1803.01002v1](https://arxiv.org/html/1803.01002v1), Eqs. (4)--(6), (10)--(14) and supplement II | Quadratic BCS leads, charge-changing tunnelling, a required fourth-order entangler and continuously timed ordinary gates. | Both leads participate in each gate block. The source provides neither a native selector nor the stress test's common drift covariance, measured gate-speed ratio or full noisy order instrument. |
| [Bravyi, DiVincenzo and Loss, *Schrieffer-Wolff transformation for quantum many-body systems*, arXiv:1105.0675v1](https://arxiv.org/html/1105.0675v1), Sections 2--3 | Standard direct rotation and exact effective low-energy Hamiltonians. | The component supplies an elementary retained-bath/reference estimate under bounded global perturbation and a common bare vacuum. Weak on-shell hybridization, fourth-order truncation, finite temperature and ramps need additional arguments. |
| [Simonov et al., *Universal Quantum Computation via Superposed Orders of Single-Qubit Gates*, arXiv:2311.13654v4](https://arxiv.org/html/2311.13654v4), Sections II--III | Gate synthesis through commutator/anticommutator branches. | Order-based synthesis is established. Vacuum extensions, controlled implementations and the full input/output interface must be priced; this is not a source for the component's drift law or a practical robustness advantage. |

## Retained-photon gate synthesis and readout

The [retained-photon component](methods/remote-spin-phase.md#nr-r11-retained-photon-gate)
specifies a full unknown-input gate and restricted ordinary query/readout
classes. Its branch bounds do not establish priority or a physical
advantage against all ordinary instruments and memories.

| Primary work | Input used | Scope to preserve |
| --- | --- | --- |
| [Daiss source](methods/remote-spin-phase.md#nr-r11-measured-cavity-interface) | Internal source navigation. | A selected quantum output can avoid readout for either architecture; it supplies no online classical occupancy herald. |
| [Niemietz et al., *Nondestructive detection of photonic qubits*, arXiv:2103.14677v1](https://arxiv.org/html/2103.14677v1), main text, Methods and supplement | A polarization-preserving one-rail photon-presence detector. | Conditional detection given survival, survival probability and conditional mean polarization fidelity are different quantities. They do not specify a full path-flag, vacuum and reference-complete gate instrument. |
| [Kono et al., *Quantum non-demolition detection of an itinerant microwave photon*, arXiv:1711.05479v1](https://arxiv.org/html/1711.05479v1), Figs. 1–4, Methods and supplement | Dispersive reflection, weak-coherent-input detection slope, mean-number survival and no-input flips. | These statistics do not specify the joint survival/flag instrument or a dual-rail/time-bin unknown-qubit-preserving extension. The stationary reflection diagnostic does not supply an adjustable Hamiltonian dwell gate or a coherent return loop. |
| [Sinclair et al., *Proposal and proof-of-principle demonstration of non-destructive detection of photonic qubits using a Tm:LiNbO3 waveguide*, Nature Communications **7**, 13454 (2016)](https://doi.org/10.1038/ncomms13454), Figs. 1–4 and Methods | A stored probe acquires a signal-dependent phase; the proof of principle uses macroscopic signal pulses. | Neither the measured classical temporal-mode response nor total probe recall specifies the single-photon cross-history bath state. The intervening pure-loss probe calculation is an explicit diagnostic model, not an AFC fit. |
| [Stas et al., *Entanglement-assisted non-local optical interferometry in a quantum network*, Nature **651**, 326–332 (2026)](https://doi.org/10.1038/s41586-026-10171-w), Eqs. (3)–(5) and Methods | Ordinary photon-mode erasure and electron heralding transfer a signal phase into nuclear memory; remote sensing uses event-ready memory entanglement. | Matter-memory storage differs from retention of the flying photon. The ideal time-bin operator extension is derived here; phase visibility does not certify an arbitrary-input/reference storage process. |
| [Rudolph, Spekkens and Turner, *Unambiguous discrimination of mixed states*, arXiv:quant-ph/0303071v2](https://arxiv.org/abs/quant-ph/0303071), Section II | Established positive-effect support/kernel conditions for zero-error discrimination. | The vacuum-support argument is standard. Its use in the declared two-bin meter does not establish a new general discrimination theorem or a converse for every physical occupancy detector. |
| [Arwas et al., *Blueprint for a fault-tolerant compound photon–atom quantum architecture*, arXiv:2606.30385v1](https://arxiv.org/html/2606.30385v1), Section II.3, Eqs. (8)–(13) | Symmetric cavity reflection with a spin-independent selected amplitude on the interacting rail. | The architecture parameters are projected. The bypass must match the full complex transfer, and the extra polarization selection consumes physical modes. |
| [Hacker et al., *Deterministic creation of entangled atom-light Schrödinger-cat states*, arXiv:1812.09604v2](https://arxiv.org/html/1812.09604v2), Methods and Eq. (S3) | Complex detuned input–output response and distinct cavity/emission loss outputs. | The closed-transition single-photon dilation used here is a declared model, not a complete apparatus fit. Carrier balance alone does not give a finite-pulse gate or a coherent-order network. |
| [Simonov et al., *Universal Quantum Computation via Superposed Orders of Single-Qubit Gates*, arXiv:2311.13654v4](https://arxiv.org/html/2311.13654v4), Sections II–III | Established order-based gate synthesis and local feedback. | Their controlled-product gates differ from the present fixed remote contacts. Vacuum extensions and controlled optical implementations remain resources. |
| [Oreshkov, *Time-delocalized quantum subsystems and operations*, Quantum **3**, 206 (2019)](https://quantum-journal.org/papers/q-2019-12-02-206/) | Distinguishes global temporal circuit descriptions from the supplied operation subsystems. | A circuit using additional vacuum-extended call opportunities does not settle causal separability or simulate two opaque queries at the same query count. Encounter counts alone give no physical latency lower bound. |
| [Saberi, *Ancilla-assisted sequential approximation of nonlocal unitary operations*, PRA **84**, 032323 (2011)](https://doi.org/10.1103/PhysRevA.84.032323), Sections II–IV | Operator-Schmidt and sequential-ancilla obstructions. | Its unitary decoupling task differs from a retained flying data qubit with postselection and classical feedback; that no-go theorem is not imported as the present measured-instrument upper bound. |
| [Saberi, *Genuine fidelity gaps associated with a sequential decomposition of genuinely entangling isometry and unitary operations*, arXiv:1306.0430v1](https://arxiv.org/html/1306.0430v1), Sections II–VI | Matrix-product descriptions and deterministic sequential fidelity gaps. | The retained-photon sequence here permits postselection, classical feedback and a specified CZ primitive; its success-probability coefficient is not a deterministic fidelity-gap statement. |
| [Gour, *A Family of Concurrence Monotones and its Applications*, PRA **71**, 012318 (2005), arXiv:quant-ph/0410148v2](https://arxiv.org/html/quant-ph/0410148v2), Eqs. (19), (21)–(22), Theorem 1 and Eq. (45) | Determinant weights, homogeneous local-filter scaling and average product bounds for LOCC chains. | The determinant-potential technique is established. The independent-edge-state theorem does not specify the reused four-mode bus, its fixed CZ visits or the target-specific local coefficient proved here; this bounded comparison establishes no priority claim. |

## Calibration windows and multimode interfaces

The [persistent-coupler comparison](backaction.md#nr-r19-native-interface)
owns the bounded hardware screen. These sources do not establish the
fresh unknown-coupler prior or a useful retained-output order interface.

| Primary work | Access relevant to the comparison | Scope to preserve |
| --- | --- | --- |
| [Tan et al., Communications Engineering **3**, 57 (2024)](https://doi.org/10.1038/s44172-024-00198-0), simulation and experiment sections | Mueller-parameter estimation and ordinary polarization compensation. | Simulated controller timings differ from the quasistatic classical-link experiment. |
| [Herrera Valencia et al., *A large-scale reconfigurable multiplexed quantum photonic network*, Nature Photonics **20**, 202–207 (2026)](https://doi.org/10.1038/s41566-025-01806-x), Methods | Classical transmission-matrix characterization, inverse-designed phase planes and quantum entanglement routing. | The reported access and destructive state analysis do not establish the proposed fast-refresh two-processor retained-output service. |
| [Tagliavacche et al., *Frequency-bin entanglement-based Quantum Key Distribution*, npj Quantum Information **11**, 60 (2025)](https://doi.org/10.1038/s41534-025-00991-5), active phase-drift compensation and Fig. 4 | Implemented ordinary RF/pilot compensation and destructive QKD measurements. | Scalar drift and its correction do not establish a pair of required unknown multimode interactions. |

The same owner distinguishes private programs from unkeyed unknown
hardware oracles. [Wei et al., Science **388**, 509–513 (2025), v2](https://arxiv.org/html/2412.03020v2),
[Drmota et al., PRL **132**, 150604 (2024)](https://doi.org/10.1103/PhysRevLett.132.150604)
and [Baranes et al., arXiv:2505.21621v1](https://arxiv.org/html/2505.21621v1)
supply private client choices together with ordinary matter-photon
resources and adaptive control. Their secrecy restrictions remain in
the ordinary comparison. The ideal conditional-gate identity is an
access check, not a new security proof or a physical fresh-coupler claim.

The same [program-resource owner](backaction.md#nr-r19-private-programs)
now gives explicit correction-key and coherent-resource identities.
Its CCZ specialization credits [Mo et al., PRA **109**, 062428 (2024), arXiv:2311.15494v2](https://arxiv.org/html/2311.15494v2),
Theorem 1, for established magic activation, and the existing Simonov
comparison for order-based gate synthesis. The conditional ordinary
compiler and local-control factory do not certify a native port, security
claim or hardware resource optimum.
The [source-backed extension](backaction.md#nr-r19-reflected-source)
uses the author-deposited [Zenodo v2 code](https://zenodo.org/records/14854711)
for a static ideal-pulse, single-photon model audit; the concept DOI is
[10.5281/zenodo.14769739](https://doi.org/10.5281/zenodo.14769739).
It separates that selected model from calibrated hardware phases,
weak-coherent sectors and full rejected/loss instruments. The role-reversed
phase-CZ comparison uses a different physical interface and does not
infer a retained four-mode apparatus from the cited gate predecessor.

## Recovery, inversion, and verification

The [passive-qubit transfer component](communication.md#nr-r09-passive-qubit-transfer)
uses [Diekmann et al., PRX Quantum **7**, 043013 (2026), arXiv:2605.12018v3](https://arxiv.org/html/2605.12018v3),
Eqs. (1)–(4), (12), (16) and footnote 1. Its endpoint and separate
fresh-channel filter arguments are analytic deductions, with no
new passive-transfer, parity-check or hardware-priority claim.

The [natural-exchange screen](backaction.md#nr-r19-natural-exchange) uses
[Scazza et al., corrected arXiv:1403.4761v3](https://arxiv.org/html/1403.4761v3),
[Widera et al., arXiv:cond-mat/0505492v2](https://arxiv.org/html/cond-mat/0505492v2)
and [Emperauger et al., arXiv:2503.15034v3](https://arxiv.org/html/2503.15034v3).
The spectral examples are declared model deductions; these experiments
do not certify the proposed full coupler pair or its unknown-input service.

The [online-calibration assessment](architecture.md#nr-online-detector-feedback)
credits [Sivak et al., Nature **655**, 879–884 (2026), arXiv:2511.08493v4](https://arxiv.org/html/2511.08493v4),
especially Methods and supplement I.B, VI.A and VII.A–B. Its experiment,
simulation and projected timing retain their distinct scopes.

- [Quintino et al., *Reversing Unknown Quantum Transformations*](https://arxiv.org/abs/1810.06944), PRL **123**, 210502 (2019), gives heralded physical inversion of an unknown unitary and analyzes adaptive strategies and indefinite-order advantages. [Dong et al., *Success-or-Draw*](https://arxiv.org/abs/2011.01055), PRL **126**, 150504 (2021), develops retries whose draw branch preserves the input. Heralding alone does not give the present noisy filter that preservation property.
- [Trillo, Dive, and Navascués, *A universal quantum rewinding protocol with an arbitrarily high probability of success*](https://arxiv.org/abs/2205.01131), PRL **130**, 110201 (2023), uses unknown repeatable qubit operations and switch parity branches for adaptive physical recovery. Almost-sure finite stopping is distinct from a finite expected query budget. These results preclude a broad first-recovery or first-rewinding claim.
- [Salek, Ebler, and Chiribella, *Quantum communication in a superposition of causal orders*](https://arxiv.org/abs/1809.06655) (2018), already gives a heralded error-free physical transmission branch. Its communication task and comparison do not establish restoration of the specified Bell alignment against the present ordinary receivers.
- [Bai and Chiribella, *Test one to test many: a unified approach to quantum benchmarks*](https://arxiv.org/abs/1711.10240), PRL **120**, 150502 (2018), and [Barizien et al., *Quantifying the fidelity of a quantum memory*](https://arxiv.org/html/2610.08445) (2026), provide channel-test and probabilistic-fidelity context. A Bell overlap and an explicit rejection reward are standard operational tools; the task-specific expected-cost separation is the contribution.

## Retained atomic motion in scattering

The [moving-CAPS component of NR-R11](methods/moving-caps.md) uses
[Kikura et al., arXiv:2606.26542v1](https://arxiv.org/html/2606.26542v1),
Eqs. (3)–(8), (12)–(16) and Fig. 2, as its pinned local reflected-sector
model. The two-node composition, passive bound and ordinary comparisons
are deductions with separate routing, loss and numerical-tail premises;
the source does not demonstrate the proposed order-controlled apparatus.

## Unknown timed-pulse gates

The [unknown timed-pulse gate comparison NR-R21](unknown-pulse-gates.md#nr-r21)
credits [Zhao and Yuan, Quantum **5**, 534 (2021), §4.3 and Appendix D.2](https://arxiv.org/html/2103.07988v2)
for exact anticommuting-sum simulation using controlled LCU access. The
uncontrolled opaque-pulse premise requires a separate comparison.
[Taminiau et al., Nature Nanotechnology **9**, 171–176 (2014), Methods and
supplement VII, IX and XIII](https://arxiv.org/html/1309.5452v2) supplies
the NV conditional-Hamiltonian and readout screen; it does not demonstrate
the new result's unknown orthogonal equal-rate pair or native order helper.
The switch-repair precedent is Trillo, Dive and Navascués cited above.
These bounded source comparisons do not establish priority for the protocol
or its task-specific exact-query certificate.

## Efficient frames and representation input

[Brandão, Harrow, and Horodecki, *Local random quantum circuits are approximate polynomial-designs*](https://arxiv.org/html/1208.0692v4), CMP **346**, 397–434 (2016), corrected v4, supplies the efficient frame construction. Definition 2 uses relative CP-order approximation; Lemma 3 bounds its additive twirl diamond error by twice that parameter. Corollary 7 permits a fixed finite inverse-closed universal algebraic gate alphabet. At fixed order six, the gate count is $O_G(n[n+\log(1/\varepsilon)])$, hence polynomial even for the exponentially small additive accuracy required in the [theorem](theorem.md). This is an **approximate** design construction with an unspecified gate-set constant, not an exact-design or practically small-depth claim.

The design substitution controls the proof's explicit bounded-degree moment contractions after the stopping argument reduces to finite prefixes. It does not assert that sixth moments fool every unbounded-query decoder. Because the manufactured modules contain both $U$ and $U^\dagger$, a generic statement about forward queries alone cannot replace that contraction argument. Fresh private circuit sampling is an access convention, not a cryptographic pseudorandom-unitary assumption.

[Grinko and Ozols, *Linear Programming with Unitary-Equivariant Constraints*](https://doi.org/10.1007/s00220-024-05108-1), CMP (2024), Theorem 3.8 and Remark 3.10, states mixed Schur–Weyl duality for tensor powers of $U$ and its complex conjugate, including the stable-range decomposition. Its original mixed-tensor reference is [Benkart et al., *Journal of Algebra* **166**, 529–567 (1994)](https://doi.org/10.1006/jabr.1994.1166). These are the standard representation-theory inputs. The specialized sector analysis, remainder estimate, and causal cost bound are proved in this topic's own method, not asserted by those references.

## Scope of the local-noise instance

The calibrated independent local noise acts once **after each entire module**. Its per-qubit rate decreases as the register grows, keeping the module's total no-Pauli-error weight fixed. This does not establish a fixed-rate threshold for faults throughout every elementary gate in the compiled frame. The visibility calculation covers the declared scalar order-control dephasing, rather than arbitrary routing loss or hardware faults. Fresh frames prevent calibration from being amortized across challenges; persistent-device workloads require a different comparison. The physical theorem establishes the stated average one-shot restoration reward, not unrestricted throughput, cryptographic privacy, or a reusable gate program.
