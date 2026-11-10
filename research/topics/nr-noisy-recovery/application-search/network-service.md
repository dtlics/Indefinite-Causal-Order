<a id="nr-r27"></a>

# Finite Bell-pair delivery under a standard-network cut

[Investigation handoff](README.md) · [Application assessment](../architecture.md)

**Status and scope.** Secondary communication detour. Comparison is LOCC plus specified links, not all ordinary uses of the same physical apparatus. Parameters are assumptions, not measurements. Supplied analytical derivations and scoped checks; not a new Lean audit or a publication-priority claim.

## 1. A service that changes an executable computation

Two quantum-processing modules, Alice and Bob, start with no entanglement across the network cut. They want one Bell pair Phi+ across that cut. The service must flag DELIVER or ABORT, with

- probability of DELIVER at least s*=0.99;
- conditional Bell fidelity F=<Phi+|rho_deliver|Phi+> at least F*=0.99.

All attempts, including losses, count. This is a finite output-state task, not a statement about an unknown code's asymptotic existence.

A delivered Bell pair can be consumed by a remote CNOT/CZ gate via local operations and classical communication. The Bell-pair fidelity target is not a claim that 1% total logical-gate error meets a fault-tolerance threshold. Better gate accuracy would require another finite code/error budget. Gate errors from the subsequent gate-teleportation hardware are additional.

## 2. The two resource interfaces being compared

### Ordinary network interface

A finite or almost-surely terminating adaptive protocol may use:

- arbitrary local ancillas, entanglement within a module, and arbitrarily large local quantum memories;
- arbitrary local gates, measurements, feedback and error-correcting codes;
- unlimited two-way classical communication;
- any serial or parallel arrangement of the available noisy quantum communication contacts, with interspersed permitted operations;
- full classical descriptions of the channels and arbitrary classical computation.

Its only nonlocal quantum resources are uses of the declared noisy contacts. There is no initial shared entanglement, clean quantum bypass, free remote quantum gate, or independent entanglement supplier. All crossings using the declared contacts are counted. For the lower bound we even remove loss and local implementation errors. Adding loss or extra local noise cannot improve that competitor.

The simplest model is a cut between two modules. The same argument holds for a standard network if every quantum edge crossing a fixed separating cut has the declared channel simulation resource and the total charged number of such uses is q. It does not apply to a free coherent routing operation across that cut: such an operation is an additional resource.

### Switch-enabled interface

A provider additionally supplies the standard switch of two labeled noisy invocations. The order qubit is initialized in |+>, cannot be used by Alice to encode her message, and is measured in X by the provider, who sends only the outcome bit to Bob. Both target contacts are counted. All non-classical routing/control ports are part of this additional resource, not asserted to be ordinary free operations.

This is the resource interface used in switch-assisted quantum Shannon theory [1,6]. Other coherent-control interfaces can match some switch advantages [7]. Therefore the claim is a comparison with standard network access, not a proof that indefinite order is the uniquely necessary microscopic resource. The reduced channel descriptions alone do not establish that a physical device realizes this switch.

A hardware audit must exclude a message-carrying clean side channel and account for vacuum sectors, path/time records and accessible environments. A control marginal independent of the message is not, by itself, a proof of fair resource equivalence.

## 3. Elementary noise and tolerances

Let

E_c(rho)=a X rho X+b Y rho Y,

a=(1+c)/2, b=(1-c)/2, |c|<=c*=0.001.

Since Y differs from XZ only by a global phase,

E_c = Ad_X o D_c,

D_c(rho)=(1+c)/2 rho+(1-c)/2 Z rho Z.

Thus |c| is the residual coherence of a dephasing contact. c=0 is complete dephasing, followed by a deterministic X; c=0.001 is near, but not at, that point. In a Markovian phase-damping interpretation c=exp(-t/T2), the illustrative choice is t/T2=ln(1000). No apparatus or actual duration is inferred from this formula.

The channels in the two slots may have distinct c_A,c_B. Allow additional actual errors

N_j=R_j o E_{c_j},

where each R_j is CPTP and D_half_diamond(R_j,id)<=xi=0.001.

**The postprocessing condition is essential.** It preserves the ordinary entanglement upper bound by data processing. An arbitrary channel in a diamond ball around E_c could have more entanglement-transmitting power; that broader perturbation class requires a new converse.

Each invocation and attempt has fresh independent private environments; there is no replayable hidden error label. The switch extension pairs each invocation's environment across its two order histories. Shared-bath/time-dependent implementations not satisfying this rule need another model.

Further declared specifications:

- symmetric control-sign error eta=0.01, independent of target state and channel errors;
- each complete switched attempt survives with probability a_s=0.9, independently and with a state-independent herald; a loss has no hidden successful delivery;
- conditioned on a retained delivery/loss history, all local preparation, storage, correction, twirling, purification and decoding differ from the ideal local protocol by at most beta=0.005 in complete trace/half-diamond error. A sufficient implementation condition is that the sum of the corresponding local operation error bounds on any such history is at most beta. This is a whole-protocol budget, not a per-gate error.

The loss model is a separately declared heralded erasure of the complete switched attempt. Its compatibility with a real microscopic loss process is not inferred from a quoted transmission efficiency.

These are supplied channel/hardware contracts for the service; the twenty-contact count does not include experimentally certifying them from an untrusted apparatus. The ordinary protocol is granted even complete exact knowledge of the contracts. The switched correction itself needs no estimate of c_A or c_B, only the calibrated X/Y frame and the stated error bounds.

## 4. The switch returns a correctable error, not a learned scalar

For ideal slots E_{c_A},E_{c_B}, the four Kraus pairs are weighted versions of (X,X),(X,Y),(Y,X),(Y,Y).

- Equal Paulis commute and their product is I.
- Unequal Paulis anticommute and their product is Z up to a phase.

Consequently the subnormalized output maps after control readout are

M_+(rho)=(a_A a_B+b_A b_B) rho,

M_-(rho)=(a_A b_B+b_A a_B) Z rho Z.

Correcting the minus branch by Z makes the sum exactly rho. This holds on every input including an arbitrary inaccessible reference. It does not require c_A=c_B or c_A=0.

The provider sends the sign bit; Bob implements the correction. Both outcomes are used: there is no success-only phase postselection.

A symmetric sign-flip probability eta makes the corrected map

C_eta(rho)=(1-eta)rho+eta Z rho Z.

Its action on one half of a locally prepared Bell state has Bell infidelity eta. This channel identity holds for all c_A,c_B. The ideal raw plus probability is (1+c_A c_B)/2, which contains no message dependence.

For N_A,N_B, deterministic superchannel contractivity in each fixed switch slot implies

D(S[N_A,N_B],S[E_{c_A},E_{c_B}])<=2xi.

The sign-noise/readout/correction processing contracts this distance. Thus every surviving raw Bell pair has fidelity at least 1-e0 with

e0=eta+2xi=0.012.

Independent bilateral Pauli twirling preserves Bell fidelity and makes each pair Bell diagonal. This turns arbitrary small postprocessing errors into a classical Pauli-error distribution without asserting that the original R_j was Pauli. With independent attempts, the retained Bell pairs have independent such errors, each with probability at most e0. Twirling noise is included in the local beta ledger.

## 5. A finite five-pair purification, not an asymptotic coding theorem

Use the [[5,1,3]] stabilizer code with generators

XZZXI, IXZZX, XIXZZ, ZXIXZ,

and logical X=XXXXX, Z=ZZZZZ. The generators commute and are independent. The 15 weight-one Pauli errors have distinct nonzero syndromes; identity has zero syndrome. Each can therefore be corrected exactly.

The corresponding one-way entanglement-purification protocol is local: both parties measure the (conjugate as needed) four stabilizers, Alice sends four syndrome bits, Bob infers the relative error syndrome and corrects, and both decode to one retained Bell pair. It produces one output pair deterministically once five raw pairs have arrived. A stabilizer measurement uses a local ancilla and known controlled Pauli couplings; no remote entangling gate is hidden in the code.

Since every zero- or one-error event is corrected, the output infidelity is at most

f5(e0)=1-(1-e0)^5-5e0(1-e0)^4.

For e0=0.012 this is exactly

686401389/488281250000 = 0.001405750044672.

No assumption about the proportions of X,Y,Z errors is required. The total Bernoulli probability of two or more errors is monotone in each error probability, so the same upper bound holds for independent non-identically distributed errors bounded by e0.

After local implementation error beta=0.005,

F_deliver >=1-f5(e0)-beta
           =0.993594249955328.

The inequality is conditional on delivery. Because losses are independent of payload/errors and local trace-preserving faults do not modify the declared loss process, conditioning on collecting five successes does not bias the raw quantum state beyond the specified budgets.

The exact checker enumerates all 4^5=1024 Pauli errors, constructs the syndrome correction table, and verifies all 16 weight-zero/one patterns. It does not simulate an unprovided hardware pulse implementation.

## 6. Count losses and every contact

Attempt generation until five pairs arrive or ten complete attempts have been made. An attempt always charges two elementary noisy contacts, including its failed/lost version.

With survival a_s=0.9,

P_abort = sum_{j=0}^4 binom(10,j) a_s^j(1-a_s)^(10-j)
        =734513/5000000000
        =0.0001469026.

Therefore

P_deliver=0.9998530974,

Q_switch<=20.

The exact expected number of elementary contacts is 11.11076354, and in particular it is no more than 2*5/0.9=100/9. This counts all attempted contacts, not only survivors. The proof uses at most five stored pairs (five storage qubits at each endpoint), plus local syndrome ancillas, the traveling target for an active attempt and the provider's order qubit. Finite local Clifford processing and classical messages are additional resources with the stated beta budget. No hardware-time ratio is inferred merely from the contact ratio.

The specified service has fidelity and delivery probability exceeding 0.99. Surplus fidelity is not used to make the ordinary lower bound artificially larger: its target remains only 0.99/0.99.

## 7. An all-strategy finite ordinary converse

Define E_R(rho)=inf_{sigma separable}D(rho||sigma), with base-two logarithms. It cannot increase under LOCC, is subadditive on tensor products, and is strongly monotone on average under flagged LOCC.

### 7.1 A single contact contributes at most g(c*) entanglement resource

Up to a local X correction, the normalized Choi state of E_c is

omega_c=a|Phi+><Phi+|+b|Phi-><Phi-|.

Use the separable state

sigma_sep=(|00><00|+|11><11|)/2.

Then

D(omega_c||sigma_sep)=1-h2((1-c)/2)=:g(c).

Therefore E_R(omega_c)<=g(c). Equality is known for dephasing, but the upper bound is all that is needed here.

Because E_c is a Pauli channel, ordinary teleportation with resource state omega_c simulates one channel use exactly. R o E_c is simulated by the same resource followed by local R at the receiving side. Hence its resource cost is no greater. Teleportation simulation is valid on inputs entangled with arbitrary retained local memories.

Stretching an arbitrary adaptive q-contact network protocol across the separating cut yields an LOCC map on q such resource states. Intermediate encodings, decoding, measurements, feedback, large block codes, and two-way classical messages remain contained in that LOCC map. Since |c_j|<=c*,

E_R(rho_output,including_flags) <= q g(c*).

The ordinary competitor can have perfect local operations and no loss; this makes it stronger than the actual service. Restricting only to a fixed serial word would be insufficient and is not what this proof does.

### 7.2 Any successful Bell pair requires a fixed amount of that resource

For any two-qubit state rho with Bell fidelity F>=1/2, measurement with {Phi+,I-Phi+} gives probabilities (F,1-F). For every separable sigma its Bell probability t is at most 1/2. Data processing of relative entropy implies

D(rho||sigma) >= D_bin(F||t) >= D_bin(F||1/2)=1-h2(F).

Minimizing over separable sigma therefore gives

E_R(rho)>=1-h2(F).

If delivery is heralded with probability s, flag monotonicity gives

E_R(rho_output,including_flags) >= s E_R(rho_deliver)
                                  >= s[1-h2(F)].

Reject branches are included and have nonnegative entanglement. Combining the two parts,

q >= s[1-h2(F)] / g(c*).                                      (1)

This is a finite, one-output-pair inequality, not division by an asymptotic coding capacity.

For s=F=0.99 and c*=0.001,

g(c*) = 7.21347640669... * 10^-7,

q >= 1261548.16922798... .

At a budget of only twenty ordinary calls, the same inequality gives delivery probability at most 0.00001569501 for conditional fidelity at least 0.99. Thus the comparison also yields a finite delivery-probability inequality, not merely an asymptotic rate comparison.

Thus any hard cap must be at least 1,261,549. The checker certifies the integer implication with rational logarithm/series intervals, not just floating-point evaluation.

### 7.3 Expected budgets and early stopping

The expected version follows from resource amortization. Each ordinary contact can increase the average REE by at most g(c*); local instrument steps cannot increase it on average. Truncate after L contacts, mapping unfinished branches to an abort flag. Its average final REE is at most g(c*) E[min(N,L)]. The successful output subnormalized states converge as L increases for an almost-surely terminating service. Their success probabilities and normalized Bell fidelities converge to s,F; the binary fidelity lower bound above is continuous. Taking L to infinity gives

E[N] >= s[1-h2(F)]/g(c*),

assuming finite mean; an infinite mean already pays more. Thus cheap typical branches and rare expensive branches do not remove the lower bound. No nontermination is treated as a free successful output.

### 7.4 Interpretation

The huge number comes from tiny entanglement per ordinary use, not from a large register, inaccessible Haar basis, or difficulty computing a known formula. The task is to deliver a quantum resource across a cut. The same formula can be known perfectly and the transmission task remain difficult.

At c*=0, the channels are entanglement breaking; ordinary LOCC plus any number of uses cannot deliver fidelity above 1/2. The ideal switch remains correctable. Our numerical example deliberately uses nonzero c*=0.001 so it has a finite ordinary lower bound instead of relying on an exact zero-capacity endpoint.

## 8. Connection to a remote gate

The delivered pair is Bell diagonal after ideal twirling and Pauli-code processing. Its trace distance from the ideal Bell state equals its infidelity. Local implementation errors increase the distance by at most beta. Thus the pair's half-trace error is at most f5(e0)+beta=0.006405750044672.

A fixed ideal gate-teleportation LOCC map consumes the pair and any two-module data input, including a reference. Contractivity therefore bounds the induced remote-gate half-diamond error by that same number. Actual gate-teleportation errors add their own budget. No unknown live payload is sent while the Bell-pair preparation attempts can fail; the application waits for DELIVER.

This is a useful finite object: an executable Bell-pair factory feeding a remote entangling gate, not only a statement that some long code exists.

## 9. What could invalidate the comparison

1. A clean quantum bypass or pre-shared entanglement is available at no charge. Then sending/storing/teleporting through it defeats the noise bottleneck.
2. The physical switch's control/path/temporal modes supply additional callable quantum channels to the ordinary strategy. The resource set must be enlarged and the converse re-proved. The bound here is not a universal causally-ordered optical-circuit no-go theorem.
3. The measured noise is mainly a reproducible classical rotation that can be estimated by pilots or echoed inside a contact. Then the declared memoryless channel interface is not the complete available interface.
4. The environments carry order timestamps that invalidate the paired-history switch. Its full control-target channel must be established; single-use process tomography is not enough.
5. Loss is state dependent, unheralded, or correlated with error histories. The simple binomial/conditional-fidelity ledger no longer applies.
6. Extra imperfections are arbitrary perturbations, rather than the postprocessing degradation assumed in the converse. Recompute the entanglement resource; an arbitrary closeness ball alone need not preserve the million-use bound.
7. Local preparation/storage/code faults exceed the whole-protocol beta budget.
8. The goal changes back to local channel characterization. Bell probes with retained local data can simulate known-basis Pauli switch statistics cheaply; the network no-bypass restriction is doing essential work.

This list is part of the theorem's scope, not an assertion that all requirements are already met on a physical platform.

## 10. Research status and literature

The activation mechanism is established [1], and communication-engineering uses of switch-assisted teleportation/entanglement distribution also predate this note [8]. The value of this calculation is its explicit finite delivery objective, a nonasymptotic converse against all standard adaptive network protocols, a concrete five-pair purification operation, and accounting for failures and declared imperfections.

The workload is real [5], and dephasing/erasure-Pauli models are used in fiber-entanglement studies [9]. Those facts do not prove a native switch with the specified parameters exists. Conversely, demonstrations of optical switches [10] do not certify the hidden-environment, network-cut, local storage or loss assumptions used here.

For a new architecture paper, the main unresolved contribution is identifying a full physical interface where this service comparison is fair, and showing the native parameters and all ordinary alternatives satisfy it. This is not an already established improvement of a particular deployed quantum network.

# References and precise use

[1] G. Chiribella et al., **Indefinite causal order enables perfect quantum communication with zero capacity channels**, New Journal of Physics 23, 033039 (2021), arXiv:1810.10457v4.
https://arxiv.org/html/1810.10457v4
Known perfect-activation mechanism for the 50/50 X/Y channel; fixed provider order-control preparation/readout; no first-activation claim is made here. Our different c_A,c_B formula is a direct expansion of the same switch.

[2] S. Pirandola, R. Laurenza, C. Ottaviani, L. Banchi, **Fundamental limits of repeaterless quantum communications**, Nature Communications 8, 15043 (2017), arXiv:1510.08863.
https://arxiv.org/html/1510.08863
Pauli-channel teleportation simulation, adaptive stretching and relative-entropy bounds. The finite heralded-fidelity inequality in PROOF.md is derived explicitly, rather than inferred by dividing by an asymptotic rate.

[3] S. Pirandola et al., **Theory of channel simulation and bounds for private communication**, Quantum Science and Technology 3, 035009 (2018), arXiv:1711.09909v2.
https://arxiv.org/html/1711.09909v2
Accessible exposition of nonasymptotic adaptive-to-block stretching and dephasing entanglement flux, especially Sections V and VI.2.

[4] C. H. Bennett, D. P. DiVincenzo, J. A. Smolin, W. K. Wootters, **Mixed-state entanglement and quantum error correction**, Physical Review A 54, 3824 (1996), arXiv:quant-ph/9604024.
https://arxiv.org/html/quant-ph/9604024
One-way entanglement purification / quantum-code equivalence and a five-qubit single-error-correcting code. The 5-input finite Bernoulli bound is evaluated in this package.

[5] D. Main et al., **Distributed quantum computing across an optical network link**, Nature 638, 383-388 (2025), arXiv:2407.00835.
https://www.nature.com/articles/s41586-024-08404-x
https://arxiv.org/abs/2407.00835
Actual distributed-computing motivation: Bell pairs feed remote entangling gates. Its apparatus is NOT asserted to satisfy our proposed noise/switch parameters. The published gate fidelity is not used in our hypothetical budget.

[6] H. Kristjansson et al., **Resource theories of communication**, New Journal of Physics 22, 073014 (2020), arXiv:1910.08197v3.
https://arxiv.org/html/1910.08197v3
Formal resource accounting for channel placement, local wiring, coherent control, and no side-channel requirement. Relevant to why the resource model must be explicit.

[7] P. A. Guerin, G. Rubino, C. Brukner, **Communication through quantum-controlled noise**, Physical Review A 99, 062317 (2019), arXiv:1812.06848.
https://arxiv.org/abs/1812.06848
Alternative definite-order quantum-controlled processes can match or exceed some switch advantages; the authors dispute causal-order-only interpretations. This package does not settle that debate or claim superiority over arbitrary extra coherent-path interfaces.

[8] M. Caleffi and A. S. Cacciapuoti, **Quantum Switch for the Quantum Internet: Noiseless Communications Through Noisy Channels**, IEEE Journal on Selected Areas in Communications 38, 575-588 (2020).
https://ieeexplore.ieee.org/document/8966996/
https://arxiv.org/abs/1907.07432
Prior engineering-oriented analysis of switch-assisted entanglement distribution and teleportation. The use case is not new merely because we name a remote-gate workload.

[9] **Fundamental limits on polarization entanglement distribution in optical fiber**, Physical Review Research 8, 033222 (2026), DOI 10.1103/xqrp-xrby.
https://journals.aps.org/prresearch/abstract/10.1103/xqrp-xrby
Use of erasure-Pauli and dephasing-dominated models for practical entanglement distribution. It does not establish our native coherent switch or chosen parameter combination. No figures or PDF tables from this paper were used.

[10] **Demonstration of a Quantum Switch in a Sagnac Configuration**, Physical Review Letters 131, 060803 (2023), DOI 10.1103/PhysRevLett.131.060803.
https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.131.060803
Photonic switch implementation; not evidence for the complete specific network, storage, loss and fault assumptions made in PROOF.md.

[11] A. Seif et al., **Entanglement-enhanced learning of quantum processes at scale**, arXiv:2408.03376.
https://arxiv.org/html/2408.03376v1
Ordinary entanglement-assisted process-learning baseline. The product-local two-copy support test in BASELINES.md is derived here, without a novelty claim.

## Attribution summary

Published ingredients: communication activation; quantum-channel simulation by Choi resources; REE monotonicity; stabilizer purification; remote gate teleportation; resource-model debate.

Derived in this note: the explicit 99%/99% service operating point, one-output finite lower bound, exact stopping probabilities, the stated robustness ledger, rational arithmetic checks, and the product-local noise-baseline calculation.

Not established: a hardware implementation meeting all assumptions; a novel activation mechanism; a huge advantage for unrestricted local black-box channel characterization; superiority over every causal coherent-path apparatus.
