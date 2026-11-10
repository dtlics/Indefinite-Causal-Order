<a id="nr-r23"></a>

# Matched-fidelity noise-model validation

[Investigation handoff](README.md) · [Application assessment](../architecture.md)

**Status and scope.** Core application candidate. The large query separation inherits the existing hidden-basis theorem; no realistic local-noise advantage is established. Supplied analytical derivations and scoped checks; not a new Lean audit or a publication-priority claim.

## 2. Task and access convention

All square channels act on dimension d=2^n unless stated otherwise. They return a quantum output. Their classical measurement records, Kraus labels, hidden basis descriptions, and coherent Stinespring ports are not available unless explicitly granted.

An ordinary algorithm may prepare entangled probes, retain arbitrary finite quantum memory, apply arbitrary known instruments, choose the next device through classical adaptation, and perform collective final measurements. Calibration, rejection histories, and every invocation count. The lower bound is not a restriction to tomography, product measurements, stabilizer processing, or bounded memory.

The switch user additionally receives a standard, representation-independent, paired-history channel switch. A switch on powers E^k must be an explicitly available coherent ordering of those whole blocks. It is not inferred merely from availability of a primitive classical channel port. All 2k elementary contacts count.

Use

    D(E,F) = ||E-F||_diamond / 2,

and

    v(A,B) = Re sum_ij Tr(A_i^† B_j^† A_i B_j) / d,
    p_-(A,B) = (1-v(A,B))/2.

For independent calls to a fixed channel E, write v(E,E) for its self-switch visibility. “Independent” means fresh call-local meters, not a new hidden basis at each call.

No statement below identifies NCOM with arbitrary POVM joint-measurability incompatibility.

## 3. General model-rejection certificate

### Proposition 1: a scalar discrepancy certifies channel-model mismatch

Let E be an actual fixed memoryless channel and M a proposed model. Then

\[
D(E,M)\ge\frac14|v(E,E)-v(M,M)|. \tag{1}
\]

**Proof.** For a fixed channel in one switch slot, the remaining slot is a deterministic superchannel. It has a chronological realization using a controlled dilation of the fixed channel and therefore contracts diamond distance. Replacing the two slots successively gives

\[
D(S[E,E],S[M,M])\le2D(E,M).
\]

On the specified input, measuring a norm-one X observable changes its expectation by at most twice the output trace distance. Therefore the visibility difference is at most 4D(E,M). This is a mathematical fixed-arm realization, not a grant of an unknown dilation to a learner. QED.

This is a sound, one-sided falsification certificate. Agreement does not certify correctness: every unitary has self-visibility one, including unitaries very far from the intended identity.

### Statistical version

Estimate the actual visibility from N independent +/-1 results. With failure probability at most delta,

\[
|\hat v_E-v(E,E)|\le e_N,
\qquad e_N=\sqrt{2\log(2/\delta)/N}.
\]

If the model prediction has certified error e_M and the readout/implementation adds a separately justified visibility bias at most b, then

\[
D(E,M)\ge\frac{[|\hat v_E-\hat v_M|-e_N-e_M-b]_+}{4}. \tag{2}
\]

The combined coverage must be valid; repeated searches and adaptive stopping require allocated failure probabilities or confidence sequences. A model-dependent bias budget is not inferred from detector fidelity alone.

For a sampleable Pauli model M(rho)=sum_P p_P P rho P, the model visibility is the classical expectation of the commutation sign of two independent Pauli samples. This makes the prediction inexpensive. It does not make actual non-Pauli noise easy to learn.

### Consequence for inverse-model PEC

Assume M is invertible as a linear map and an idealized signed mitigation estimator applies M^{-1} after the actual E. Define R=M^{-1}E; it need not be CP. Then

\[
\tfrac12\|R-\mathrm{id}\|_\diamond
\ge D(E,M)
\ge\tfrac14|v(E,E)-v(M,M)|. \tag{3}
\]

Indeed, E-M=M(R-id), and left composition by the CPTP map M contracts the diamond norm. Thus a failed model test certifies a nonzero **worst-case residual bias** even with noiseless implementation of the modeled inverse. Actual noisy cancellation operations need separate accounting.

The witness may depend on an unknown input/reference and observable. Equation (3) does not say that every observable in a particular algorithm has this bias, and it is not a replacement for observable-aware mitigation such as [L6].

## 4. Matched-fidelity noise models: explicit separation

Fix 0<p<=1 and a hidden orthonormal basis U. Define

\[
E_{p,U}=(1-p)\mathrm{id}+p\Delta_U,
\quad
\Lambda=\frac{\mathrm{id}+d\Omega}{d+1},
\quad
M_p=(1-p)\mathrm{id}+p\Lambda.
\]

Write

\[
q=\frac{pd}{d+1},\qquad \alpha=1-q,
\qquad M_p=\alpha\mathrm{id}+(1-\alpha)\Omega. \tag{4}
\]

Here E_{p,U} has a fixed, persistent pointer basis. M_p is a known memoryless depolarizing model. The alternative channels E_{p,U} are themselves memoryless, conditional on their fixed U. This binary model-validation problem need not be described as quantum non-Markovianity.

### Proposition 2: calibration summaries, switch gap, and exact channel distance

For every U,

\[
F_e(E_{p,U})=F_e(M_p)=1-p+p/d, \tag{5}
\]

\[
F_{\rm avg}(E_{p,U})=F_{\rm avg}(M_p)
=1-\frac{p(d-1)}{d+1}. \tag{6}
\]

Using the standard unital-channel unitarity,

\[
u(E_{p,U})=\frac{1+d(1-p)^2}{d+1},
\quad u(M_p)=\alpha^2,
\quad u(E_{p,U})-u(M_p)=\frac{p^2d}{(d+1)^2}. \tag{7}
\]

The self-switch values are

\[
v(E_{p,U},E_{p,U})=1,
\quad v(M_p,M_p)=1-p^2\frac{d-1}{d+1}, \tag{8}
\]

while their channel distance is exactly

\[
D(E_{p,U},M_p)=p\frac{d-1}{d+1}. \tag{9}
\]

**Proof of calibration identities.** A Kraus list for E is sqrt(1-p)I together with sqrt(p)P_i. Hence its identity entanglement fidelity is 1-p+p/d. For M, F_e=alpha+(1-alpha)/d^2, which is the same. The usual average-fidelity relation gives (6). On traceless operator space E has eigenvalue 1 on the d-1 diagonal traceless directions and 1-p on the d^2-d off-diagonal directions. Its unitarity is the mean squared singular value on that space, giving (7).

All Kraus operators of E commute, proving its visibility. Bilinearity and v(id,N)=1 give v(M,M)=1-q^2(1-d^{-2}), which simplifies to (8).

**Proof of the distance, including the upper bound.** In the U-rotated Weyl basis, Delta_U is the uniform mixture over d commuting phase operators. Omega is uniform over all d^2 Weyl operators. The difference Delta_U-Lambda has zero identity coefficient, positive coefficient 1/(d+1) on d-1 nonidentity phase operators, and negative coefficient -1/[d(d+1)] on the d^2-d remaining operators. The coefficient l1 norm is 2(d-1)/(d+1), giving the diamond upper bound. The normalized Choi states diagonalize in orthogonal Weyl-error states and saturate it. Multiplication by p gives (9). QED.

Interpretation: average gate fidelity is exactly blind to this distinction. Fixed-precision unitarity does not resolve the O(p^2/d) difference at large d. The switch gap is O(p^2), independent of d for fixed p. This does not claim that all randomized-benchmarking data, all conceivable higher-order benchmarking tests, or all ordinary observations are identical. The all-strategy lower bound requires the separate dependency below.

### Exact finite-depth model error

For every integer m>=1,

\[
E_{p,U}^m=(1-p)^m\mathrm{id}+[1-(1-p)^m]\Delta_U,
\quad
M_p^m=\alpha^m\mathrm{id}+(1-\alpha^m)\Omega,
\]

and

\[
\boxed{D(E_{p,U}^m,M_p^m)=(1-1/d)(1-\alpha^m).} \tag{10}
\]

The lower bound is achieved by any hidden basis state. For the upper bound, use the same common Weyl representation. Coefficients outside the phase subgroup are all negative. The nonidentity phase coefficients are positive. The identity coefficient is nonnegative because the function x^m is convex on [0,1]: the mean of the mth powers of E's traceless eigenvalues is at least the mth power of their mean alpha. Summing the negative coefficients gives (10), and the Choi test again saturates the bound.

Thus m=Theta(1/p) contacts can produce an order-one discrepancy in the predicted complete channel even though every one-step average fidelity agrees. The distinguishing inputs or optimal measurements depend on the hidden structure; no efficiently known witness is being given to the ordinary learner.

M predicts forgetting:

\[
D(M_p^m,\Omega)=\alpha^m(1-1/d^2).
\]

In contrast, E fixes every P_i, so D(E^m,Omega)>=1-1/d. This is a finite-time information-erasure qualification endpoint, not merely an asymptotic capacity statement.

### Exact inverse-model failure

The signed inverse-model map after m contacts is R_m=M_p^{-m}E_{p,U}^m. On a hidden eigenstate P_i,

\[
R_m(P_i)=\alpha^{-m}P_i+(1-\alpha^{-m})I/d.
\]

Its half trace-norm difference from P_i is

\[
(\alpha^{-m}-1)(1-1/d). \tag{11}
\]

The bounded observable 2P_i-I has expectation bias twice that value. This explicitly realizes a QEM model-failure witness; the signed output need not be a physical state. It does not supply P_i or its measurement implementation to a practitioner for free.

## 5. Conditional ordinary-query lower bound

### Dependency H, taken from the repository

The C5 endpoint bounds the final states of every ordinary q-contact learner under a fixed Haar-hidden Delta_U and Omega by

\[
B(q,d)=\frac{18(2q)(2q+1)}{d^{1/8}}
       +\frac{4q}{\sqrt{d-2q}}+\frac{q^2}{d}.
\]

In the stated small-query regime q<=d^{1/16}/100 it gives B<=0.0509. Because D(Lambda,Omega)<=1/(d+1), the same learner on Delta_U versus Lambda has final half trace distance at most B+q/(d+1)<=0.0609. Equal-prior success is consequently at most 0.53045.

This is quoted as a hypothesis, not reproved. It is the actual all-adaptive physical endpoint used by the repository's NR-R22; it is stronger information than merely quoting a full-switch simulation obstruction.

### Theorem 3: weak-noise model validation requires Omega(d^{1/16}/p) ordinary contacts

Promise the unknown physical channel is either M_p or E_{p,U}, with U fixed and hidden. An ordinary algorithm that succeeds with probability at least 2/3 on every U and on M_p has

\[
Q_{\rm ordinary}=\Omega(d^{1/16}/p). \tag{12}
\]

The statement also holds for average query cost under the balanced hard prior, for finite/almost-surely terminating strategies with the required finite mean.

**Proof.** Start from a strong oracle that is either Delta_U or Lambda. Simulate each weak-channel contact by an independent Bernoulli-p coin: on success call the strong oracle, otherwise apply identity. This exactly implements E_{p,U} or M_p, even with retained entangled memory. The mean number of strong contacts is p E[Q]. Let L=floor(d^{1/16}/100)>=1. Truncate before an (L+1)st strong contact. Markov's inequality bounds the probability of truncation by p E[Q]/L. If E[Q]<=L/(12p), balanced success after truncation is at least 2/3-1/12=7/12, contradicting H's upper bound 0.53045. For unbounded known-processing times, truncate them separately with arbitrarily small additional loss under the stated halting condition. QED.

This is an application/reduction of C5, not an independent new lower-bound technique. The explicit constants are very conservative and do not certify a useful small-device crossover.

### Why replayable noise and public descriptions invalidate the premise

If U is supplied as an efficient circuit, its channel can be compiled coherently and the hidden-oracle lower bound does not apply. If a device is promised to be a Pauli channel in a known basis, Bell sampling is available. If individual random-unitary realizations can be selected and replayed, sample the two realizations and apply the ordinary three-query unitary switch simulation; averaging reproduces the channel switch. A random-time Hamiltonian simulator controlled by the experimenter often grants precisely this stronger interface.

An efficiently generated pseudorandom hidden basis could replace Haar under the repository's stated inverse-secure cryptographic assumptions. That gives a computational hardness statement for efficient learners, not the same unconditional information-theoretic theorem for the finite family.

## 6. Switch protocol and optimal weak-noise scaling

### Primitive self-switch

Using two E invocations gives

\[
p_- =0\quad\text{under structured noise},\qquad
p_-=\frac{p^2(d-1)}{2(d+1)}\quad\text{under the model}. \tag{13}
\]

Declare MODEL if any minus occurs; otherwise declare STRUCTURED. The false-MODEL probability is zero in the ideal promised setting. The false-STRUCTURED probability after N independent trials is (1-p_-)^N. This uses O(p^{-2} log(1/delta)) primitive contacts.

### Theorem 4: switched-block amplification

Assume coherent switching of two whole k-contact blocks is available. Let

\[
k=\lceil1/q\rceil,\qquad q=pd/(d+1).
\]

Then the structured block remains a mixture of identity and one fixed dephaser, with commuting Kraus operators, so its self-switch minus probability is zero. The model block is depolarizing with parameter 1-alpha^k, giving

\[
p_{-,k}=\frac12(1-\alpha^k)^2(1-d^{-2})
\ge p_*:=\frac38(1-e^{-1})^2>0.149. \tag{14}
\]

A number of block trials O(log(1/delta)) therefore suffices, and the elementary-contact cost is

\[
Q_{\rm switch}=O(p^{-1}\log(1/\delta)). \tag{15}
\]

There is no postselection: every trial returns a decision sample and every elementary call is counted.

Together with (12), at fixed error probability the conditional separation is

\[
Q_{\rm ordinary}=\Omega(d^{1/16}/p),
\qquad Q_{\rm switch}=O(1/p).
\]

For very large p, a primitive trial can be cheaper than the chosen block policy. The O(1/p) statement is an asymptotic weak-noise scaling, not an assertion that this k minimizes every finite-instance cost.

### Optimality in p

Any bounded-contact circuit built from known CPTP maps and standard switches has a slotwise hybrid bound: its final trace distance between the two hypotheses is at most Q D(E_{p,U},M_p)<=Qp. Each fixed one-slot higher-order transformation is diamond-contracting. Equal-prior success 2/3 needs trace distance at least 1/3. Hence Q>=1/(3p). The amplified protocol is order-optimal in p within this primitive-contact accounting, at fixed confidence.

### Unknown p

The same entanglement fidelity occurs under both hypotheses. An ordinary Bell test fails with probability p(1-1/d), allowing constant-relative estimation of p using O(p^{-1} log(1/delta)) calls. A valid lower confidence bound on p selects a conservative block length. Thus supplying p is not essential for the order scaling, provided the input has a positive-noise promise and the calibration apparatus/reference cost is charged. Uniform finite-cost discrimination at p=0 is impossible because the hypotheses coincide.

### Implementation noise and storage

If each actual contact is within half-diamond distance zeta of its promised nominal map, a 2k-contact block-switch output differs by at most 2k zeta. Let b be a separate bound on the measurement event error from routing/control/readout. If

\[
2k\zeta+b\le p_*/4,
\]

the two minus-event probabilities remain separated around threshold p_*/2. Hoeffding gives a fixed, dimension-independent number of trials. The required per-contact nuisance tolerance scales as O(p), and the order control must remain coherent across O(1/p) contacts. Fixed apparatus noise cannot be ignored as p tends to zero.

If each contact costs time tau, include 2k tau plus routing and reset time per trial; control dephasing over that interval and heralded loss must be measured. A contact saving is not automatically a time, gate, or memory saving.

## 7. Capacity consequence and its finite-code boundary

For p=3/4, the fitted model has q=3d/[4(d+1)]>=1/2. It is postprocessing of an erasure channel with erasure probability q, hence has zero unassisted quantum capacity.

For the structured channel, use its d mutually orthogonal commuting phase-error unitaries. At input I/d its coherent information is

\[
I_c=n-H(1-p+p/d,p/d,\ldots,p/d)
\ge(1-p)n-h_2(p).
\]

Therefore

\[
Q(E_{3/4,U})\ge n/4-h_2(3/4)>0\quad(n\ge4),
\qquad Q(M_{3/4})=0. \tag{16}
\]

This capacity implication is closely related to the already-existing NR-R20/NR-R22 results. It is not claimed as a new coding theorem, the first capacity test, or an efficient decoder construction. The additional point here is that the same pair has exactly matched average fidelity and the finite-depth discrepancy (10).

### Proposition 5: a supplied-code/known-workload test limits what can be claimed

Suppose one fixed ordinary workload J, requiring L unknown-channel contacts, has an accessible bounded score whose mean differs by at least gamma between the two promised channel classes, uniformly over their unknown members. Independent repetitions of J and Hoeffding give an ordinary classifier using O(L gamma^{-2}) contacts at fixed confidence. Under Theorem 3,

\[
L/gamma^2=\Omega(d^{1/16}/p). \tag{17}
\]

Thus these hard families cannot simultaneously admit a supplied, short, uniformly successful ordinary test with a constant score gap. A working finite code and decoder plus an ordinary logical Bell test is such a test when it distinguishes the hypotheses.

This is not a failure of the capacity theorem: its coding limit can involve large blocks and unknown-channel-dependent training. It explains why an existence-of-code qualification must not be advertised as immediate finite-code runtime improvement. The repository already states a more specific finite-block obstruction for NR-R22.

The practitioner endpoint supported here is **uniform model qualification before a usable code or a known worst-case witness is supplied**. For a particular known observable or known code, use direct ordinary tests first.


## Related owners

Existing noise-memory, capacity and forgetting results retain their sources in [noise-model selection](../noise-model-selection.md), [memory qualification](../memory-qualification.md), and [C6 applications](../../c6-hidden-dephasing/applications.md). The [ordinary baselines](ordinary-baselines.md) qualify the claimed scope.

### Primary literature used

[L1] Gao et al., *Measuring incompatibility and clustering quantum observables with a quantum switch*, PRL 130, 170201 (2023), arXiv:2208.06210v4. Source of MED/NCOM and the switch estimator; not a new protocol in this note.

[L2] Bavaresco et al., *Simulating the quantum switch with quantum circuits is computationally hard*, Nature Communications 16, 10216 (2025), arXiv:2409.18202v2. Repeated-query simulation and the unitary-member construction.

[L3] Wallman et al., *Estimating the Coherence of Noise*, New Journal of Physics 17, 113020 (2015), arXiv:1503.07865. Unitarity and ordinary coherence benchmarking.

[L4] Harper and Flammia, *Learning Correlated Noise in a 39-Qubit Quantum Processor*, PRX Quantum 4, 040311 (2023), DOI 10.1103/PRXQuantum.4.040311. Motivation for predictive error models and correlated-noise baselines.

[L5] van den Berg et al., *Probabilistic error cancellation with sparse Pauli–Lindblad models on noisy quantum processors*, Nature Physics 19, 1116–1121 (2023), arXiv:2201.09866. Practical model-based noise inversion.

[L6] Eddins, Tran, and Rall, *Lightcone shading for classically accelerated quantum error mitigation*, arXiv:2409.04401. Observable-sensitive mitigation, distinct from a worst-case channel certificate.

[L7] White et al., *Non-Markovian Quantum Process Tomography*, PRX Quantum 3, 020344 (2022), DOI 10.1103/PRXQuantum.3.020344. Ordinary multi-time characterization and predictive control.

[L8] Pfister et al., *Capacity estimation and verification of quantum channels with arbitrarily correlated errors*, Nature Communications 9, 27 (2018), arXiv:1611.05411. Capacity certification without full tomography predates this proposal.

[L9] Seif et al., *Entanglement-enhanced learning of quantum processes at scale*, arXiv:2408.03376. Strong ordinary Pauli-learning comparator.

[L10] Pandey et al., *Adiabatic eigenstate deformations as a sensitive probe for quantum chaos*, PRX 10, 041017 (2020), arXiv:2004.05043. Scientific relevance of eigenstate sensitivity and adiabatic gauge potentials.

[L11] Kammerlander et al., *The Compendium of Super-Quadratic Computational Quantum Advantages*, arXiv:2610.32595v1, Section 5.1. Ordinary quantum-versus-classical OTOC task, not a switch-versus-circuit separation.

[L12] Wei et al., *Direct estimation of quantum channel incompatibility via a quantum switch*, Science China Information Sciences 68, 180502 (2025), DOI 10.1007/s11432-025-4500-8. Direct noisy-channel experiments and tomography comparisons already exist.

[L13] Loizeau and Grinbaum, *Channel capacity enhancement with indefinite causal order*, PRA 101, 012340 (2020), arXiv:1906.08505. Self-channel noncommutativity and communication relationships are prior work.

[L14] Liu, Hu, Yuan, and Yang, *Fully-Optimized Quantum Metrology: Framework, Tools, and Applications*, arXiv:2409.07068. Optimized finite-query ordinary/switch comparisons; no new calibration advantage is claimed here.

[L15] Xie et al., *Noise-Agnostic Unbiased Quantum Error Mitigation for Logical Qubits*, PRL 136, 010603 (2026), arXiv:2504.12864. An important model-light ordinary QEM comparator when its Pauli-error-sampling interface is available.

[L16] Devetak, *The private classical capacity and quantum capacity of a quantum channel*, IEEE TIT 51, 44–55 (2005), arXiv:quant-ph/0304127. Coherent-information coding direct theorem.

[L17] Chiribella, D’Ariano, and Perinotti, *Memory effects in quantum channel discrimination*, PRL 101, 180501 (2008), arXiv:0803.3237; *Theoretical framework for quantum networks*, PRA 80, 022339 (2009), arXiv:0904.4483. Causal-tester framework for the independent finite-query certificate.

[L18] Collins and Śniady, *Integration with respect to the Haar measure on unitary, orthogonal and symplectic group*, CMP 264, 773–795 (2006), arXiv:math-ph/0402073. Exact Haar-moment methods.

[L19] Chiribella, *Perfect discrimination of no-signalling channels via quantum superposition of causal structures*, PRA 86, 040301(R) (2012), arXiv:1109.5154. Prior switch discrimination advantage; no first-discrimination-advantage claim is made here.

