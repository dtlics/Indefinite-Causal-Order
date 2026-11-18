# Quantum-switch applications: code-aware recovery and natural black-box boundaries

**Research date:** 17 November 2026.

**Status:** analytical derivations, exact combinatorial checks, floating-point channel identities, and numerical recovery optimizations. Preserved on the `more-applications` branch as exploratory research. No publication-priority claim. This is a further investigation, not a claim that the original large practical-advantage objective is solved.

<a id="section-0"></a>

## 0. Scope and what changed

The objective is a substantial advantage for an existing quantum-computing/QEC task under a natural opaque-device interface. Unknown channel probabilities, a nonzero commutator, a better postselected fidelity, or beating a deliberately fixed decoder are not sufficient. The ordinary competitor receives the genuinely available state preparation, quantum memory, syndrome records, known controls, and encoding choices.

This round tests: completed and partial opaque recovery modules; coherent correlated faults; independent and collective nonunital relaxation; bosonic loss/gain and number dephasing; fermionic-mode loss; partial measurement records; rare logical errors; and channels whose unknown behavior can be extracted as a quantum program. It also audits a recent QEC/sensing proposal.

The numerical workload comprises 57 spin-code/noise configurations and 12 finite-level oscillator configurations. Eight two-qubit configurations additionally receive primal/dual recovery optimization. Separate scripts test 60 full recovery-channel identities, 54 self-switch identities, 42 program-state identities, 40 coherent-error code constructions, ordinary noiseless-subsystem comparators, 55 exact graph counts, 32 coarse-record cases, and 48 fermionic-mode pairs. Parameter points are not distinct application mechanisms.

**Main positive construction:** a flag can separate arbitrary coherent errors into two correctable operator spaces and restore a prescribed code exactly without learning the channel coefficients. The explicit example is also defeated by intermediate ordinary recovery or a different ordinary noiseless-subsystem encoding. It is a synthesis rule, not yet an all-ordinary advantage.

**Main exact baseline:** two unknown CPTP recovery maps returning everything to the same known code and fixing that code have a full-switch simulator with at most one unknown call. Their device outcomes need not be accessible.

**Main weak-noise limitation:** a self-switch is exactly a two-branch quantum instrument. Its best unconditional fidelity improvement is at most the rare antisymmetric-branch weight. For commuting jump operators this cannot remove a leading quadratic code-error term in a short-time cycle.

<a id="section-1"></a>

## 1. Conventions and targets

Channels are square, fixed, memoryless CPTP maps with independently reset private environments. Each labeled invocation is paired across its coherent histories according to the standard SWITCH; shared quantum bath memory or arrival-time-dependent maps require another model.

For A={A_i}, B={B_j},

$$
W_{ij}=|0\rangle\langle0|\otimes B_jA_i+|1\rangle\langle1|\otimes A_iB_j.
$$

On a plus control, X readout gives

$$
K^\pm_{ij}=(B_jA_i\pm A_iB_j)/2,\qquad
\mathcal M_\pm(\rho)=\sum_{ij}K^\pm_{ij}\rho K^{\pm\dagger}_{ij}.
$$

For maximally mixed target,

$$
p_-=(4d)^{-1}\sum_{ij}\|[B_j,A_i]\|_F^2.
$$

For encoded data, probabilities instead use the actual encoded input or its reference purification. All logical fidelities below are identity entanglement fidelities for the maximally mixed logical qubit, and all control branches are counted. A conditional normalized score is not automatically a linear channel or a worst-case logical-error bound.

Known gate processing is free only in the query model. Its circuit size, ancillary space, error, and measurement time remain separate implementation costs. The tests below do not quietly impose a communication cut or remove a clean local bypass to rescue a noise-correction claim.

<a id="section-2"></a>

## 2. Exact full simulation for completed opaque QEC recoveries

### Theorem 1

Let P be a known code projector and Q=I-P. Suppose R and S are unknown CPTP maps satisfying:

1. every output is supported on P;
2. every state supported on P is fixed pointwise.

Then the full SWITCH of R,S on arbitrary control-target-reference inputs is implemented by an ordinary circuit with **at most one query to either R or S** and a known coarse code-membership measurement {P,Q}.

The maps need not have accessible outcome records, be Pauli, or have the same recovery action on errors.

### Kraus normal form

Each map admits a Kraus family

$$
R=\{P,R_\alpha\},\quad R_\alpha=PR_\alpha Q,
\qquad
S=\{P,S_\beta\},\quad S_\beta=PS_\beta Q.
$$

Proof: preserving every pure code state implies that each Kraus restriction to P is a scalar times the identity on P. Linearity on superpositions makes the scalar independent of the code vector. Rotate the Kraus family so that the first restriction is P and the others vanish on P. Trace preservation on the P-Q offdiagonal block then forces the first Kraus operator's Q part to vanish. The output-range condition supplies the left P on the remaining Kraus operators.

Consequently, R_alpha S_beta=S_beta R_alpha=0, P R_alpha=R_alpha, R_alpha P=0, and similarly for S. For a control-block input sigma,

$$
\mathcal S[R,S](\sigma)=
\begin{pmatrix}
R(\sigma_{00})&P\sigma_{01}P\\
P\sigma_{10}P&S(\sigma_{11})
\end{pmatrix}.
$$

### Ordinary circuit

Measure only {P,Q}. On P, retain the control coherently and do nothing. On Q, measure the control in Z; query R for control zero and S for control one, then return that classical control label and the output. This gives exactly the displayed map, including its action on references.

**Do not replace the coarse measurement by an unnecessarily refined syndrome measurement for arbitrary R,S.** Resolving which error syndrome can destroy Q-Q coherences that a general recovery uses. For a known stabilizer code, implement a coherent syndrome extraction, compute the all-zero/nonzero indicator, uncompute the fine syndrome, and measure only the indicator. This costs known gates/ancillas; the theorem is a query construction, not a gate-free hardware assertion. For ordinary syndrome-resolving recovery policies, their finer record is already compatible with the map.

If the actual maps are within half-diamond distances delta_R,delta_S of such ideal maps, the same circuit using the actual boxes has full-switch error at most

$$
\delta_R+\delta_S+\max(\delta_R,\delta_S).
$$

This follows by comparing the native switch and simulator separately to the ideal construction. It is at most 3 delta for equal bounds.

**Boundary:** different codes, nontrivial logical operations, unknown code projectors, finite-time incomplete return, subsystem gauges not reduced to this subspace model, and nonmemoryless feedback are not covered.

[retraction_tests.py](experiments/retraction_tests.py) checks arbitrary unrelated retractions, randomly rotated known code projectors, and full Choi matrices in five dimension/code-size combinations. The largest of 60 residuals was below 7e-16.

### Partial recovery modules

On code/error syndrome sectors, consider

$$
A_0=P+\sqrt{1-a}Q,\quad A_1=\sqrt a\,U\otimes|0\rangle\langle1|,
$$

and B with strength b and arbitrary logical unitary V. Direct calculation gives

$$
E_-=
rac{a(1-\sqrt{1-b})^2+b(1-\sqrt{1-a})^2}{4}Q.
$$

The probability is independent of the chosen feedback unitaries U,V. The minus map is a mixture of the corresponding corrected outputs, not a coherent comparison of their logical quality. At a=b small, its probability on the error sector is a^3/8+O(a^4). Sixteen parameter combinations with unrelated feedback unitaries were checked.

<a id="section-3"></a>

## 3. How much can the same-run flag help a decoder?

### Theorem 2: exact self-switch instrument and approximation distance

For one channel E used twice, define M_+,M_- as above. For arbitrary control-target inputs,

$$
\mathcal S[E,E]
=(\mathrm{id}_C\otimes\mathcal M_+)
 +(\operatorname{Ad}_{Z_C}\otimes\mathcal M_-).
$$

The mixed symmetric/antisymmetric Kraus terms cancel on exchanging their indices. Also M_++M_-=E^2. Thus the ordinary circuit that applies E twice and leaves the controller unchanged obeys

$$
\boxed{\tfrac12\|\mathcal S[E,E]-\mathrm{id}_C\otimes E^2\|_\diamond
=\|E_-\|_\infty,\quad E_-=\sum K_-^\dagger K_-.}
$$

The upper bound uses the diamond norm of a CP map, ||M_-||_diamond=||M_-^dagger(I)||_infinity, and ||Ad_Z-id||_diamond=2. Equality is attained with a plus controller and a target eigenvector of E_- with largest eigenvalue. References do not increase the bound.

With plus input, the self-switch output is classical in the X basis. Keeping the control coherent cannot improve on optimal flag-conditioned decoding, because no offdiagonal X-basis blocks remain.

### Fidelity gain bound

For any two-outcome instrument M_+,M_- and fixed encoded Bell input, let p_s be its branch probabilities. Let F_flag be the best entanglement fidelity using the flag and F_unflag the best fidelity after discarding it. Then

$$
0\le F_{\rm flag}-F_{\rm unflag}\le\min(p_+,p_-).
$$

Proof: apply the optimal plus-branch recovery also to the minus branch of the unflagged channel. The loss compared with choosing the optimal minus recovery is at most the total minus weight, because each subnormalized fidelity lies between zero and that weight. Exchange the roles for the other bound.

For a self-switch this bounds **all** final decoders, including joint processing of the control and physical data. It is not merely a property of the chosen numerical decoder. For a heterogeneous A,B pair, a retained quantum control can contain additional information; the purely classical-flag bound alone does not cover arbitrary coherent decoding.

### Weak-noise consequence

For E_t=e^{t L} in finite dimension,

$$
p_-(\rho)=\frac{t^2}{4}\sum_{ab}\operatorname{Tr}([L_a,L_b]\rho[L_a,L_b]^\dagger)+O(t^3).
$$

If the jump operators commute, p_-=O(t^3). Therefore a fixed-code serial optimum with a leading c t^2 logical infidelity cannot have that leading term removed by a self-switch followed by arbitrary final recovery: the gain is only O(t^3).

For independent qubit amplitude damping with gamma and h=1-sqrt(1-gamma), the exact self-switch effect is

$$
E_-^{(n)}=\tfrac12\left[I-\bigotimes_{j=1}^n(I-\gamma h^2|1\rangle\langle1|_j)\right].
$$

On the four-qubit amplitude-damping code [R2], the encoded maximally mixed state has excitation weights 1/4 at 0, 1/2 at 2, 1/4 at 4. Put f=1-gamma h^2. Then

$$
p_-=\tfrac12[1-(1+f^4)/4-f^2/2]=\gamma^3/4+O(\gamma^4).
$$

At gamma=.01 this bounds any same-code final-decoder fidelity improvement by about 2.51e-7. A decoder cannot turn this into elimination of a quadratic logical-failure term by a more clever final readout.

[self_switch_bound.py](experiments/self_switch_bound.py) verifies 54 full-channel identities and saturation inputs, plus the exact code formula at five strengths.

<a id="section-4"></a>

## 4. Constructive code-aware cancellation of arbitrary coherent faults

This is a positive algebraic construction, followed by a complete baseline screen. It is not a claim that the final architecture beats all ordinary strategies.

Use three physical qubits, with the first two initially |00> as syndrome qubits and the third carrying the unknown logical state. Define

$$
G_1=X_1,\quad G_2=Z_1X_2,\quad
L=Z_3,\quad G_3=iG_1G_2L=Y_1X_2Z_3.
$$

The G_i are Hermitian involutions, mutually anticommute, and commute with L. They map the code into three different syndrome sectors. The operator space

$$
\mathfrak E=\operatorname{span}\{I,G_1,G_2,G_3\}
$$

is correctable by a known recovery on this code. The physical noise may have arbitrary coherent Kraus combinations in this space; it need not be a stochastic Pauli mixture and no coefficients are learned.

Let both arbitrary CPTP slots have Kraus operators in E. Their anticommutators belong to E and commutators belong to L E. Hence

$$
K^+_{ij}\in\mathfrak E,\qquad K^-_{ij}\in L\mathfrak E.
$$

After the switch, apply L on the minus flag, then the ordinary E-recovery. The complete logical map is exactly identity for every input, with no rejected branch. Forty random non-Pauli random-unitary mixtures in this span were verified. Fixed ordinary final recovery fidelities ranged approximately .5136 to .9984; flagged correction was one up to roundoff.

The mechanism is useful: **the flag identifies which error space is present**, not just whether an error occurred. In general one should seek branch-wise Knill-Laflamme conditions

$$
P K_{\alpha}^{s\dagger}K_{\beta}^{s}P=c^s_{\alpha\beta}P
$$

with a recovery that does not require unknown channel information. This is an application of standard QEC criteria, not a new version of the Knill-Laflamme theorem.

### Why this example is not yet a switch advantage

Ordinary recovery between the two calls fixes each layer exactly. More decisively, the known error algebra has a noiseless subsystem at the same three-qubit size. Fix Z3=+1. Logical operators

$$
\overline Z=X_2,\qquad\overline X=X_1Z_2
$$

commute with every G_i and anticommute with each other. A known Clifford encoding stores the logical qubit in this multiplicity subsystem while the noise acts on a gauge subsystem. Twenty independent channel pairs verified exact ordinary preservation.

Thus the construction upgrades a **fixed delayed-decoding policy**, but not the best ordinary choice of code. This is precisely why error algebra and alternative encodings must be searched together. Operator-algebra/noiseless-subsystem QEC is established prior work [R4].

<a id="section-5"></a>

## 5. Non-Pauli QEC comparisons with stronger decoders

### Models and methods

Codes: the four-qubit Leung amplitude-damping code [R2], two-qubit dual rail, three-qubit repetition, and a finite-level oscillator surrogate with codewords (|0>+|6>)/sqrt(2), |3>.

Noise: independent cooling/cooling, cooling/heating, orthogonal-axis cooling, opposed finite-temperature relaxation; collective lowering/raising and phase-weighted lowering; loss/loss, loss/gain, loss/number-dephasing.

For encoded Kraus L_j, the transpose/Petz decoder [R3] has Kraus

$$
R_j=L_j^\dagger\left(\sum_kL_kL_k^\dagger\right)^{-1/2},
$$

with inverses restricted to support. Complete it arbitrarily on the unused output kernel. We compare both serial orders, flag-conditioned recovery, joint control-target recovery, and ordinary recovery plus reencoding between the two noise contacts.

Petz recovery is not asserted optimal. For eight two-qubit configurations a separate SDP optimizes over **all final CPTP decoders** for fixed encodings. The primal is an achievable decoder; the dual is an upper bound. A log-det Newton solver is implemented without external conic solvers. These are floating-point feasibility brackets, not exact rational/interval certificates. The formulation is established by Fletcher-Shor-Win [R5]. The solver was checked against the analytic optimal amplitude-damping decoder and trace/positivity conditions.

### Optimized dual-rail example, then a cheaper ordinary counterexample

For cooling followed by heating, both of strength gamma=.3, fixed dual-rail encoding gives approximately

| Protocol | Optimal/achieved logical entanglement fidelity |
|---|---:|
| Best serial order, optimized final decoder | .6175000 |
| Switch with measured flag, optimized final decoder | approximately .6490000 |
| Switch, joint coherent-control decoder | approximately .6490000 |
| Constructive ordinary intermediate recovery | .6175000 |

The numerical primal/dual widths were below 2.1e-6. This is a real improvement for this **fixed encoding and correction layout**.

But simply send the logical state on one physical qubit and leave the other unused. Ordinary cooling/heating then has fidelity

$$
F=1-\gamma+\gamma^2/4=.7225.
$$

It beats even the optimized fixed-dual-rail switched result. The same comparison succeeds at all four tested strengths. For orthogonal-axis cooling, an unencoded qubit has fidelity [2-gamma+2(1-gamma)^(3/2)]/4 and likewise beats the optimized dual-rail switch in all four tested strengths. Thus all eight tested fixed-dual-rail gains disappear against this different ordinary encoding. Decoder optimization alone is not enough; the code itself can be the weak baseline.

### Collective relaxation

On three-qubit repetition, collective cooling/heating at t=.2 gives serial-Petz .646453, flagged .710453, coherent .716581, and intermediate-Petz .654222. However, the known three-qubit spin-1/2 multiplicity subsystem [R4] preserves a logical qubit exactly under arbitrary collective SU(2) noise.

The supplied isometry W obeys

$$
J_-W=W(I_L\otimes\sigma_-),\qquad
J_+W=W(I_L\otimes\sigma_+).
$$

Direct channel calculations at four times verified fidelity one without a switch. A common unknown spatial orientation remains within the same collective algebra.

### A useful analytic upper bound on every final decoder

Barnum-Knill [R3, Theorem 3] gives, for the single logical maximally mixed input,

$$
F_{\rm Petz}\ge F_{\rm optimal}^2,
\qquad F_{\rm optimal}\le\sqrt{F_{\rm Petz}}.
$$

Thus some candidates can be eliminated without numerically optimizing a very large decoder. In six of the 69 noise-code configurations, the explicit ordinary intermediate recovery exceeds this upper bound for **every final decoder of the specified switched layout**.

Examples:

| Code/noise | Switched Petz fidelity | Upper bound on any switched final decoder | Achieved ordinary intermediate fidelity |
|---|---:|---:|---:|
| AD4, cooling/heating gamma=.01 | .98012776 | .99001402 | .99947431 |
| AD4, cooling/heating gamma=.1 | .81295018 | .90163750 | .94848679 |
| Finite oscillator, loss/gain t=.01 | .99791484 | .99895688 | .99992131 |

The inequality is analytical; displayed channel evaluations are floating point. The margin is much larger than the observed arithmetic residuals, but these entries are not interval-certified numerical theorems. Extra ordinary syndrome/gate operations are required and must be charged in a hardware comparison; the primitive-noise contact count is the same.

### Bosonic scope

The oscillator calculations use a 12-level truncated lowering operator and finite-dimensional Lindblad channels, not an unqualified infinite-Fock-space channel. They are screening evidence only, not an energy-constrained diamond-norm theorem or a bosonic fault-tolerance threshold. Known binomial-code protection and intermediate correction are admitted. A small Petz gain for loss/number-dephasing at strong noise is retained in the data; no all-ordinary advantage is asserted.

<a id="section-6"></a>

## 6. Informative record leakage: one bit can be enough

Consider the SAME/MUB rank-one projective promise, with starting state I/d. Suppose the A device reveals only a stable coarse label f(i), not its full outcome. In A-B-A, compare the first and last coarse labels.

Under SAME, agreement probability is one. Under MUB, the two fine A outcomes are independent and uniform, so

$$
P(\text{agreement}|\mathrm{MUB})=\sum_g(r_g/d)^2,
$$

where r_g counts the fine labels in group g. A **single balanced bit** therefore gives agreement 1 versus 1/2. Seven repetitions, 21 calls, give worst-case error at most 1/128<1%.

With independent classical bit-readout errors eta, SAME disagreement is 2 eta(1-eta), while MUB disagreement remains 1/2. At eta=.01, forty thresholded repetitions, 120 calls, suffice by Hoeffding for error below1%.

This estimates the stated promise, not the full arbitrary visibility or the full switch. The coarse label must be balanced, stable, and tied to the actual projective outcome. An independent coin label or an unknown outcome-dependent disturbance is not covered. The original unread-outcome hardness assumptions must not be silently applied to a device exporting such a bit. The full-record ABA experiment is prior work [R1]; the coarse-bit calculation is a direct extension here.

<a id="section-7"></a>

## 7. Geometry of known low-weight error support

Let G be a known interaction graph with maximum degree Delta. Suppose unknown Kraus operators lie in the span of I, all one-site Paulis, and all two-site Pauli products on edges of G. Coherent, non-Pauli combinations are allowed.

The known-span Choi contraction T from the previous report satisfies

$$
\boxed{\|T\|^2=2+6\Delta.}
$$

Proof: each anticommuting ordered pair of basis Paulis maps to one output Pauli with unit modulus. The rows are orthogonal, so TT^dagger is diagonal and its eigenvalues count preimages. A one-site output at v has 2+6 deg(v) preimages. A two-site output on an edge has eight. A three-site output has four per possible central vertex, at most12. No other support can arise. For Delta>=2 the one-site maximum dominates; Delta1 gives8; Delta0 gives2. Exact enumeration checked55 graphs.

Therefore two ordinary Choi probes and a known collective effect estimate

$$
P_{\rm ordinary}=p_-/(2+6\Delta).
$$

For bounded-degree graphs there is no dimension-exponential measurement normalization penalty, even for genuine off-diagonal process-matrix coefficients. This is not an assertion that preparing four target-sized registers or implementing the collective effect is free in a laboratory. It rules out automatically importing a high-dimensional unrestricted-query separation into this exact low-weight support family.

A finite-time local Lindbladian can develop many-jump Kraus products beyond this span. A truncation error bound is required before applying the proposition to it. If the actual channel is Pauli diagonal, the stronger exact full-switch compiler from the earlier report applies regardless of graph or weight.

<a id="section-8"></a>

## 8. Fermionic-mode loss: a large carrier but a simple ordinary calibration state

Use Jordan-Wigner encoded fermionic modes. For normalized mode u, put a_u=sum u_j a_j, n_u=a_u^dagger a_u. A loss channel of probability gamma has Kraus

$$
K_0=I-h n_u,\quad K_1=\sqrt\gamma a_u,\qquad h=1-\sqrt{1-\gamma}.
$$

For two modes u,v let eta=|u^dagger v|^2. Direct canonical-anticommutation algebra gives

$$
p_-=
\frac{h_A^2h_B^2}{8}\eta(1-\eta)
+\frac{\eta}{8}(\gamma_Ah_B^2+\gamma_Bh_A^2)
+\frac{\gamma_A\gamma_B}{4}(1-\eta).
$$

Forty-eight random mode pairs on 2,3,4 encoded modes agree numerically. These are qubit-encoded channel calculations. A physically fermionic coherent-order implementation must additionally handle parity/graded environment conventions; it is not automatically supplied by the matrix formula.

The natural ordinary probe is the fully occupied state, invariant up to phase under mode rotations. Apply the two loss channels and count whether two particles were lost:

$$
P(\text{two holes})=\gamma_A\gamma_B(1-\eta).
$$

The individual rates are measured by separate contacts on the same known filled state. No hidden mode calibration is needed.

For gamma_A=gamma_B=1, the ordinary two-hole test perfectly distinguishes the same mode from orthogonal modes. The switch control instead gives p_-=1/4 in both cases. This is a useful caution: high-dimensional collective support need not hide the desired relation when a known extremal probe state exists.

<a id="section-9"></a>

## 9. Another full-simulation sufficient condition: extract a quantum program

Suppose a family has a known processor P and an unknown program state sigma_theta:

$$
A_\theta(\rho)=\mathcal P(\rho\otimes\sigma_\theta).
$$

Assume sigma_theta can be prepared with m ordinary A queries on expendable inputs, and a known unitary dilation of P can be coherently controlled. Keep the same program and processor auxiliaries across

$$
C_0(V_{\mathcal P})\longrightarrow B\longrightarrow C_1(V_{\mathcal P}),
$$

then discard them. This gives the exact full switch using m A queries and one B query. The program can be mixed; its purification is not required. A purification proof shows that each program/environment label gives the correct paired ordered Kraus products, and tracing them gives the channel switch.

This extends classical white-box compilation to a genuine quantum-program interface. It does not say every channel has an extractable program. Environment-parametrized and environment-seizable channels are established concepts [R6]; the switch compilation is the direct construction here.

Examples:
- Unknown replacement/reset state: one call supplies the program; a known SWAP processor suffices.
- Known rank-one measurement basis, arbitrary unknown prepared state tau_i after each outcome: one query on each known basis vector supplies the product program tensor_i tau_i. A known coherent measurement/swap processor implements the map. For a binary reset/readout module, two A calls plus one B call suffice.
- Known orthogonal-unitary mixtures: the earlier Bell-sampling compiler is a special case.

No measurement record from the original device is required for these examples. Known effects alone do not guarantee this structure for a general instrument. Large numbers of outcomes may make the program construction expensive. Shared environmental memory would invalidate the independent-program use model.

Thirty-two random mixed-program processors and ten arbitrary binary measure/prepare devices were compared against the full switch Choi map; residuals were below1e-15.

<a id="section-10"></a>

## 10. Rare logical failures cannot be inferred for free by changing causal order

Suppose the actual allowed oracle is E_p=(1-p)E_0+p F, with independent private flags on each of q slots, versus E_0. For any deterministic q-slot circuit or valid switch-based arrangement, the no-fault history has probability (1-p)^q and exactly reproduces the E_0 output. Therefore balanced discrimination satisfies

$$
P_{\rm win}\le1-\frac12(1-p)^q.
$$

All failed/postselected histories are retained in this bound; discarding them does not remove their cost. For99% success,

$$
q\ge\left\lceil\frac{\log .02}{\log(1-p)}\right\rceil.
$$

At p=10^-6 this is3,912,022 calls, and at p=10^-9 it is3,912,023,004 calls. The obstruction applies equally to the switch. A switch may reveal the structure of equally strong errors; it cannot force an event with probability p to occur in O(1) deterministic contacts.

This statement applies to the complete allowed oracle interface. If off-code probes reveal a large channel difference, or the fault model is coherent rather than a stochastic mixture, another analysis is required.

<a id="section-11"></a>

## 11. Recent QEC-sensing literature: separate ordinary checks from time-direction access

Xu et al., arXiv:2601.01404 [R7], study an auxiliary gate D coherently ordered with noisy evolution. In their commuting-signal regime, this is an ordinary known-arm compiler:

$$
C_0(D)\longrightarrow E_{L,H}\longrightarrow C_1(D).
$$

The protocol's error-flag identity can be useful, but it does not by itself establish an unrestricted ordinary-causal query advantage when these known controlled gates are admitted.

The source explicitly introduces **indefinite time direction** in the anticommuting-signal regime: one branch receives E_{L,H}, the other E_{L,-H}. This is additional access, not merely a standard switch of two unchanged CPTP maps. Do not import the headline parallel-noise improvement without importing that stronger interface and comparing its ordinary use.

For example, if the physically supplied resource is a coherent conditional signal Hamiltonian omega Z_control tensor Z_probe while the noise is Z_probe, an ordinary circuit can initialize the probe to |0>. The control then accumulates the noiseless phase and has QFI4t^2. This is a conditional comparator for that explicit oracle, not a claim that every microscopic time-flip realization equals it or a refutation of the whole paper.

<a id="section-12"></a>

## 12. What remains a credible application lead

The exact code-aware construction is a useful synthesis rule: search for branch error spaces that are separately correctable but whose union is not, then require that ordinary intermediate recovery, ordinary check sandwiches, alternative encodings, and extractable-program simulation do not erase the benefit under the actual interface.

The current examples do not yet establish a large natural-black-box application advantage. In particular:

- completed same-code recoveries now have an exact one-call ordinary simulator;
- known bounded-degree coherent fault support has a bounded-normalization ordinary scalar test;
- a single informative projective-record bit defeats the SAME/MUB promise gap;
- simple collective relaxation has a noiseless subsystem;
- rare stochastic logical-error detection pays its event rate in either architecture;
- correctable code-algebra constructions may have even better ordinary encodings;
- more serious finite-time, multi-qubit, nonunital modules remain outside these theorems, but require task-specific evidence.

This investigation therefore does not substitute a communication resource, a stabilizer-only resource theory, or an enormous Haar instance for the original objective. The next natural candidate must specify a real opaque module and a useful live-data or model-validation task first. Finite-time autonomous backaction, different-code conversion, or nonreplayable correlated environments may supply richer interfaces, but none is automatically hard or automatically described by two memoryless channels.

<a id="section-13"></a>

## 13. Reproduction and evidence levels

From the repository root, run `python research/more-applications/reproduce.py --study code-aware`. NumPy and SciPy are required; [structured_bounds.py](experiments/structured_bounds.py) also uses standard-library combinatorics. The driver writes logs and generated output to `_build/more-applications/`. The [single current validation record](../validation.json) lists script exit codes, source hashes, versions and scope.

- Exact statements are proved algebraically above. Their floating-point matrix checks are regression tests, not proof substitutes.
- Pauli graph counts are exact integer enumeration; general graph proof is above.
- Decoder SDP bounds are numerical with checked primal/dual residuals. They are not rational/interval certificates and do not optimize every encoding or all adaptive ordinary circuits.
- Barnum-Knill supplies an analytic bound on all final decoders for a fixed encoded channel; the channel fidelities inserted into it are numerical.
- Finite oscillator calculations do not establish infinite-dimensional or hardware performance.
- No claims about optimal ordinary algorithms are inferred solely from failed optimizer searches.
- The ordinary program compiler and code-membership tests may have nontrivial gate/memory cost. Query efficiency is not a hardware runtime theorem.

## Primary references

[R1] Gao et al., *Measuring incompatibility and clustering quantum observables with a quantum switch*, PRL130,170201(2023), https://arxiv.org/html/2208.06210v4 . Existing statistic and readable projective ABA.

[R2] Leung, Nielsen, Chuang, Yamamoto, *Approximate quantum error correction can lead to better codes*, PRA56,2567(1997), https://arxiv.org/abs/quant-ph/9704002 . Four-qubit amplitude-damping code.

[R3] Barnum and Knill, *Reversing quantum dynamics with near-optimal quantum and classical fidelity*, JMP43,2097(2002), updated arXiv v2(2026), https://arxiv.org/html/quant-ph/0004088v2 . Equation12 and Theorem3; single-state entanglement-fidelity guarantee.

[R4] Knill, Laflamme, Viola, *Theory of Quantum Error Correction for General Noise*, PRL84,2525(2000), https://arxiv.org/abs/quant-ph/9908066 . Interaction algebras and noiseless subsystems, including collective noise.

[R5] Fletcher, Shor, Win, *Optimum Quantum Error Recovery using Semidefinite Programming*, PRA75,012338(2007), https://arxiv.org/abs/quant-ph/0606035 . Fixed-encoding optimal recovery SDP.

[R6] Wilde, Berta, Hirche, Kaur, *Amortized Channel Divergence for Asymptotic Quantum Channel Discrimination*, LMP(2020), https://arxiv.org/html/1808.01498v2 . Environment-parametrized/seizable channel concepts; not a claim that their paper contains the exact switch compiler developed here.

[R7] Xu et al., *Noise-Resilient Heisenberg-limited Quantum Sensing via Indefinite-Causal-Order Error Correction*, https://arxiv.org/html/2601.01404v1 . Equations2-8 distinguish the short-time channel, known auxiliary gate, and additional time-direction access.

[R8] Bavaresco et al., *Simulating the quantum switch with quantum circuits is computationally hard*, Nature Communications16,10216(2025), https://arxiv.org/html/2409.18202v2 . Full-output task and known-unitary/dilation access boundaries.

[R9] Gonzales et al., *Quantum Error Mitigation by Pauli Check Sandwiching*, Scientific Reports13,2122(2023), https://arxiv.org/abs/2206.00215 . Ordinary known-check comparator.

The shared [core.py](../common/core.py) is reused as an algebra utility; all new scripts and source distinctions are listed in [the research entry point](../README.md). No new independent proof of the repository's Haar lower bounds is claimed or used as a substitute for these task calculations.
