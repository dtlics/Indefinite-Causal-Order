<a id="c6-r08"></a>

# C6-R08 — Algorithm certification from hidden measurement geometry

These analytic operational corollaries of [C6-R01](README.md) supply new certification outputs. The robust finite-horizon theorem permits arbitrary CPTP perturbations of the hard families; the separate arbitrary-basis analysis states what the scalar can certify without that promise. They reuse the existing lower-bound theorem and MED experiment; they do not assert a new lower-bound method or a new Lean endpoint.

## Common definitions and inherited theorem

Let d=2^n with n≥1. On a d-dimensional query register Q, let

\[
A(X)=\sum_{i=1}^{d}P_iXP_i,\qquad
B(X)=\sum_{j=1}^{d}Q_jXQ_j,\qquad
\Omega(X)=\operatorname{Tr}(X)I/d,
\]

where each projector family is an orthonormal rank-one resolution of the identity. The promise is either SAME, meaning A=B as channels, or MUB, meaning Tr(P_iQ_j)=1/d for every i,j. In both cases AB=BA: the product is A under SAME and Ω under MUB. Each basis is fixed throughout the experiment. Oracle invocations have fresh call-local environments.

For channel comparison use the reference-complete distance

\[
D_\diamond(\mathcal E,\mathcal F)
=\sup_{R,\rho_{QR}}\frac12
\|[(\mathcal E-\mathcal F)\otimes\mathrm{id}_R](\rho_{QR})\|_1
=\frac12\|\mathcal E-\mathcal F\|_\diamond .
\]

The supremum includes arbitrary finite passive references and density operators. The ordinary learner may use arbitrary finite quantum memory, reference entanglement, known coherent processing, adaptive classical choices of query name and collective measurements. Query count is the maximum total number of calls on any branch. Success is unconditional and is required with probability at least 2/3 for every promised input. The oracles provide only their channel action: stable projective outcomes, the hidden basis unitary and its inverse, and a coherent Stinespring/purification port are not supplied.

The [C6 owner](README.md) and [manuscript, Theorem thm:c6](../../../paper/main.tex) prove that an ordinary learner distinguishing these promises needs

\[
q>d^{1/16}/100.
\tag{C6}
\]

The theorem already covers the strong ordinary learner just defined. Its exponent is not asserted optimal. Its hard prior uses one fixed Haar U and the pairs (Δ_U,Δ_U) or (Δ_U,Δ_UH), with the same U reused across all calls and H the known Walsh transform. The derivations below invoke this existing theorem as a dependency.

## Lemma: exact reference-complete distance of a pinching from replacement

For any rank-one pinching A,

\[
D_\diamond(A,\Omega)=1-1/d.
\tag{1}
\]

**Proof.** For an arbitrary state ρ_QR, write

\[
(A\otimes\mathrm{id})(\rho)=\sum_iP_i\otimes\rho_i,
\quad \rho_i\ge0,\quad \sum_i\operatorname{Tr}\rho_i=1.
\]

The R marginal is Σ_i ρ_i. Consequently

\[
[(A-\Omega)\otimes\mathrm{id}](\rho)
=\sum_i(P_i-I/d)\otimes\rho_i.
\]

Trace-norm multiplicativity and the triangle inequality give

\[
\frac12\|[(A-\Omega)\otimes\mathrm{id}](\rho)\|_1
\le \frac12\sum_i\|P_i-I/d\|_1\operatorname{Tr}\rho_i
=1-1/d.
\]

Equality is attained by the unreferenced input ρ=P_i, whose outputs are P_i and I/d. This proves both bounds, including every reference. ∎

## Corollary1: verify reference-complete forgetting of one opaque Markov primitive

### Input, required answer and native interface

The input is a single opaque memoryless primitive

\[
\Phi=(A+B)/2,
\tag{2}
\]

promised to arise from one of the SAME/MUB pairs above. The internal selector is independently redrawn on every invocation. The certification task asks whether the supplied primitive is a rapid forgetter of its input, including reference correlations, or preserves a hidden classical algebra. More concretely, its answer must distinguish

\[
\begin{array}{c|c|c}
 & D_\diamond(\Phi^3,\Omega) & \text{stationary behavior}\\ \hline
\text{MUB} & \le (1-1/d)/4\le1/4 &
I/d\text{ unique; gap }1/2\\
\text{SAME} & =1-1/d\ge1/2 &
d\text{-dimensional fixed algebra}.
\end{array}
\tag{3}
\]

The promise in(2) is essential. Equation(3) is not a claim that self-SWITCH visibility certifies mixing of every arbitrary channel.

The native extra resource is the standard SWITCH of two invocations of the same Φ. It may prepare a target inI/d, prepare its control in plus and measure that control in X. The measured outputs are used only for certification, not to execute or modify the production Markov step.

### Reference-complete forgetting proof

Under MUB, A and B are Hilbert–Schmidt orthogonal projections on operator space with common projection Ω. Put A_0=A−Ω and B_0=B−Ω. Direct use of A²=A, B²=B and AB=BA=Ω gives

\[
A_0^2=A_0,\quad B_0^2=B_0,\quad A_0B_0=B_0A_0=0.
\]

They are orthogonal traceless projections of rank d−1 each. Thus

\[
\Phi=\Omega+\tfrac12(A_0+B_0),\quad
\operatorname{spec}(\Phi)=
\{1^{[1]},(1/2)^{[2d-2]},0^{[(d-1)^2]}\}.
\tag{4}
\]

This proves fixed-point uniqueness and the gap statement directly. For every integer t≥1,

\[
\begin{aligned}
\Phi^t
&=\Omega+2^{-t}(A+B-2\Omega)\\
&=2^{1-t}\Phi+(1-2^{1-t})\Omega.
\end{aligned}
\tag{5}
\]

Combining(1), convexity of the diamond norm and(5) gives the independent reference-complete mixing proof

\[
\begin{aligned}
D_\diamond(\Phi^t,\Omega)
&=2^{1-t}D_\diamond(\Phi,\Omega)\\
&\le2^{1-t}\tfrac12[
D_\diamond(A,\Omega)+D_\diamond(B,\Omega)]\\
&=2^{1-t}(1-1/d).
\end{aligned}
\tag{6}
\]

Taking t=3 proves the first row of(3). More generally, (6) gives a logarithmic sufficient mixing horizon for any requested error ε>0. It is a proved upper bound, not a claim that the displayed coefficient is always the exact worst-input norm.

Under SAME, Φ=A, so Φ^t=A for all t≥1. Equation(1) proves the second row of(3). The d basis projectors are fixed, and their span is precisely the fixed algebra. In particular, the statement does not infer trace-norm convergence from the gap alone. ∎

### Native certification cost

For Kraus families E_i,F_j, a standard SWITCH on control plus and target I/d has

\[
p_-=\frac1{4d}\sum_{i,j}\|[E_i,F_j]\|_{\mathrm{HS}}^2,
\qquad v=1-2p_-.
\tag{7}
\]

This is the established channel noncommutativity experiment of [Gao et al., PRL130,170201(2023), Eqs.(6)–(9)](https://arxiv.org/html/2208.06210v4), not a protocol introduced by this corollary.

Choose the Kraus family of Φ as (P_i/√2)_i together with (Q_j/√2)_j. The same-family commutators vanish, and the two cross families give

\[
v(\Phi,\Phi)=\tfrac12[1+v(A,B)],
\qquad
p_-(\Phi,\Phi)=\tfrac14[1-v(A,B)].
\tag{8}
\]

The usual hidden-basis visibility is v(A,B)=1 under SAME and 1/d under MUB. Thus the self-SWITCH minus probability is 0 versus(1−1/d)/4≥1/8.

Repeat the experiment nine times independently. Output MUB/RAPID if any minus occurs, and SAME/NONMIXING otherwise. SAME is never mislabeled. MUB is missed with probability at most

\[
(7/8)^9=40353607/134217728<1/3.
\tag{9}
\]

There are 18Φ invocations in total. No outcome-conditioned renormalization or unknown-basis learning is used.

### Strong ordinary lower bound

Suppose an ordinary algorithm makes at most q calls to Φ and correctly certifies(3) on every promised Φ. Construct an ordinary A/B algorithm that simulates each such call by sampling a fresh classical selector, calling A or B once on the designated query register and discarding the selector.

For every joint input with all retained memory, the simulated action is exactly(Φ⊗id). Replacing the calls one at a time preserves all adaptive outcome probabilities and the final state. Each call consumes exactly one primitive A/B query, so the hard query budget remains q. Under the two C6 hypotheses it supplies exactly the two promised instances of(2). The proposed certificate therefore distinguishes the C6 hypotheses with the same success probability. Applying(C6) proves

\[
q_\Phi>d^{1/16}/100.
\tag{10}
\]

This reduction already includes reference entanglement, adaptive tests and collective readout. If ordinary algorithms are additionally given A and B separately, the ledger becomes N_Φ+N_A+N_B, and the same lower bound applies to that total.

Selector secrecy is not needed for this ordinary lower bound: revealing which component was called still admits the same C6 simulation, since C6 allows classically chosen names. However, the experiment in(8) uses fresh independent call-local selectors. Reusing one selector across the two self-SWITCH slots gives only AA or BB and a zero minus probability even under MUB. Stable projective-outcome records or coherent access to hidden dilations are stronger resources outside the stated theorem.

## Corollary2: safe deletion of an opaque unread subroutine

The input program applies A thenB. The compiler must output DELETE when replacing B∘A by A has error at most 1/4, and KEEP when its error is at least 1/2, with probability at least 2/3 on every promised input. Soundness and completeness are both required.

Under SAME, B∘A=A and the rewrite error is 0. Under MUB, B∘A=Ω, so by(1)

\[
D_\diamond(B\circ A,A)=1-1/d\ge1/2.
\tag{11}
\]

Thus any correct ordinary compiler certificate distinguishes the same C6 hypotheses. Its maximum total primitive-query budget must exceed d^(1/16)/100.

The native compiler tests A,B directly with four independent standard SWITCH assays. SAME has minus probability 0 and MUB has minus probability(1−1/d)/2≥1/4. Output KEEP if any minus occurs. Its worst miss probability is(3/4)^4=81/256<1/3, and its cost is eight primitive calls.

This is a certificate about deleting a quantum-channel instruction. It is not a Trotter reordering theorem; A and B commute as superoperators in both cases. An optimizer allowed to refuse every optimization can always retain B and execute a correct two-call program. Hence(11) gives an exponential query advantage for the required complete certification task, not automatically for end-to-end execution or state preparation. Workload reuse and downstream costs must be stated separately if such an advantage is claimed.

<a id="c6-r08-robust"></a>

## Robust fixed-horizon certification for C6-R08

This section strengthens the exact application corollaries above. The unknown maps are fixed, memoryless CPTP channels; all trial environments are fresh. The perturbations need not be unital, reversible, self-adjoint or known. The conclusion concerns three-step reference-complete forgetting and a safe-rewrite error. Exact stationary states, spectral gaps and invariant algebras of the perturbed maps are not certified.

All channel distances below use D(E,F)=||E−F||diamond/2. Let d=2^n, n≥1, and a=1−1/d. Ideal rank-one pinchings A0,B0 obey the C6 SAME/MUB promise. Their exact pinching-mixture center is Φ0=(A0+B0)/2. C6-R08 supplies

\[
D(A_0,\Omega)=a,\qquad
\Phi_0^t=2^{1-t}\Phi_0+(1-2^{1-t})\Omega\quad(t\ge1,\ {\rm MUB}),
\]

and therefore D(Φ0³,Ω)≤a/4 under MUB, while Φ0=A0 and D(Φ0³,Ω)=a under SAME. The underlying C6-R01 ordinary lower bound is q>d^(1/16)/100 with arbitrary finite ordinary memory, reference entanglement, adaptive classical choices of oracle and collective readout.

### The robust theorem

Fix 0≤ε≤1/24.

**Single primitive.** The input is a fixed unknown Φ promised to satisfy D(Φ,Φ0)≤ε for some ideal center above. The required output distinguishes the following properties of the supplied Φ:

\[
\begin{array}{c|c}
{\rm center\ class}&D(\Phi^3,\Omega)\\ \hline
{\rm MUB\ (RAPID)}&\le17/48\\
{\rm SAME\ (SLOW)}&\ge18/48.
\end{array}
\tag{R1}
\]

Forty-three independent self-SWITCH assays on control plus and target I/d suffice: output RAPID iff at least three minus outcomes occur. This uses 86 primitive Φ invocations. Both error probabilities are strictly below 1/3.

**Safe deletion.** Alternatively the inputs are fixed unknown A,B with D(A,A0)≤ε and D(B,B0)≤ε for some ideal promised pair. The required output distinguishes whether deleting B from B∘A has

\[
\begin{array}{c|c}
{\rm center\ class}&D(B\circ A,A)\\ \hline
{\rm SAME\ (DELETE)}&\le1/8\\
{\rm MUB\ (KEEP)}&\ge3/8.
\end{array}
\tag{R2}
\]

Five independent direct SWITCH assays suffice: output KEEP iff any minus occurs. This uses ten primitive A/B invocations, with both error probabilities strictly below 1/3.

For either task, an ordinary algorithm succeeding with probability at least 2/3 on every robustly promised input still requires more than d^(1/16)/100 primitive calls. These are feasible constant-shot protocols, not claims that the shot counts or tolerance radius are optimal. The two robust classes are disjoint by their displayed property bounds.

### 1. The universal higher-order continuity step

For any fixed CPTP B, the map A↦SW[A,B] is a deterministic one-slot superchannel. Here is an explicit construction, including the environment needed for that statement.

Choose a Stinespring unitary U_B on Q⊗E with E initially in |0〉 and B_j=〈j|U_B|0〉. Before the one common A call, apply

\[
P_B=|0\rangle\langle0|_C\otimes I_{QE}
    +|1\rangle\langle1|_C\otimes U_B.
\]

After A acts on Q, apply

\[
Q_B=|0\rangle\langle0|_C\otimes U_B
    +|1\rangle\langle1|_C\otimes I_{QE},
\]

then trace E. The SAME environment E is used before and after. Refining the single A call into A_i gives the Kraus operators

\[
|0\rangle\langle0|\otimes B_jA_i
+|1\rangle\langle1|\otimes A_iB_j,
\]

which are exactly those of the standard SWITCH. This equality includes arbitrary control/target/reference inputs. Separate newly initialized B environments in the two placements would generally destroy the required pairing.

The pre- and post-processings are CPTP. Hence, by diamond-norm contractivity,

\[
D({\rm SW}[A,B],{\rm SW}[A',B])\le D(A,A').
\tag{R3}
\]

The same holds in the other slot. Applying the triangle inequality one slot at a time proves

\[
D({\rm SW}[A,B],{\rm SW}[A',B'])
\le D(A,A')+D(B,B').
\tag{R4}
\]

For two self-slots each perturbed by ε, this is the full-output bound 2ε. Any fixed output event changes in probability by at most 2ε. The construction is a proof of contractivity for a fixed B; it does not grant a learner the unavailable description or controlled dilation of its unknown oracle.

By itself, (R4) is too loose to prove the single-primitive assay at ε=1/24: its exact event gap can be only 1/8. A pinching-specific event estimate below supplies the necessary stronger bound. It is not an improvement of (R4) for the full output channel.

### 2. Perturbation of the properties being certified

Write δ=Φ−Φ0. The exact noncommutative telescope is

\[
\Phi^3-\Phi_0^3
=\delta\Phi^2+\Phi_0\delta\Phi+\Phi_0^2\delta.
\tag{R5}
\]

CPTP composition is diamond-contracting, so universally D(Φ³,Φ0³)≤3ε. In particular, under SAME,

\[
D(\Phi^3,\Omega)\ge a-3\epsilon\ge3/8=18/48.
\tag{R6}
\]

For a MUB center, Φ0²=(Φ0+Ω)/2. Since δ is trace-annihilating, Ωδ=0, even after adjoining any passive reference. Consequently Φ0²δ=Φ0δ/2. The three terms in (R5) have distance budgets ε, ε and ε/2. This gives

\[
D(\Phi^3,\Omega)
\le a/4+(5/2)\epsilon
\le1/4+5/48=17/48.
\tag{R7}
\]

This argument proves the complete-channel horizon-three bound directly. It does not infer mixing from an operator-space gap, assume Φ(I/d)=I/d, or replace Ωδ=0 by the generally false identity δΩ=0.

For deletion, the triangle inequality and two-slot composition contraction give

\[
\left|D(B\circ A,A)-D(B_0\circ A_0,A_0)\right|
\le D(B\circ A,B_0\circ A_0)+D(A,A_0)\le3\epsilon.
\tag{R8}
\]

The ideal errors are 0 under SAME and a under MUB. Equation (R8) proves (R2).

### 3. A trace-annihilating diamond-ball decomposition

We require a signed quadratic remainder bound without treating a non-CP map as a physical channel.

**Lemma.** If δ is a difference of channels and ||δ||diamond≤2ε, then, for ε>0, there are CPTP C,D with

\[
\delta=\epsilon(C-D).
\tag{R9}
\]

**Proof.** Use UNNORMALIZED Choi matrices J^u, for which Tr_out J_C^u=I for a channel. The channel-distance SDP of [Watrous, *Semidefinite Programs for Completely Bounded Norms*, Section 4](https://www.theoryofcomputing.org/articles/v005a011/) has dual

\[
\frac12\|\delta\|_\diamond
=\min\{\|\operatorname{Tr}_{\rm out}Z\|_\infty:
Z\ge J_\delta^u,\quad Z\ge0\}.
\tag{R10}
\]

Take such a Z with P=Tr_out Z≤εI. Both Z and Z−Jδ^u are positive and have the same partial trace P, because δ is trace-annihilating. Fix any output density operator σ and put F=σ⊗(εI−P) in the output⊗input Choi convention. Then

\[
J_C^u=(Z+F)/\epsilon,\qquad
J_D^u=(Z-J_\delta^u+F)/\epsilon
\]

are positive with input partial trace I. They are therefore channel Choi matrices, and their difference proves (R9). If the upper bound ε is larger than the actual distance, the same positive filler completes the unused trace budget. The ε=0 case is immediate. ∎

This is a finite-dimensional SDP/CP-completion argument; it is not an assumption that the physical perturbation is a probabilistic mixture with its ideal center.

### 4. The pinching tester gives the sharper event bound

Let p(E,F) denote the minus probability of the standard SWITCH on control plus and target I/d. It is symmetric and affine in each channel slot, and extends bilinearly to their linear differences. For CPTP E,F, 0≤p(E,F)≤1.

For a rank-one pinching A0 with projectors P_i and a channel C with Kraus K_j, direct expansion gives

\[
p(C,A_0)=\frac12\left[
1-\frac1d\sum_{i,j}|\operatorname{Tr}(P_iK_j)|^2\right].
\tag{R11}
\]

For this event calculation use the NORMALIZED Choi state

\[
\widehat J_C=J_C^u/d,\qquad
\Pi_A=\sum_i|P_i\rangle\!\rangle\langle\!\langle P_i|.
\]

The vectors |P_i〉〉 are Hilbert–Schmidt orthonormal, so Π_A is an orthoprojector. Thus (R11) is p(C,A0)=[1−Tr(Π_A Jhat_C)]/2.

If the fixed other slot is Φ0=(A0+B0)/2, replace Π_A by T=(Π_A+Π_B)/2, still satisfying 0≤T≤I. For two channels C,C' within distance ε, normalized-Choi trace distance is at most ε. Therefore

\[
|p(C,\Phi_0)-p(C',\Phi_0)|\le\epsilon/2.
\tag{R12}
\]

The same inequality holds when the fixed slot is either individual ideal pinching.

For the self-primitive perturbation δ=Φ−Φ0, bilinearity gives

\[
p(\Phi,\Phi)-p(\Phi_0,\Phi_0)
=2p(\delta,\Phi_0)+p(\delta,\delta).
\]

The linear part has magnitude at most ε by (R12). Using (R9), the quadratic term is

\[
\epsilon^2[p(C,C)+p(D,D)-p(C,D)-p(D,C)],
\]

whose magnitude is at most 2ε². Hence

\[
|p(\Phi,\Phi)-p(\Phi_0,\Phi_0)|
\le r(\epsilon):=\epsilon+2\epsilon^2.
\tag{R13}
\]

For the pair, put δ_A=A−A0 and δ_B=B−B0. Each linear term in

\[
p(A,B)-p(A_0,B_0)
=p(\delta_A,B_0)+p(A_0,\delta_B)+p(\delta_A,\delta_B)
\]

is bounded by ε/2. Apply (R9) separately to δ_A and δ_B; the four-term quadratic expression is again bounded by 2ε². The same event bound r(ε) therefore applies to p(A,B).

This improved estimate concerns the specified scalar event at I/d. It does not assert diamond distance r(ε) between complete switched channels or an analogous bound for arbitrary target states.

### 5. Exact constant-shot protocols

At ε≤1/24, r(ε)≤13/288.

For self-Φ, the ideal event probabilities are 0 and a/4≥1/8. Thus

\[
p_{\rm SLOW}\le13/288,\qquad
p_{\rm RAPID}\ge23/288.
\tag{R14}
\]

Let K be the number of minus outcomes in 43 independent assays. The rule K≥3 has worst-case errors bounded by

\[
\begin{aligned}
e_{\rm SLOW}
&\le1-\frac{\sum_{k=0}^2\binom{43}{k}13^k275^{43-k}}{288^{43}}
<1/3,\\
e_{\rm RAPID}
&\le\frac{\sum_{k=0}^2\binom{43}{k}23^k265^{43-k}}{288^{43}}
<1/3.
\end{aligned}
\tag{R15}
\]

These are exact integer-rational comparisons; their decimal values are approximately .306929 and .321875. Monotonicity of binomial tails makes the endpoint comparisons valid for the entire bands in (R14).

For the pair, the ideal probabilities are 0 and a/2≥1/4, so

\[
p_{\rm DELETE}\le13/288,\qquad
p_{\rm KEEP}\ge59/288.
\tag{R16}
\]

In five independent assays the any-minus rule has errors at most

\[
1-(275/288)^5<1/3,\qquad (229/288)^5<1/3,
\tag{R17}
\]

approximately .206218 and .317845. No minimization of the number of trials is claimed. Independent repetition and majority vote can reduce failure probability further with dimension-independent overhead.

A conventional sample-mean threshold also gives a dimension-independent protocol: in (R14), threshold 1/16 has margin 5/288, so Hoeffding gives 2/3 success with at least ceil(41472 ln3/25) assays. The smaller explicit (R15) protocol is the one counted in the theorem.

### 6. Inherited ordinary hardness and scope

The robust promise includes every exact C6-R08 input. For the single primitive, the existing exact reduction simulates each ordinary Φ0 query with one freshly classically chosen A0/B0 query, preserving the whole adaptive/reference state. Therefore an ordinary algorithm solving every robust instance with success at least 2/3 would solve every exact instance with the same hard cap. It still needs q>d^(1/16)/100 primitive calls. For deletion, restrict directly to the exact A0,B0 instances and apply C6-R01. Neither argument is a new lower-bound method.

The closeness assumptions are promises about opaque channels, not a supplied certification of those assumptions. The theorem does not cover coherent access to the hidden bases, stable projective outcome records, inverse/purification access, or explicit circuit/Kraus descriptions. It also does not cover an arbitrarily correlated multitime process in place of fixed memoryless channels. The one-slot superchannel proof is a continuity argument, not a free known-dilation oracle for the learner.

Long-time nonmixing is deliberately absent. For example, (1−τ)A0+τΩ is arbitrarily close to a SAME pinching but eventually mixes for every τ>0. Likewise small nonunital perturbations need not keep I/d stationary. Only the complete finite-horizon defects in (R1), and the rewrite errors in (R2), are certified.

These results strengthen C6-R08 without a new MED protocol, lower-bound method or formal Lean endpoint. The [finite exact checker](../nr-noisy-recovery/checks/architecture/verify_theory_applications.py) checks the rational tester and sampling ingredients; the all-dimension superchannel, norm and SDP arguments remain analytic.

<a id="c6-r08-arbitrary-bases"></a>

## What the SWITCH scalar certifies for an arbitrary pair of pinchings

This is an analytic extension beyond the exact SAME/MUB promise. It introduces no ordinary-query lower bound. The channel and selector assumptions are those of the existing mixer application: two fixed rank-one pinching channels, with a fresh independent selector on each invocation of their mixture. The conclusions concern the supplied mixture, rather than the cost of preparing its known stationary state by another process.

Let

\[
A(X)=\sum_{i=1}^d P_iXP_i,\qquad
B(X)=\sum_{j=1}^d Q_jXQ_j,\qquad
\Phi=(A+B)/2,
\]

where \(P_i=|a_i\rangle\langle a_i|\), \(Q_j=|b_j\rangle\langle b_j|\), and \(d\ge2\). Define the real doubly stochastic, in fact unistochastic, matrix

\[
T_{ij}=\operatorname{Tr}(P_iQ_j)=|\langle a_i|b_j\rangle|^2,
\qquad
1=\sigma_1(T)\ge\sigma_2(T)\ge\cdots\ge\sigma_d(T)\ge0.
\]

Repeated singular value one is allowed. Write \(\Omega(X)=\operatorname{Tr}(X)I/d\).

### Exact spectrum, including the degenerate cases

Treat matrices as a complex Hilbert space with Hilbert–Schmidt inner product. Both \(A\) and \(B\) are orthogonal projections of rank \(d\). The isometries

\[
V_Px=\sum_i x_iP_i,\qquad V_Qy=\sum_j y_jQ_j
\]

obey \(V_P^\dagger V_Q=T\). Their common uniform vector maps to \(I/\sqrt d\). On its orthogonal complement, choose singular vectors \(l,r\) with singular value \(\sigma\), and set \(p=V_Pl\), \(q=V_Qr\). Then

\[
Ap=p,\quad Bq=q,\quad Aq=\sigma p,\quad Bp=\sigma q,
\quad \langle p,q\rangle=\sigma.
\]

For \(\sigma<1\), the two nonzero orthogonal directions \(p+q,p-q\) have \(\Phi\) eigenvalues \((1+\sigma)/2,(1-\sigma)/2\). For \(\sigma=1\), one has \(p=q\): there is one fixed direction, and the formal minus direction vanishes. The subspace orthogonal to both diagonal algebras lies in the kernel.

Consequently the **traceless spectrum, with algebraic multiplicities**, can be written compactly as

\[
\operatorname{spec}(\Phi|_{\operatorname{Tr}=0})
=\left\{\frac{1+\sigma_i}{2},\frac{1-\sigma_i}{2}:i=2,\ldots,d\right\}
\cup\{0^{[(d-1)^2]}\}.
\tag{G1}
\]

If \(k\) of \(\sigma_2,\ldots,\sigma_d\) equal one, the actual multiplicities are: eigenvalue one has multiplicity \(k\); every nonunit singular value supplies the two displayed eigenvalues; and zero has multiplicity \((d-1)^2+k\). Thus the zeros formally paired with unit singular values in (G1) come from the ambient kernel, not from a nonexistent vector \(p-q\). The dimensions sum to \(d^2-1\).

Define the **gap for mixing to replacement**, which is zero if any traceless fixed direction survives, by

\[
g_{\mathrm{rep}}:=1-\|\Phi|_{\operatorname{Tr}=0}\|_{2\to2}
=\frac{1-\sigma_2(T)}2.
\tag{G2}
\]

All eigenvalues are nonnegative. Therefore \(\Phi^m\to\Omega\) exactly when \(\sigma_2<1\); in that case \(I/d\) is the unique stationary state. If \(\sigma_2=1\), a gap above a larger fixed algebra may still exist, but it is not a positive gap for replacement mixing. SAME gives the full spectrum \(1^{[d]},0^{[d^2-d]}\). MUB gives \(1^{[1]},(1/2)^{[2d-2]},0^{[(d-1)^2]}\), recovering the existing special case.

### The scalar gives a Frobenius constraint, not the second singular value

For the maximally mixed target, the cross-channel SWITCH scalar is

\[
v(A,B)=\frac1d\sum_{ij}\operatorname{Tr}(P_iQ_jP_iQ_j)
=\frac{\|T\|_F^2}{d}.
\]

Set

\[
\delta:=dv-1
=\left\|T-\frac{J_d}{d}\right\|_F^2
=\sum_{i=2}^d\sigma_i^2,\qquad 0\le\delta\le d-1.
\tag{G3}
\]

Here \(J_d\) is the all-ones matrix. Thus

\[
\sqrt{\frac{\delta}{d-1}}\le\sigma_2
\le\min\{1,\sqrt\delta\},
\]

\[
\frac{1-\min\{1,\sqrt\delta\}}2
\le g_{\mathrm{rep}}
\le\frac{1-\sqrt{\delta/(d-1)}}2.
\tag{G4}
\]

These are useful bounds, but the sum of squared singular values generally does not determine their largest member. For \(d=2\) there is only one nontrivial singular value, so this particular ambiguity disappears.

If the measured experiment instead switches two independently selected uses of \(\Phi\), its self scalar and minus probability are

\[
\eta(\Phi)=\frac{1+v(A,B)}2,\qquad
p_-(\Phi,\Phi)=\frac{1-v(A,B)}4.
\tag{G5}
\]

In particular the cross scalar \(v\) and self scalar \(\eta\) must not share a numerical label.

### An exact four-dimensional obstruction

Fix the computational basis for \(P\), and take the columns of a unitary \(U\) as the \(Q\) basis. Let \(H_m\) denote a normalized real symmetric Walsh Hadamard matrix, so \(H_m^2=I\) and every entry has squared modulus \(1/m\).

First choose \(U_1=H_2\oplus H_2\). Then

\[
T_1=\begin{pmatrix}J_2/2&0\\0&J_2/2\end{pmatrix},
\quad \operatorname{sing}(T_1)=(1,1,0,0),
\quad v_1=1/2.
\]

The block imbalance \(\operatorname{diag}(1,1,-1,-1)\) is fixed by both pinchings. Hence \(g_{\mathrm{rep},1}=0\) and the full mixture spectrum is \(1^{[2]},(1/2)^{[4]},0^{[10]}\). A state initially confined to the first block keeps block probability one, whereas replacement has probability \(1/2\); consequently its half trace distance from replacement is at least \(1/2\) after every number of steps.

Next choose

\[
U_2=cI+isH_4,\qquad c,s\in\mathbb R,
\quad c^2+s^2=1,\quad a:=c^2=1/\sqrt3.
\]

This is unitary. Real and imaginary entry contributions have no cross term, so

\[
T_2=aI+(1-a)J_4/4,\qquad
\operatorname{sing}(T_2)=(1,a,a,a),
\quad v_2=(1+3a^2)/4=1/2.
\]

Now the unique fixed state is \(I/4\), and

\[
g_{\mathrm{rep},2}=(1-1/\sqrt3)/2>0.
\]

Its full spectrum is \(1^{[1]},[(1+a)/2]^{[3]},[(1-a)/2]^{[3]},0^{[9]}\). Both devices have **the same dimension and exact cross scalar \(1/2\)**, equivalently the same self scalar \(3/4\) and self minus probability \(1/8\), while one never mixes to replacement and the other does.

Even assuming primitivity does not provide a uniform positive gap at this scalar. Define

\[
B(r)=\frac12\begin{pmatrix}1+r&1-r\\1-r&1+r\end{pmatrix},
\quad T_r=B(r)\otimes B(s),\quad
s:=\sqrt{\frac{1-r^2}{1+r^2}}\ge0,\quad 1/\sqrt2\le r<1.
\]

Each \(B(r)\) is the squared-modulus matrix of a real two-dimensional rotation, so \(T_r\) is unistochastic. Every entry is positive. Its singular values are \(1,r,s,rs\), with \(r\ge s\), and

\[
\|T_r\|_F^2=(1+r^2)(1+s^2)=2.
\]

Thus \(v=1/2\) throughout this primitive family, but \(g_{\mathrm{rep}}=(1-r)/2\to0\). Exact scalar knowledge therefore cannot bound a positive replacement-mixing gap uniformly over these primitive examples.

### What a near-minimum certificate can still prove

Suppose a valid upper confidence bound gives

\[
v\le v_U\le\frac{1+r^2}{d},\qquad 0\le r<1.
\tag{G6}
\]

Then (G3)–(G4) certify uniqueness and the dimension-independent Hilbert–Schmidt gap \(g_{\mathrm{rep}}\ge(1-r)/2\). In particular \(v<2/d\) is a sufficient strict ergodicity test. The minimum \(v=1/d\) is attained exactly for flat \(T=J_d/d\), namely MUB.

The threshold \(2/d\) and the lower gap bound are sharp within the unitary-overlap family. For \(d=2m\), take a real rotation \(R_r\) whose squared-modulus matrix is \(B(r)\), and a flat \(m\)-dimensional unitary \(F_m\). Then

\[
U=R_r\otimes F_m,\quad
T=B(r)\otimes J_m/m,\quad
\operatorname{sing}(T)=(1,r,0,\ldots,0).
\]

It has \(v=(1+r^2)/d\) and exactly the lower gap in (G4). At \(r=1\) it becomes two disconnected flat blocks, with \(v=2/d\) and zero replacement-mixing gap. For Walsh dimensions, the upper gap bound is also attained: choose \(U=cI+isH_d\) with \(c^2=r/\sqrt{d-1}\), giving all \(d-1\) nontrivial singular values equal to \(r/\sqrt{d-1}\) at the same scalar.

Hence even a scalar tending to zero does not by itself imply ergodicity: the nonergodic two-block family has \(v=2/d\to0\). A useful guarantee in (G6) requires additive scalar resolution of order \(1/d\) near the minimum, rather than a dimension-independent additive error. For self visibility this is the equivalent requirement

\[
2d\left[\eta-\frac{d+1}{2d}\right]=\delta<1.
\]

Using only independent control-sign samples, resolving an additive separation of order \(1/d\) near these interior Bernoulli means costs order \(d^2\) samples for fixed confidence. This concerns that sampling interface; it is not a lower bound for coherent amplitude-estimation access. The original SAME/MUB decision retains a constant scalar contrast and does not incur this near-minimum precision cost.

The failure can be almost maximal in reference-complete distance. More generally, let the common diagonal algebra have minimal orthogonal block projections \(R_a\), of ranks \(n_a\), summing to \(I\). The fixed space is precisely the intersection of the two diagonal algebras: equality in the projection norm inequality forces \(AX=BX=X\) whenever \(\Phi X=X\). All other eigenvalues are below one, so

\[
\Phi^k\longrightarrow\mathcal E_\cap,
\qquad
\mathcal E_\cap(X)=\sum_a\frac{\operatorname{Tr}(R_aX)}{n_a}R_a,
\]

\[
D_\diamond(\mathcal E_\cap,\Omega)
=1-\min_a\frac{n_a}{d}.
\tag{G7}
\]

For an arbitrary reference, write the output difference as
\(\sum_a(R_a/n_a-I/d)\otimes\mu_a\), with \(\mu_a\ge0\) and \(\sum_a\operatorname{Tr}\mu_a=1\). The triangle inequality gives the upper bound in (G7), since \(\tfrac12\|R_a/n_a-I/d\|_1=1-n_a/d\). Any input supported in the smallest block attains it. In particular \(U=1\oplus F_{d-1}\), with a flat unitary on the second block, still has \(v=2/d\), but its limiting distance is \(1-1/d\to1\). Small absolute scalar value therefore need not mean approximate forgetting even after arbitrarily many steps.

For a positive certificate of reference-complete forgetting, a norm argument must be supplied. A safe, potentially loose consequence of (G6), valid for \(k\ge1\), is

\[
D_\diamond(\Phi^k,\Omega)
\le\min\left\{1,\frac{\sqrt{d-1}}2
\left(\frac{1+r}{2}\right)^{k-1}\right\}.
\tag{G8}
\]

To prove this for any reference, use the measure-and-prepare form of the first \(\Phi\): its output is \(\sum_\ell S_\ell\otimes\mu_\ell\), where each \(S_\ell\) is one of the rank-one \(P_i,Q_j\), \(\mu_\ell\ge0\), and \(\sum_\ell\operatorname{Tr}\mu_\ell=1\). Put \(\lambda=(1+r)/2\). Each remaining term satisfies

\[
\|\Phi^{k-1}(S_\ell)-I/d\|_1
\le\sqrt d\,\lambda^{k-1}\|S_\ell-I/d\|_2
=\sqrt{d-1}\,\lambda^{k-1}.
\]

The triangle inequality and positive reference weights prove (G8) uniformly over all references. This improves the general norm-conversion bound \(d\lambda^k/2\), and supplies an all-reference argument rather than equating a spectral gap with a diamond contraction. At fixed \(r<1\), (G8) gives a sufficient horizon of order \(\log d+\log(1/\epsilon)\). No optimality or impossibility of a stronger family-specific diamond bound is asserted. The exact MUB power identity supplies its stronger dimension-free bound separately.

The resulting extension is a robust near-MUB gap certificate with an explicit precision requirement. It does not turn the scalar into a universal mixing-time estimator, and it does not extend C6 hardness beyond the existing promise without a separate reduction.

## Primary context, ownership and limits

Gao et al. also give a concrete quantum algorithm that clusters unknown measurement contexts with this statistic. A SAME/MUB partitioning corollary and the deletion certificate above are alternative algorithmic applications of the same C6 relation. They must not be counted as independent lower-bound methods.

[Loizeau and Grinbaum, PRA101,012340(2020)](https://arxiv.org/abs/1906.08505) already study a representation-independent self-channel commutator quantity and switched channel behavior. Nothing here claims the first self-channel commutator experiment.

The algorithmic relevance of mixing is explicit in [Chen–Kastoryano–Gilyén's quantum Gibbs sampler](https://arxiv.org/abs/2311.09207v2) and [the discrete-time generalizations of quantum Glauber/Metropolis dynamics](https://arxiv.org/abs/2405.20322v2): their computational analyses use mixing, fixed points and spectral gaps. Those sources motivate a verification endpoint; the present promise is not a claim of improved execution of their known-circuit algorithms.

These results certify the supplied opaque irreversible process. They do not speed up preparing the known state I/d, which is trivial if replacement of the process is allowed. They do not cover explicit circuit descriptions, known Kraus data, coherent block-encodings, Stinespring access or inverse access. The arbitrary-basis analysis gives fixed-dimension examples with identical scalars but nonmixing or arbitrarily slow mixing. A generic near-minimum scalar certificate has a dimension-dependent precision requirement; the constant-shot robust theorem instead assumes closeness to the stated hard families.

The existing NR-R20 production channel(1−η)id+η(B∘A) is a distinct capacity endpoint of C6. It also has a direct mixing interpretation, but it should be referenced rather than reintroduced as another independent lower-bound construction. The linked [finite exact checks](../nr-noisy-recovery/checks/architecture/verify_theory_applications.py) exercise selected pinching, mixer, visibility and trial-count identities. The all-dimension diamond-norm and query reductions above remain analytic; no new formal-kernel audit is claimed.
