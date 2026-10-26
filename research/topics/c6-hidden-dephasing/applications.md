<a id="c6-r08"></a>

# C6-R08 — Algorithm certification from hidden measurement geometry

These analytic operational corollaries of [C6-R01](README.md) supply new certification outputs. They reuse the existing lower-bound theorem and MED experiment; they do not assert a new lower-bound method or a new Lean endpoint.

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

## Primary context, ownership and limits

Gao et al. also give a concrete quantum algorithm that clusters unknown measurement contexts with this statistic. A SAME/MUB partitioning corollary and the deletion certificate above are alternative algorithmic applications of the same C6 relation. They must not be counted as independent lower-bound methods.

[Loizeau and Grinbaum, PRA101,012340(2020)](https://arxiv.org/abs/1906.08505) already study a representation-independent self-channel commutator quantity and switched channel behavior. Nothing here claims the first self-channel commutator experiment.

The algorithmic relevance of mixing is explicit in [Chen–Kastoryano–Gilyén's quantum Gibbs sampler](https://arxiv.org/abs/2311.09207v2) and [the discrete-time generalizations of quantum Glauber/Metropolis dynamics](https://arxiv.org/abs/2405.20322v2): their computational analyses use mixing, fixed points and spectral gaps. Those sources motivate a verification endpoint; the present promise is not a claim of improved execution of their known-circuit algorithms.

These results certify the supplied opaque irreversible process. They do not speed up preparing the known state I/d, which is trivial if replacement of the process is allowed. They do not cover explicit circuit descriptions, known Kraus data, coherent block-encodings, Stinespring access or inverse access. Nor is a self-commutator scalar a universal gap witness: adding an untouched spectator can preserve extra information without removing the active subsystem's commutator signal. The exact input promise is therefore part of both statements.

The existing NR-R20 production channel(1−η)id+η(B∘A) is a distinct capacity endpoint of C6. It also has a direct mixing interpretation, but it should be referenced rather than reintroduced as another independent lower-bound construction. The linked [finite exact checks](../nr-noisy-recovery/checks/architecture/verify_theory_applications.py) exercise selected pinching, mixer, visibility and trial-count identities. The all-dimension diamond-norm and query reductions above remain analytic; no new formal-kernel audit is claimed.
