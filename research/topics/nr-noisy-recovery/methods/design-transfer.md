# Finite-design transfer

This is the hidden-frame generation and moment-transfer method for [NR-R01](../theorem.md). It transfers the local-noise Haar prefix bounds to a finite circuit ensemble, including receivers with unbounded possible query counts and finite expected cost. The result owner states the recovery game, payoff bounds, and physical access assumptions.

Write $D=2^n$ and

$$
A_U=U(X\otimes I)U^\dagger,\qquad
B_U=U(Y\otimes I)U^\dagger,\qquad
C_U=iB_UA_U=U(Z\otimes I)U^\dagger.
$$

The same secret $U$ is used for every call in one instance. A new instance has an independent secret draw. The ensemble and its sampler may be public; the selected word, seed, and any unpaid frame-correlated initial memory are unavailable to the receiver. Known processing, ancillary dimension, entangled probes, classical adaptive device selection, repeated labels, and input-dependent stopping are otherwise unrestricted as in NR-R01.

Define the **standard** $t$-copy twirling channel by

$$
\mathcal T_{\mu,t}(X)
=\mathbb E_{U\sim\mu}
 U^{\otimes t}X(U^\dagger)^{\otimes t}.
$$

The approximation assumption is the full, unhalved additive diamond norm

$$
\|\mathcal T_{\mu,6}-\mathcal T_{H,6}\|_\diamond
\le\epsilon,\qquad
\epsilon\le\frac1{2000D^{10}},                         \tag{1}
$$

where $H$ denotes Haar measure. A spectral moment-operator error, a relative CP-order design parameter, and a half-diamond distance are different conventions; the conversions used below are explicit.

## Balanced degree and exact transfer

In the Bell game of NR-R01, the receiver acts only on the local half of the supplied scrambled Bell pair; the original reference remains inaccessible. For its accepted CP map $M_U$, with Kraus operators $K_{U,j}$, the acceptance and accepted Bell-pass weight are directly

$$
p_U=\operatorname{Tr}M_U(I/D),\qquad
q_U=\frac1{D^2}\sum_j
       |\operatorname{Tr}(C_UK_{U,j})|^2.             \tag{2}
$$

The equality for $q_U$ follows by applying $M_U\circ\operatorname{Ad}_{C_U}$ to the standard Bell pair and testing that same pair. Thus the scrambling contributes the target factor already present in $q_U$; it is not an additional free frame-dependent program. The receiver's initial marginal is exactly $I/D$ for every $U$. In particular, the probability $r_1$ that the original protocol launches its first query is frame independent.

For the optional secret-plaintext variant, apply its projective $2$-design reduction first. It gives the same $p_U,q_U$ and the same input marginal. The degree and resource arguments below are unchanged; only the final score functional differs.

An entry of $UPU^\dagger$, for fixed $P$, has bidegree $(1,1)$ in the entries of $U,U^*$. A unitary-channel Choi entry has bidegree $(2,2)$. A $k$-query accepted comb is multilinear in its $k$ channel Choi operators. Consequently its unnormalized acceptance $p_k$ has bidegree at most $(2k,2k)$. The target Bell projector adds $(2,2)$, giving bidegree at most $(2k+2,2k+2)$ for $q_k$.

| Accepted prefix | Degree of $p_k$ in each of $U,U^*$ | Degree of $q_k$ in each of $U,U^*$ |
| --- | ---: | ---: |
| Zero calls | $0$ | $2$ |
| One call | $2$ | $4$ |
| Two calls, including repeated labels | $4$ | $6$ |

Measurements and adaptation change the comb coefficients, not this degree. A collection of accepted histories is one positive finite-slot subcomb, including histories integrated over measurement outcomes. The receiver may design its operations using full knowledge of the ensemble; for each fixed strategy its coefficients remain independent of the sampled $U$.

Use reference-first vectorization. Then

$$
|UPU^\dagger\rangle\!\rangle
  =(U^*\otimes U)|P\rangle\!\rangle.
$$

Full transposition of a queried Choi operator changes this representation to $U\otimes U^*$. The two-query fidelity objective therefore has signature

$$
(-,+,-,+,-,+)
\quad\text{on}\quad(P,A_I,A_O,B_I,B_O,F).
$$

There are three ordinary and three conjugate factors in this representation; conjugating a density operator gives six factors of each type. Its expectation is therefore controlled by the standard sixth moment. Entries of $U^\dagger$ are the same conjugate entries already included in the balanced moment. The sampled distribution need not be inverse closed for this argument. Global phases also cancel.

It follows that an exact unitary $6$-design preserves every zero-, one-, and two-query objective used by the Haar converse. This includes the initial device choice and two calls to the same device. What transfers is an **integrated prefix inequality**. One must not transfer the Haar proof's conditional assertion about the missing axis after revealing exact $A_U$: for a finite ensemble, exact knowledge of $A_U$ could reveal additional information about $B_U$.

The complete statistics of an arbitrarily long protocol need not agree with Haar statistics. Exact transfer is applied only to the short prefixes. The tail and stopping argument is then performed under $\mu$ itself.

## Mixed twirls and trace-norm factors

Condition (1) implies the same additive diamond bound for every standard moment $t\le6$: append normalized identities to the input, apply the sixth twirl, and trace out the extra copies. These are CPTP preprocessing and postprocessing maps.

For partial transpose $\Gamma_S$ on a subsystem of dimension $L$,

$$
\|\Gamma_S(X)\|_1\le L\|X\|_1.                    \tag{3}
$$

For a rank-one $|x\rangle\langle y|$, expand both vectors in Schmidt decompositions across $S$. The triangle bound is the product of their Schmidt-coefficient $\ell_1$ norms, at most $L$ for unit vectors. A singular-value decomposition extends the bound to arbitrary $X$, including reference ancillas.

Let $\Gamma_-$ transpose the negative wires of a mixed representation $R_U$, with $U^*$ on those wires and $U$ elsewhere. Pointwise in $U$,

$$
\operatorname{Ad}_{R_U}
 =\Gamma_-\circ\operatorname{Ad}_{U^{\otimes t}}
             \circ\Gamma_-.                        \tag{4}
$$

This identity gives the required mixed twirl from the standard twirl. Partial transpose is not being assumed CP or contractive: if there are $s$ negative $D$-dimensional wires, its two occurrences cost at most $D^{2s}$ by (3).

Use unnormalized channel Choi operators $J_G$, with trace $D$. For $k\le2$, the canonical fidelity objective is

$$
\Omega_{f,k}
 =\frac{J_C\otimes\bigotimes_{j=1}^k J_{G_j}^{T}}{D^2}.
$$

It is positive, has trace $D^{k-1}$, and has $k+1$ negative wires. Applying (3) on both sides of the standard $(2k+2)$-copy twirl difference gives

$$
\|\Omega_{f,k}^{\mu}-\Omega_{f,k}^{H}\|_1
 \le\epsilon D^{2k+2}D^{k-1}
 =\epsilon D^{3k+1}.                               \tag{5}
$$

The probability objective is

$$
\Omega_{p,k}
 =\frac{I_{P,F}\otimes\bigotimes_{j=1}^k J_{G_j}^{T}}D,
$$

with trace $D^{k+1}$. Twirl only the $2k$ query wires and treat the untouched $P,F$ identities as ancillas in the diamond norm. There are $k$ negative query wires, so

$$
\|\Omega_{p,k}^{\mu}-\Omega_{p,k}^{H}\|_1
 \le\epsilon D^{2k}D^{k+1}
 =\epsilon D^{3k+1}.                               \tag{6}
$$

Transposing the two identity ancillas would introduce an unnecessary $D^2$ factor. For $k=0$, acceptance is frame independent and the target moment is treated separately below.

### Frame-independent local Pauli noise

The physical slot is a fixed post-module Pauli mixture,

$$
G_{U}=\sum_P w_P\operatorname{Ad}_P
                      \circ\operatorname{Ad}_{A_U}
\quad\text{or}\quad
\sum_P w_P\operatorname{Ad}_P
                      \circ\operatorname{Ad}_{B_U},
$$

with frame-independent probabilities. For a fixed error $P$,

$$
J_{\operatorname{Ad}_P\circ G}^{T}
 =(I\otimes P^*)J_G^T(I\otimes P^T).
$$

Thus each fixed error tuple conjugates the ideal objective by a fixed unitary on its Choi output wires. This preserves the trace norm in (5)–(6). Averaging with the noise probabilities is contractive; no factor equal to the number of Pauli errors appears. Repeated labels use the corresponding repeated-axis seed and the same bound.

The local Pauli distribution is not globally covariant under $U$. Covariance is neither asserted nor needed: the fixed error conjugations are kept outside the ideal mixed twirl. The independent, fresh post-module noise assumption remains the one in NR-R01.

## The resource factor in a subcomb

Let $Q\ge0$ be an accepted $k$-call temporal subcomb. Its initial known instrument has launch effect $E$ on the original input. A deterministic completion with that same effect has trace $D^k\operatorname{Tr}E$. Positivity and domination by the completion give

$$
\|Q\|_\infty\le\operatorname{Tr}Q
 \le D^k\operatorname{Tr}E
 =D^{k+1}r_1,
\qquad r_1=\operatorname{Tr}E/D.                    \tag{7}
$$

Combining (5)–(7) bounds the change in either unnormalized objective by

$$
|\Delta p_k|,\ |\Delta q_k|
 \le\epsilon D^{4k+2}r_1.                          \tag{8}
$$

In particular, put

$$
\delta=\epsilon D^{10}\le\frac1{2000}.
$$

The two-query loss is $\delta r_1$, rather than an error paid once even by a strategy that almost never queries. Internal memory is absorbed into the finite external-slot comb; its implementation dimension does not occur in (7).

For adaptive temporal labels $EE,EF,FE,FF$, retain the label and instrument records and identify the two quantum sockets by time, rather than by device name. Insert arbitrary common channels into those sockets. The known instruments still form a valid completion. Hence the positive branch subcombs satisfy

$$
\sum_h\operatorname{Tr}Q_h\le D^3r_1.               \tag{9}
$$

Apply the uniform objective norm bound to each branch and sum (9). Assigning a separate full $r_1$ to every label would overcount the launch resource.

For a zero-query accepted map, let $\rho_0=J_{M_0}/D$, so $\operatorname{Tr}\rho_0=p_0$. Its target Bell projector has trace one and one negative wire in its two-copy mixed twirl. Equations (3)–(4) give

$$
|\Delta q_0|\le\epsilon D^2p_0=:d_0p_0,
\qquad\Delta p_0=0.                               \tag{10}
$$

## Transfer the one- and two-query prefixes together

Use the local Haar prefix inequalities from NR-R01. In its notation,

$$
r=\frac{81}{100},\qquad
A=\frac{2749735788563}{146597076480000},\qquad
\beta=\frac2{D^2},\qquad
\alpha_0=\frac1{D^2-1}.
$$

Partition accepted histories by $N=0,1,2,\ge3$, with weights $p_0,p_1,p_2,p_T$ and target-good weights $q_0,q_1,q_2,q_T$. The integrated short-prefix inputs are

$$
q_0\le\alpha_0p_0,\qquad
q_1+q_2-\beta p_1-rp_2\le Ar_1.                    \tag{11}
$$

The two-call inequality includes repeated-device histories by their missing-axis bound. The conditional missing-axis distribution is used only in establishing the Haar input (11), not after replacing its prior.

Represent accepted $N=1$ and $N=2$ histories as one two-call subinstrument. Pad an $N=1$ acceptance by storing its output and making a dummy second call on a discarded probe. Mark longer continuations as failure after the second call. Complete the remaining failed branches similarly. This preserves every accepted output for every $U$, and the completion retains the original launch effect. Padding is used only to estimate moments; the original $N$ and its expected cost are not changed in the stopping argument.

Transfer $q_1+q_2$ once, using the accepted subinstrument and (9), at cost at most $\delta r_1$. Transfer the weighted probability $\beta p_1+rp_2$ once as a positive CP effect: the histories are distinct instrument outcomes and their weights lie in $[0,r]$. Its loss is at most $r\delta r_1$. Therefore the combined error is precisely

$$
e r_1,
\qquad e=(1+r)\epsilon D^{10}
 \le\frac{181}{200000}<\frac1{1000}.                \tag{12}
$$

Together with (10), the transferred inequality is

$$
q\le(\alpha_0+d_0)p_0+\beta p_1+rp_2+p_T
                         +(A+e)r_1.                \tag{13}
$$

It is important to combine the one- and two-call accepted histories before transferring the weighted expression. Separate normalized branch estimates would lose the shared resource factor and would not justify the no-yield-floor conclusion.

### Arbitrarily long stopping histories

All probabilities and expectations in the rest of the argument are under $\mu$. Pointwise fidelity and event counting give

$$
q_T\le p_T,\qquad
r_1\ge p_1+p_2+p_T,\qquad
c=\mathbb E_\mu N\ge r_1+p_2+2p_T.                \tag{14}
$$

For unbounded possible $N$ with finite expectation, the tail-sum identity $c=\sum_{j\ge1}\Pr_\mu(N\ge j)$ follows from Tonelli. Only its first three nonnegative terms are used. Long-query histories need no moment approximation and may be perfect. No equality $c_\mu=c_H$, equality of total long-protocol outputs, fixed stopping horizon, or independence of stopping time from the frame is assumed.

Set

$$
k=1-r,\qquad b=3r+A-2.
$$

The coefficient conditions needed below are

$$
A+e\le k,\qquad
2r\ge1+\beta,\qquad
b+e\ge\alpha_0+d_0.                               \tag{15}
$$

Subtract $kc$ from (13), use (14), and then use $A+e-k\le0$. This gives

$$
\begin{aligned}
q-kc
&\le(\alpha_0+d_0)p_0+\beta p_1
 +(2r-1)(p_2+p_T)+(A+e-k)r_1\\
&\le(\alpha_0+d_0)p_0
 +(\beta+A+e-k)p_1+(b+e)(p_2+p_T)\\
&\le(b+e)(p_0+p_1+p_2+p_T).
\end{aligned}
$$

The last line uses $2r-1-\beta\ge0$ and the third condition in (15). Thus

$$
q\le(b+e)p+kc.                                    \tag{16}
$$

For the parameter range of NR-R01, the conditions hold even after relaxing $e$ to $1/1000$ and $d_0$ to $1/2000$. Their scalar arithmetic is checked exactly in [local_recovery.py](../checks/recovery/local_recovery.py).

For the main Bell game, put $B=b+e$. Its score is $\mathsf S=2q-p$. If $B<1/2$, then

$$
\mathsf S\le\frac{q-Bp}{1-B}
 \le\frac{k}{1-B}\,c,                               \tag{17}
$$

because

$$
(1-B)(2q-p)-(q-Bp)=(1-2B)(q-p)\le0.
$$

For the optional secret-plaintext variant, the projective $2$-design identity instead gives

$$
R=\frac{2Dq-(D-1)p}{D+1}.
$$

If $b+e<(D-1)/(2D)$, combine $q\le p$ with (16) to obtain

$$
R\le\frac{q-(b+e)p}{1-b-e}
 \le\frac{k}{1-b-e}\,c.
$$

Indeed, after multiplying the first inequality by $(D+1)(1-b-e)$, its left side minus its right side is

$$
\bigl(D-1-2D(b+e)\bigr)(q-p)\le0.
$$

This transfers the receiver bound without imposing a minimum acceptance yield or interpreting a frame-dependent accepted map as a normalized channel. NR-R01 owns the resulting numerical payoff comparison.

## The switch is a fixed positive process

The same approximation controls the prescribed switch, without treating it as an ordinary causal comb. Define the two temporal wiring vectors by their components

$$
\begin{aligned}
(v_{EF})_{p,a_i,a_o,b_i,b_o,f}
 &=\delta_{p,a_i}\delta_{a_o,b_i}\delta_{b_o,f},\\
(v_{FE})_{p,a_i,a_o,b_i,b_o,f}
 &=\delta_{p,b_i}\delta_{b_o,a_i}\delta_{a_o,f}.
\end{aligned}
$$

They satisfy

$$
\|v_{EF}\|^2=\|v_{FE}\|^2=D^3,
\qquad\langle v_{EF},v_{FE}\rangle=D.
$$

For a $|+\rangle$ control and the minus outcome, the process operator is

$$
Q_-=
 \left|\frac{v_{EF}-v_{FE}}2\right\rangle
 \left\langle\frac{v_{EF}-v_{FE}}2\right|\ge0,
\qquad
\operatorname{Tr}Q_-=\frac{D^3-D}{2}\le D^3.        \tag{18}
$$

Equations (5)–(6) and (18), including the fixed local-Pauli conjugations, imply

$$
|\Delta p_{\rm sw}|,\ |\Delta q_{\rm sw}|
 \le\epsilon D^{10}=\delta.                        \tag{19}
$$

No causality property of $Q_-$ is needed for this trace/objective pairing estimate. The main Bell score $2q-p$ has absolute coefficient sum exactly $3$. The optional plaintext score has sum $(3D-1)/(D+1)<3$. Both therefore lose at most $3\delta$.

The optional scalar phase-dephasing visibility $\nu\in[0,1]$ replaces the minus map by

$$
M_-(\nu)=\nu M_-+\frac{1-\nu}{2}C_{\rm diag},
\qquad C_{\rm diag}=\frac{F\circ E+E\circ F}{2}.
$$

This identity holds for arbitrary channels. Its fixed process is positive and has trace

$$
\nu\frac{D^3-D}{2}+(1-\nu)\frac{D^3}{2}
 =\frac{D^3-\nu D}{2}\le D^3.
$$

Thus (19) and the same $3\delta$ score loss remain valid. This transfers the specified visibility model; arbitrary faulty routing requires its own error model.

## Finite gates and a fixed random-bit budget

The implementation source is Brandão, Harrow and Horodecki, [*Local random quantum circuits are approximate polynomial-designs*, corrected arXiv v4](https://arxiv.org/html/1208.0692v4), published in *Communications in Mathematical Physics* **346**, 397–434 (2016), [DOI](https://doi.org/10.1007/s00220-016-2706-8). The corrected version supplies the relevant norm conventions and finite-gate corollary.

Their Definition 2 uses a relative CP-order parameter $\eta$:

$$
(1-\eta)\mathcal T_{H,t}
 \preceq_{\rm CP}\mathcal T_{\mu,t}
 \preceq_{\rm CP}(1+\eta)\mathcal T_{H,t}.
$$

Their Lemma 3 implies full diamond error at most $2\eta$. If sampling and alphabet gates are exact, $\eta\le\epsilon/2$ suffices for (1). To retain explicit sampling and synthesis reserves, instead choose

$$
\eta\le\epsilon/4,                                \tag{20}
$$

so the ideal random-circuit ensemble spends at most $\epsilon/2$. At the maximal tolerance in (1), this is $\eta\le1/(8000D^{10})$.

Corollary 7 applies to a fixed finite inverse-closed universal algebraic gate alphabet $G\subset SU(d^2)$. For fixed local dimension $d=2$ and $t=6$, it gives sequential nearest-neighbor circuit length

$$
L=O_G\!\left(n\,[n+\log(1/\eta)]\right).           \tag{21}
$$

Here $d$ is the local dimension and $D=2^n$ the global dimension. With $\epsilon$ a fixed positive constant times $D^{-10}$, (20)–(21) give $L=O_G(n^2)$. The gate-set-dependent constant is not a practical numerical depth estimate. The sequential construction has no even-$n$ restriction. A Clifford-only alphabet is insufficient for this sixth moment. An inverse-closed algebraic universal two-qubit alphabet may be chosen up to physically irrelevant global phases; these cancel in every balanced twirl and in the conjugated modules.

For comparison of norm conventions, BHH also use spectral moment error $g(\mu,t)$, and their Lemma 4 gives relative error at most $D^{2t}g(\mu,t)$. Thus $g(\mu,6)\le\epsilon/(4D^{12})$ suffices for (20). A bare claim $g\le\epsilon$ would omit a dimension factor. The needed small spectral error enters the walk length logarithmically.

At each of the $L$ sequential steps, the ideal sampler chooses an edge and an alphabet gate uniformly. Let

$$
M=(n-1)|G|.
$$

Exact uniform integer sampling has polynomial expected bit cost. A fixed finite-bit sampler is also sufficient. Draw $b$ fair bits per step and reduce the represented integer modulo $M$. The total variation error per step is at most $M/2^b$; the word-distribution error is at most $LM/2^b$. Averaging unitary channels changes the standard sixth twirl by at most twice this total variation. Therefore choose

$$
b\ge\left\lceil\log_2\frac{8LM}{\epsilon}\right\rceil. \tag{22}
$$

The resulting sampling error is at most $\epsilon/4$ in full diamond norm. For fixed precision constant in $\epsilon=\Theta(D^{-10})$, $b=O(n+\log n)$; the seed length $Lb$ and generation time are polynomial, with $O_G(n^3)$ seed bits sufficient. This elementary sampling calculation is separate from the BHH mixing theorem.

In the ideal finite-alphabet model, the word specifies its algebraic unitaries exactly. If each local gate is instead compiled to a unitary with operator-norm error at most $\xi$, then telescoping and sixfold tensoring give

$$
\|\operatorname{Ad}_{U^{\otimes6}}
   -\operatorname{Ad}_{\widetilde U^{\otimes6}}\|_\diamond
 \le12L\xi.
$$

Choosing $\xi\le\epsilon/(48L)$ spends the remaining $\epsilon/4$. The ideal-design, finite-bit, and optional compilation contributions then total at most $\epsilon$. The required logarithmic precision is polynomial. Noisy nonunitary native gates require a separate physical error budget; the design theorem concerns ideal unitary generation.

Once the word is selected, its adjoint is obtained by reversing the word and taking gate inverses. The source modules $U(X\otimes I)U^\dagger$ and $U(Y\otimes I)U^\dagger$, and the source scrambling operation, consequently have polynomial ideal gate descriptions and preserve the promised anticommutation relation. This does not expose the selected word to the receiver.

An exact finite $6$-design is sufficient for zero transfer loss, but exact-design existence alone does not establish efficient sampling or synthesis in $n$. The approximate finite-gate construction above is the implementation used here. It invokes no pseudorandom-unitary or computational indistinguishability assumption; the ordinary comparison remains information theoretic.

## Verification and scope

The degree count, mixed-twirl norm estimates, and comb trace argument above are analytic proofs. [local_recovery.py](../checks/recovery/local_recovery.py) checks the scalar coefficient conditions and resulting rational bounds. [Checks and their scope](../checks/README.md) records the executable evidence and its limits. These checks are not a new formal-kernel verification of the complete theorem.

This method removes the need to generate a generic Haar matrix. It does not assert that a sixth design fools arbitrary long-query receivers, that a stopping transcript preserves the original frame prior after conditioning, or that Haar and design expected costs coincide. It also does not change NR-R01's fresh-frame convention, hidden-label delivery rule, classical oracle-label interface, or post-module noise model. Hardware runtime, persistent-device amortization, and arbitrary control faults remain separate questions.
