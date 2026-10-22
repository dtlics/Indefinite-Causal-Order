# Local-noise moment bound and homogeneous two-call frontier

This is the analytic local-noise proof component of [NR-R01](../theorem.md), not a separate research result. It proves the six-wire operator estimate and the homogeneous inequality

$$
q-rp\le a_D(r,\mu)w,
\qquad
a_D(r,\mu)=\frac{3r(1-r)}D+
\frac{4\mu}{(1-D^{-2})^2}+\frac{128}{D^2}.
\tag{1}
$$

Here $w$ is the probability of launching a first query, before any module has been used. The stopping-time, recovery-score, finite-parameter, and design-transfer consequences are owned by [the main theorem](../theorem.md).

## Model, metric, and notation

Let $D=2^n\ge8$, let $U$ be Haar distributed on $U(D)$, and set

$$
A_U=U(X\otimes I_{D/2})U^\dagger,
\quad B_U=U(Y\otimes I_{D/2})U^\dagger,
\quad W_U=B_UA_U.
$$

Thus $A_U,B_U$ are traceless Hermitian involutions and $A_UB_U=-B_UA_U$. A global phase of $W_U$ does not change the target channel. The two physical modules are

$$
\mathcal E_U=\mathcal N_E\circ\operatorname{Ad}_{A_U},
\qquad
\mathcal F_U=\mathcal N_F\circ\operatorname{Ad}_{B_U},
$$

where the known post-unitary noise channels are Pauli mixtures

$$
\mathcal N_E(\rho)=\sum_P e_P P\rho P,
\qquad
\mathcal N_F(\rho)=\sum_Q f_Q Q\rho Q.
$$

The Pauli representatives are Hermitian, orthogonal in Hilbert–Schmidt inner product, and include $I$. The probabilities sum to one. Noise is fresh and independent between invocations, including repeated uses of the same module. No error label is available. The main theorem uses identical product distributions, but the proof only needs independent distributions $e,f$. Define

$$
r=e_If_I,
\qquad
\mu=\max_{(P,Q)\ne(I,I)}e_Pf_Q,
\qquad
\beta=\frac2{D^2}.
\tag{2}
$$

In particular, $\mu$ is the **largest joint nonidentity error-pair probability**. It is neither the largest marginal error probability nor the total probability of an error. Assume $r\ge\beta$.

An ordinary strategy has at most two total module calls. It may use arbitrary noiseless memory, encodings, known coherent processing and routing among registers, entangled probes, input-dependent success flags, classical adaptive module selection, repeated-module calls, and early stopping. Its two calls may be spent on training or program probes. Additional free queries, coherent oracle-identity multiplexing, and noise-environment records are not supplied.

Let $\lvert\Phi_D\rangle=D^{-1/2}\sum_i\lvert i,i\rangle$, and let $\mathcal M_U^s$ be the accepted physical output operation. With an inaccessible Bell reference, write

$$
\sigma_U=(\operatorname{id}\otimes\mathcal M_U^s)
 (\lvert\Phi_D\rangle\langle\Phi_D\rvert),
\quad
p=\mathbb E_U\operatorname{Tr}\sigma_U,
\quad
q=\mathbb E_U\langle W_U\rvert\sigma_U\lvert W_U\rangle,
$$

where $\lvert W_U\rangle=(I\otimes W_U)\lvert\Phi_D\rangle$. Then $0\le q\le p$. These are prior-averaged, unnormalized accepted quantities. A fixed-frame success probability can depend on the input; the proof does not assert a fixed-frame conditional channel or diamond-norm guarantee.

Let $E$ be the input effect of the initial event that launches a first query. This event occurs before any module use, so $E$ is independent of $U$. Its Bell-input probability is

$$
w=\frac{\operatorname{Tr}E}{D}.
\tag{3}
$$

The factor $w$ in (1) is retained throughout the proof.

## Six-wire normalization

Use physical wire order

$$
(P,A_I,A_O,B_I,B_O,F)=(0,1,2,3,4,5).
$$

For a matrix $M$, its **unnormalized** Choi ket is

$$
\lvert M\rangle\!\rangle_{\mathrm{in},\mathrm{out}}
=\sum_{i,o}M_{oi}\lvert i\rangle_{\mathrm{in}}
 \lvert o\rangle_{\mathrm{out}}.
$$

A unitary Choi ket has squared norm $D$. Put

$$
g_U=\frac1D
\lvert W_U\rangle\!\rangle_{05}\otimes
\lvert\overline{A_U}\rangle\!\rangle_{12}\otimes
\lvert\overline{B_U}\rangle\!\rangle_{34},
\qquad
\Omega=\mathbb E_U\lvert g_U\rangle\langle g_U\rvert.
\tag{4}
$$

The bars are entrywise conjugation. Thus $\|g_U\|^2=D$ and $\operatorname{Tr}\Omega=D$, rather than one. The conjugated slot kets implement the transposed module Choi matrices in the link convention. The normalized Bell input and target projection supply the total factor $D^{-2}$. For a successful ordinary comb $C_s$, its ideal target-good weight is $\operatorname{Tr}(C_s\Omega)$.

The mixed-tensor signature of the six wires is

$$
(-,+,-,+,-,+).
$$

Write $\lvert\Omega_{ij}\rangle=\sum_a\lvert a\rangle_i\lvert a\rangle_j$ for an unnormalized cup and define the two composition wirings

$$
v_{EF}=\lvert\Omega_{01}\rangle\lvert\Omega_{23}\rangle
 \lvert\Omega_{45}\rangle,
\qquad
v_{FE}=\lvert\Omega_{03}\rangle\lvert\Omega_{41}\rangle
 \lvert\Omega_{25}\rangle.
\tag{5}
$$

They satisfy

$$
\|v_{EF}\|^2=\|v_{FE}\|^2=D^3,
\qquad \langle v_{EF},v_{FE}\rangle=D.
$$

The operator estimate needed below is

$$
\boxed{\quad
\Omega=\lvert\xi\rangle\langle\xi\rvert+R,
\qquad
\xi=\frac{v_{EF}-v_{FE}}{D(D^2-1)},
\qquad
0\le R\le\frac{128}{D^5}I.
\quad}
\tag{6}
$$

## Exact invariant projection and the entire adjoint layer

The invariant subspace is spanned by the six bijections between the three plus and three minus wires. Their cup-matching Gram matrix is

$$
G_{\sigma,\tau}=D^{\#\operatorname{cycles}(\sigma^{-1}\tau)}.
$$

Direct contraction of (4) gives

$$
\langle v_{EF},g_U\rangle=1,
\qquad
\langle v_{FE},g_U\rangle=-1,
$$

and zero for the other four matchings. The vanishing contractions contain a trace of one axis or of a product of two distinct axes. The two nonzero matchings differ by a three-cycle. Their signed overlap vector is orthogonal to the constant and permutation-parity vectors, and the cup Gram matrix has eigenvalue $D(D^2-1)$ on that vector. Equivalently, a direct multiplication of the six-by-six Gram matrix gives

$$
P_{\mathrm{inv}}g_U=\xi,
\qquad
\|\xi\|^2=\frac2{D(D^2-1)}.
\tag{7}
$$

The other five invariant directions have zero weight. Haar averaging removes cross terms between $\xi$ and its orthogonal complement, so subtracting $\lvert\xi\rangle\langle\xi\rvert$ leaves a positive operator.

The span of tensors with at least two disjoint cups is generated by 18 partial matchings, each leaving one plus and one minus wire open. The remaining matrix splits into its scalar and traceless parts. The scalar parts span the six invariants; the traceless parts span the **whole adjoint isotypic component**, including all 18 multiplicity copies.

Contract $g_U$ against any such two-cup matching. If its contraction graph has a closed component, that component contains the trace of one of $A_U,B_U,W_U$, or the trace of two distinct axes, and is zero. Otherwise the open chain contains all three axes. Since $A_U,B_U,W_U=B_UA_U$ form a quaternion triple, their product in any order is a scalar multiple of $I$. It is orthogonal to every remaining traceless matrix. Hence every two-cup traceless contraction vanishes, and the adjoint isotypic component of $g_U$, and therefore of $\Omega$, is exactly zero.

## Complete one-cup weight bound

For each of the nine plus-minus pairs $e$, let

$$
Q_e=\lvert\Omega_e\rangle\langle\Omega_e\rvert\otimes I,
\qquad \Pi_e=Q_e/D.
$$

Let $L$ be the full two-cup span and $J=L^\perp$. Cup composition preserves $L$: it reconnects two cups or produces three. Since $Q_e$ is Hermitian, it also preserves $J$, and $\Pi_e|_J$ is an orthogonal projection. The span of these nine restricted ranges is the complete one-cup harmonic layer $K_1$.

For disjoint pairs $e,f$, $\Pi_e\Pi_f$ projects into a two-cup space, so it vanishes on $J$. For pairs sharing one wire, direct contraction gives

$$
Q_eQ_fQ_e=Q_e,
\qquad
\Pi_e\Pi_f\Pi_e=\Pi_e/D^2.
\tag{8}
$$

Their range overlap therefore has operator norm at most $1/D$. The nine cups form a three-by-three rook graph: each cup has four shared-endpoint neighbors, while its other four distinct neighbors are disjoint.

Let $T((x_e)_e)=\sum_ex_e$ be the synthesis map from the direct sum of the restricted ranges. Its Gram form has identity diagonal, off-diagonal norm at most $1/D$ on the rook graph, and zero elsewhere. Applying $2ab\le a^2+b^2$ on its edges gives

$$
T^\dagger T\ge(1-4/D)I,
\qquad
\sum_e\Pi_e\ge(1-4/D)P_{K_1}\quad\text{on }J.
\tag{9}
$$

This is an operator-valued frame estimate, including all multiplicities. It also shows that the nine harmonic cup insertions form a direct sum in the stable range used here.

Of the nine cup contractions of $g_U$, three close one axis and vanish. Each of the other six unnormalized contractions has squared norm one; its normalized projection weight is therefore $1/D$. Thus

$$
\sum_e\|\Pi_eg_U\|^2=6/D.
$$

Projection to $J$ cannot increase the sum, because every $\Pi_e$ commutes with $P_J$. For $D\ge8$, (9) consequently gives the total one-cup weight

$$
\|P_{K_1}g_U\|^2
\le\frac{6/D}{1-4/D}
=\frac6{D-4}\le\frac{12}D.
\tag{10}
$$

## Sector completeness and physical Weyl dimensions

The representation-theory input is the stable mixed-tensor decomposition for $U^{\otimes3}\otimes\overline U^{\otimes3}$. Mixed Schur–Weyl duality in this setting is given by [Grinko and Ozols, Theorem 3.8 and Remark 3.10](https://doi.org/10.1007/s00220-024-05108-1); the original mixed-tensor treatment is [Benkart et al.](https://doi.org/10.1006/jabr.1994.1166). See the topic [references](../references.md). Our range $D\ge8>3+3$ is stable.

The contraction filtration identifies the lower layers explicitly above. Its complete physical decomposition is:

| Layer | Physical irreducible sectors | Multiplicity |
| --- | --- | --- |
| Three cups | Trivial, dimension 1 | 6 |
| Two cups | Adjoint, dimension $D^2-1$ | 18 |
| One cup | Four pairs $(\lambda,\mu)$, $\lambda,\mu\vdash2$ | 9 each |
| No cups | Nine pairs $(\lambda,\mu)$, $\lambda,\mu\vdash3$ | $f_\lambda f_\mu$ |

Here $f_{(3)},f_{(21)},f_{(111)}=1,2,1$. There are 15 distinct physical irreducible sectors. Their multiplicity squares sum to $720$, and their multiplicity-weighted physical dimensions sum to $D^6$. These identities check the formulas; the spanning/classification assertion is the mixed-tensor theorem, not an inference from the dimension sums alone.

For partitions $\lambda,\mu$, the physical dimension is obtained from the mixed Weyl product

$$
d_{\lambda,\mu}(D)=s_\lambda(1^D)s_\mu(1^D)
\prod_{i,j}
\frac{t_{ij}(t_{ij}+\lambda_i+\mu_j)}
 {(t_{ij}+\lambda_i)(t_{ij}+\mu_j)},
\qquad t_{ij}=D+1-i-j,
\tag{11}
$$

where $s_\lambda(1^D)=\prod_{(i,j)\in\lambda}(D+j-i)/h_{ij}$ is the hook-content dimension. These are the **physical irrep dimensions**, not the at-most-18-dimensional multiplicity matrices.

For the quartic sectors, the symmetric table in partition order $(2),(11)$ is

$$
\begin{aligned}
d_{2,2}&=D^2(D-1)(D+3)/4,\\
d_{2,11}&=(D-2)(D-1)(D+1)(D+2)/4,\\
d_{11,11}&=D^2(D-3)(D+1)/4=:d_4.
\end{aligned}
$$

The differences from $d_4$ are $D^3$ and $(D^3-D^2+2)/2$, so $d_4$ is the minimum. For $D\ge8$,

$$
\frac{d_4}{D^4}
=\frac{(1-3/D)(1+1/D)}4
\ge\frac5{32}>\frac18.
\tag{12}
$$

The sextic dimension table is symmetric in its two partitions. Its six distinct entries are

$$
\begin{aligned}
d_{3,3}&=D^2(D-1)(D+1)^2(D+5)/36,\\
d_{3,21}&=D^2(D-2)(D-1)(D+2)(D+4)/18,\\
d_{3,111}&=(D-3)(D-2)(D-1)(D+1)(D+2)(D+3)/36,\\
d_{21,21}&=(D-3)(D-1)^2(D+1)^2(D+3)/9,\\
d_{21,111}&=D^2(D-4)(D-2)(D+1)(D+2)/18,\\
d_{111,111}&=D^2(D-5)(D-1)^2(D+1)/36=:d_6.
\end{aligned}
\tag{13}
$$

For completeness, the five differences from $d_6$ factor as

$$
\begin{aligned}
d_{3,3}-d_6&=D^3(D-1)(D+1)/3,\\
d_{3,21}-d_6&=D^2(D-1)(D^3+13D^2-7D-37)/36,\\
d_{3,111}-d_6&=(D-1)(D+1)(D^3-3D^2+6)/6,\\
d_{21,21}-d_6&=(D-1)^2(D+1)(D^3+3D^2-12D-12)/12,\\
d_{21,111}-d_6&=D^2(D+1)(D^3-D^2-19D+37)/36.
\end{aligned}
$$

The four residual cubics, at $D=8+x$, are respectively

$$
x^3+37x^2+393x+1251,\quad
x^3+21x^2+144x+326,\quad
x^3+27x^2+228x+596,\quad
x^3+23x^2+157x+333.
$$

They are positive for $x\ge0$, proving that $d_6$ is the minimum. Moreover

$$
\frac{d_6}{D^6}
=\frac{(1-1/D)^2(1-5/D)(1+1/D)}{36}
\ge\frac{147}{18432}>\frac1{128}
\quad(D\ge8).
\tag{14}
$$

## Haar twirling and the remainder

On an isotypic component $V_\lambda\otimes M_\lambda$, Haar twirling a rank-one positive operator gives

$$
\frac{I_{V_\lambda}}{d_\lambda}
\otimes
\operatorname{Tr}_{V_\lambda}
 \lvert g_\lambda\rangle\langle g_\lambda\rvert.
$$

Its operator norm is at most the **total isotypic trace weight** divided by the physical dimension $d_\lambda$. This handles arbitrary multiplicity coherences without an additional factor of 9 or 18.

By (10) and (12), every quartic block is bounded by

$$
\frac{12/D}{D^4/8}=\frac{96}{D^5}.
$$

The bulk trace weight is at most $\|g_U\|^2=D$, so (14) bounds every sextic block by

$$
\frac{D}{D^6/128}=\frac{128}{D^5}.
$$

There is no adjoint block, and the whole invariant component has already been removed exactly in (7). Cross terms between inequivalent sectors vanish under the twirl. This proves (6), including positivity of $R$ and all multiplicities.

## Post-Pauli errors and the joint-pair bound

An output error $P$ after $A$, and $Q$ after $B$, conjugates the ideal objective on wires 2 and 4 by

$$
V_{PQ}=\overline P_2\,\overline Q_4.
$$

For Hermitian Pauli representatives, a bar changes only a harmless phase. The nonidentity-error part of the performance operator is

$$
\Omega_{\mathrm{err}}=
\sum_{(P,Q)\ne(I,I)}e_Pf_Q
 V_{PQ}\Omega V_{PQ}^\dagger.
\tag{15}
$$

The remainder contribution is at most $128I/D^5$, since this is a subnormalized mixture of unitary conjugations of $R$.

For each wiring order separately, the Pauli errors act on two different cups. Thus its $D^4$ shifted wiring kets are orthogonal:

$$
\langle V_{PQ}v_{\mathrm{ord}},
 V_{P'Q'}v_{\mathrm{ord}}\rangle
=D^3\delta_{P,P'}\delta_{Q,Q'}.
\tag{16}
$$

Consequently

$$
\sum_{(P,Q)\ne(I,I)}e_Pf_Q
 \lvert V_{PQ}v_{\mathrm{ord}}\rangle
 \langle V_{PQ}v_{\mathrm{ord}}\rvert
\le D^3\mu I.
$$

Using $\lvert x-y\rangle\langle x-y\rvert
\le2\lvert x\rangle\langle x\rvert+2\lvert y\rangle\langle y\rvert$ on the two wiring families, and then (6), gives

$$
0\le\Omega_{\mathrm{err}}
\le\left[\frac{4D\mu}{(D^2-1)^2}+
 \frac{128}{D^5}\right]I.
\tag{17}
$$

No orthogonality of the shifted **difference** vectors $V_{PQ}\xi$ is assumed. Orthogonality is used only for each separate wiring family in (16).

## Comb normalization and initial query effects

In wire order $0,\ldots,5$, a deterministic one-each channel comb obeys

$$
\operatorname{Tr}_5 C=C^{(1)}_{0123}\otimes I_4,
\quad
\operatorname{Tr}_3 C^{(1)}=C^{(0)}_{01}\otimes I_2,
\quad
\operatorname{Tr}_1 C^{(0)}=I_0.
$$

Therefore $\operatorname{Tr}C=D^3$. A success comb is dominated by a deterministic completion. For an initial querying subinstrument with input effect $E$, the final prefix equality has $E^{\mathsf T}$ in place of $I_0$ in this input-first Choi convention, and the completion trace is

$$
D^2\operatorname{Tr}E=D^3w.
\tag{18}
$$

It follows from positivity, (17), and (18) that the nonidentity-error good weight is at most

$$
b_D(\mu)w,
\qquad
b_D(\mu)=\frac{4\mu}{(1-D^{-2})^2}+\frac{128}{D^2}.
\tag{19}
$$

An input-dependent initial instrument can choose the first module and retain quantum memory. If its branch effects are $E_j$, their maximally mixed input probabilities are $\alpha_j=\operatorname{Tr}E_j/D$, with $\sum_j\alpha_j=w$. Completing subsequent processing gives branch comb trace $D^3\alpha_j$. Summing (19) therefore charges $b_D(\mu)w$ only once. Dividing a branch map by $\alpha_j$ is not assumed to turn it into a channel.

For the opposite query order, relabel the slots; $AB=-BA$ changes only the target's global phase. The same operator and trace bounds apply. For acceptance-only estimates the inaccessible Bell reference may be traced out, leaving a subnormalized query-memory **state** of trace $\alpha_j$; normalizing that state is legitimate and does not normalize the branch map.

## Acceptance transfer without replacing the physical noise model

The [four-port acceptance bound](acceptance.md) states that any one-each causal acceptance tester with initial trace $w$ satisfies

$$
\left|p_{II}-p_{\Omega_D,\Omega_D}\right|
\le\frac{3w}{2D},
\qquad
\Omega_D(\rho)=\operatorname{Tr}(\rho)I/D.
\tag{20}
$$

Full replacement is only a mathematical reference experiment in this step. The actual noise remains the specified local Pauli channel.

For fixed known errors $P,Q$, absorb their output conjugations into the tester. This preserves its initial normalization and is a legal causal circuit. Its all-replacement event probability is unchanged, because those output conjugations fix $\Omega_D$. Applying (20) to the original and modified testers gives

$$
\lvert p_{PQ}-p_{II}\rvert\le\frac{3w}D.
$$

The identity pair has probability $r$ and no deviation. For ideal acceptance $x$ and acceptance $y$ under the actual physical error mixture,

$$
\lvert y-x\rvert\le\frac{3(1-r)}D\,w.
\tag{21}
$$

This does not assume that the local noise is globally covariant or close in diamond norm to replacement noise.

## Repeated calls, stopping, and the homogeneous frontier

Retain only successful histories that query both module identities. On a launched path that stops early or requests a repeated identity, mark failure and make a dummy call to the unused identity. This is a mathematical one-each completion on the launched paths; it preserves the retained success operation on **every** pair of physical channels and does not require a third call. Initial zero-query paths stay outside this completion. Its initial querying effect is the original $E$, so all estimates retain the same $w$.

Let $x,y$ be this retained event's ideal and actual noisy acceptance probabilities. Its identity-pair good weight is at most $rx$, while (19) bounds the rest. Thus

$$
q_{\mathrm{one\ each}}\le rx+b_D(\mu)w.
\tag{22}
$$

Every other accepted history has queried at most one hidden axis, possibly twice. Condition mathematically on the queried reflection $A$. In a basis with $A=\operatorname{diag}(I_m,-I_m)$, the missing reflection is

$$
B=\begin{pmatrix}0&V\\V^\dagger&0\end{pmatrix},
\qquad V\text{ Haar on }U(m),\quad m=D/2.
$$

The normalized target Choi projector has conditional average

$$
\mathbb E_{B\mid A}\lvert W\rangle\langle W\rvert
=\frac2{D^2}\Pi_{\mathrm{off}},
\tag{23}
$$

where $\Pi_{\mathrm{off}}$ projects onto the two off-diagonal matrix blocks. This follows from the first unitary moment of $V$; cross terms vanish under $V\mapsto e^{i\theta}V$. The output of a branch that queries only $A$, even repeatedly and with known local noise, depends on $A$ and not on this missing $V$. Positivity therefore bounds its good weight by $\beta$ times its success probability. The same holds with the identities exchanged. A zero-query branch obeys the smaller bound $1/(D^2-1)\le\beta$, since the unconditional target Choi state is uniform on the traceless-operator subspace.

This missing-axis argument applies to repeated or missing-identity histories. It is not applied to one-each local-error histories, which still retain both axes.

Writing $p=y+p_{\mathrm{miss}}$, combine (21)–(23):

$$
\begin{aligned}
q-rp
&\le r(x-y)+b_D(\mu)w+(\beta-r)p_{\mathrm{miss}}\\
&\le\left[\frac{3r(1-r)}D+b_D(\mu)\right]w,
\end{aligned}
$$

where the last step uses $r\ge\beta$. This proves (1) for arbitrary ordinary at-most-two-total-call instruments, including initial order selection, repeats, early stopping, quantum memory, encoders, flags, and query-input probes.

The intercept is homogeneous in the **original first-query probability**. In particular, an initial instrument may decide whether to query as a function of the unknown input. The proof scales both the comb trace and the acceptance bound by the same $w$; it never gives separate normalization to later continuations. This is the precise input needed by the main theorem's [expected-stopping and physical recovery argument](../theorem.md).

## Exact checks and proof scope

The current local replay entry points are [structural contractions](../checks/local/verify_structural.py) and [physical dimensions](../checks/local/verify_dimensions.py). They reproduce the six invariant overlaps, all 18 two-cup contractions, cup-composition and rook-graph identities, Weyl products, dimension sums, and lower-bound arithmetic. The mixed-tensor classification cited above remains the explicit representation-theory input; a dimension sum or a finite spectral sample alone would not establish completeness.

The result is a Haar-prior operator inequality and a prior-averaged accepted-score frontier. It does not become a worst-frame guarantee or a fixed-frame conditional channel statement. The physical local-noise model, calibrated parameter choices, approximate-design transfer, and operational expected-cost theorem are stated once in [NR-R01](../theorem.md).
