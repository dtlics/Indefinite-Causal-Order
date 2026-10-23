# Capacity certificates from commutators and nonunitality

This is a proof component of [NR-R20](../memory-qualification.md#nr-r20).
It gives a channel-level entropy and capacity certificate for every finite
dimensional CPTP map, with nonunitality charged separately. For unital
channels only identity entanglement fidelity and the self-switch statistic
are required. The earlier
[orthogonal-unitary proof](pauli-entropy-capacity.md) and
[bounded-overlap proof](unitary-error-overlap.md) retain their realization
entropy statements and model-specific comparisons. Here the entropy being
bounded is the channel's Choi entropy, so no random-unitary representation
or orthogonal-unitary promise is needed.

The [exact checker](../checks/architecture/verify_unital_entropy.py) checks
the index, energy, spectral-tail, full pinching and flagged-channel
identities on non-mixed-unitary, Schur and nonunital examples.
Its finite cases do not prove the all-dimension entropy or coding theorems.
No efficient encoder, native model or query advantage is established.

Let $\mathcal E(X)=\sum_iK_iXK_i^\dagger$ be a channel on dimension
$D\ge2$, with $n=\log_2D$, normalized Choi state
$J=D^{-1}\sum_i|K_i\rangle\!\rangle\langle\!\langle K_i|$,
and define
$$
\eta=\frac1D\operatorname{Re}\sum_{i,j}
 \operatorname{Tr}(K_j^\dagger K_i^\dagger K_jK_i),
\quad e=1-\eta,\quad
u=\frac{\|\mathcal E(I)-I\|_F^2}{D}.
$$
The identity entanglement fidelity is
$$
f=\langle\Phi_D|J|\Phi_D\rangle
 =\sum_i\left|\frac{\operatorname{Tr}K_i}{D}\right|^2,
\qquad r=1-f.
$$
Here $|\Phi_D\rangle=D^{-1/2}\sum_a|a\rangle|a\rangle$;
when used as an operator, $\Phi_D=|\Phi_D\rangle\langle\Phi_D|$
denotes its normalized rank-one projector.
The channel is fixed and used independently. Capacities below are
unassisted asymptotic entanglement-transmission rates in qubits per
$D$-dimensional use, with arbitrary encoding and decoding, no
input-bearing clean bypass and no two-way assistance.

All displayed channel quantities are independent of the Kraus representation. In particular,
unitary mixing or isometric padding of the Kraus list preserves each
double commutator-energy sum below.

## 1. A general CP-family spectral lemma

Take any finite family of square matrices $L_i$, not necessarily a channel.
Set
$$
J_L=\frac1D\sum_i|L_i\rangle\!\rangle\langle\!\langle L_i|,
\quad m=\operatorname{Tr}J_L>0,\quad
G=\frac1{2D}\sum_{i,j}\|[L_i,L_j^\dagger]\|_F^2.
$$
Then
$$
S(J_L/m)\le
\min\left\{2n,\ \left(1+\frac{\sqrt G}{m}\right)n+C_D\right\},
\qquad C_D=\frac{2-D^{-1}}{\ln2}<3.                 \tag{A}
$$

To prove it, use a canonical Hilbert--Schmidt orthogonal Kraus list for
$J_L/m$, denoted $M_i=L_i'/\sqrt m$. Its eigenvalue probabilities are
$q_i=\operatorname{Tr}(M_i^\dagger M_i)/D$ and
$\operatorname{Tr}(M_i^\dagger M_j)=Dq_i\delta_{ij}$.
The global mixed-adjoint energy is $G/m^2$. The number of nonzero
eigenvalues is at most $D^2$.

For any subset $T$ of this canonical list put
$$
A_T=\sum_{i\in T}M_i^\dagger M_i,\quad
B_T=\sum_{i\in T}M_iM_i^\dagger,\quad
w=\frac{\operatorname{Tr}A_T}{D}
 =\frac{\operatorname{Tr}B_T}{D}=\sum_{i\in T}q_i,
$$
and
$$
\eta_T=\frac1D\operatorname{Re}\sum_{i,j\in T}
 \operatorname{Tr}(M_j^\dagger M_i^\dagger M_jM_i).
$$
Direct expansion, including the non-Hermitian case, gives
$$
\frac1{2D}\sum_{i,j\in T}\|[M_i,M_j^\dagger]\|_F^2
=\frac{\operatorname{Tr}A_T^2+\operatorname{Tr}B_T^2}{2D}
 -\eta_T.                                             \tag{B}
$$
For the cross term, cyclicity gives
$\operatorname{Tr}(M_jM_i^\dagger M_j^\dagger M_i)
=\operatorname{Tr}(M_i^\dagger M_j^\dagger M_iM_j)$;
swapping $i,j$ in the full restricted sum is exactly the trace defining
$\eta_T$. The two positive terms are $\operatorname{Tr}A_T^2$ and
$\operatorname{Tr}B_T^2$.

Each squared commutator is nonnegative, so the restricted sum is at most
the global sum. Cauchy--Schwarz for the two positive matrices gives
$\operatorname{Tr}A_T^2,\operatorname{Tr}B_T^2\ge Dw^2$.
Therefore
$$
w^2-\eta_T\le G/m^2.                                \tag{C}
$$
This is the step that avoids any tail imbalance $A_T-B_T$.

For $J_T=D^{-1}\sum_{i\in T}|M_i\rangle\!\rangle
\langle\!\langle M_i|$, direct four-index expansion yields
$$
\eta_T=D\operatorname{Re}
 \sum_{a,b,c,d}(J_T)_{ab,cd}(J_T)_{ca,db}.
$$
The second index arrangement is a permutation. Complex Cauchy--Schwarz
for this bilinear sum, and canonical orthogonality, imply
$$
|\eta_T|\le D\operatorname{Tr}J_T^2
          =D\sum_{i\in T}q_i^2.                     \tag{D}
$$
No unitarity, trace preservation or normality of $M_i$ was used.

For $T=\{i:q_i\le\beta/D\}$, (C)--(D) give
$$
w^2-\beta w\le G/m^2,\qquad
w\le\beta+\sqrt G/m.
$$
Draw $I\sim q$. The tail of $X=-\log_2q_I$ satisfies both
$$
\Pr[X>s]\le\sqrt G/m+D2^{-s},
\qquad \Pr[X>s]\le D^22^{-s}.
$$
Integrating the first bound on $[n,2n]$, the counting bound on
$[2n,\infty)$, and one on $[0,n]$ proves (A), with exactly
$C_D=(1-D^{-1})/\ln2+1/\ln2$.
Strict convexity of $1/x$ on $[1,2]$ gives
$\ln2=\int_1^2x^{-1}\,dx>2/3$, while $2-D^{-1}<2$,
so $C_D<3$.

## 2. Energy identities for a trace-preserving channel

For any matrix family, with $A=\sum_iK_i^\dagger K_i$ and
$B=\sum_iK_iK_i^\dagger$,
$$
\begin{aligned}
\sum_{i,j}\|[K_i,K_j]\|_F^2
 &=2\operatorname{Tr}(AB)-2D\eta,\\
\sum_{i,j}\|[K_i,K_j^\dagger]\|_F^2
 &=\operatorname{Tr}A^2+\operatorname{Tr}B^2-2D\eta.
\end{aligned}                                                    \tag{E}
$$
Thus the second sum minus the first is $\|A-B\|_F^2$.
For a trace-preserving channel $A=I$ and $\operatorname{Tr}B=D$.
Consequently
$$
\frac1{2D}\sum_{i,j}\|[K_i,K_j]\|_F^2=e,\qquad
\frac1{2D}\sum_{i,j}\|[K_i,K_j^\dagger]\|_F^2
 =e+\frac u2.                                        \tag{F}
$$
In particular $e\ge0$. For a unital channel $u=0$.

Applying (A) to the normalized full Choi state, $m=1$, gives
$$
S(J)\le
\min\left\{2n,\ (1+\sqrt{e+u/2})n+C_D\right\}.         \tag{G}
$$
For every unital CPTP channel this is exactly
$S(J)\le(1+\sqrt{1-\eta})\log_2D+C_D$.

If a unital channel has $e=0$, (F) makes every mixed-adjoint
commutator zero. Taking $i=j$ shows that each $K_i$ is normal.
The ordinary commutators also vanish, so the Kraus operators are
simultaneously diagonalizable. Their span has dimension at most $D$,
hence $\operatorname{rank}J\le D$ and $S(J)\le n$ exactly.
This is consistent with the stronger trace-preserving endpoint
[Fraas, *Commuting Kraus operators are normal*, arXiv:2308.05450](https://arxiv.org/abs/2308.05450),
which requires only $\sum_iK_i^\dagger K_i=I$ plus pairwise commutation.
The present unital endpoint already follows from (E)--(F).

## 3. Identity-fidelity pinching gives a positive capacity witness

It is generally false that $J-f\Phi_D$ is positive: identity fidelity
need not be a Choi eigenvalue. Instead set
$$
\alpha_i=\operatorname{Tr}K_i/D,\qquad
L_i=K_i-\alpha_iI,\qquad
J_L=\frac1D\sum_i|L_i\rangle\!\rangle\langle\!\langle L_i|.
$$
Each $L_i$ is traceless. The pinching of $J$ along $\Phi_D$ and its
orthogonal complement is exactly
$$
\mathcal P(J)=f\Phi_D+J_L,\qquad \operatorname{Tr}J_L=r.
$$
Pinching does not decrease von Neumann entropy, so for $r>0$
$$
S(J)\le h_2(f)+rS(J_L/r).                            \tag{H}
$$
Both ordinary and mixed-adjoint commutators are unchanged by subtracting
scalar multiples of identity:
$[L_i,L_j]=[K_i,K_j]$ and
$[L_i,L_j^\dagger]=[K_i,K_j^\dagger]$.
Hence the CP-family lemma applies to $J_L$ with mass $m=r$ and
$G=e+u/2$. It follows that
$$
S(J)\le h_2(f)+\bigl[r+\sqrt{e+u/2}\bigr]n+rC_D.       \tag{I}
$$
The residual support is orthogonal to $\Phi_D$, so the combined entropy
estimate, including its dimension cap, is
$$
S(J)\le
\min\left\{
h_2(f)+r\log_2(D^2-1),\
h_2(f)+[r+\sqrt{e+u/2}]n+rC_D
\right\}.                                             \tag{I'}
$$
One may additionally use the unconditional bound (G).

For the input $I/D$, coherent information equals
$S(\mathcal E(I)/D)-S(J)$. The channel's output purity is
$$
\operatorname{Tr}[(\mathcal E(I)/D)^2]=(1+u)/D.
$$
Its entropy is at least $n-\log_2(1+u)$ by the Rényi-2 entropy bound.
The direct quantum coding theorem therefore gives
$$
Q(\mathcal E)\ge
\max\left\{0,\ [f-\sqrt{1-\eta+u/2}]n-h_2(f)
 -(1-f)C_D-\log_2(1+u)\right\}.                       \tag{J}
$$
If an independently justified lower bound on the actual output entropy
is stronger, it can replace this Rényi-2 step.

For all unital CPTP channels the clean consequence is
$$
\boxed{
Q(\mathcal E)\ge
\max\{0,\ [F_e(I/D,\mathcal E)-\sqrt{1-\eta}]\log_2D
 -h_2(F_e)-(1-F_e)C_D\}.}                           \tag{K}
$$
If $r=0$, each traceless residual $L_i$ vanishes and the channel is
identity; then $e=u=0$ and $Q=n$. No division by zero is required
to evaluate (J)--(K).

At $\eta=1$ a trace-preserving channel has pairwise commuting Kraus
operators by (F). Fraas's theorem implies their simultaneous
diagonalizability and automatic unitality. Alternatively, under an
already known unital premise, (F) itself proves normality and
commutation as above. The traceless residual matrices then lie in a
$(D-1)$-dimensional diagonal subspace. Thus the exact endpoint improves to
$$
S(J)\le\min\{n,\ h_2(f)+(1-f)\log_2(D-1)\},\qquad
Q\ge\max\{0,n-h_2(f)-(1-f)\log_2(D-1)\}.              \tag{L}
$$
For $f=1$, the identity case applies directly. An observation close to
$\eta=1$ is not being converted into a bound on $u$ without a separate
quantitative argument.

The achievability dependency is the unassisted quantum coding direct theorem,
e.g. [Devetak, IEEE TIT 51, 44--55 (2005), Theorem 5](https://arxiv.org/pdf/quant-ph/0304127).
These are existence certificates for a fixed memoryless channel,
not efficient encoders, finite-block guarantees or estimates of an
existing decoder's performance.

## 4. Simultaneous confidence

Suppose jointly valid bounds give
$$
f\ge f_*,\qquad \eta\ge c_*,\qquad 0\le u\le u_*,
\quad 0\le f_*\le1,\quad -1\le c_*\le1.
$$
No independence of the three confidence procedures is required; their
joint coverage must be justified. Replacing $h_2(f)$ by one and
separately worsening the monotone terms in (J) gives
$$
Q\ge\max\left\{0,\
[f_*-\sqrt{1-c_*+u_*/2}]n-1
-(1-f_*)C_D-\log_2(1+u_*)\right\}.                  \tag{M}
$$
Known unitality sets $u_*=0$. For example, at $n=32$ with simultaneous
lower bounds $f_*=19/50$ and $c_*=24/25$, use
$\sqrt{1-c_*}=1/5$ and $C_D<3$ to obtain
$$
Q\ge(19/50-1/5)32-1-3(31/50)=29/10.
$$
This is a finite-confidence sufficient rate certificate under the
channel and calibration assumptions. It supplies no finite-block
encoder or practical service claim.

### A supplied distance bound to a unital model

There is a different robustness route when a stronger model promise is
available. Suppose some unital CPTP map $\mathcal E_0$ satisfies
$$
\tfrac12\|\mathcal E-\mathcal E_0\|_\diamond\le\varepsilon,
\qquad 0\le\varepsilon\le\tfrac12.
$$
This promise needs separate physical or mathematical justification.
It is not inferred from $f,\eta,u$, and no inexpensive universal
certification procedure for it is supplied here.

If jointly valid data bounds for the actual channel give
$f_{\mathcal E}\ge f_*$ and $\eta_{\mathcal E}\ge c_*$, set
$$
a=\max\{0,f_*-\varepsilon\},\qquad
b=\max\{-1,c_*-4\varepsilon\}.
$$
The identity-fidelity probability changes by at most $\varepsilon$,
so $f_{\mathcal E_0}\ge a$. Replacing either self-switch slot changes
its output state's trace distance by at most $\varepsilon$.
For clarity, with the other channel fixed, its Stinespring unitary
can be applied before the variable slot in one control branch and
after it in the other, using the same environment without resetting
it. This realizes the SWITCH as a deterministic one-slot superchannel;
diamond-distance contraction follows from ordinary pre/postprocessing.
A two-slot hybrid therefore gives output trace distance at most
$2\varepsilon$, and the norm-one helper observable gives mean
difference at most $4\varepsilon$. Thus $\eta_{\mathcal E_0}\ge b$.
This argument is a norm bound, not a claim that those known controlled
dilations are free hardware resources.

For $g_d(t)=t\log_2(d-1)+h_2(t)$,
[Audenaert, Theorem 1](https://arxiv.org/pdf/quant-ph/0610146)
gives the sharp entropy-continuity bound in terms of trace distance
$t$. Its derivative is nonnegative for $t\le1-1/d$.
Consequently an upper bound $t\le\varepsilon\le1/2$ may safely
replace $t$ for both dimensions $d=D$ and $d=D^2$.
The output and Choi states are each within trace distance
$\varepsilon$ of their model states, so
$$
I_c(I/D,\mathcal E)
\ge n-S(J_{\mathcal E_0})
-3\varepsilon n-2h_2(\varepsilon).
$$
Here $\log_2(D-1)+\log_2(D^2-1)\le3n$ was used.
The unital entropy certificate for the model, with $h_2(f_{\mathcal E_0})
\le1$, now yields
$$
Q(\mathcal E)\ge\max\left\{0,\
[a-\sqrt{1-b}-3\varepsilon]n
-1-(1-a)C_D-2h_2(\varepsilon)\right\}.                \tag{N}
$$
As with (M), all statistical and model bounds must hold jointly;
statistical independence is unnecessary. This route charges the
stronger distance promise and the continuity penalty instead of
inferring a small nonunitality from the two scalar observations.

## 5. Measurement and limitation ledger

The statistic $\eta$ is the standard self-switch control-$X$ mean
only for a separately prepared control and target marginal $I/D$.
For general Kraus channels it is not target independent. The two
slots must be independently initialized uses of the same fixed channel.
The fidelity $f$ is the usual identity entanglement fidelity and may
be estimated by a trusted Bell test; in qubit dimensions, the existing
[random-sign local product-fidelity estimator](pauli-local-certification.md)
also applies to arbitrary
CPTP maps. Preparing $I/D$, coherent-order control, the clean reference
if used, loss, rejected attempts and all physical uses remain charged.

For nonunital channels $u$ is an additional promised or estimated
quantity; no cheap universal $u$ estimator is supplied here.
One cannot replace $u$ by a constant multiple of $e$ uniformly:
for $K_0=\operatorname{diag}(1,c,1,\ldots,1)$ and
$K_1=\sqrt{1-c^2}|0\rangle\langle1|$, $0\le c<1$, direct expansion gives
$$
e=\frac{(1-c^2)(1-c)^2}{D},\qquad
u=\frac{2(1-c^2)^2}{D},\qquad
\frac ue=\frac{2(1+c)}{1-c}\longrightarrow\infty.
$$
In the damping parameter $1-c^2$, $u$ is quadratic while $e$ is
cubic to leading order. Known output entropy can be used instead
of its purity lower bound in (J), but the mixed-energy correction
still remains.

The Choi entropy itself, not the Shannon entropy of an arbitrary
nonorthogonal Kraus or random-unitary representation, is being bounded.
Adding duplicate representation labels can change the latter without
changing any channel quantity. No positivity of a Pauli Fourier
transform, mixed-unitary representation, orthogonal unitary realization
or approximate-commutation structural theorem is required for (G)--(K).

For a concrete non-mixed-unitary test, the odd-dimensional
[Werner--Holevo channel, Eqs. (6)--(7)](https://arxiv.org/html/quant-ph/0203003v1)
has Kraus matrices
$(|i\rangle\langle j|-|j\rangle\langle i|)/\sqrt{D-1}$ for $i<j$.
Their normalized Choi support is the antisymmetric matrix subspace.
Every odd-dimensional antisymmetric matrix is singular, since
$\det M=\det M^{\mathsf T}=\det(-M)=-\det M$. Thus that support contains
no unitary matrix. A random-unitary decomposition would require its
unitary Choi vectors to lie in the same support, which is impossible.
The exact checker covers $D=3,5$, a four-dimensional Schur channel,
a three-dimensional bistochastic matrix-unit channel whose canonical
spectral tail has $A_T\ne B_T$, and real and complex
three-dimensional amplitude-damping channels.
It checks complete matrix identities rather than floating spectral
entropy values.

The nonunital correction is necessary in the proof, even in dimension
three. For
$K_0=\operatorname{diag}(1,3/5,1)$ and
$K_1=(4/5)|0\rangle\langle1|$, one has
$e=64/1875$ and $u=512/1875$. The one-jump canonical tail has
$w=16/75$ and $\eta_T=0$, so $w^2-\eta_T>e$.
The corrected mixed-energy bound is valid. This finite counterexample
excludes dropping $u$ from that tail argument; it is not a proof that
every alternative nonunital entropy theorem must use this parameter.

### Omitting nonunitality can falsely certify a positive capacity

There is also an operational counterexample to using the unital
certificate for arbitrary CPTP maps. On dimension $D$, let
$\mathcal A_\gamma$ be the common-ground amplitude-damping channel
$$
K_0=|0\rangle\langle0|
 +\sqrt{1-\gamma}\sum_{j=1}^{D-1}|j\rangle\langle j|,
\qquad
K_j=\sqrt\gamma\,|0\rangle\langle j|
\quad(1\le j<D).
$$
Its Stinespring isometry, with a $D$-dimensional environment, is
$$
|0\rangle\longmapsto|0\rangle_S|0\rangle_E,\qquad
|j\rangle\longmapsto
\sqrt{1-\gamma}|j\rangle_S|0\rangle_E
 +\sqrt\gamma|0\rangle_S|j\rangle_E.
$$
The images are orthonormal. For an input block matrix relative to
$|0\rangle\oplus\operatorname{span}\{|j\rangle:j\ge1\}$,
$$
\mathcal A_\gamma
\begin{pmatrix}a&v^\dagger\\v&C\end{pmatrix}
=
\begin{pmatrix}
a+\gamma\operatorname{Tr}C&\sqrt{1-\gamma}\,v^\dagger\\
\sqrt{1-\gamma}\,v&(1-\gamma)C
\end{pmatrix}.
$$
Tracing the system instead gives the same formula with $\gamma$
replaced by $1-\gamma$. Thus a complementary channel is exactly
$\mathcal A_{1-\gamma}$. Amplitude-damping survivals multiply under
composition:
$$
\mathcal A_\alpha\circ\mathcal A_\beta
=\mathcal A_{1-(1-\alpha)(1-\beta)}.
$$
For $\gamma\ge1/2$, set $\delta=(2\gamma-1)/\gamma$.
Then $0\le\delta\le1$ and
$$
\mathcal A_\delta\circ\mathcal A_{1-\gamma}
=\mathcal A_\gamma.
$$
The receiver output can therefore be reconstructed from the
environment: the channel is antidegradable and has $Q=0$.
For completeness, coherent-information data processing gives
$I(R\rangle B)\le I(R\rangle E)=-I(R\rangle B)$ for a pure
reference/system/environment state. This remains true for every
tensor power and every input. The regularized coherent-information
capacity formula therefore gives zero, consistently with no cloning.

Put $\gamma=16/25$ and $s=\sqrt{1-\gamma}=3/5$; the degrading
parameter is $\delta=7/16$. The only nonzero ordinary Kraus
commutators are those between $K_0$ and $K_j$, with
$[K_0,K_j]=(1-s)\sqrt\gamma\,|0\rangle\langle j|$.
Direct calculation gives
$$
\begin{aligned}
f&=\frac{[1+(D-1)s]^2}{D^2}\ge\frac9{25},\\
e&=\frac{D-1}{D}\gamma(1-s)^2\le\frac{64}{625},\\
u&=\gamma^2(D-1)=\frac{256(D-1)}{625}.
\end{aligned}
$$
The expression for $u$ follows from
$\mathcal A_\gamma(I)-I
=\gamma[(D-1)|0\rangle\langle0|-\sum_{j\ge1}|j\rangle\langle j|]$.
These are deterministic population bounds, not fitted confidence
claims.

At $D=2^{80}$, applying (M) with $u$ incorrectly omitted would use
$f_*=9/25$, $c_*=1-64/625$, $h_2\le1$ and $C_D<3$ to assert
$$
Q\ge
\left(\frac9{25}-\frac8{25}\right)80
-1-\frac{16}{25}\,3
=\frac7{25}>0,
$$
although $Q(\mathcal A_{16/25})=0$. The growing nonunitality term
prevents this false conclusion in (J)--(M). The exact checker
reconstructs the complementary channel and the degrading composition
as full Choi matrices in dimensions 2, 3 and 4, and separately checks
the rational $D=2^{80}$ contradiction. This is a scope obstruction,
not an estimate of a finite device's usable rate.

## 6. Relation to established entropy and coding bounds

The general-channel commutator observable is established:
[Gao et al., PRL 130, 170201 (2023), Eqs. (8)--(9)](https://arxiv.org/html/2208.06210)
measure its squared-commutator form for arbitrary CPTP processes.
At maximally mixed input their squared noncommutativity is
$e=1-\eta$ with the normalization here.
[Loizeau and Grinbaum, PRA 101, 012340 (2020), Eq. (18)](https://arxiv.org/html/1906.08505)
also give a Kraus-representation-independent self-commutator scalar
in their qubit setting. The observable is not introduced here.

[Chen and Ma, *Commutator Geometry and Information Preservation in
the Quantum Switch* (2026)](https://arxiv.org/html/2609.21310)
relate Kraus-commutator geometry to joint control/target fidelity and
encoded QFI. This is a related information-preservation precedent.
The inspected text does not state a general-channel Choi-entropy
upper bound or an original-channel quantum-capacity certificate of
the form proved here. This comparison is not an exhaustive priority
claim about commutator geometry or information preservation.

[Schumacher, *Sending entanglement through noisy quantum channels*
(1996), Sections 5--6](https://arxiv.org/pdf/quant-ph/9604023) supplies
the entropy-exchange interpretation and quantum Fano bound. At identity
fidelity $f$, its dimension-only entropy bound is
$S(J)\le h_2(f)+(1-f)\log_2(D^2-1)$, which is retained in (I').
The additional commutator term is proved here by the CP-family
spectral-tail and pinching arguments, rather than inferred from that
dimension-only estimate.

Fraas's commuting-Kraus theorem supplies the stronger
trace-preserving exact endpoint noted above; it does not state the
quantitative mixed-energy tail bound. Devetak supplies the coding
direct theorem used after bounding coherent information and the
regularized capacity formula used for the antidegradable obstruction. These
dependencies and comparisons are not an exhaustive priority claim.
