# Random-unitary capacity certificates with bounded branch overlaps

This is a proof component of [NR-R20](../memory-qualification.md#nr-r20).
It extends the entropy/capacity method to a promised approximately
orthogonal random-unitary realization. The
[entropy component](pauli-entropy-capacity.md) owns the Pauli and
exact-orthogonal statements. No channel-learning lower bound, efficient
encoder or native switch advantage follows here. A separate
[general-channel proof](unital-entropy-capacity.md) bounds Choi entropy
without this realization promise; it does not bound the Shannon entropy
of arbitrary representation labels.
For capacity qualification alone, that theorem can be used without
the cardinality or overlap promise, since random-unitary channels are
unital. The realization-entropy estimate below remains a separate claim.

## Realization, statistic and theorem

Let $D\geq2$, $n=\log_2D$, and let $U_1,\ldots,U_K$ be unitaries on
$\mathbb C^D$, with $K\leq D^2$. Suppose

$$
\frac{|\operatorname{Tr}(U_i^\dagger U_j)|}{D}\leq\mu
\quad(i\ne j),\qquad
m=\mu^2,\quad\kappa=Dm<1,\quad\zeta=1-\kappa>0.        \tag{UO1}
$$

Cardinality and overlap are hypotheses on this realization; being
random unitary alone does not supply them. The branches may be complex,
non-Hermitian and nonorthogonal. For a probability law $q$, define

$$
c(q)=\sum_{i,j}q_iq_j
 \frac{\operatorname{Re}\operatorname{Tr}
 (U_j^\dagger U_i^\dagger U_jU_i)}{D},
\qquad e=1-c(q),\qquad C_D=\frac{2-D^{-1}}{\ln2}.       \tag{UO2}
$$

This is the standard independent self-switch control mean with target
$I/D$. General random-unitary channels need not have an
input-independent control mean. Entropies below are in bits. Then

$$
H(q)\leq
\min\left\{\log_2K,\
 \left(1+\sqrt{\frac e\zeta}\right)n+\frac{C_D}{\zeta}
\right\}.                                           \tag{UO3}
$$

A smaller valid finite-size constant replacing $C_D/\zeta$ is

$$
C_{\rm ov}=
\frac{(1-m)(1-D^{-1})/\zeta+1}{\ln2}
\leq\frac{C_D}{\zeta}.                               \tag{UO4}
$$

The clean form (UO3) is useful for confidence certificates.
As $\kappa$ approaches one its correction grows; $\mu^2<1/D$ is
an additional geometric promise.

## Choi contraction and the weighted tail estimate

For nonnegative subweights $v_i$ with $w=\sum_i v_i$, write
$c(v)$ for the same quadratic expression and put

$$
J_v=\frac1D\sum_i v_i|U_i\rangle\!\rangle
                       \langle\!\langle U_i|.
$$

Thus $(J_v)_{ab,cd}=D^{-1}\sum_i v_i(U_i)_{ab}
\overline{(U_i)_{cd}}$. The reshaping/Cauchy argument also used in the
[exact-orthogonal method](pauli-entropy-capacity.md) gives

$$
c(v)=D\sum_{a,b,c,d}(J_v)_{da,cb}(J_v)_{cd,ba},
\qquad |c(v)|\leq D\operatorname{Tr}(J_v^2).           \tag{UO5}
$$

For completeness, expand the trace in (UO2) to obtain the displayed
contraction. Its sum is real because the $i,j$ terms pair with their
complex conjugates. Both index arrangements permute all entries of
$J_v$. Scalar Cauchy--Schwarz bounds the absolute contraction by its
entrywise squared norm, equal to $\operatorname{Tr}(J_v^2)$ since
$J_v$ is Hermitian. No positivity of individual entries is required.

The Gram expansion and (UO1) give

$$
\begin{aligned}
\operatorname{Tr}(J_v^2)
 &=\sum_{i,j}v_iv_j
       \left|\frac{\operatorname{Tr}(U_i^\dagger U_j)}D\right|^2\\
 &\leq(1-m)\sum_i v_i^2+m w^2,\\
c(v)&\leq D(1-m)\sum_i v_i^2+\kappa w^2.
\end{aligned}                                                   \tag{UO6}
$$

For a threshold $\beta>0$, let
$v_i=q_i\mathbf1_{\{q_i\leq\beta/D\}}$.
Then $\sum_i v_i^2\leq(\beta/D)w$. Moreover

$$
\begin{aligned}
w^2-c(v)
 &=\sum_{i,j}v_iv_j\frac{\|[U_i,U_j]\|_{\rm HS}^2}{2D}\\
 &\leq\sum_{i,j}q_iq_j
       \frac{\|[U_i,U_j]\|_{\rm HS}^2}{2D}
 =1-c(q)=e .
\end{aligned}                                                   \tag{UO7}
$$

The inequality holds because every squared-commutator summand is
nonnegative. Combining (UO6)–(UO7) yields

$$
\zeta w^2-(1-m)\beta w\leq e,\qquad
w\leq\sqrt{e/\zeta}+\frac{(1-m)\beta}{\zeta}
 \leq\sqrt{e/\zeta}+\frac{\beta}{\zeta}.              \tag{UO8}
$$

The middle bound follows from the positive root of the quadratic and
$\sqrt{x^2+y}\leq x+\sqrt y$ for $x,y\geq0$.
Draw $I\sim q$ and set $X=-\log_2q_I$; zero-mass labels never occur.
For $W(s)=\Pr[X>s]$, (UO8) with $\beta=D2^{-s}$ bounds the tail.
Counting at most $D^2$ labels also gives $W(s)\leq D^22^{-s}$.
The layer-cake identity gives

$$
\begin{aligned}
\int_0^n W(s)\,ds&\leq n,\\
\int_n^{2n}W(s)\,ds
 &\leq n\sqrt{e/\zeta}
       +\frac{(1-m)(1-D^{-1})}{\zeta\ln2},\\
\int_{2n}^{\infty}W(s)\,ds&\leq\frac1{\ln2}.
\end{aligned}
$$

Adding proves (UO3)–(UO4), together with $H(q)\leq\log_2K$.
The estimate remains valid when $\sqrt{e/\zeta}>1$, although the
cardinality bound is then usually stronger.

## The commuting endpoint and its necessary correction

If $c(q)=1$, (UO7) forces every pair of positive-mass branches to
commute. Normality makes them simultaneously diagonalizable; their
vectorizations lie in a $D$-dimensional space. Hence their Choi
mixture has rank at most $D$ and entropy exchange at most $\log_2D$.
This does not imply $H(q)\leq\log_2D$ for nonorthogonal branches.

An exact counterexample is $D=2$, $K=3$,

$$
\omega=e^{2\pi i/3},\qquad
U_j=\operatorname{diag}(1,\omega^j),\quad
q_j=1/3,\quad j=0,1,2.                              \tag{UO9}
$$

All branches commute, $U_0=I$, and $c=1$. For distinct $i,j$,
$|1+\omega^{j-i}|^2=1$, so $\mu=1/2$ and $\kappa=1/2<1$.
Yet $H(q)=\log_2 3>1$. Their averaged channel is complete dephasing,
since $1+\omega+\omega^2=0$, and its entropy exchange is one bit.
The example separates mixing entropy from exchange entropy.

A corrected support endpoint follows from the elementary Welch
argument. If $s$ branches have positive mass and commute, their unit
vectors lie in dimension $D$. Their Gram matrix has trace $s$ and
rank at most $D$, so its squared Frobenius norm is at least $s^2/D$.
By (UO1) it is at most $s+s(s-1)m$. Rearranging gives

$$
s\leq\frac{D(1-m)}{1-Dm},\qquad
H(q)\leq\log_2\min\left\{K,\frac{D(1-m)}{1-Dm}\right\}. \tag{UO10}
$$

The cube-root example saturates this count. At $m=0$ it restores the
exact-orthogonal endpoint $H(q)\leq\log_2D$.

## Capacity and identity probability from entanglement fidelity

Consider the fixed memoryless channel
$\mathcal E_p=\sum_i p_i\operatorname{Ad}_{U_i}$.
Its output on $I/D$ is $I/D$, and its normalized Choi state is $J_p$.
The entropy of this mixture of pure states obeys $S(J_p)\leq H(p)$.
Equivalently, dephasing the complementary output in the branch basis
has entropy $H(p)$ and cannot decrease entropy. Thus coherent
information and the quantum coding direct theorem give

$$
Q(\mathcal E_p)\geq
\max\{0,n-S(J_p)\}\geq\max\{0,n-H(p)\}.               \tag{UO11}
$$

This is unassisted asymptotic transmission in qubits per $D$-dimensional
use, with independent uses, no input-bearing bypass and no two-way
assistance. The coding dependency is
[Devetak, IEEE TIT **51**, 44–55 (2005), Theorem 5](https://arxiv.org/pdf/quant-ph/0304127).
An encoder or finite-block reliability guarantee is not constructed.

Suppose one designated branch is $U_0=I$, with probability $p_0$,
and put $r=1-p_0$. For $r>0$, condition on the nonidentity branches
and denote their self-switch mean by $c$. Their pairwise bound is
still (UO1). Since identity commutes with all branches,

$$
1-c(p)=r^2(1-c),\qquad H(p)=h_2(p_0)+rH(q).
$$

Apply (UO3) to this conditional family to obtain

$$
Q(\mathcal E_p)\geq
\max\left\{0,\
\left[p_0-\sqrt{\frac{1-c(p)}{\zeta}}\right]n
-h_2(p_0)-\frac{(1-p_0)C_D}{\zeta}\right\}.           \tag{UO12}
$$

For $p_0=1$ the channel is identity and $Q=n$. This is a sufficient
certificate; an identity-mass-only entropy estimate may be larger.
Equality $S(J_p)=H(p)$ is not used in (UO11)–(UO12).

The identity entanglement fidelity is

$$
F_e=\sum_i p_i\left|\frac{\operatorname{Tr}U_i}{D}\right|^2,
\qquad
p_0\leq F_e\leq p_0+(1-p_0)m,
\qquad
p_0\geq\max\left\{0,\frac{F_e-m}{1-m}\right\}.         \tag{UO13}
$$

The cube-root example attains the inversion exactly:
$F_e=1/2$ and $(F_e-1/4)/(1-1/4)=1/3=p_0$.
Here $p_0$ is the designated branch probability of the promised
realization, whereas $F_e$ is a property of the channel.

For simultaneous lower confidence bounds $F_e\geq f$, $0\leq f\leq1$,
and $c(p)\geq c_*$, $-1\leq c_*\leq1$, and a known overlap upper
bound $0\leq m<1/D$, put
$z=\max\{0,(f-m)/(1-m)\}$. A convenient monotone certificate is

$$
Q(\mathcal E_p)\geq
\max\left\{0,\
\left[z-\sqrt{\frac{1-c_*}{\zeta}}\right]n
-1-\frac{(1-z)C_D}{\zeta}\right\}.                  \tag{UO14}
$$

It uses $h_2\leq1$ and is increasing in each supplied lower bound.
Keeping $h_2(z)$ instead of one is also valid after taking the positive
part: the untruncated expression is convex in $z$, negative at zero,
and increasing wherever it is positive. Neither rule identifies
entanglement fidelity with identity-branch probability.

At the exact endpoint $c(p)=1$, entropy exchange gives a further
branch without an orthogonality assumption. The conditional Choi state
has rank at most $D$, so
$S(J_p)\leq h_2(p_0)+(1-p_0)n$ and
$Q\geq\max\{0,p_0n-h_2(p_0)\}$. This bounds exchange entropy,
not the classical label entropy disproved in (UO9).

## A rational positive example and a non-Pauli realization

Let $D=2^{32}$. Suppose simultaneous confidence bounds are
$F_e\geq19/50$, $c(p)\geq24/25$, and the promised realization obeys
$m\leq1/(100D)$. Then

$$
z\geq379/1000,\qquad
\zeta\geq99/100,\qquad
\sqrt{\frac{1-c(p)}{\zeta}}<101/500,\qquad
\frac{C_D}{\zeta}<100/33.
$$

For the last inequality, $C_D<3$ follows from $\ln2>2/3$.
Equation (UO14) certifies

$$
Q\geq
\left(\frac{379}{1000}-\frac{101}{500}\right)32
-1-\frac{621}{1000}\frac{100}{33}
=\frac{7651}{2750}>2.78.                            \tag{UO15}
$$

The confidence region is nonempty with all $D^2$ branches present.
Start with the [full-support Pauli example](pauli-entropy-capacity.md)
and keep its weights. For every nonidentity Hermitian Pauli $P_i$,
replace it by
$U_i=aP_i+ibI$, with real $a,b$, $a^2+b^2=1$,
$0<b^2\leq1/(100D)$, and keep $U_0=I$. These are unitary,
their maximum distinct normalized overlap squared is $b^2$, and
$[U_i,U_j]=a^2[P_i,P_j]$ for nonidentity indices. Thus their total
commutator defect is $a^4$ times the original defect; $F_e$ can only
increase. The vectors remain linearly independent for $a>0$, so
positive branch weights also give a full-rank Choi state. This is a
construction satisfying the mathematical promise, not an efficient
device or an experimental certificate of the overlap bound.

## Prior position and verification scope

The switch commutator diagnostic is established by
[Gao et al., PRL **130**, 170201 (2023), Eqs. (6)–(10)](https://arxiv.org/html/2208.06210v4)
and the earlier self-channel scalar of
[Loizeau and Grinbaum, PRA **101**, 012340 (2020), Section V](https://arxiv.org/html/1906.08505).
The entropy-exchange inequality and orthogonal equality are established
random-unitary facts; see
[Bouda and Ziman, J. Phys. A **40**, 5415–5426 (2007), Section 2](https://arxiv.org/pdf/0710.2004).
The Gram argument behind (UO10) is standard Welch geometry; see
[Datta, Howard and Cochran, *Geometry of the Welch Bounds*](https://arxiv.org/pdf/0909.0206).

[Glebsky, Theorem 2](https://arxiv.org/pdf/1002.3082) treats normalized
Hilbert--Schmidt approximation of a fixed finite family with all
pairwise commutators small. Here the defect is weighted, rare branches
may fail to commute, and the family can grow with $D$. That structural
theorem is not being invoked for (UO3), nor does (UO3) establish that
the whole family is close to a commuting algebra. A bounded primary
source check did not identify the corrected weighted entropy inequality
in those works; it is not an exhaustive novelty or priority claim.

The [finite exact guard](../checks/architecture/verify_approx_unitary_capacity.py)
uses rational-complex matrices in dimensions two and four to check the
Choi contraction, Gram purity bounds, weighted defects, threshold
inequalities and fidelity inversion. It also checks the cube-root
overlap algebra and rational certificate (UO15). It uses no
floating-point entropy or spectral approximation as proof evidence.
The layer-cake argument, all-dimension entropy statement and coding
theorem remain analytic. Estimating the switch statistic, certifying
the realization geometry and obtaining encoder access are separate
resource questions; no ordinary estimator lower bound or substantial
physical architecture advantage has been established here.
