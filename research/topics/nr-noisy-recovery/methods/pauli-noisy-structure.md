# Ordinary estimation with noisy Pauli structure

<a id="nr-r06-pauli-noisy-structure"></a>

This is a proof component of [NR-R06](../architecture-baselines.md#nr-r06),
complementing the [weighted exact-support learner](pauli-subspace-calibration.md)
and [spectral estimator](../architecture-baselines.md#nr-r06-pauli-spectral-closure).
It supplies ordinary baselines for the
[NR-R20 capacity witness](../memory-qualification.md#nr-r20), without
claiming an optimum ordinary algorithm or a native advantage.

All experiments use a fixed stationary stochastic Pauli channel on
$n\ge1$ qubits, fresh independent errors on repeated calls, public
physical Pauli axes and trusted specified controls. Write
$D=2^n$, $\chi(a,b)=(-1)^{[a,b]}$, and
$\eta(p,p)=\mathbb E_{a,b\sim p}\chi(a,b)$.
Take $0<\varepsilon,\delta<1$. The stabilizer and product-probe
protocols use no extra clean quantum references. The mixed-target
variant counts one clean helper and additional controlled-Pauli ports.
Preparation, readout, reset and known gates remain resources.

The first two estimators use polynomially many queries and exponential
classical processing. The short-window estimator has polynomial query,
control and classical costs under its stronger ideal or quantitatively
conditioned measurement interface.

## 1. Uniform subspaces with identity and white contamination

Let $V\le\mathbb F_2^{2n}$ be an unknown **rank-$n$** linear
subspace, not necessarily isotropic, and suppose
$$
 p=\alpha\delta_0+\beta\operatorname{Unif}(V)
       +\gamma\operatorname{Unif}(\mathbb F_2^{2n}),
 \quad \alpha,\beta,\gamma\ge0,\quad
 \alpha+\beta+\gamma=1,\quad\beta>0.                    \tag{NS1}
$$
The mixture weights are supplied and known. The actual identity weight
is $p_0=\alpha+\beta/D+\gamma/D^2$, not $\alpha$.
This is a specified full-support contamination model, not robustness
against arbitrary adversarial outliers or unknown SPAM.

Choose a uniform known Lagrangian $M$, prepare its stabilizer state,
query the channel and measure its $n$ commuting stabilizers by a known
Clifford followed by terminal computational readout. If
$W=\pi_M(V)\le M^*$, the syndrome law is exactly
$$
 P_W=\alpha\delta_0+\beta\operatorname{Unif}(W)
                       +\gamma\operatorname{Unif}(\mathbb F_2^n).
 \tag{NS2}
$$
A linear image of a uniform subspace is uniform; $\pi_M$ maps the
full Pauli space surjectively onto $M^*$.

For a nonzero syndrome character $v$,
$$
 \mathbb E(-1)^{v\cdot Y}
 =\begin{cases}\alpha+\beta,&v\in W^\perp,\\
                \alpha,&v\notin W^\perp.
   \end{cases}                                        \tag{NS3}
$$
From $m$ independent observed syndromes, scan all $D-1$ nonzero
characters and accept those with empirical mean greater than
$\alpha+\beta/2$; include zero separately. If every mean has error
at most $\beta/4$, the accepted set is exactly $W^\perp$.
Hoeffding and a union bound over $K$ settings give
$$
 \Pr(\text{any character error}>\beta/4)
 \le2DK e^{-m\beta^2/32}\le\delta/2
 \quad\text{for}\quad
 m=\left\lceil32\beta^{-2}\ln(4DK/\delta)\right\rceil.
 \tag{NS4}
$$
No independence among character estimates on one shot is assumed.
On a bad record the accepted set can fail to be linear; take its span
to define an output on every data set.

The recovered annihilator represents $M\cap V^\perp$.
It need not equal $M\cap V$, but their dimensions agree because
$\dim M=\dim V=n$. Thus its dimension gives exactly
$$
 X_M=|M\cap V|=2^{\dim W^\perp}.                        \tag{NS5}
$$
The [NR-R08 subgroup-moment proof](../architecture-baselines.md#nr-r08-subgroup-ordinary),
including its Lagrangian inclusion count and four-tuple rank argument,
supplies the all-dimension identities
$$
 \begin{split}
 \mu=\mathbb E_M X_M^2
 &=1+\frac{3(D-1)}{D+1}
 +\frac{(1+\eta_V)D^2/2-3D+2}{(D+1)(D/2+1)}
 =a_D+g_D\eta_V,\\
 g_D&=\frac{D^2}{(D+1)(D+2)}\ge\frac13,\qquad
 \mathbb E_M X_M^4\le270,
 \end{split}                                          \tag{NS6}
$$
where $\eta_V=\mathbb E_{a,b\sim\operatorname{Unif}(V)}\chi(a,b)$.
This linked moment theorem remains the owner of that geometric proof.

Expanding the three mixture components in (NS1) gives
$$
 \eta(p,p)=2\alpha-\alpha^2+\beta^2\eta_V
              +2\beta\gamma/D+\gamma^2/D^2.            \tag{NS7}
$$
Identity commutes with every label; a full-space character average
vanishes unless its other label is zero, which supplies the two
dimension-dependent terms.

Here is an explicit failure and precision ledger. If
$\beta^2\le\varepsilon/2$, omit its unknown term in (NS7) and
evaluate the remaining known expression to error at most
$\varepsilon/2$. Otherwise set
$\varepsilon_V=\varepsilon/(2\beta^2)<1$, and choose
$$
 b=\left\lceil\frac{1080}{g_D^2\varepsilon_V^2}\right\rceil,
 \quad t=\text{smallest odd integer at least }8\ln(2/\delta),
 \quad K=bt.                                          \tag{NS8}
$$
For the ideal independent $X_M^2$'s, (NS6) and Chebyshev give
batch-mean error greater than $g_D\varepsilon_V$ with probability
at most $1/4$. The median of $t$ batch means fails with probability
at most $e^{-t/8}\le\delta/2$. Couple the computed values to these
ideal values on the all-character-good event (NS4), and union-bound
the two failures. Do not condition the moment concentration on
successful rank recovery. Invert $\mu=a_D+g_D\eta_V$, clip into
$[0,1]$, and insert into (NS7). Statistical error is at most
$\beta^2\varepsilon_V=\varepsilon/2$; reserve $\varepsilon/2$
for classical evaluation and supplied-weight numerical precision.
Exact rational weights and rational arithmetic can remove that
numerical error entirely.

The query count is $Km$, polynomial in
$n,\beta^{-1},\varepsilon^{-1},\ln(1/\delta)$.
The nonzero-character scan takes $O(Dmn)$ classical work per
setting, with polynomial memory when streamed and only a basis of
accepted characters retained. A fast Walsh transform changes the
time/space tradeoff, not the exponential-time ceiling. The global
Clifford preparation/readout gates are polynomially constructible
known controls, with their actual durations and errors charged.

## 2. Hidden weak-product bursts and the qualification promise

Let $C$ be one fixed unknown Clifford on $n$ qubits, and let $F_q$
be the product of identical one-site Pauli channels with probabilities
$(1-q,q/3,q/3,q/3)$. The physical error law is
$$
 p_{\alpha,q,C}=\alpha\delta_0+\beta C_*f_q,\qquad
 \beta=1-\alpha,\quad \alpha=0.38,\quad\beta=0.62.
$$
Here $q$ is latent activity, not physical single-site activity after
dense conjugation. Every call is fresh and independent, with the same
$C,\alpha,q$ throughout calibration and use. Put $t=1-4q/3$.
For $0\le q\le3/4$, direct one-site calculation gives
$$
 \lambda_p(b)=\alpha+\beta t^{\operatorname{wt}(C^{-1}b)},\qquad
 p_0=\alpha+\beta(1-q)^n,
$$
$$
 \eta(p,p)=1-\beta^2+\beta^2(1-4q^2/3)^n.                 \tag{L1}
$$
The self-commutation mean is independent of $C$. If the complete
model and $q$ are supplied, it is known without queries.

Even a supplied upper promise $q\le c_{\max}/\sqrt n$, with constant
$c_{\max}$, already gives a capacity certificate independent of $C$.
Conditioning on the burst flag yields
$$
 H(p)\le h_2(\beta)+\beta n[h_2(q)+q\log_2 3]
       =O(\sqrt n\log n),
$$
and hence standard hashing gives $Q\ge n-O(\sqrt n\log n)$.
This does not validate the promise or supply a decoder. A qualification
task cannot assume this exact upper promise and then claim that
measuring $\eta$ is necessary to infer positive capacity.

For $q=c/\sqrt n$,
$$
 \eta\longrightarrow1-\beta^2+\beta^2e^{-4c^2/3}.
$$
The NR20 certificate can be positive for sufficiently small constant
$c$, while the exact-model entropy estimate is stronger asymptotically.
A nontrivial inference problem must specify unknown $q$, uncertainty
in $\alpha$, or departures from the model.

### Finite-size fidelity and purity comparisons

With known $\alpha$, ordinary identity-rate measurements already
identify $q$, without learning $C$. In the random stabilizer
experiment, a zero label always returns the zero syndrome, while any
nonzero label does so with probability $1/(D+1)$. Thus its one-bit
return probability is
$$
 \mu_0=\frac{1+Dp_0}{D+1},\qquad
 q=1-\left(\frac{p_0-\alpha}{\beta}\right)^{1/n}.
 \tag{L1a}
$$
For $T$ independent shots, intersect the affine image of the
Hoeffding interval
$\widehat\mu_0\pm\sqrt{\ln(2/\delta)/(2T)}$
with the model range
$p_0\in[\alpha+\beta4^{-n},1]$. Invert its endpoints through
(L1a), in reversed order, to obtain a valid $q$ interval. Then
use (L1), decreasing on $q\in[0,3/4]$, for its $\eta$ interval.
If the intersection is empty, report inconsistency at that confidence
level rather than an arbitrary parameter estimate. This is a
polynomial-time finite-size estimator; the number of shots needed for
a narrow interval can be large.

The [product-probe identity estimator](pauli-local-certification.md)
is a cheaper-control alternative: $Z=(-1/2)^{N_-}$ has mean $p_0$
and lies in $[-1/2,1]$, where $N_-$ is its number of local minus
outcomes. Thus the direct interval
$\overline Z\pm(3/2)\sqrt{\ln(2/\delta)/(2T)}$ can replace the
random-stabilizer return and affine conversion above. Its preparation
and readout are product operations, with the same subsequent activity
conditioning. Under the mixed-target controller interface proved in
(PC1)–(PC3), a uniform full dual label and its helper outcome instead
have mean $p_0$, also without global stabilizer probes or target reset.

Its actual conditioning is
$$
 \frac{d\eta}{dp_0}
 =\frac{8\beta q}{3}
   \left(\frac{1-4q^2/3}{1-q}\right)^{n-1}.
 \tag{L1b}
$$
For $q=c/\sqrt n$, $c>0$ fixed, it grows as
$\exp[c\sqrt n+O(1)]/\sqrt n$. Consequently this estimator is
not a polynomial-query asymptotic closure in that scaling, even
though it can be useful at finite sizes. An implementation stopping
adaptively must use simultaneous confidence intervals, not reuse
one fixed-$T$ failure budget at every stopping time.

Choi purity and serial return moments provide further ordinary
comparators. Define
$v=(1-q)^n$ and
$u=[(1-q)^2+q^2/3]^n$. Direct convolution gives
$$
 \sum_a p_a^2=\alpha^2+2\alpha\beta v+\beta^2u,
 \qquad
 p_0(E^m)=
 \sum_{j=0}^m\binom mj\alpha^{m-j}\beta^j
       \left(\frac{1+3t^j}{4}\right)^n.                \tag{L1c}
$$
The $m=2$ return equals the collision probability. For every
$m\ge1$ and $0\le t\le1$,
$$
 0\le p_0(E^m)-\alpha^m\le(1-q)^n,
 \tag{L1d}
$$
because each $j\ge1$ factor is bounded by its $j=1$ value.
These particular invariants therefore retain an exponentially small
activity-dependent correction at $q=c/\sqrt n$. This is a
limitation of these measurements, not a lower bound against ordinary
adaptive or collective protocols. With unknown $\alpha$, (L1a)
alone is nonidentifying; the joint-fit conditioning must be analyzed
instead of treating the mixture coefficient as measured $p_0$.

## 3. Polynomial queries for the hidden weak-product family

For a uniform known Lagrangian $M$, prepare its stabilizer state,
query once and read its $n$-bit syndrome $\pi_M(a)$.
Retain both $M$ and the syndrome as one observation, with distribution
$R(p)$. Sampling $M$ and implementing its Clifford are polynomial;
no extra clean reference qubits are used. For distinct labels,
$$
 \Pr_M[\pi_M(a)=\pi_M(b)]=\frac1{D+1},\qquad D=2^n.
$$
For two laws supported on a union of at most $2m$ labels, each signed
label mass in their difference is alone in its syndrome bucket except
with probability at most $(2m-1)/(D+1)$. Summing isolated absolute
masses gives the projected-$\ell_1$ bound. If each full law is within
TV distance $\tau$ of an $m$-supported law, contraction and triangle
inequalities give
$$
 \operatorname{TV}(R(p),R(p'))
 \ge\operatorname{TV}(p,p')-h-4\tau,\qquad
 h=\frac{2m-1}{D+1}.                                   \tag{L2}
$$
This is the joint random-setting experiment, not a claim about every
fixed setting or a union bound over all hidden frames.

For every $q\le c_{\max}/\sqrt n$, the number $W$ of nonidentity
latent sites is binomial with mean at most $c_{\max}\sqrt n$.
Exponential Markov gives
$$
 \Pr(W>L)\le\exp[(e-1)c_{\max}\sqrt n-L].
$$
Take $L=\min\{n,\lceil2c_{\max}\sqrt n+\ln(1/\tau)\rceil\}$.
The tail is at most $\tau$, or zero if $L=n$.
Truncate/renormalize the burst law, keeping its identity atom. Its
support has size at most
$$
 m=\sum_{j=0}^{L}\binom nj3^j.                           \tag{L3}
$$
For fixed $c_{\max},\tau$, this is
$\exp[O(\sqrt n\log n)]=o(D)$, uniformly over $C$ and $q$.

Here is a finite-class estimator that avoids assuming exact
maximum-likelihood robustness to a discretized true parameter.
Set $\kappa=a=\tau=\varepsilon/128$.
Use a $q$-grid of spacing at most $\kappa/(2n)$ in the allowed
range. If $\alpha$ is unknown, also use an $\alpha$-grid of spacing
at most $\kappa/2$. Product coupling gives
$$
 \operatorname{TV}(p_{\alpha,q,C},p_{\alpha',q',C})
 \le|\alpha-\alpha'|+n|q-q'|\le\kappa                   \tag{L4}
$$
for a nearest grid model, and also after applying $R$.
The number $J$ of grid/frame hypotheses obeys
$$
 \log J=O(n^2+\log(n/\varepsilon)),
$$
because $|\mathrm{Sp}(2n,2)|<2^{2n^2+n}$; Clifford phases do not
affect error labels.

For every ordered pair form its Scheffe set
$A_{ij}=\{z:R_i(z)>R_j(z)\}$, compute its model probabilities by
finite enumeration, and choose a model minimizing
$$
 \max_{i,j}|\widehat P(A_{ij})-R_{\rm model}(A_{ij})|.
$$
Hoeffding and a union bound over at most $J^2$ sets give empirical
error at most $a$ simultaneously, with failure at most $\delta$,
when
$$
 N_{\rm shots}\ge\frac{\ln(2J^2/\delta)}{2a^2}.           \tag{L5}
$$
For a grid model $R_*$ within $\kappa$ of the true $R(p)$, its
criterion is at most $\kappa+a$, as is the chosen model's.
Apply those two bounds on the Scheffe set between the selected model
and $R_*$: their TV distance is at most $2\kappa+2a$.
The selected model therefore lies within $3\kappa+2a$ of $R(p)$.

The exact Lipschitz inequality
$$
 |\eta(p,p)-\eta(p',p')|\le4\operatorname{TV}(p,p')
$$
and (L2) now bound the scalar error by
$$
 4(3\kappa+2a+h+4\tau)\le40\varepsilon/128<\varepsilon,
 \quad\text{if }h\le\varepsilon/128.                    \tag{L6}
$$
Thus the stated family has a zero-reference ordinary estimator with
$O(\varepsilon^{-2}[n^2+\log(n/(\varepsilon\delta))])$
queries whenever the explicit effective-support condition holds.
For fixed constant accuracy and $c_{\max}$, it holds for all
sufficiently large $n$, excluding an asymptotic exponential
query-only lower bound for this family.

Enumerating symplectic frames, model probabilities, Scheffe sets and
model comparisons takes exponential classical time in $n^2$.
This is not a polynomial-total-resource learner or a practical
finite-size proposal. The explicit condition in (L6) must remain;
this argument does not silently give a polynomial all-accuracy bound
by replacing its exceptional small sizes with exponential algorithms.

## 4. Polynomial total resources with a short-window port

Suppose the additional repeatable interface
$$
 E_s=\alpha\,\mathrm{Id}+\beta C_*F_{q_s},\qquad
 \frac1{8n}\le q_s\le\frac1{4n}                         \tag{L7}
$$
is available, with the same fixed $C$, known $\beta>0$, fresh
noise and the ideal product-preparation/readout interface used by the
population-recovery theorem below. A physical implementation needs
certified systematic errors and at most polynomial conditioning costs
for those probes and the final high-weight parity. Calibration alone
does not imply such conditioning. A tunable conditional burst semigroup
can supply (L7); positive integer powers of the fixed full-window
channel do not supply a shorter window.

Every physical image of a latent weight-one Pauli has probability
$$
 v_1=\frac{\beta q_s}3(1-q_s)^{n-1}
 \ge\frac{\beta}{32n},                                 \tag{L8}
$$
using $(1-1/(4n))^{n-1}\ge3/4$.
Every latent weight-at-least-two label has probability at most
$$
 v_{\ge2}\le\frac{\beta q_s^2}{9}(1-q_s)^{n-2}
 \le\frac{\beta}{144n^2}.                              \tag{L9}
$$
The maximum occurs at weight two because
$q_s/[3(1-q_s)]<1$; there are no such labels when $n=1$.

Run product-probe population recovery, with failure budget $\delta/2$,
at coordinate accuracy
$\theta=\beta/(512n)$, and retain nonzero labels with estimated
probability greater than $\beta/(64n)=8\theta$.
The true one-site labels have probability at least $16\theta$;
all higher-weight labels have probability at most
$(32/(9n))\theta$. Coordinate error at most $\theta$ consequently
isolates exactly the $3n$ latent one-site labels.

The primary input is
[Flammia and O'Donnell, Pauli error estimation via Population Recovery,
Quantum 5, 549 (2021), Theorem 1](https://doi.org/10.22331/q-2021-09-23-549)
([primary text](https://arxiv.org/html/2105.02885)).
Its product-preparation/readout method estimates error probabilities
in $\ell_\infty$, without requiring low physical Pauli weight.
At this inverse-polynomial $\theta$, its query count is
$$
 O\!\left(n^2\beta^{-2}
          \ln\frac{n^2}{\beta\delta}\right),
 \tag{L10}
$$
and its classical processing is polynomial. It is not an arbitrary
unknown-SPAM guarantee. If no label is accepted on a bad recovery
record, return a fixed scalar estimate.

**Only one recovered label is needed for the scalar.**
For any recovered nonzero weight-one latent label $s$, the original
full-window channel satisfies
$$
 \lambda_p(s)=1-\frac{4\beta q}{3},\qquad
 q=\frac{3[1-\lambda_p(s)]}{4\beta}.                    \tag{L11}
$$
Prepare a physical product $+1$ eigenstate of the known $P_s$,
query the full window and read $P_s$ by local measurements and
classical parity. This needs no inverse Clifford, global entangling
probe or additional references. Its high physical weight can make
actual parity/readout contrast expensive; that cost must be measured.

For optional structure validation, the recovered labels' anticommutation
graph consists of $n$ disjoint triangles; within each, the sum of
two labels equals the third. Choosing two per triangle gives a
symplectic basis and, if needed, a known inverse Clifford by polynomial
symplectic elimination. This stronger control is not required by (L11).

For a uniform conservative accuracy ledger,
$$
 \left|\frac{d\eta}{dq}\right|
 =\frac{8\beta^2nq}{3}(1-4q^2/3)^{n-1}\le2\beta^2n
 \quad(0\le q\le3/4).
$$
For a complete ledger, choose
$\zeta=\min\{1,\varepsilon/(3\beta n)\}$ and take
$$
 R=\left\lceil2\zeta^{-2}\ln(4/\delta)\right\rceil
 \tag{L12}
$$
fresh full-window eigenvalue-probe calls. Conditional on successful
recovery, every selected label is valid; Hoeffding makes the error in
its mean at most $\zeta$, except with probability $\delta/2$.
Use (L11) and clip $\widehat q$ into $[0,3/4]$. Then
$$
 |\widehat q-q|\le\frac{3\zeta}{4\beta},\qquad
 |\eta(\widehat q)-\eta(q)|
 \le\frac32\beta n\zeta\le\varepsilon/2.
 \tag{L13}
$$
Reserve $\varepsilon/2$ for classical evaluation; for rational
inputs this can instead be done exactly with polynomial bit cost.
Recovery and final-mean failures sum to at most $\delta$.
The total queries are (L10) plus (L12), and the known controls are
product preparations, product readout and parity processing only.
At $q=O(n^{-1/2})$, the local derivative is $O(\sqrt n)$, allowing
tighter conditioned bounds. Unknown $\beta$ requires independent
calibration or a joint fit with its uncertainty propagated.

Under an actual tunable semigroup and the exact model, ordinary
return-probability pilots can locate a suitable range (L7):
$p_0(E_s)=\alpha+\beta(1-q_s)^n$, whose two endpoint values are
separated by a constant multiple of $\beta$.
This observation does not create a duration-control port or certify
that $\alpha,\beta,C$ stay fixed as duration varies.

The bounded primary
[Zhou and Gong, Characterizing Arbitrary Lindbladian Dynamics with a
Few Pauli Measurements (2026)](https://arxiv.org/html/2607.23044v1)
also gives sparse nonlocal Lindblad learning with chosen positive-time
evolution access. Its short-time/derivative interface is consistent
with this elementary specialization. The fixed mixture
$\alpha\mathrm{Id}+\beta e^{\mathcal L}$ and access to its powers do
not provide that interface or its calibration assumptions.

### A mixed target and one counted helper

There is a separate ordinary implementation when pure $n$-qubit
probe preparation is unavailable but known controlled physical Paulis
are available. It uses a target initialized in $I/D$, reuses that
mixed target without resetting it, and prepares/measures/resets one
clean helper on every shot. These controller ports are additional
resources; they are not automatically supplied by a bare switch.

Let $P_b$ be a known Hermitian Pauli. Prepare the helper in
$|+\rangle$, apply controlled $P_b$, call the ordinary Pauli
channel on the target, apply controlled $P_b$ again, and measure
helper $X$. For every realized Pauli $P_a$, the complete joint
unitary is
$$
 (\operatorname{ctrl}P_b)(I\otimes P_a)
       (\operatorname{ctrl}P_b)
 =\bigl(|0\rangle\langle0|
       +\chi(a,b)|1\rangle\langle1|\bigr)\otimes P_a.
 \tag{PC1}
$$
Thus the helper outcome $X_b\in\{-1,1\}$ has mean
$\lambda_p(b)$. More strongly, its target instrument is
$$
 \mathcal I_y(\rho)=
 \sum_{a:\chi(a,b)=y}p_aP_a\rho P_a,\qquad
 \mathcal I_y(I/D)=\Pr(X_b=y)\,I/D.
 \tag{PC2}
$$
The target is still $I/D$ conditional on **every** helper record.
This justifies repeated adaptive probes without data reset under the
stated fresh Pauli model. It does not preserve an arbitrary supplied
unknown state. Two known controlled strings use at most $2n$
controlled single-qubit Paulis; their fidelity and duration are charged.

Write the binary error label as $a_1,\ldots,a_\ell$, with
$\ell=2n$. Nondegeneracy gives public dual labels $g_j$ satisfying
$[a,g_j]=a_j$. To estimate the probability mass $M_s$ of a
specified length-$k$ prefix $s$, choose a fresh uniform
$z\in\mathbb F_2^k$, put $b(z)=\sum_{j\le k}z_jg_j$, run the
one-query experiment above and return
$Y_s=(-1)^{s\cdot z}X_{b(z)}$. Character orthogonality gives
$$
 \mathbb EY_s
 =\sum_a p_a\,2^{-k}\sum_z(-1)^{z\cdot(a_{1:k}+s)}
 =\Pr(a_{1:k}=s)=M_s.                                 \tag{PC3}
$$
All outcomes have absolute value one. The zero dual label can be
handled deterministically; charging it as one query is a safe bound.

Here is a complete heavy-label tree with no error-law sparsity
assumption. Fix $0<\theta<1$, put
$$
 B=\lceil4/\theta\rceil,\quad T=2\ell B,\quad
 m=\left\lceil32\theta^{-2}\ln(2T/\delta)\right\rceil.
 \tag{PC4}
$$
Start with the empty prefix. At every level, estimate each of the
two children of every retained prefix using $m$ fresh shots of
(PC3). Retain children with empirical mean at least $\theta/2$.
If a level would retain more than $B$ prefixes, abort and return
a fixed failure output. Thus at most $T$ prefix tests occur on
every data set, including bad ones.

Conditional on any previous records, the next tested prefix is fixed
and its fresh estimator still has mean $M_s$, by (PC2), (PC3) and
stationarity. Hoeffding gives conditional failure at most
$2e^{-m\theta^2/32}\le\delta/T$ for error greater than
$\theta/4$. Union-bound over the at most $T$ adaptive tests.
On their simultaneous good event, every retained prefix has true
mass at least $\theta/4$. Since same-level prefixes are disjoint,
there are at most $4/\theta$, and the abort cap is inactive.
Every label with $p_a\ge\theta$ has all ancestor masses at least
$\theta$, whose estimates exceed the retention threshold.
Consequently all such labels survive; every retained leaf has
probability at least $\theta/4$.

The one-helper call count is therefore
$$
 Tm=O\!\left(n\theta^{-3}\ln\frac{n}{\theta\delta}\right),
 \tag{PC5}
$$
with polynomial classical prefix bookkeeping and known-control
count, one helper reset per shot and no mixed-target reset.
This is an error-probability heavy-hitter procedure, not a universal
polynomial-cost estimator of $\eta$ for diffuse full-window laws.

Apply it to the short-window family (L7) with
$\theta=\beta/(512n)$, using failure budget $\delta/2$.
At the final leaves retain only **nonzero** labels with estimated mass
greater than $8\theta$. Their leaf estimates already have error at most
$\theta/4$. Equations (L8)–(L9) then isolate exactly the $3n$
latent weight-one labels, as in the product-probe protocol.
Choose any nonzero one, and estimate its full-window eigenvalue
using (PC1)–(PC2) on the same $I/D$ target, with the
$\delta/2$ budget and $R$ in (L12). Equations (L11) and (L13)
give the same $\varepsilon$-accurate scalar. Its total calls are
$$
 O\!\left(n^4\beta^{-3}
       \ln\frac{n^2}{\beta\delta}\right)
 +O\!\left(\zeta^{-2}\ln(1/\delta)\right).              \tag{PC6}
$$
This variant trades pure full-register preparation for one counted
clean helper and trusted coherent controlled-Pauli sandwiches.
It does not assume access to the hidden encoder or its inverse.

All instrument identities here are ideal. A known independent helper
visibility can be divided out at its inverse-square sampling cost,
but visibility alone does not certify the conditional target map
(PC2). Controlled-gate faults, target-dependent readout and unknown
SPAM require a full joint-instrument bias and conditioning budget.
Polynomial cost requires at most inverse-polynomial conditioning.
The extra controller and timing ports, and the short-window premise,
must be available on the same terms to the ordinary benchmark.

## 5. Verification, limits and the remaining step

The self-contained standard-library
[finite exact checker](../checks/architecture/verify_pauli_noisy_structure.py)
has API $\texttt{verify()}$, a JSON CLI with status
$\texttt{passed}$, and a guard against assertion-disabling optimized
Python. It checks finite mixture/Fourier/moment identities, hidden
product invariants, short-window extraction/probe algebra and the
controlled-Pauli/prefix-instrument identities.
The all-dimension query, concentration, support-truncation and physical
conditioning arguments remain the analytic proofs here and the linked
NR-R08 moment theorem; finite replay is not a formalization.

The fixed-window family is not query-hard against unrestricted
classical model selection. Known $q$ gives zero-query scalar
evaluation; the supplied weak-activity upper promise already gives a
stronger exact-model hashing certificate. Short exposures, or public
encoder/inverse ports, permit a polynomial ordinary scalar calibration.

For an exact fixed full-window channel with hidden $C$, no tunable
strength, no encoder/inverse port and zero or a fixed small number of
clean references, this note does not provide a polynomial-time learner.
The [general cross-paired ordinary estimator](../architecture-baselines.md#nr-r06-pauli-coset-scalar)
already has polynomial cost when $n-k=O(\log n)$, with its $k$
references and both channels' Bell-probe costs counted. No open-case
claim is made for that near-full-reference regime. The concrete
missing step is efficient extraction of enough hidden tensor/symplectic
factor structure, or an invariant replacement, from low-reference
syndrome samples whose useful individual full-window Fourier
coefficients may be exponentially small. This is not the all-eigenvalue
task, and no hardness follows from failure of a parity scan, local
product kernel, physical-axis Lindblad fit, collision estimator or
empirical span heuristic.

A computational application must justify why the native device hides
its encoder and excludes short exposures or other control ports
equally for both receivers. The switch also needs its coherent two-order
implementation at the same operating point, with helper, timing,
bath records, resets and failed attempts priced. No such hardware
advantage follows from the scalar gap.
