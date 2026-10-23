# Coherent dispatch with counter dephasing

[Application assessment](architecture.md) · [Ordinary baselines](architecture-baselines.md) · [Topic](README.md)

<a id="nr-r12"></a>

## NR-R12 — Exact binary dispatch, with unresolved native-device costs

This result specializes an established self-switch correction mechanism to
a two-instruction quantum dispatcher. It gives an exact universal query
comparison for a full coherent quantum output. It does **not** establish a
hardware application, a latency advantage, or an evaluated approximation
or expected-cost lower bound. Its ordinary constructions and qualitative
fixed-dimension converse have separate scopes. The correction mechanism and the underlying
unitary-switch obstruction are prior results; the interface reduction below
states precisely what they imply here.

### Interface and task

Let $P$ be a counter qubit and $T$ a $d$-dimensional data register,
$d\ge2$. The fixed, reusable subroutines $V_0,V_1$ are arbitrary unknown
unitaries on $T$. Define

$$
U=|1\rangle\langle0|_P\otimes V_0
  +|0\rangle\langle1|_P\otimes V_1,
\qquad Z=Z_P\otimes I_T.
$$

Then $ZU=-UZ$ and

$$
W=U^2=|0\rangle\langle0|_P\otimes V_1V_0
       +|1\rangle\langle1|_P\otimes V_0V_1. \tag{1}
$$

The supplied noisy module is

$$
\mathcal E_p=(1-p)\operatorname{Ad}_U
               +p\operatorname{Ad}_{ZU},\qquad0\le p\le1. \tag{2}
$$

Thus the only module fault is a counter-$Z$ phase after the complete ideal
dispatcher. Ordinary counted channel uses have fresh independent phase
bits; the subroutines themselves remain fixed. There are no faults inside
$V_j$ in this model. The task is to
implement the entire channel $\operatorname{Ad}_W$ on $P,T$, including
coherence between the counter values and correlations with an inaccessible
reference. No classical description, precomputed gate program, phase-fault
record or separately controlled $V_j$ is supplied.

An ordinary circuit may use arbitrary known processing, clean ancillary
registers and memory, encodings, measurements, classical adaptation, data
routing, early stopping and repeated calls. Its stated budget is a **hard
total query cap**, including training calls. The additional switch resource
is the standard coherent-order use of two independent identical channel
slots carrying (2). Physical realization of those slots is a separate
premise, discussed below.

### Perfect all-outcome correction for every $p$

Take $K_0=\sqrt{1-p}\,U$ and $K_1=\sqrt p\,ZU$. With the external
order control initialized in $|+\rangle$, measuring it in $X$ gives
conditional Kraus operators

$$
L_{ab}^{\pm}=\frac{K_bK_a\pm K_aK_b}{2}.
$$

Directly,

$$
K_0K_0=(1-p)W,\qquad K_1K_1=-pW,\qquad
K_1K_0=-K_0K_1=\sqrt{p(1-p)}\,ZW.
$$

Consequently the two unnormalized outcome maps are

$$
\mathcal C_+=\alpha\operatorname{Ad}_W,\qquad
\mathcal C_-=\beta\operatorname{Ad}_{ZW},\qquad
\alpha=(1-p)^2+p^2,\quad\beta=2p(1-p). \tag{3}
$$

Their probabilities are input independent and sum to one. Apply the known
$Z$ on a minus outcome. Every outcome then implements $W$, so two switched
calls realize (1) deterministically, with no postselection and no knowledge
of $p,V_0,V_1$. In contrast, two uncorrected ordinary calls give
$\alpha\operatorname{Ad}_W+\beta\operatorname{Ad}_{ZW}$.

This is contained in the established self-switching construction of
[Chiribella and Kristjánsson, Section IV.4, self-switching and perfect communication](https://arxiv.org/html/1812.05292).
Its two anticommuting unitary Kraus choices can be written $U$ and
$iZU$: they have the same square $W$, and
$\operatorname{Ad}_{iZU}=\operatorname{Ad}_{ZU}$. Equation (3) is the
direct weighted specialization. Keeping the useful unknown square $W$
does not create a new noise-correction mechanism.

### The exact ordinary two-query obstruction

At $p=1/2$, complete counter dephasing gives the exact instrument

$$
\mathcal E_{1/2}(\rho)
=\sum_{j=0}^1 |1-j\rangle\langle1-j|_P\otimes
 V_j\langle j|_P\rho|j\rangle_P V_j^\dagger. \tag{4}
$$

It holds when $\rho$ is entangled with arbitrary external registers.
One module call therefore equals measuring its input counter in $Z$,
classically choosing one query to $V_j$, and returning counter value
$1-j$. The label can be recorded without further disturbance because
the module output counter already contains it. Thus every ordinary
at-most-two-call implementation reduces to at most two **classically
indexed** $V_0/V_1$ queries, retaining all its original memory,
measurements and encodings.

The following argument includes adaptive repeated-label and stopping
branches; a fixed one-query-per-label assumption is not imposed.
Suppose the reduced protocol deterministically implements
$\operatorname{Ad}_{W(V_0,V_1)}$ for every pair of unknown unitaries.
Group its terminal CP maps by classical query word, of length at most
two. Their positive Choi matrices sum to the rank-one Choi matrix of
this unitary channel. Hence every word's CP map is a nonnegative scalar
multiple of that same unitary channel.

A word omitting $V_k$ has a CP map independent of $V_k$. For fixed
$V_j$, it cannot be nonzero and proportional to $\operatorname{Ad}_W$
for all $V_k$. Indeed, varying $V_k$ from $I$ to a nonscalar unitary
changes $W$ by a nonscalar block-diagonal unitary: its blocks are
$V_k$ and $V_jV_kV_j^\dagger$, in one order or the other. The two
unitary channels are distinct. Their rank-one Choi spans intersect only
at zero. Thus the zero-query, one-query and repeated-label words all
have zero probability for all unitary inputs. Only words $01$ and $10$
remain.

Group the output maps instead by their first query label $j$. Each group
again equals a scalar multiple $\lambda_j(V_0,V_1)\operatorname{Ad}_W$.
The first label is selected by a known instrument before either unknown
unitary acts, with an input effect $F_j$ independent of both unitaries.
Its outcome probability is $\operatorname{Tr}(F_j\rho)$. Trace
preservation of the complete subsequent protocol, and the zero mass of
the omitted/repeated words, imply

$$
\operatorname{Tr}(F_j\rho)
=\lambda_j(V_0,V_1)\operatorname{Tr}\rho
\quad\text{for all }\rho.
$$

Therefore $F_j=\lambda_j I$ and $\lambda_j$ is independent of the
input and of both unitaries. Some $\lambda_j$ is positive. Condition
the initial known preparation on that label and divide it by
$\lambda_j$; it is a normalized known channel. The resulting protocol
first queries $V_j$ and then, on every reachable history, $V_{1-j}$.
Replace any unreachable repeat or stop decision by a dummy call to
$V_{1-j}$. This yields a deterministic fixed-order circuit querying
each unknown unitary once and implementing the full unitary switch (1).

That contradicts the standard unitary-switch no-go theorem. The
[original proof](https://arxiv.org/html/0912.0195), Lemma 4 and Theorem 3
with Appendix B, uses complete positivity and pure unitary Choi outputs
to obtain the obstruction already from unitary inputs; the remark after
Lemma 4 states the extension to every $d>2$ using shift-and-multiply
unitaries. This known no-go theorem is the external mathematical
dependency here. The reduction above supplies the additional
classically adaptive repeated/omitted-query scope of this interface.

The obstruction extends to any fixed $0<p<1$. Freeze a putative exact
two-query protocol, including any settings chosen using its known $p$,
and preassign its two possible phase-fault bits. Every bit pattern has
positive probability. Its conditional output channel is CPTP, even
when the protocol stops early. A positive mixture of their Choi matrices
is a unitary Choi matrix only if every conditional channel is that same
unitary channel. Replacing their positive weights by the $p=1/2$
weights would therefore preserve exact implementation, contradicting
(4). At $p=0$ or $1$, two ordinary calls already implement $W$ up to an
irrelevant global phase, so those endpoints are excluded from the lower
bound.

### Three ordinary calls suffice

Store the original counter coherently in a clean control register and
use a separate physical query counter initialized to $0$. Its successive
known basis values toggle $0\to1\to0\to1$, so three module calls extract
the noiseless subroutine sequence $V_0,V_1,V_0$. Any $Z$ fault on this
basis counter is an irrelevant phase. A fixed pure dummy data register
$D$ and known controlled swaps route:

| Call | Original counter $0$ | Original counter $1$ |
| --- | --- | --- |
| $V_0$ | Real data | Dummy $D$ |
| $V_1$ | Real data | Real data |
| $V_0$ | Dummy $D$ | Real data |

The final data operations are $V_1V_0$ and $V_0V_1$, respectively,
while the dummy receives $V_0$ exactly once in either branch. Its final
state factors identically and can be discarded. Return the stored
original counter and the real data, discarding the known physical query
counter. This realizes $W$ on every entangled input for every $p$.
It is the usual extra-query unitary-switch construction applied through
the classical instruction interface.

Thus, for $0<p<1$, the bounded worst-case number of ordinary calls for
exact universal synthesis is three, while the ideal switch uses two.
This is not an ordinary expected-cost lower bound. For example, running
the three-call simulator with probability $2/3$ and rejecting otherwise
already has mean cost two and a perfect accepted output. It scores
$2/3$ if success/failure/rejection are scored $+1/-1/0$. Nor does the
exact no-go alone provide a numerical bound on optimal approximate
two-query simulation.

### Ordinary approximations and average query cost

These are ordinary achievable protocols for the full controlled-order channel
$W=\operatorname{diag}(BA,AB)$, with data dimension $d\ge2$. They use
known gates, clean memory, controlled routing, and classical selection of the
queried subroutine. Under complete counter dephasing those subroutine calls
are extracted by preparing the physical query counter in a fixed basis state.
Their helper operations have physical costs even though they consume no
unknown-module queries. A hard cap on calls per job and an average call budget
are different resource constraints.

Use normalized Choi matrices throughout. For an accepted map let $p$ be its
Choi trace and $q$ its overlap with the pure target Choi state
$\Phi_W$. Conditional entanglement fidelity is $q/p$; signed Bell reward
is $2q-p$. Half-diamond error is one half the diamond norm distance between
normalized channels. The constructions below have input-independent yields.

#### A minimax zero-query channel and explicit average-cost curves

Put $D=2d$, $r=2d^2-1$, and $m=1/r$. For a known orthogonal data Weyl
basis $\{Q_j\}_{j=0}^{d^2-1}$, with $Q_0=I$, define $\Gamma_*$ as
the uniform mixture of the $r$ known unitary channels

$$
\{I_P\otimes Q_j:0\le j<d^2\}\ \cup\
\{Z_P\otimes Q_j:1\le j<d^2\}.
$$

Let $\Pi$ project onto vectorized counter-block-diagonal operators, and
let $\Phi_Z$ denote the normalized Choi projector of $Z_P\otimes I$.
Then $J(\Gamma_*)=m\Pi_*$, where $\Pi_*=\Pi-\Phi_Z$ is an orthogonal
projector of rank $r$. Every target lies in this support: it is block
diagonal and
$\operatorname{Tr}[(Z_P\otimes I)^\dagger W]=\operatorname{Tr}BA-\operatorname{Tr}AB=0$.
Consequently

$$
J(\Gamma_*)-m\Phi_W=m(\Pi_*-\Phi_W)\succeq0.
$$

Both normalized Choi matrices have output marginal $I_D/D$. Thus
$(\Gamma_*-m\operatorname{Ad}_W)/(1-m)$ is CPTP. This gives a
half-diamond upper bound $1-m$; the Bell input attains it, because
$(1-m)\Phi_W$ and $m(\Pi_*-\Phi_W)$ are the orthogonal positive and
negative parts of $\Phi_W-J(\Gamma_*)$. Pointwise for every $A,B$,

$$
F_e(\Gamma_*,W)=m,\qquad
\tfrac12\|\Gamma_*-\operatorname{Ad}_W\|_\diamond=1-m.
$$

This zero-query guarantee is minimax optimal over the complete unknown-pair
family. To see this, with probability $1/r$ choose $A=B=I$. Otherwise
choose $M$ uniformly among the nonidentity data Weyls, choose $A$ Haar
independently, and set $B=MA^\dagger$. The two target blocks are then
$M$ and $AMA^\dagger$. Uniform nonidentity Weyls have isotropic second
moment on traceless operators; Haar conjugation has the same moment, and
the cross-block moment vanishes because $\mathbb E_A AMA^\dagger=0$.
Including the identity case yields
$\mathbb E\Phi_W=\Pi_*/r=J(\Gamma_*)$. For any zero-query channel
$\Lambda$, positivity and $\operatorname{Tr}J(\Lambda)=1$ give
$\mathbb EF_e(\Lambda,W)\le m$. Some pair therefore has fidelity at
most $m$, and Bell projection gives half-diamond error at least $1-m$.
The displayed channel attains both bounds on every pair. This witness prior
is deliberately correlated; it is not the independent-Haar pair prior.

The exact ordinary three-call routing circuit can now be used with an
independent probability $s=c/3$, with $\Gamma_*$ used otherwise.
For $0\le c\le3$, this always-accept channel has mean cost $c$ and,
uniformly over the unknown pair and all external references,

$$
F_e=s+(1-s)m,\qquad \delta_\diamond=(1-s)(1-m).
$$

For $c=2,d=2$, these values are $5/7$ and $2/7$. It matches or
improves the prescribed switch decoder's fidelity and half-diamond error
when $\kappa\le1/3+2/[3(2d^2-1)]$, which is $3/7$ for qubit data.
This compares two specified implementations, not their optimized frontiers.

More generally, to prescribe acceptance $\pi\in[0,1]$ and budget
$c\in[0,3]$, put $s=\min(\pi,c/3)$. Run and accept the exact circuit
with probability $s$, use and accept $\Gamma_*$ with probability
$\pi-s$, and otherwise reject without a call. The accepted map has

$$
q=m\pi+(1-m)s,\quad F_{e,\mathrm{acc}}=m+(1-m)s/\pi,\quad
\delta_{\diamond,\mathrm{acc}}=(1-s/\pi)(1-m),\quad
\mathbb EN=3s\le c.
$$

The conditional formulas require $\pi>0$. Running the exact circuit
with probability $2/3$ and otherwise rejecting gives mean cost two,
$p=q=2/3$, and signed reward $2/3$. The mean-two always-accept
qubit channel has signed reward only $3/7$. Under the *different*
independent-Haar pair prior, identity fallback instead gives average fidelity
$2/3+1/(3d^2)$, or $3/4$ for qubits, because
$\operatorname{Tr}W=2\operatorname{Tr}BA$ and
$\mathbb E|\operatorname{Tr}BA|^2=1$. That is an average guarantee, not
the uniform $5/7$ guarantee or a $2/7$ diamond guarantee. No positive
query-cost curve here is asserted optimal.

#### A hard-two-query controlled-teleportation family

This family uses the standard
[postselected teleportation simulation](https://arxiv.org/html/0912.0195v4),
with an initial counter instrument selecting the chronological order.
Its displayed achievable constants are not claimed to optimize that
larger class of simulations or to establish a new mechanism's priority.

Choose $a,b\ge0$ with $a^2+b^2=1$. Apply the known counter instrument
$D_0=\operatorname{diag}(a,b)$, $D_1=\operatorname{diag}(b,a)$.
Select chronological oracle order $A,B$ on outcome zero and $B,A$ on
outcome one. On the first order branch, prepare $\Phi_{RS}$, swap data
$T$ with $S$ controlled on $P=1$, query $A$ on $T$, undo
that controlled swap, query $B$ on $T$, swap $T,S$ on $P=1$,
and Bell-measure $R,S$. With the Bell convention that outcome $j$
inserts a Weyl $Q_j$, the full effective Kraus operators, including the
initial instrument, are

$$
\begin{aligned}
K_0&=\operatorname{diag}(aBA,(b/d)AB),&
K_j&=|1\rangle\langle1|\otimes(b/d)AQ_jB\quad(j\ne0),\\
K'_0&=\operatorname{diag}((b/d)BA,aAB),&
K'_j&=|0\rangle\langle0|\otimes(b/d)BQ_jA\quad(j\ne0).
\end{aligned}
$$

The two order outcomes are classical. Their effects sum to identity, so the
complete instrument is TP. Retaining only identity Bell outcomes gives

$$
p=a^2+b^2/d^2,\qquad q=(a+b/d)^2/2,\qquad
2q-p=2ab/d.
$$

Its normalized accepted channel, relative to $W$, is counter dephasing
with visibility $2ab/(dp)$. Thus its conditional fidelity is $q/p$
and half-diamond error is $1-q/p$. At $a=b=1/\sqrt2,d=2$, the yield
is $5/8$, conditional fidelity $9/10$, half-diamond error $1/10$,
and signed reward $1/2$. At $a=b/d$, it is the exact target with
yield $2/(d^2+1)$. This adaptive initial-order instrument is outside a
fixed-order success-probability bound.

For an all-outcome channel, apply the same known traceless data unitary
$R$ after every nonidentity Bell outcome; for example a cyclic shift.
Weyl Parseval gives, for every $A$,
$\sum_{j\ne0}|\operatorname{Tr}(A^\dagger RAQ_j)|^2=d^2$, and the
same identity holds for $B$. Consequently, for every unknown pair,

$$
F_e=\frac{a^2}{2}+\frac{ab}{d}+\frac{b^2}{d^2}=:f(a,b;d).
$$

This also gives the exact half-diamond error $1-f$. For completeness,
conjugate the output by $W^\dagger$, write $\Phi_I,\Phi_Z$ for the
normalized full-system identity and counter-Z Choi projectors, and let
$\Pi_z$ project onto all vectorized operators supported in counter block
$z$. Let $e_z$ be the normalized identity direction in that block and
$h_z$ the normalized direction of the corresponding conjugate of $R$.
The two vectors are orthogonal because $\operatorname{Tr}R=0$. Directly
summing the Kraus projectors yields

$$
J=f\Phi_I+
\left[\frac{(a-b/d)^2}{2}+\frac{b^2}{2d^2}\right]\Phi_Z+
\frac{b^2}{2d^2}\sum_{z=0}^1(\Pi_z-|e_z\rangle\langle e_z|-|h_z\rangle\langle h_z|).
$$

Each residual summand is an orthogonal projector; its support is orthogonal
to $\Phi_I$. The complement, normalized by $1-f$, is CPTP because
the original and target Choi marginals agree. The resulting convex-channel
decomposition proves the upper bound $1-f$, and the target Bell test
attains it. Optimizing this *family* gives the largest eigenvalue of
$\left(\begin{smallmatrix}1/2&1/(2d)\\1/(2d)&1/d^2\end{smallmatrix}\right)$.
For qubit data its fidelity is $(3+\sqrt5)/8$ and its exact half-diamond
error is $(5-\sqrt5)/8$. These are achievable values, not an optimal
hard-two-query converse. Nonidentity failures have a counter-subspace kernel,
so this instrument does not support free retry on the original arbitrary
input.

The standard-library replay `checks/architecture/verify_dispatch_baselines.py`
checks the full normalized Choi, TP, projector/PSD certificates, accepted
maps, and fidelity/diamond formulas on four rational noncommuting pairs at
$d=2,3$, without floating-point arithmetic. It checks three rationally
represented filter ratios, including the equal-amplitude and exact-success
settings. Irrational optimizer values and the all-dimension proofs are
analytic claims, not finite-sample conclusions.

#### A qualitative average-cost separation at each fixed dimension

Here fix the module noise at $p=1/2$, so (4) supplies the classically
indexed subroutine access used in the proof. The statements below do not
automatically cover every interior $p$ or the physical vacuum ports.

The exact two-query impossibility does imply a qualitative approximate
separation under a fresh independent-Haar pair prior, but does not by itself
give an explicit noise threshold. Here is the required transfer argument.

First, any terminal branch that never queried one of the two gates obeys
$\bar q\le\bar p/d^2$. To prove this, condition on the queried gate
$A$. Averaging the normalized target Choi over the unqueried Haar gate
$B$ gives, in the two matched counter blocks,
$$
\mathbb E_B\Phi_W=\frac1{2d^2}
\begin{pmatrix}I&R_A\\R_A^\dagger&I\end{pmatrix},
$$
where $R_A$ is unitary. Its eigenvalues are $1/d^2$ and zero. The
matrix entries, for row $(a,b)$ and column $(c,e)$, are
$(R_A)_{ab,ce}=A_{eb}\overline{A_{ca}}$; summing over $c,e$ gives
$R_AR_A^\dagger=I$ by unitarity of $A$. The
branch's accepted Choi operator is positive and independent of $B$, so
its overlap is at most its trace divided by $d^2$. This permits arbitrary
memory, postselection, and repeated calls to the other gate. In particular
every terminal history with at most one query has nonpositive signed reward.

Let $S_2(d)$ be the optimum Haar-average signed reward over every ordinary
protocol with a hard two-call cap, arbitrary memory, early stopping,
accept/reject outputs, and classical adaptive gate labels. This optimum is
attained: padding stopped histories with discarded dummy queries represents
all such instruments by a fixed finite-dimensional classical-control tree
of positive combs satisfying closed linear normalization constraints. The
accepted comb is constrained by a normalized total comb, $C_{\rm acc}\preceq
C_{\rm tot}$. The set is compact, and the integrated objective is linear and continuous.
Arbitrarily large ancillary memories and classical record alphabets do not
enlarge this finite-dimensional Choi set.

If $S_2(d)=1$, nonnegativity of
$1-(2q-p)=(1-p)+2(p-q)$, continuity in $A,B$, and full support of Haar
measure force $p=q=1$ for every pair. Positivity then forces the full Choi
operator to equal the pure target, giving a deterministic universal exact
two-query implementation. The exact NR-R12 no-go excludes that possibility.
Therefore $S_2(d)<1$ for each fixed $d$.

Now allow any classical stopping rule with $\mathbb EN\le2$, including
unbounded rare tails, with every query and rejection charged. Nontermination
is scored as rejection; finite expected oracle count alone does not exclude
infinite computation using no further oracle. Let
$r=\Pr(N\le1)$ and $u=\Pr(N\ge3)$, evaluated in the Haar/Bell
experiment. Since $\mathbb EN\ge2-2r+u$, one has $u\le2r$.
The short-terminal reward bound gives $\bar R\le1-r$. Truncate the
protocol after query two and reject every history about to query again.
Its reward is at most $S_2(d)$, and restoring the long histories can add
at most $u$. Thus
$$
\bar R\le\min\{1-r,S_2(d)+2r\}\le\frac{2+S_2(d)}3<1.
$$

This proves a positive margin below perfect-switch reward for each fixed
dimension in this ideal query model. It provides no evaluated margin,
dimension-uniform bound, hardware advantage, or numerical robustness
threshold. In particular, the achievable mean-two reward $2/3$ remains
an ordinary lower bound. A coherent path-occupation cost, frame-correlated
advice, persistent training across jobs, or extra controlled oracle ports
would be different resource models.

### Residual phase error from an imperfect external control

For the prescribed unmodified external order control, let its state be
$\omega_\kappa=(I+\kappa X)/2$, $0\le\kappa\le1$, or equivalently
let mandatory scalar phase dephasing of visibility $\kappa$ occur before
its $X$ readout. This is the stated scalar model, not arbitrary router,
memory or module noise. Put $a=(1+\kappa)/2$ and $b=(1-\kappa)/2$.
The specified syndrome measurement and minus-$Z$ feedback give the
complete corrected instrument

$$
\begin{aligned}
\mathcal D_+&=a\alpha\operatorname{Ad}_W
                  +b\beta\operatorname{Ad}_{ZW},\\
\mathcal D_-&=a\beta\operatorname{Ad}_W
                  +b\alpha\operatorname{Ad}_{ZW}.
\end{aligned} \tag{5}
$$

Summing both retained outcomes gives exactly

$$
\mathcal D_++\mathcal D_-
=\left[a\,\mathrm{id}+b\operatorname{Ad}_Z\right]
 \circ\operatorname{Ad}_W. \tag{6}
$$

Its entanglement fidelity relative to $W$ is $a$, because
$\operatorname{Tr}Z=0$, and its half-diamond error is exactly $b$:
the triangle bound is attained on a coherent superposition of the two
counter eigenspaces. Thus $\kappa=0.97$ gives fidelity $0.985$ and
half-diamond error $0.015$ for this decoder. These formulas do not
establish a robust advantage over optimal ordinary approximate synthesis.
The decoder is not asserted optimal for every known $p,\kappa$; for
example, at $p=0$ one should ignore an unreliable syndrome.

### Physical resources and application limits

**Two coherent-use slots.** Equal reduced maps do not make two chronological
visits to one noisy processor a self-switch. If both arms encounter the
same time-ordered Kraus events $K_{t_1}$ then $K_{t_2}$, both have the
same product and no order-parity flag appears. A realization needs two
appropriately matched module slots, or a specified equivalent
time-delocalized implementation. The dilation must associate its
environment records with those slots and avoid additional which-time or
which-order leakage. Independence of the two channel slots in the
abstract switch does not specify the temporal bath correlations needed
when a physical slot is visited early in one arm and late in the other.
The [trajectory framework, Section IV.2](https://arxiv.org/html/1812.05292)
explicitly treats that distinction. Ordinary memoryless chronological
gate noise cannot simply be relabelled as this coherent-use resource.
The two slots must implement the same $V_0,V_1$; fabrication mismatch,
drift, reset and phase conventions need calibration and a separate error
analysis.

In particular, a quasistatic phase bit on a reused physical processor is
an ordinary bypass, rather than the fresh-call noise model above. If the
same bit $s$ persists for two ordinary visits, then
$(Z^sU)^2=(-1)^sW$, so those two visits already implement $W$ perfectly.
A proposed physical dilation must support the switch's early/late slot
coherence without silently granting this repeated-use cancellation to
the ordinary circuit. The channel equations alone do not establish that
resource. The event-indexed construction below resolves logical consistency,
but does not identify a native processor offering it cheaply.

**An explicit coherent event memory.** A consistent engineered dilation
uses a private visit head $Q_m$ and independent retained fault coins
$E_{m,k}$ at each station $m=A,B$. Initially the head is $0$ and every
coin is diagonal with probabilities $(1-p,p)$. An occupied visit applies

$$
|k\rangle_{Q_m}|s_m\rangle_E|\psi\rangle
\longmapsto |k+1\rangle_{Q_m}|s_m\rangle_E
 Z^{s_{m,k}}U|\psi\rangle. \tag{7}
$$

The vacuum sector acts as the identity, including on the head and tape.
The coin is selected by visit number, not by laboratory time. For a
bounded horizon $M$, supply $M$ independent coins and $M+1$ head states;
complete the head shift unitarily on unused states and forbid exhaustion.
An infinite reusable memoryless channel requires fresh reservoir blocks,
not silent wraparound. Coin preparation, addressing and refresh count.

In history $0$ the early visit advances $Q_A$ and the late visit advances
$Q_B$; history $1$ reverses them. Both histories finish with heads
$|1,1\rangle$ and unchanged tapes. For each fixed tape trajectory their
payload products are $K_{s_{B,0}}K_{s_{A,0}}$ and
$K_{s_{A,0}}K_{s_{B,0}}$, respectively, where $K_s=Z^sU$.
Tracing these common final environment states gives exactly the product
switch of (2), including every control/data/reference input. On ordinary
repeated occupied calls, the next unexposed independent coin is used even
conditional on the accessible past. Thus this same port has the fresh-call
comb law. Reusing one stable coin would instead give the ordinary echo;
rewinding the head without replacing its tape grants that bypass, and
reading a used coin grants a direct correction syndrome.

The intermediate heads are $|1,0\rangle$ and $|0,1\rangle$ in the two
histories. They must retain coherence until their reversible alignment;
a classical detector or dissipative increment exports an arrival-time
record. If their $|0\rangle\langle1|$ coherences acquire independent
factors $\lambda_A,\lambda_B$, and the remaining path visibility is $v$,
(5) holds with $\kappa=v\lambda_A\lambda_B$. The prescribed decoder's
half-diamond error is $(1-v\lambda_A\lambda_B)/2$. With
$\lambda_m=e^{-\Delta t/T_{2,m}}$ and ideal routing, visibility $0.97$
requires

$$
\Delta t/T_{2,A}+\Delta t/T_{2,B}\le-\ln(0.97).
$$

The equal-head threshold is $2\Delta t/[-\ln(0.97)]\simeq65.66\Delta t$;
$66\Delta t$ is sufficient. This is coherence storage, not stability of a classical count.
If each complete occupied/vacuum station-window macro has additional
half-diamond error $\epsilon_{m,t}$ on the correlated head/tape inputs,
a four-macro hybrid adds at most $\sum_{m,t}\epsilon_{m,t}$, plus routing
errors. Occupied-channel tomography alone does not certify this norm.
Already modeled storage errors must not be charged twice.

These are explicit extra resources: protected heads, reversible occupation
triggers, stable private coins, quantum addressing, no exported timestamp,
and a specified reset policy. Nondestructive photon–matter coupling has
been demonstrated by [Reiserer et al.](https://arxiv.org/abs/1311.3625) and
[Niemietz et al.](https://arxiv.org/abs/2103.14677), but those experiments
do not supply the full head/tape dispatcher. The construction instantiates
the environmental-memory issue already present in the
[trajectory framework](https://arxiv.org/html/1812.05292), rather than a
new correction mechanism. An operator's actual rewind, readout and routing
controls must be admitted to the ordinary comparison. Granting unrestricted
coherent routing on the full microscopic ports also grants the chronological
circuit implementing this construction; the abstract causal-order query
comparison and a hardware comparison are different statements.

**Clock-indexed phase bits are different.** If the four station/window
events instead use independent bits with occupied unitary $Z^sU$ and the
same identity-on-vacuum extension, the two histories use disjoint bits.
Their diagonal payload map is
$\alpha\operatorname{Ad}_W+\beta\operatorname{Ad}_{ZW}$ and their
cross-history map is $(1-2p)^2\operatorname{Ad}_W$: each averaged
two-gate product is $(1-2p)W$. Substitution into the $X$ measurement and
$Z$ feedback leaves exactly that ordinary diagonal map. It gives no
correction gain. This assertion fixes the vacuum phase convention;
one-call dephasing marginals alone do not fix it.

**Parallel ordinary baseline.** The query saving is not automatically a
latency saving on two native processors. Four ordinary calls implement
$W$ in two parallel query rounds using **two separate** pure dummy
registers $D_0,D_1$. In round one, $V_0$ acts on data for counter $0$
and on $D_0$ for counter $1$; simultaneously $V_1$ acts on data for
counter $1$ and on $D_1$ for counter $0$. Round two reverses those
allocations. The real data receives the desired order, while $D_0$
receives $V_0$ once and $D_1$ receives $V_1$ once in both branches.
The total unitary factors as $W\otimes V_0\otimes V_1$, so there is
no discarded-order record. Initialize the two native counters to $0$
and $1$. Their automatic toggles swap which physical port supplies
$V_0$ and $V_1$ in round two; adjust the known routing accordingly.
Both native counters remain in basis states and need no between-round
reset. This costs four native calls, two matching processors, two dummy
data memories and controlled routing; preparation, interjob reset and
readout also count where applicable. A single dummy passing through both products would not
factor in general. The related four-box resource comparison is
established in [Fellous-Asiani et al.](https://doi.org/10.1103/PhysRevResearch.5.023111).
Consequently two versus three sequential calls cannot be advertised as
a universal two-versus-three wall-clock speedup.

**Access and noise assumptions.** Known cheaply compilable subroutines,
their controlled versions, a protected encoded dispatch interface or a
known phase-fault bit change the baseline. An observed random-$Z$ fault
bit permits correction after each ordinary call. A computational-basis
measurement outcome from (4) only identifies the collapsed program
value and does not restore its prior coherence. Separately available
$V_0,V_1$ ports plus an order router already implement the original
unitary switch; the outer noisy dispatcher is then not the minimal
resource. Counter-$Z$ is a cheap transported symmetry, since
$UZ=(-Z)U$, but a check of that relation cannot detect a fault commuting
with $Z$. Protecting the counter by a code requires its compatibility
with arbitrary unknown dispatch, rather than merely a clean external
control. The ordinary lower bound includes clean external memories and
encodings; it does not exclude stronger native encoded gates or supplied
fault records.

**Coherent control flow and reuse.** A classical counter needs no repair:
two ordinary module calls already apply the requested data product
perfectly. The full coherent counter output is essential; discarding it
also changes the task. [Yuan, Villanyi and Carbin's Quantum Control Machine](https://arxiv.org/html/2304.15000v5)
provides a precise motivation for program counters in superposition and
synchronized control flow. It explicitly presents a theoretical
programming/compilation model, not a near-term hardware realization of
(2). Its known instruction circuits do not automatically supply opaque
arbitrary-unitary subroutines or post-dispatch-only dephasing. A real
application must justify those restrictions and count fetch/decode,
compilation, routing, helper memory, control coherence and internal gate
faults. Fixed reusable $V_j$ may also be calibrated once and compiled
across later jobs; all training and synthesis costs must be amortized
within the actual drift window. No result here bounds that reusable
hardware frontier.

### Time-varying classical phase fields: a matched ordinary construction

There is a second precise microscopic model, distinct from (7). Let the
occupied gate at station $j$ in window $t$ be

$$
K_{j,t}=e^{-i\theta_{j,t}Z}U,
$$

with identity action on vacuum. The four real phases are classical fields
independent of the chosen path, with no extra arrival records, backaction,
loss or internal data errors. A stochastic global phase relative to vacuum
would be an additional specified noise process. Equal occupied dephasing
channels are insufficient to assert this extension.

For any two arms $e^{-ixZ}W$ and $e^{-iyZ}W$, the plus Kraus operator is
$\cos[(x-y)/2]e^{-i(x+y)Z/2}W$. After minus-$Z$ feedback the minus Kraus
operator is $-i\sin[(x-y)/2]e^{-i(x+y)Z/2}W$. Retaining both outcomes
therefore gives that same unitary channel for each fixed trajectory.
The physical switched histories $B_2A_1,A_2B_1$ have angles
$\theta_{B,2}-\theta_{A,1}$ and
$\theta_{A,2}-\theta_{B,1}$, so their corrected output is

$$
\operatorname{Ad}_{e^{-irZ}W},\qquad
r=\frac{\theta_{A,2}-\theta_{A,1}+\theta_{B,2}-\theta_{B,1}}2. \tag{8}
$$

An ordinary coherent path filter uses histories $A_2A_1$ and $B_2B_1$.
Their angles are $\theta_{A,2}-\theta_{A,1}$ and
$\theta_{B,2}-\theta_{B,1}$, so the same measurement and feedback give
exactly (8), trajectory by trajectory and including any reference.
The flag distributions need not agree. With identical external visibility
$v$, both corrected sums additionally acquire the same phase channel
$[(1+v)\mathrm{id}+(1-v)\operatorname{Ad}_Z]/2$.

Both physical circuits use two installations, two windows, four potential
station/window interactions, two occupied payload visits, one coherent path
qubit, one $X$ readout and one conditional $Z$. Interwindow crosslinks in
the switched circuit become local delay loops in the ordinary circuit.
Their actual loss, delay and stabilization costs must be measured; neither
permutation is intrinsically an additional entangling gate. This comparison
requires those local loops and the stated coherent vacuum access. It is not
a two-query simulation in the earlier channel-only interface.

**Optimal Gaussian decoding, including accepted outputs.** Suppose the two
stations are independent copies of a centered Gaussian pair
$(\theta_1,\theta_2)$, with equal variance $\sigma^2$ and correlation
$\rho\in[-1,1]$. Define

$$
s=\frac{\theta_{B,2}+\theta_{B,1}-\theta_{A,2}-\theta_{A,1}}2,
\quad k_r=e^{-2\sigma^2(1-\rho)},\quad k_s=e^{-2\sigma^2(1+\rho)}.
$$

Then $r,s$ are independent Gaussians, with variances
$\sigma^2(1-\rho)$ and $\sigma^2(1+\rho)$. The switched isometry before
averaging is

$$
e^{-irZ}\bigl[\cos s\,|+\rangle I-i\sin s\,|-\rangle Z\bigr]W.
$$

Symmetry makes the averaged $X$-basis off-diagonal block zero. Thus even
a joint quantum postdecoder receives a classical flag: its true value
$t$ has probabilities $(1+(-1)^t k_s)/2$, and the payload has $Z^t$
followed by independent dephasing of bias $k_r$. External visibility $v$
flips that flag with probability $(1-v)/2$. For a generic true-flag bias
$k$, the reported flag masses and conditional signed payload biases are

$$
m_\pm(k)=\frac{1\pm vk}{2},\qquad
b_+(k)=\frac{k_r(v+k)}{1+vk},\qquad
b_-(k)=\frac{k_r(k-v)}{1-vk}. \tag{9}
$$

Omit any zero-mass flag. Correct the more probable $I/Z$
error in each flag. This attains

$$
F_{\mathrm{sw,opt}}=\frac{1+k_r\max(v,k_s)}2,
\qquad
\epsilon_{\mathrm{sw,opt}}=\frac{1-k_r\max(v,k_s)}2. \tag{10}
$$

These are optima over arbitrary CPTP postdecoders for entanglement fidelity
and half-diamond distance, not only over a specified syndrome rule. For
payload dimension $n=2d$, Hilbert–Schmidt orthogonality of $I,Z$ gives

$$
\sum_\ell\bigl(|\operatorname{Tr}C_\ell|^2+
|\operatorname{Tr}C_\ell Z|^2\bigr)
\le n\sum_\ell\operatorname{Tr}C_\ell^\dagger C_\ell=n^2
$$

for any decoder. Hence its fidelity on either flagged $I/Z$ mixture is
at most the larger mixture weight. A trace-decreasing accepted decoder
replaces the last expression by $n^2p$: both hidden components have
maximally mixed payload marginal on the Bell test. Scaled unitary
corrections attain the bound. The Bell input also lower-bounds the diamond
error by $1-F$; the corrected dephasing channel attains equality.

Ordinary cross-station serial processing has visibility
$e^{-4\sigma^2}=k_rk_s$. Ordinary same-order path filtering with minus-$Z$
feedback has visibility $vk_r$. Choosing the better ordinary procedure
matches (10) for every $\rho$. This choice presumes calibrated field
parameters and the same native controls. It is a recovery comparison, not
a parameter-independent simulator for an unknown noise-estimation task.

For $\rho\ge0$ the ordinary path filter is stronger still. Its independent
differential phase is
$[(\theta_{A,2}-\theta_{A,1})-(\theta_{B,2}-\theta_{B,1})]/2$,
with variance $\sigma^2(1-\rho)$, so its flag bias is $k=k_r\ge k_s$.
Write $f_\pm(k)=(1+|b_\pm(k)|)/2$. At Bell-input acceptance yield $p$,
the exact maximal unnormalized correct Bell mass is

$$
Q_k(p)=
\begin{cases}
p f_+(k),&0\le p\le m_+(k),\\
m_+(k)f_+(k)+(p-m_+(k))f_-(k),&m_+(k)\le p\le1.
\end{cases} \tag{11}
$$

The preceding Kraus bound includes arbitrary accepted payload filters;
accepting the higher-fidelity flag first attains every point. As $k$
increases, its top fidelity $f_+$, available mass $m_+$, and total
$Q_k(1)=[1+k_r\max(v,k)]/2$ all increase. Before the larger breakpoint
the top ordinary segment dominates; beyond it the difference is affine
with nonnegative endpoint values. Consequently
$Q_{k_r}(p)\ge Q_{k_s}(p)$ for all $p$. This covers the full Bell
acceptance–fidelity frontier, including the signed reward $2Q-p$.
For negative $\rho$, (10) is still matched, but no complete low-yield
frontier comparison is claimed here. Unequal or phase-dependent loss,
non-Gaussian backaction and nonclassical baths require new instruments.

### Verification and unresolved extension

[The exact replay](checks/architecture/verify_dispatch.py) uses only
standard-library Gaussian-rational arithmetic. It constructs noncommuting
rational unitary examples at $d=2,3$ and compares the full normalized
counter-data Choi matrices, including the reported flag, at
$p\in\{0,1/2,9/10\}$ and $\kappa\in\{0,97/100,1\}$. It also checks
(4), the three-call dummy factorization, and the four-call two-dummy
factorization. These finite examples check signs, normalization and
reference coherence; the general algebra and the cited unitary-switch
no-go are analytic dependencies. This result is not formalized in Lean.

The same replay checks 96 full quantum-output Choi identities for (8),
including rational phase trajectories, static fields and imperfect
controls. It deliberately distinguishes the two flag instruments.
Nine exact event-head cases retain the reported flag, three clock-indexed
cases check the failed correction, and six reuse/rewind cases check the
fresh-reservoir premise. The Gaussian integrals, optimal-decoder and
whole-frontier arguments are analytic; finite replay does not fit a
hardware bath or establish a protected event-memory implementation.

Higher-dimensional cyclic counters and cyclic instruction orders are a
possible next question. Their resource-optimality, prior overlap and
native implementation have not been established here and are not part
of NR-R12. A usable architecture still needs a named physical dispatcher,
a validated coherent-use/noise model and a measured advantage over the
ordinary memory, parallel, compilation and reuse alternatives above.
