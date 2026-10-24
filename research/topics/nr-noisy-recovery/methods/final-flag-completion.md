# Final-flag completion and two-order Hamiltonian simulation

<a id="nr-r06-final-flag-completion"></a>

This proof component of [NR-R06](../architecture-baselines.md#nr-r06)
gives a scoped ordinary comparator for postselected state-output protocols.
If the native accepted payload map has a physically realizable ordinary
completion, a common payload decoder and an always-success target, that
ordinary completion has no greater all-launch diamond error. Applied to
the bare two-order Hamiltonian-simulation step, ordinary random order
supplies exactly that completion with the same worst-case module calls.
This does not assess branch-dependent recovery, retained-control decoding
or a service whose specification legitimately permits rejection.

[Exact replay](../checks/architecture/final_flag_completion.py) checks the
finite CP identities and cost ledgers. The diamond comparison is analytic;
the finite replay is not a numerical diamond-norm certificate or a physical
routing certificate.

## A final-flag completion lemma

All spaces are finite dimensional. Let $\mathcal A$ be the accepted CP,
trace-nonincreasing payload map of a native instrument. Assume an ordinary,
physically realizable CPTP map $\mathcal O_0$ has an exact decomposition
$\mathcal O_0=\mathcal A+\mathcal T$, with $\mathcal T$ CP. Let
$\mathcal D$ be a payload-only CPTP decoder, the same decoder on
$\mathcal A$ and $\mathcal O_0$. Let $\mathcal J$ be any rejected CP map,
possibly with a different payload space and additional rejection records,
satisfying

$$
\mathcal J^*(I)=I-\mathcal A^*(I).
$$

The complete native channel and the ordinary decoded channel are

$$
\mathcal N
=|s\rangle\langle s|\otimes\mathcal D\mathcal A
+|f\rangle\langle f|\otimes\mathcal J,
\qquad
\mathcal O=\mathcal D\mathcal O_0.
$$

For any always-success CPTP target $\mathcal U$, embedded in the success
space as $\mathcal N_{\rm ideal}=|s\rangle\langle s|\otimes\mathcal U$,

$$
\frac12\|\mathcal O-\mathcal U\|_\diamond
\le\frac12\|\mathcal N-\mathcal N_{\rm ideal}\|_\diamond.
\tag{FC1}
$$

To prove this, take any input density matrix $\rho$ on the payload and an
arbitrary reference. Since $\mathcal O_0$ and $\mathcal D$ are TP,

$$
\mathcal T^*(I)=I-\mathcal A^*(I),\qquad
\operatorname{Tr}[(\mathcal D\mathcal T\otimes\operatorname{id})(\rho)]
=\operatorname{Tr}[(\mathcal J\otimes\operatorname{id})(\rho)].
$$

The triangle inequality and positivity give

$$
\begin{aligned}
\|[(\mathcal O-\mathcal U)\otimes\operatorname{id}](\rho)\|_1
&\le
\|[(\mathcal D\mathcal A-\mathcal U)\otimes\operatorname{id}](\rho)\|_1
+\operatorname{Tr}[(\mathcal D\mathcal T\otimes\operatorname{id})(\rho)]\\
&=\|[(\mathcal N-\mathcal N_{\rm ideal})
       \otimes\operatorname{id}](\rho)\|_1.
\end{aligned}
$$

The equality uses the orthogonal success and reject output blocks and
positivity of the rejected block. The density-operator characterization
of the diamond distance between CPTP maps now proves (FC1). No unitary
assumption on the primitive calls or target is needed.

For every positive payoff operator $M$ on the decoded payload and reference,
the same assumptions imply

$$
\operatorname{Tr}[M(\mathcal O\otimes\operatorname{id})(\rho)]
\ge
\operatorname{Tr}[M(\mathcal D\mathcal A\otimes\operatorname{id})(\rho)],
\tag{FC2}
$$

because their difference is the positive operator
$(\mathcal D\mathcal T\otimes\operatorname{id})(\rho)$.
This is an all-launch positive linear score, with rejected launches scoring
zero. It does not order signed-observable scores or success-normalized
fidelity, which is nonlinear in $\mathcal A$.

The lemma supplies a comparator only when $\mathcal O_0$ is actually
realizable at the counted resources. Abstract existence of a CP complement
does not establish this. It does not reproduce the native flagged
instrument. It does not constrain useful branch-dependent payload decoding,
a joint retained-control decoder, a legitimate accepted-only output service,
or a target with a specified nonzero safe-reject branch. Different accepted
branch decoders also need a fresh analysis unless the decoded sum itself
has a realizable ordinary CP completion. These are scope conditions; they
do not assert an advantage for any excluded extension.

## The bare two-order simulation step

Let $A,B$ be bounded self-adjoint Hamiltonians, $h\in\mathbb R$, and the
available calls be $U_A(h)=e^{-ihA}$ and $U_B(h)=e^{-ihB}$. Put
$U=U_BU_A$ and $V=U_AU_B$. Coherent order control initialized in
$|+\rangle$ and read in $X$ gives

$$
K_+=\frac{U+V}{2},\qquad K_-=\frac{U-V}{2},\qquad
\Gamma_\pm=\operatorname{Ad}_{K_\pm}.
$$

Expanding the two Kraus products cancels the cross terms exactly:

$$
\mathcal R
=\frac{\operatorname{Ad}_U+\operatorname{Ad}_V}{2}
=\Gamma_++\Gamma_-.
\tag{TS1}
$$

One ordinary random-order bit, two module calls and discarding the internal
bit realize $\mathcal R$. This needs neither controlled-$U_A$ nor a unitary
square root or half-duration access. If the application requires retaining
the random seed as an output record, that output service needs its own
comparison.

Stepwise composition uses the actual same calls and a fresh-channel
interface. Fitted reduced maps for a persistent bath do not establish it.
For a correlated device/bath history, retain the physical whole-history
instrument and establish an actually realizable ordinary $\mathcal O_0$
before applying the general lemma. A single-step fit grants no bath reset.

For $r$ steps, possibly with different $U_j,V_j$, define

$$
\mathcal P=\Gamma_{+,r}\cdots\Gamma_{+,1},\qquad
\mathcal O_0=\mathcal R_r\cdots\mathcal R_1.
$$

Expanding each $\mathcal R_j=\Gamma_{+,j}+\Gamma_{-,j}$ gives

$$
\mathcal O_0=\mathcal P+\mathcal T,\qquad
\mathcal T=
\sum_{w\in\{+,-\}^r\setminus\{+^r\}}
\Gamma_{w_r,r}\cdots\Gamma_{w_1,1}.
$$

Every summand of $\mathcal T$ is CP. An all-plus native protocol that aborts
at its first minus, with arbitrary physically complete rejected processing
and a common accepted payload decoder, therefore satisfies (FC1)–(FC2).
The ordinary random-order process has at most the same all-launch diamond
error to any always-success target, including the intended time evolution.
The comparison holds for every $h,r$ without a short-time approximation.

The native abort payload need not equal $\mathcal T$: the latter applies
later steps after the first minus, whereas the aborting protocol may stop.
Only the effects and total traces agree. For static $K_\pm$, first-minus
Kraus operators are $L_k=K_-K_+^{k-1}$, $1\le k\le r$, and completeness
$K_+^*K_++K_-^*K_-=I$ telescopes to

$$
\sum_{k=1}^rL_k^*L_k
=I-(K_+^r)^*K_+^r
=\mathcal T^*(I).
\tag{TS2}
$$

The same telescoping with ordered products holds for different steps.
Measuring or forgetting a minus flag does not justify retrying on unknown
data: $K_-$ generally damages it. Known-input preparation is a different
resource than an unknown input/reference and must be charged anew. Useful
minus-branch recovery or feedback requires a fresh complete instrument;
(TS1) alone does not assess that candidate.

## Error order, rejection and call budgets

Write $X=-iA$, $Y=-iB$. The cubic coefficient of $K_+$ is

$$
\frac{X^3+Y^3}{6}
+\frac{X^2Y+XY^2+Y^2X+YX^2}{4}.
$$

Subtracting $(X+Y)^3/6$ yields

$$
K_+(h)-e^{h(X+Y)}
=\frac{h^3}{12}
 \bigl([X,[X,Y]]+[Y,[Y,X]]\bigr)+O(h^4).
\tag{TS3}
$$

Thus the generic plus amplitude matches through second order. Its cubic
term need not vanish: $A=\sigma_x$, $B=\sigma_z$ give the coefficient
$i(A+B)/3$, since the nested commutators contribute $4iB$ and $4iA$.
This is not a generic third- or higher-order formula. Special cancellations
need a workload and an ordinary comparator using the same algebra.

For bounded self-adjoint $A,B$, the commutator identity

$$
[A,e^{-ihB}]
=-i\int_0^h e^{-i(h-s)B}[A,B]e^{-isB}\,ds
$$

and its application inside

$$
[e^{-ihA},e^{-ihB}]
=-i\int_0^h e^{-i(h-u)A}[A,e^{-ihB}]e^{-iuA}\,du
$$

give $\|[U_A(h),U_B(h)]\|\le h^2\|[A,B]\|$, because all exponential
factors are unitary. Hence

$$
\|K_-\|\le\frac{h^2\|[A,B]\|}{2},\qquad
\Gamma_-^*(I)\le\delta I,\qquad
\delta=\min\left\{1,\frac{h^4\|[A,B]\|^2}{4}\right\}.
$$

Completeness gives $\Gamma_+^*(I)\ge(1-\delta)I$. Iterating its trace
bound on each surviving positive input, including a reference, proves

$$
\Pr(+^r\mid\rho)\ge(1-\delta)^r\ge1-r\delta.
\tag{TS4}
$$

Different steps admit the corresponding product of $1-\delta_j$.
For static $h=t/r$, failure probability is at most
$\min\{1,t^4\|[A,B]\|^2/(4r^3)\}$. A negative lower bound in (TS4)
is uninformative.

Ordinary random order is a known second-order simulation with global
diamond error $O(t^3/r^2)$ for bounded fixed Hamiltonians. The exact (FC1)
comparison orders the actual all-launch errors; comparison of separate
upper bounds is not required.

Both processes use at most $2r$ module calls. If the native process aborts
after its first minus, its input-dependent mean is
$2\sum_{j=0}^{r-1}s_j$, where $s_j$ is survival through $j$ steps, whereas
ordinary random order uses exactly $2r$. Thus (FC1) is not an exact
equal-mean-call-budget statement. If native all-launch half-diamond error
to an always-success target is at most $\epsilon<1$, every input has
failure probability at most $\epsilon$: the success difference block has
trace $-p_f$ and the reject block trace $p_f$, so their trace norms sum
to at least $2p_f$. Since $s_j\ge s_r\ge1-\epsilon$,

$$
\mathbb E[Q_N\mid\rho]\ge2r(1-\epsilon),\qquad
2r\le\frac{\mathbb E[Q_N\mid\rho]}{1-\epsilon}.
\tag{TS5}
$$

Early abort therefore provides no substantial asymptotic mean module-call
reduction at high required all-launch accuracy. This statement does not
price arbitrary decoder operations, conditional wall time or helper hardware.

For uninterrupted static repetitions, ordinary Strang splitting

$$
\bigl(U_A(h/2)U_B(h)U_A(h/2)\bigr)^r
$$

merges adjacent identical $A$ half evolutions and uses $2r+1$ calls,
rather than $3r$. This requires actual half-duration access, identical
static generators and no intervening operations obstructing the merge.
A fixed black-box $U_A(h)$ does not grant $U_A(h/2)$. The exact
random-order comparator (TS1) needs no such stronger port. Neither
comparison is a lower bound over all ordinary simulation algorithms.

## Ordinary literature and access models

[Childs, Ostrander and Su, *Faster quantum simulation by randomization*,
Quantum **3**, 182 (2019), arXiv:1805.08385v2](https://arxiv.org/html/1805.08385v2),
Section 2, Eqs. 9–20, Lemma 1 and Theorem 1, already give forward/reverse
amplitude averaging and the ordinary randomized-order channel, including
global diamond error $O(t^3/r^2)$. They discuss LCU implementation of the
nonunitary average and its ancilla cost, and credit Zhang's earlier
random forward/reverse output-state analysis. This is direct prior art
for the apparent order improvement. The elementary completion lemma here
is a scoped comparison, with no novelty or priority claim.

[Faehrmann et al., *Randomizing multi-product formulas for Hamiltonian
simulation*, arXiv:2101.07808v3](https://arxiv.org/html/2101.07808v3),
Sections 1–3 and Table 1, address expectation-value estimation with
controlled evolution, randomized sampling and extra circuit evaluations.
Their oracle includes controlled evolution for arbitrary real durations,
including negative time. This estimator, with its sampling overhead,
does not supply a deterministic unknown-data output channel. If a task
needs only observables, such ordinary multiproduct sampling belongs in
its comparator set. Coherent LCU and amplitude amplification can instead
support state simulation, with controlled-select ports, ancillas, inverses
and repeated calls charged.

## Architecture and verification scope

A physical candidate must identify a many-body unknown-data register that
can coherently traverse the same Hamiltonian modules in both orders, with
common evolution times, stable branch phases and preserved reference
entanglement. Ordinary availability of $e^{-ihA}$ and $e^{-ihB}$ alone
does not grant this routing/control interface. Charge routing or controlled
selection, helper preparation/readout/reset, module occupancy, storage,
calibration, communication and all rejected launches. Specify an
always-success state output, a legitimate heralded output, or an observable
estimation task before choosing a metric. An all-plus two-order state
simulator with a common decoder is covered by (TS1)/(FC1). A candidate using
minus branches, retained coherent control or an accepted-only service
requires its own endpoint instrument and ordinary comparator with the
same physical resources. No substantial native application is established
by the bare simulation step.

The standard-library exact helper checks noncommuting Gaussian-rational
unitary fixtures in dimensions $2,3$, static and varying steps, and
$r=1,2,3$. It checks every input matrix unit and output coefficient,
including an explicit identity reference, all plus/minus histories,
ordinary random order, its explicit CP complement and a nonunitary common
CPTP decoder. It checks abort effects and traces, expected-call ledgers,
nonzero cubic coefficients and witnesses that abort and full-history
reject payloads differ. Its quiet `verify()` API reports exact counts and
scope. These are finite algebraic guards. They do not numerically certify
a diamond norm, a physical routing port, an infinite-dimensional extension
or a uniform exponential remainder. The analytic arguments above supply
(FC1) and (TS3)–(TS5).
