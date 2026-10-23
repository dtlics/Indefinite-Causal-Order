# Coherent dispatch with counter dephasing

[Application assessment](architecture.md) · [Ordinary baselines](architecture-baselines.md) · [Topic](README.md)

<a id="nr-r12"></a>

## NR-R12 — Exact binary dispatch, with unresolved native-device costs

This result specializes an established self-switch correction mechanism to
a two-instruction quantum dispatcher. It gives an exact universal query
comparison for a full coherent quantum output. It does **not** establish a
hardware application, a latency advantage, or a quantitative approximation
or expected-cost lower bound. The correction mechanism and the underlying
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
the ordinary circuit. No such device/noise construction is established
by the channel equations alone.

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

Higher-dimensional cyclic counters and cyclic instruction orders are a
possible next question. Their resource-optimality, prior overlap and
native implementation have not been established here and are not part
of NR-R12. A usable architecture still needs a named physical dispatcher,
a validated coherent-use/noise model and a measured advantage over the
ordinary memory, parallel, compilation and reuse alternatives above.
