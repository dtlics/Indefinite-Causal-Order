# Clean conjunction phases from two lookup modules

[Architecture assessment](architecture.md) · [Ordinary baselines](architecture-baselines.md) · [References](references.md) · [Checks](checks/README.md)

<a id="nr-r13"></a>

## NR-R13 — Measurement-based cleanup changes the two-lookup comparison

Two persistent Boolean lookup modules admit an exact ordinary clean
AND-phase implementation with success $1/2$ using two calls, or deterministic
output with expected cost $5/2$. Allowing immediate rejection gives success
$4/5$ at mean cost two. By contrast, the particular balanced switch below,
followed only by fixed junk-register cleanup, has clean success at most
$1/3$ when all three junk types must remain coherent. These are scoped
constructions and an erasure bound, not an optimal ordinary frontier or a
claim that all switch protocols lose.

### Task and native interface

Let $f,g:\{0,\ldots,N-1\}\to\{0,1\}$ be fixed throughout an invocation.
The separate supplied modules preserve the address $x$ and act on a common
answer qubit $B$:

$$
V_X=\sum_x|x\rangle\langle x|\otimes X^{f(x)},\qquad
V_Z=\sum_x|x\rangle\langle x|\otimes Z^{g(x)}.
$$

An ordinary XOR-read oracle for $g$ supplies $V_Z$ by a known Hadamard on
$B$ before and after its call. The requested physical output is the clean
phase oracle

$$
P_h|x\rangle=(-1)^{h(x)}|x\rangle,\qquad h(x)=f(x)g(x).
$$

Clean means the successful address subchannel is exactly
$p\operatorname{Ad}_{P_h}$, including its action on arbitrary entangled
references; no address-dependent dataset record remains in discarded work.
Returning an entangled answer bit or learning a classical AND at a known
address is a different task. All module calls, rejected attempts and
correction calls count. The query comparison treats known preparations,
measurements and feedforward as available; their physical costs remain to
be specified for an architecture claim.

### Ordinary two-call herald and adaptive correction

Prepare $B$ in $|0\rangle$ and apply $V_X$ followed by $V_Z$. On a pure
address-reference input, writing reference-valued amplitudes $|r_x\rangle$,
the state becomes

$$
\sum_x|x\rangle|r_x\rangle|0\rangle
\longmapsto
\sum_x(-1)^{h(x)}|x\rangle|r_x\rangle|f(x)\rangle.
$$

Measure $B$ in the $X$ basis, with outcome $s=0$ for $|+\rangle$ and
$s=1$ for $|-\rangle$. Let $P_f|x\rangle=(-1)^{f(x)}|x\rangle$.
The address Kraus operators are

$$
K_s=\frac1{\sqrt2}P_hP_f^s,\qquad K_s^\dagger K_s=I/2.
$$

Both outcomes therefore have probability $1/2$, independent of every
address/reference input. Accepting only $s=0$ gives the exact clean target
with two calls and success $1/2$. For $s=1$, prepare a fresh answer in
$|-\rangle$ and call $V_X$ once. Phase kickback implements $P_f$, so
$P_fK_1=P_h/\sqrt2$. After this correction both outcomes give the same
target; the retained measurement flag is independent fair randomness.
The algorithm is deterministic, uses at most three calls, and has

$$
p=1,\qquad c=\mathbb E N_{\rm calls}=2+\frac12=\frac52.
$$

More generally, correcting outcome one with probability $r\in[0,1]$ and
rejecting otherwise gives $p=(1+r)/2$ and $c=2+r/2$. At a mean-query budget
two, run the complete deterministic adaptive algorithm with probability
$4/5$ and reject before querying otherwise. Its accepted channel and cost
are exactly

$$
\mathcal S_{\rm acc}=\frac45\operatorname{Ad}_{P_h},\qquad
p=\frac45,\qquad c=\frac45\frac52=2.
$$

This procedure has a three-call branch; it is not a hard two-call protocol.
Immediate rejection has zero lookup calls but may still incur native reset,
delivery or latency costs. No claim is made that $1/2$, $5/2$ or $4/5$ is
optimal among all ordinary protocols under the corresponding criterion.

The cleanup mechanism is established measurement-based uncomputation.
[Luongo, Miti, Narasimhachar and Sireesh, Lemma 4.1](https://arxiv.org/html/2407.20167#S4)
give the single-garbage-bit construction using the original self-adjoint
XOR oracle only on the probability-$1/2$ correction outcome. Its arbitrary
input amplitudes can already include the phase $P_h$ above. The formulas
here apply that mechanism to the two-module clean-lookup task; they do not
claim a new uncomputation technique or free correction of an opaque bit.

### Bare balanced switch and fixed junk-only erasure

Prepare answer $|0\rangle_B$ and control $|+\rangle_C$, and apply

$$
|0\rangle\langle0|_C\otimes V_ZV_X+
|1\rangle\langle1|_C\otimes V_XV_Z.
$$

The resulting address-dependent answer/control junk is

| Truth type | Actual junk | Junk after factoring out the desired $(-1)^h$ |
| --- | --- | --- |
| $f=0$ (either $g$) | $a=|0,+\rangle$ | $a$ |
| $f=1,g=0$ | $b=|1,+\rangle$ | $b$ |
| $f=1,g=1$ | $-c=-|1,-\rangle$ | $c$ |

The vectors $a,b,c$ are orthonormal. Merely observing the order phase thus
does not produce the clean address oracle: the junk still distinguishes
these address classes.

Consider a fixed accepted CP operation on this junk only, with effective
effect $0\preceq E\preceq I$; extra initially fixed work and multiple
accepted outcomes are included by summing their effects. No subsequent
oracle call or address operation is allowed. Suppose an instance contains
all three types and this cleanup produces $p\operatorname{Ad}_{P_h}$ on
the address. On every address matrix unit, preservation of its coherence
requires

$$
\langle j_k|E|j_i\rangle=p\quad
(j_i,j_k\in\{a,b,c\}).
$$

Hence the compression of $E$ to their span is $pJ_3$, with $J_3$ the
all-ones matrix. On $(a+b+c)/\sqrt3$ its expectation is $3p$. Since
$E\preceq I$,

$$
p\le\frac13.
$$

This argument already includes an unobserved accepted environment and
arbitrarily many accepted Kraus outcomes; discarding them cannot repair
lost address coherence. Equivalently, a purified successful contraction
must map $a,b,c$ to one common vector of squared norm $p$.
Projection onto $(a+b+c)/\sqrt3$ attains $p=1/3$ within this restricted
erasure model and leaves input-independent junk.

For a single instance with only $k$ populated junk types, the same proof
only gives $p\le1/k$; there is no pointwise $1/3$ assertion for every table.
A fixed table-independent junk cleaner required to work on *all* tables
also obeys the $1/3$ bound for $N\ge2$: place any two types at two
addresses. Clean coherence forces their two diagonal and off-diagonal
effect entries to coincide. Considering all three type pairs forces
the common compression $pJ_3$. The $N=1$ case is excluded from that
universal claim because the requested phase is only a global phase.

The bound concerns this exact balanced preparation and junk-only cleanup.
It does not cover different switch preprocessing, address-dependent
corrections, other answer spaces, additional calls, adaptive address
operations or general two-slot supermaps. Outcome-dependent global phases
do not affect the proof; address-dependent phase corrections broaden the
model. No general switch-versus-ordinary optimality conclusion follows.

### Native QRAM, maintained predicates and combined-bank access

If a data owner can read both persistent classical tables, it can form
$h=f\mathbin{\rm AND}g$ using $O(N)$ Boolean work once and store another
$N$ indexed bits. A point update needs constant Boolean work and an
additional stored-bit update when both source values at that address are
classically available. A native XOR read of the maintained $h$ table on
answer $|-\rangle$ then implements $P_h$ in one online lookup. Constructing,
writing, coherently addressing and maintaining that QRAM is not free;
those costs and the update/use horizon belong in the comparison.

Likewise, a native wider-word read returning both $f(x),g(x)$ is stronger
than two opaque binary boxes. With such a reversible word read, compute
the two-bit word, apply a known controlled-$Z$ to its bits, and uncompute
the word: two word reads give a clean phase. A coherent bank-index oracle
selecting which table to read is also an additional interface. Its word
width, bank dispatch, routing, update and ownership costs must be granted
to the ordinary method on equal terms; it cannot silently be counted as
one call to each separately supplied device.

[Abbott, Mhalla and Pocreau, Theorem 1](https://arxiv.org/html/2307.10285)
equate quantum-controlled-order and fixed-order supermaps on repeated
copies of the *same unitary channel*, preserving the full quantum output
channel. Clean quantum output alone does not evade that theorem. The two
separate modules here are a different interface; applying the theorem to
a combined oracle requires a matching reduction and query accounting.
No such converse for all two-box protocols is asserted here.

Separate owners, privacy restrictions, fast updates or expensive joint
storage may make an online composite predicate useful. They require an
explicit task and native cost model. They do not remove the ordinary
measurement/feedforward construction, and they do not establish that
coherently visiting the boxes in both orders is physically cheaper.

### Verification and remaining claim boundary

The [exact lookup replay](checks/architecture/verify_lookups.py) uses
standard-library Gaussian-rational arithmetic. It checks explicit oracle
products, both measurement branches and phase-kickback correction, full
address Choi matrices, the all-four-truth-pattern switch instance, the
junk-erasure projector and exact success/cost arithmetic. It does not
prove a general query lower bound or a native QRAM implementation.

The ordinary constructions and restricted erasure theorem above supply
baselines for an application search. A surviving positive result still
needs a different full clean-output protocol, a matched ordinary bound
including mean-budget rejection, and a workload whose preprocessing and
native lookup costs have been specified. No winner, deployment claim,
or optimal resource frontier is established here.
