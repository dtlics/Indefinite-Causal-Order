# Rare-good memory screening with a priced working code

This proof component of [NR-R20](../memory-qualification.md#nr-r20)
tests a conditional end-to-end use of capacity qualification: select one
rare usable device before paying to calibrate a code on it. It proves
an expected-query saving in the classical-address oracle model, including
an explicit finite decoder and its training. It does not establish a
native hardware advantage, a practical finite crossover or a lower bound
for a coherent indexed router.

The [bootstrap bound](memory-code-bootstrap.md) charges learning a working
code on the high promise. It does not exclude saving the work of rejecting
many low devices. Conversely, multiplying the one-device lower bound by
the number of devices would not prove the selection result below. The
[exact replay](../checks/architecture/verify_memory_stream_screening.py)
guards the finite probability, stopping, code and perturbation ledgers.
C6, the all-size selection reduction, continuous prior, concentration and
physical interface arguments remain analytic.

Channel-position finding is established prior work. [Zhuang and
Pirandola, Commun. Phys. **3**, 103 (2020)](https://arxiv.org/abs/2007.14554)
use entangled signals and conditional nulling receivers for multiple
bosonic hypotheses; [Pereira, Zhuang and Pirandola, PRR **2**, 043189
(2020)](https://arxiv.org/abs/2009.10094) study noise-environment
localization and ordinary quantum receivers. Those are strong comparison
ideas, not this particular C6/code-deployment promise. Here “ordinary”
already allows entangled probes and collective quantum processing.
The local-cap proof below supplies the multi-candidate lower bound;
a binary advantage alone would not. No new search or statistical
mechanism priority is claimed.

## The labeled service and its physical access cut

There are $M$ independent candidates, each with persistent hidden basis
and fresh inaccessible slot environments. With $D=2^n$ and the known
flat Hadamard $H$, candidate $i$ supplies opaque ports $A_i,B_i$:

$$
\begin{array}{c|c|c}
 & (A_i,B_i)&\mathcal E_i=(\operatorname{id}+B_iA_i)/2\\ \hline
\mathrm{HIGH}&(\Delta_{U_i},\Delta_{U_i})
 &(\operatorname{id}+\Delta_{U_i})/2\\
\mathrm{LOW}&(\Delta_{U_i},\Delta_{U_iH})
 &(\operatorname{id}+\Omega_D)/2 .
\end{array}
\tag{S1}
$$

The $U_i$ are independent Haar draws. Let $P_0$ mean all LOW and $P_j$
mean only $j$ HIGH. The hard selection prior chooses $J$ uniformly and
then $P_J$. The required service returns NONE on all LOW with bounded
error, or a candidate
index and an explicit code for a fresh logical qubit. All-attempt code
entanglement fidelity, including failed payloads, must be at least $7/8$.
Its success probability on the unique-HIGH prior is at least $s$, for
example $2/3$. Identification of a device address is part of this
endpoint; a service coding jointly through an unlabeled bank is different.

The ordinary model permits arbitrary quantum probes and retained memory
across candidates, adaptive known instruments and collective readout.
Every candidate/port address is chosen classically. A concrete special
case is an online QA fixture: only the current package is connected;
advancing removes it and future packages are not yet queryable.
Retained quantum memory is still allowed. A real stream restriction can
justify that cut; merely choosing to use an available coherent router
classically cannot justify it.

A coherent indexed dilation is a stronger interface. Its cross-address
phases, vacuum sectors and environmental overlaps are not specified by the
individual CPTP maps. Counting visits to one address can dephase that
interface, invalidating the reduction. A sufficient alternative is a
proved full which-address record at every query, which makes measuring
the address before a query lossless. Neither that record nor its absence
follows from spatial separation alone. No general coherent-index search
composition theorem is asserted here.

## An optimistic cap charges LOW rejections

Put

$$
q=\lfloor D^{1/16}/100\rfloor\ge1,\qquad d=215/10000.
\tag{S2}
$$

C6 bounds the HIGH/LOW output-probability gap of every ordinary hard-$q$
primitive strategy by $d$, including arbitrary retained quantum memory.
For one candidate, let $\beta$ be HIGH acceptance, $\alpha$ LOW acceptance
and $c_0$ LOW mean primitive calls. Cap the calls at $q$, outputting
ACCEPT when a $(q+1)$st target call is attempted. Capped HIGH acceptance
increases; capped LOW acceptance increases by at most
$\Pr_0(N>q)\le c_0/q$. Thus

$$
\boxed{c_0\ge q(\beta-\alpha-d).}
\tag{S3}
$$

For potentially unbounded known computation, additionally cap the overall
known-step count and output REJECT there. Every original successful
accept event occurs at a finite step, so its retained probability
increases to $\beta$ as that cap grows. Capped LOW acceptance remains
at most $\alpha+\Pr_0(N>q)$. Apply C6 to each finite circuit and take
the limit. No termination property of the emulated low case is inferred
from high-case equality. An operational service must still charge runtime
and specify halting; finite query mean by itself does not do that.

The default-accept cap is important: expensive high branches alone cannot
hide arbitrarily cheap reliable rejection of low devices.

## Selection has a direct-sum bound with quantum memory

First take a finite bank algorithm and write

$$
\beta_j=\Pr_{P_j}(\mathrm{out}=j),\quad
\alpha_j=\Pr_{P_0}(\mathrm{out}=j),\quad
T_0=\sum_j\mathbb E_{P_0}N_j .
$$

For fixed $j$, treat candidate $j$ as the unknown C6 pair. All other
independent parameters can be fixed and their CPTP maps hardwired as
known processing, then averaged. These simulations need not be efficient
for a query lower bound. They preserve entanglement and adaptive quantum
memory and provide no advice correlated with the target's parameter.

Cap queries to $j$ at $q$, accepting on that local cap and otherwise
accepting exactly on output $j$. Classical addresses make the cap
observable without changing earlier queries. Its HIGH acceptance is at
least $\beta_j$; LOW acceptance is at most
$\alpha_j+\Pr_0(N_j>q)$. Therefore

$$
\beta_j\le\alpha_j+d+\Pr_0(N_j>q).
\tag{S4}
$$

Since one execution returns at most one index, $\sum_j\alpha_j\le1$.
Markov and averaging give

$$
\boxed{s:=\frac1M\sum_j\beta_j
 \le\frac1M+d+\frac{T_0}{Mq}.}
\tag{S5}
$$

If the all-LOW false-index probability is at most $\delta_0$, replace
$1/M$ by $\delta_0/M$. Testing candidates separately or keeping only
classical probe data was never assumed. Finite overall-step caps as
above justify the same limit for successful finite output events.

There is also a lower bound when only the unique-HIGH mean $c$ is
controlled; the original null mean may be infinite. Globally truncate
before primitive call $Q+1$, outputting NONE. Markov under the unique-HIGH
mixture loses at most $c/Q$ success, while the new null mean is at most
$Q$. For every positive integer $Q$, (S5) implies, with
$a=s-d-1/M>0$,

$$
c\ge Q\left(a-\frac Q{Mq}\right).
$$

Choosing $Q=\lfloor aMq/2\rfloor\ge1$ yields

$$
\boxed{c\ge\frac{a^2Mq}{4}-\frac1{Mq}
       =\Omega(MD^{1/16}) .}
\tag{S6}
$$

The integer error follows by completing the square and bounding the
distance from its maximum by one. Known-step caps handle zero-query
loops; finite query mean is not being substituted for finite circuit
size. Nontermination counts as failure of the labeled service.

For atomic production calls, the ordinary simulator uses a fresh
Bernoulli$(t)$ coin and invokes $A$ then $B$ only on its active branch.
Predictability gives
$\mathbb E N_{\rm primitive}=2t\,\mathbb E N_E$.
At $t=1/2$ these means coincide. Mixed direct/production access uses the
full ledger $\mathbb E(N_A+N_B+2tN_E)$, summed across candidates. The
decision reduction may abort midway through a simulated pair; it need
not itself be a valid storage service.

## Native early rejection includes every unsuccessful device

For the stipulated $\operatorname{SWITCH}(A_i,B_i)$ diagnostic on
$I/D$ and an independent plus control, HIGH always gives plus and LOW
has $\eta=1/D$. Its minus probability is at least $1/4$ for $D\ge2$.
This is the C6 interference experiment; the physical implementation of
its complete coherent-order process is an additional premise.

Scan candidates in a fixed order. Reject each at its FIRST minus;
certify it after $r$ consecutive plus outcomes, where

$$
r=\left\lceil\frac{\log(M/\delta)}{\log(4/3)}\right\rceil .
$$

Any LOW certifies with probability at most $(3/4)^r$, so the probability
of any false certification is at most $\delta$. HIGH passes every trial.
A tested LOW consumes at most four trials in expectation, including its
rejecting trial. A certified HIGH consumes $r$ trials. Each trial uses
two primitive module visits. Thus

$$
\boxed{\mathbb E N_{\rm screen}\le8M+2r,\qquad
       N_{\rm screen}\le2Mr\ \text{on every execution}.}
\tag{S7}
$$

The expectation is $O(M+\log M)$, not $M\log M$: early rejections
matter. All losses, resets, routing, preparation and readout require their
own launch/time/energy ledger. Omitting lost launches from the probability
model would not preserve (S7). If the first certified device fails
subsequent validation, the service may return failure; its false
certification probability has already been budgeted.

### A scoped robustness extension uses sequential likelihoods

This extension retains the production-channel promise (S1) and relaxes
only the diagnostic outcome process. Flag separation alone would not
establish the pointer-learning or code-fidelity premises below.
Ideal deterministic HIGH outcomes are not essential if a calibrated
process supplies constants $0<h<\ell<1$ such that, at every trial
conditional on previous records,

$$
\Pr(\text{minus}\mid\mathrm{HIGH},\text{history})\le h,\qquad
\Pr(\text{minus}\mid\mathrm{LOW},\text{history})\ge\ell .
\tag{S8}
$$

These are uniform process promises, not conclusions from marginal
one-use fits. Calibration cost, confidence, drift and reuse intervals
must be charged. Per-slot target/controller noise that closes this gap
is still the obstruction in the [native-cost screen](memory-native-cost.md).

For $Z=1$ on minus, accumulate

$$
S_n=\sum_{k\le n}\left[
 Z_k\log(h/\ell)+(1-Z_k)\log((1-h)/(1-\ell))\right].
$$

Stop at $S_n\ge B=\log(M/\delta)$ and certify, or
$S_n\le-A=-\log(1/\rho)$ and reject. Under LOW, $e^{S_n}$ is a
nonnegative supermartingale: its conditional multiplier is at most one
for every minus probability $\ge\ell$. Under HIGH, $e^{-S_n}$ is a
supermartingale for probabilities $\le h$. The first-crossing
supermartingale bound gives false certification at most $\delta/M$ and
HIGH false rejection at most $\rho$.

Let $c_{\rm inc}$ be the larger absolute log increment. The conditional
score drift is at most $-D_{\rm KL}(\ell\|h)$ under LOW and at least
$D_{\rm KL}(h\|\ell)$ under HIGH. On $\tau\wedge n$ the score remains
between $-A-c_{\rm inc}$ and $B+c_{\rm inc}$. Conditional expectation
and monotone convergence therefore prove, without assuming a finite
stopping mean in advance,

$$
\mathbb E_{\rm LOW}\tau\le
 \frac{A+c_{\rm inc}}{D_{\rm KL}(\ell\|h)},\qquad
\mathbb E_{\rm HIGH}\tau\le
 \frac{B+c_{\rm inc}}{D_{\rm KL}(h\|\ell)} .
\tag{S9}
$$

Thus constant separated intervals retain expected $O(M+\log M)$
trials with an extra constant HIGH rejection budget. This is a standard
[sequential likelihood-ratio method](https://doi.org/10.1214/aoms/1177731118),
not a new statistical mechanism. A hard time cap may be added, charging
its resulting failure probability; (S9) alone is an expected-time bound.
The exact replay guards finite rational likelihood multipliers, stopping
probabilities and nontrivial composite-probability examples, not the
all-history analytic supermartingale proof.

## Calibrating one survivor is finite and explicitly charged

Under HIGH, prepare a known $|0\rangle$ and estimate

$$
\sigma=\mathcal E_1(|0\rangle\langle0|),\qquad
R=2\sigma-|0\rangle\langle0|
 =\Delta_U(|0\rangle\langle0|)
 =\sum_i w_i|u_i\rangle\langle u_i|.
\tag{S10}
$$

If direct $A$ access is supplied, estimating $A(|0\rangle\langle0|)$
gives the same $R$ with a better constant. No unknown inverse or
environment outcome is supplied. A fixed Haar $U$ makes
$w_i=X_i/\sum_jX_j$ with independent $\operatorname{Exp}(1)$ variables.
This follows by normalizing independent complex Gaussian coordinates of
a Haar vector, giving the uniform simplex distribution.
For ordered weights $w_{(1)}\ge\cdots\ge w_{(D)}$, let
$G_k=w_{(k)}-w_{(k+1)}$. Subtracting $\gamma$ from each of the top
$k$ coordinates maps the event $G_k\ge\gamma$ bijectively to the ordered
simplex of total mass $1-k\gamma$. Its $(D-1)$-dimensional volume
scales by $(1-k\gamma)^{D-1}$. Consequently, for $D\ge3$ and
$0\le\gamma\le1/2$,

$$
\Pr(G_1<\gamma\ \text{or}\ G_2<\gamma)
\le 2-(1-\gamma)^{D-1}-(1-2\gamma)^{D-1}
\le3(D-1)\gamma .
\tag{S11}
$$

The last inequality is the Bernoulli inequality. Set
$\gamma=\eta/(3D)$. The two leading eigenvalues are then separated
from each other and all remaining eigenvalues by at least $\gamma$,
except on probability $\eta$.

Tomograph the $D^2-1$ nonidentity Pauli expectations of $\sigma$.
An error at most $\zeta$ in every expectation gives
$\|\widehat R-R\|_{\rm op}\le2\sqrt D\,\zeta$ by Pauli
Hilbert--Schmidt orthogonality. Set
$\epsilon=\theta\gamma/4$ and $\zeta=\epsilon/(2\sqrt D)$.
For an explicit finite recipe, measure each nonidentity Pauli on
$m=\lceil2\zeta^{-2}\log(2(D^2-1)/\eta)\rceil$ fresh outputs.
The $\{\pm1\}$ Hoeffding bound and a union bound then fail with
probability at most $\eta$. Thus $N_{\rm learn}=(D^2-1)m$ gives

$$
N_{\rm learn}
 =O\!\left(D^3\epsilon^{-2}\log(D/\eta)\right)
 =O\!\left(D^5\theta^{-2}\eta^{-2}\log(D/\eta)\right)
\tag{S12}
$$

production calls. Use another $\eta$ failure budget for tomography.
The reconstruction may be Hermitian without being positive; its
Hermitian eigenvectors still suffice.

For an explicit perturbation bound, the eigenvalue variational principle
gives eigenvalue errors at most $\epsilon$. Projecting an approximate
eigenvector's residual equation onto all other exact eigenspaces then
bounds its squared outside component by
$\epsilon^2/(\gamma-\epsilon)^2$. After choosing the irrelevant phases,
the two learned orthonormal eigenvectors define an isometry $\widetilde V$
with

$$
\|\widetilde V-V\|_{\rm op}
 \le\frac{2\epsilon}{\gamma-\epsilon}\le\theta,
\tag{S13}
$$

where $V$ encodes into two exact pointer states. No full hidden unitary
description is assumed before this measurement and computation.

The main guarantee is under the unique-HIGH Haar prior. Conditioning on
a noisy native acceptance need not preserve that prior; the failure
budget is the unconditional probability of the bad-gap event for the
one actual HIGH, intersected with selection, which is no larger than
$\eta$. A conditional uniform guarantee on every selected basis is not
being inferred. If needed, a fresh known Haar pilot after selection
makes the same weights law hold for every fixed $U$, but preparing its
copies costs known state-synthesis work and precision; it is not free.

Known $|0\rangle$ preparation and Pauli measurements take
$O(\log D)$ gates per shot. Dense Pauli reconstruction can be charged
$O(D^4)$ arithmetic and one Hermitian eigendecomposition
$O(D^3)$ arithmetic. The $O(D^5)$ observations and their accumulation,
finite precision, classical storage and synthesis of the known two-column
encoder are all charged. Use fixed finite precision/step budgets and
check the returned matrix residuals and orthogonality; return failure
if the budget is exhausted. On the separated-gap event polynomial
precision suffices for the stated vector accuracy. A rare bad-gap input
does not receive unpriced infinite matrix computation.
Conservative fixed-error known-gate/classical
work is polynomial in $D$, with $O(D^5\operatorname{polylog}D)$ as the
main Haar-prior route. This is exponential in $n$ and is not a practical
learning recommendation. Synthesis and eigenvector precision must fit
the error margin below; no exact real arithmetic or exact noisy gate
implementation is a physical free resource.

## Five uses give an all-attempt logical service

On two exact pointer states, HIGH production is

$$
V^\dagger\mathcal E_1(V\rho V^\dagger)V
 =\frac34\rho+\frac14Z\rho Z.
$$

Use the five-qubit phase-repetition code across five independent
production uses, correcting at most two phase errors. For each pattern
$e\in\{0,1\}^5$, the syndrome
$(e_1\oplus e_0,\ldots,e_4\oplus e_0)$ is independent of the logical
input. Minimum-weight correction leaves identity for $|e|\le2$ and
logical $X$ otherwise, preserving all reference matrix units on the
correct branches. The exact all-attempt Bell fidelity is

$$
F_*=\sum_{w=0}^2\binom5w(1/4)^w(3/4)^{5-w}
 =\frac{459}{512}>\frac78 .
\tag{S14}
$$

This is ordinary repetition coding, not a new correction mechanism.
It costs five uses, known encoding entanglers, syndrome/correction gates,
two-pointer transforms, readout and reset.

Use $\widetilde V$ in place of $V$. The known decoder is
$\mathcal D_{\widetilde V}(X)=\widetilde V^\dagger X\widetilde V+
\operatorname{Tr}[(I-\widetilde V\widetilde V^\dagger)X]
|0\rangle\langle0|$. A Stinespring isometry sends $x$ to
$(\widetilde V^\dagger x)\otimes|g\rangle+
|0\rangle\otimes[(I-\widetilde V\widetilde V^\dagger)x]$, with
the two environment sectors orthogonal.
On a true-code input, its good and leakage components each differ in
norm by at most $\theta$, so its difference from the ideal decoder
isometry is at most $\sqrt2\theta$. The ideal HIGH output stays in
the true code span; no full-$D$ basis-completion bound is needed.
Encoding adds at most
$\theta$. Thus one effective use has half-diamond error at most
$(1+\sqrt2)\theta\le3\theta$, or conservatively $4\theta$.
A five-use hybrid gives Bell-score loss at most $20\theta$.
At $\theta=1/4000$,

$$
F_{\min}=\frac{459}{512}-\frac1{200}>0.89>\frac78 .
\tag{S15}
$$

Known gate, preparation and measurement errors must also fit this positive
margin; the ideal known-instrument oracle model does not certify that
physical fault budget.

Freeze the learned classical encoder/decoder before validation. Fresh
Bell tests of this fixed code have a common pass probability $F$.
A threshold $(F_{\min}+7/8)/2$ and
$k\ge\log(2/\delta_v)/
 [2((F_{\min}-7/8)/2)^2]$ tests distinguish $F\ge F_{\min}$
from $F\le7/8$ with each error at most $\delta_v/2$ by Hoeffding.
This uses the positive service margin. For example, budgets
$\delta=\eta=\delta_v=1/100$ and, in (S8), $\rho=1/100$ give total
selection/learning/validation failure at most
$\delta+\rho+2\eta+\delta_v/2<1/3$; omit $\rho$ for the ideal test.
A test that merely distinguished
HIGH's $7/8$ from LOW's $3/4$ would not itself certify a $7/8$ endpoint
against intermediate-quality codes. All $5k$ validation uses and known
controls are included. At most one selected code is validated in this
upper bound; rejecting it may return failure, rather than performing an
unbudgeted adaptive search over code candidates.

This is a coded-transmission/block-use service. If the endpoint is
fixed-duration storage, five simultaneous suitable channels or another
explicit exposure schedule must be supplied. Pending inputs and output
buffers, their faults and the deadline require a physical ledger. A
protected buffer cannot become an unpriced storage bypass.

## Conditional saving and the remaining architecture test

At fixed confidence and error margins, the ideal native route has

$$
\begin{aligned}
\mathbb E N_{\rm native}
 &=O(M+\log M+D^5\log D),\\
N_{\rm ordinary}
 &=\Omega(MD^{1/16})
 \quad\text{in expected primitive calls}.
\end{aligned}
\tag{S16}
$$

The robust sequential version has the same order when its calibrated
probability intervals stay separated by constants. Calibration,
validation and learning failures consume explicit constant portions of
the overall success budget. Choosing, for example, $M=D^6$ amortizes
the conservative polynomial survivor learning. If native routing/readout,
mounting/feed and known-control work cost at most polylogarithmic multiples of one
ordinary module visit, the corresponding operational saving is at least
$D^{1/16}/\operatorname{polylog}D$. It is a conditional query/service
separation with a paid decoder, not a screening-only accounting trick.

The regime is extreme: $q\ge1$ already needs $D^{1/16}\ge100$, and
the inventory and generic hidden-basis calibration are enormous.
The result is not a convincing finite architecture benefit. Structured
noise, cheap pointer records or a supplied encoder may invalidate its
hard prior or ordinary comparator.

A QA stream adds common mounting/feed time $M\tau_{\rm mount}$.
Wall time also includes slot duration, native routing, reset, training
and validation. A bound on photon/module-call count is not a bound on
elapsed windows when an ordinary probe may contain many parallel
photons, modes or copies. The full multiphoton process, flux/energy,
sample correlations and fixture occupancy must be priced; the
single-payload CPTP maps do not specify that extension.
Slow mounting or a fixed slow production feed can erase
the wall-time saving. Quantum-tester occupancy/energy may be a different
useful objective, but must be named and measured. Parallel ordinary
testers use hardware which both competitors may buy and must charge.
If inventory fabrication/acquisition cost is part of the claimed total,
its common cost can dominate both operational budgets.

The next test is a real stream or link-selection workload with opaque
persistent orientation, sufficiently many bad candidates, useful timing,
and a complete native controlled-order instrument. Independent baths,
all cross-history timing records, protected controls, routing faults,
energy, calibration reuse and the stronger coherent-index ordinary
alternative must be resolved from that platform. The theorem by itself
does not supply any of those physical facts, and no native advantage
is established here.

