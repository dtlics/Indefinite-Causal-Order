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

## Independent flagged loss: two finite service obstructions

The following extension changes the production promise explicitly; it does
not follow from a reported retrieval efficiency. Write $\lambda$ for survival
to distinguish it from the learning failure budget $\eta$ above. Assume
state-independent flagged erasure, fresh independent noise on every use, and

$$
\begin{aligned}
\mathcal E_{t,U}&=(1-t)\mathrm{Id}+t\Delta_U,\\
\mathcal N_{\lambda,t,U}(\rho)
 &=\lambda\mathcal E_{t,U}(\rho)
 \oplus(1-\lambda)\operatorname{Tr}(\rho)|e\rangle\langle e|,
 \qquad 0\le\lambda,t\le1.
\end{aligned}
\tag{L1}
$$

The surviving HIGH in (S1) has $t=1/2$. Loss is visible to the receiver,
and all attempts, including erasures, enter the service score. Two different
statements follow: a converse for every unassisted block code in a sufficient
loss region, and a sharper loss threshold for the particular five-use
encoding in (S14). Neither statement modifies the ideal promise in (S1)--(S16).

### A full-dimensional antidegrading map

Put $P_j=|u_j\rangle\langle u_j|$ and
$\rho_{jj}=\langle u_j|\rho|u_j\rangle$. The Kraus operators
$\sqrt{1-t}I,\sqrt t P_1,\ldots,\sqrt t P_D$ give the complement

$$
\mathcal E_{t,U}^c(\rho)=\sum_j\rho_{jj}|\phi_j\rangle\langle\phi_j|,
\qquad |\phi_j\rangle=\sqrt{1-t}|0\rangle+\sqrt t|j\rangle.
\tag{L2}
$$

All $D+1$ environment label vectors are orthogonal. In particular,
$\langle\phi_i|\phi_j\rangle=1-t$ for $i\ne j$, as required for the
system's off-diagonal multiplier. A complement of (L1) is isometrically
equivalent to

$$
\mathcal N^c_{\lambda,t,U}(\rho)
 =\lambda\mathcal E_{t,U}^c(\rho)\oplus(1-\lambda)\rho.
\tag{L3}
$$

For example, choose retained-branch Kraus operators
$\sqrt\lambda K_a$ and loss Kraus operators
$\sqrt{1-\lambda}|e\rangle\langle u_j|$. Their cross blocks vanish because
the output signal and erasure sectors are orthogonal, and the loss
environment block is the full input state, including its coherences.

If $\lambda<1$, process the loss-copy block by transmitting it with
probability $a=\lambda(1-t)/(1-\lambda)$ and erasing it otherwise. In the
other block, measure in the environment label basis, prepare $P_j$ on
outcome $j>0$, and output erasure on outcome $0$. This is CPTP whenever
$a\le1$. Its signal output is
$\lambda(1-t)\rho+\lambda t\Delta_U(\rho)$; the remaining trace is exactly
$1-\lambda$. Hence

$$
\boxed{\lambda\le\frac1{2-t}
 \ \Longrightarrow\ \mathcal N_{\lambda,t,U}\text{ is antidegradable}.}
\tag{L4}
$$

This sufficient region holds for every $D$ and $U$; no necessity claim is
made outside it. The endpoint $\lambda=0$ is immediate. At $t=1$, all
$\lambda\le1$ are covered; for $\lambda=t=1$ omit the absent loss block
instead of evaluating $0/0$. At $t=0$ the criterion is the ordinary erasure
threshold $\lambda\le1/2$. The antidegrading map may depend on $U$: its
existence is a converse, not experimental access to the hidden basis.

This is the standard dephasing-plus-erasure mechanism. On two pointer
states, the dephasing probability is $p=t/2$ and the erasure probability is
$q=1-\lambda$. The qubit boundary
$q\ge(1-2p)/[2(1-p)]$ and an antidegrading construction appear in
[Leditzky, Leung and Smith, PRL 121, 160501 (2018), Appendix C](https://arxiv.org/pdf/1806.08327).
Equations (L2)--(L4) give a direct full-$D$ sufficient construction here;
no new antidegradation mechanism or optimal boundary is claimed.

### Every unassisted finite block has a Bell-fidelity ceiling in (L4)

Antidegradability gives $Q(\mathcal N)=0$ for unassisted asymptotic
transmission. A separate extension argument gives the finite endpoint
needed here. Let a code consist of an arbitrary CPTP encoder, $L$ independent
uses $\mathcal N^{\otimes L}$, and a CPTP logical-qubit decoder. Every
input-bearing system must traverse those uses; there is no protected
bypass, preshared encoder--decoder entanglement, or backward assistance.
Classical training may select the code before the unknown input arrives.
A heralded decoder is completed to a TP map and its failures are counted.
The converse is pointwise in $U$ and in the fixed code: averaging over
classical training records, including records obtained by native offline
tests, preserves it. A receiver--sender entangled program or assistance
created by a feedback protocol is outside this block-code premise.

Take a Stinespring output $BE$ of $\mathcal N$ and apply its antidegrader
to $E$, obtaining $BB'$. Both reduced channels equal $\mathcal N$;
averaging this extension with its swapped version makes it symmetric.
Tensor the extension $L$ times, apply the single encoder first, and apply
the same decoder separately to the two output banks. The normalized
reference--output state $\omega_{RBB'}$ has both logical marginals equal
to the code's Choi state. With qubit Bell projectors
$P=\Phi_{RB}\otimes I_{B'}$ and $Q=\Phi_{RB'}\otimes I_B$,

$$
2F_e=\operatorname{Tr}[(P+Q)\omega]
 \le\|P+Q\|_\infty=\frac32,
\qquad \boxed{F_e\le\frac34.}
\tag{L5}
$$

The general logical-dimension norm proof is owned by
[the supplied-code component, (DC3)](memory-code-verification.md#finite-block-logical-fidelity-has-a-low-channel-ceiling);
its $K=2$ case gives (L5). The exact eight-dimensional guard independently
reconstructs the two Bell projectors, their overlap, spectral polynomial
and a maximizing eigenvector. Here the new application is the
loss-specific extension (L2)--(L4).
The antidegradability/extendibility equivalence is standard
([Myhr and Lütkenhaus, Lemma 5](https://arxiv.org/html/0812.3667)); the
Bell-sharing bound is a case of the singlet-monogamy/cloning bounds of
[Kay, Kaszlikowski and Ramanathan, PRL 103, 050501 (2009)](https://arxiv.org/abs/0901.3626).

At $t=1/2$, $\lambda\le2/3$ therefore excludes the all-attempt $7/8$
logical-qubit endpoint for every such unassisted block code, at every
finite block length. This is stronger than merely $Q=0$. It does not
exclude success-conditional heralded branches, assisted entanglement
generation with retries, protected input-bearing storage, or a deployment
that calls a native higher-order instrument online. Those are different
resources or channels. No conclusion about them follows from (L5).

### Exact erasure sensitivity of the five-use encoding

Now fix the exactly calibrated five-carrier encoding
$|0_L\rangle=|+\rangle^{\otimes5}$,
$|1_L\rangle=|-\rangle^{\otimes5}$ on two true pointer states.
The noise in (L1) with $t=1/2$ is independent $Z$ error of probability
$1/4$ followed by independent erasure. If any carrier is erased,
tracing it kills the encoded off-diagonal matrix unit in every phase-error
branch: the two erased $X$-basis labels are orthogonal. The complete
reference--output channel on such a branch is therefore entanglement
breaking. In particular, even an ideal decoder cannot exceed $1/2$
Bell fidelity on that branch.

With no erasure, phase-error strings $s$ and their complements share a
repetition syndrome and differ by a logical Pauli. The optimum decoder
chooses the more probable member, hence errors of weight at most two,
giving $f_5=459/512$. This is optimal for this fixed encoding over all
CPTP decoders, not merely the chosen majority decoder: distinct syndrome
blocks are orthogonal, and in a block with unnormalized logical Pauli
weights $a,b$, any recovery with Kraus operators $R_k$ has
$F_e=\tfrac14\sum_k(a|\operatorname{Tr}R_k|^2+
b|\operatorname{Tr}R_kX|^2)\le\max(a,b)$.
The inequality follows by adding the other two Pauli terms and using
$\sum_k R_k^\dagger R_k=I$; applying the more likely inverse attains it.

If $r<5$ carriers survive, their commuting $X$-basis records are $r$
independent binary symmetric samples of the logical bit. Optimal classical
guessing, followed by logical-state preparation, is also the optimal
quantum decoder: for each classical record $x$, its contribution to
$F_e$ is at most $\tfrac14\max\{p(x|0),p(x|1)\}$. Thus the optimum
branch fidelities, including $r=0$, and the exact total are

$$
\begin{aligned}
(f_0,f_1,f_2,f_3,f_4,f_5)
 &=\left(\frac14,\frac38,\frac38,\frac{27}{64},
          \frac{27}{64},\frac{459}{512}\right),\\
F_{\rm five}(\lambda)
 &=\sum_{r=0}^5\binom5r\lambda^r(1-\lambda)^{5-r}f_r\\
 &=\frac14+\frac58\lambda-\frac54\lambda^2
   +\frac{55}{32}\lambda^3-\frac{85}{64}\lambda^4
   +\frac{451}{512}\lambda^5.
\end{aligned}
\tag{L6}
$$

Because all erasure-branch $f_r\le1/2$, a simpler necessary condition is

$$
F_{\rm five}(\lambda)\le\frac12+\frac{203}{512}\lambda^5,
\qquad F_{\rm five}\ge\frac78
 \ \Longrightarrow\ \lambda^5\ge\frac{192}{203}.
\tag{L7}
$$

The latter threshold is $\lambda\ge0.9889197221\ldots$. The exact
curve (L6) is strictly increasing on $(0,1)$, since its Bernstein
coefficients are nondecreasing and some adjacent differences are positive.
It reaches $7/8$ only at $\lambda=0.9907781304\ldots$; exact rational
evaluations bracket this root between $0.99077813$ and $0.99077814$.
These numbers assume perfect calibration and controls for this specified
encoding. Other encodings above the region in (L4) are not ruled out.
Small learned-code perturbations may be bounded by the earlier
diamond-distance ledger, but (L6) is not an identity for arbitrary
perturbed encoders or noise models.

### What a physical QA pool must pass first

[Meng et al., *Efficient integrated quantum memory for light*](https://arxiv.org/html/2511.05928v1)
report $69.8(1.6)\%$ efficiency for heralded single photons at $2\,\mu$s,
and $51.3(2)\%$ average efficiency over twenty temporal modes at
$10\,\mu$s. These are distinct operating points, not a channel
certificate for (L1). A mode average establishes neither uniform
state-independent survival on arbitrary superpositions nor a worst-mode
upper bound, and the experiment does not impose the surviving
$\mathcal E_{1/2,U}$ law. As illustrative substitutions in (L6), uniform
$\lambda=.513$ gives $F_{\rm five}\simeq.4130$ and uniform
$\lambda=.698$ gives $.4924$. The reported efficiencies do not meet
this particular code's near-unit survival criterion; they do not prove
zero capacity or a universal code obstruction for that actual platform.

Ordinary launch/flag counting can screen loss failures before a hidden-basis
test. Under a calibrated independent Bernoulli survival law, separating
candidates by additive margin $\Delta$ from a named survival threshold
uses $O(\Delta^{-2}\log(M/\delta))$ attempts per candidate for family-wise
error $\delta$. Every failed launch, preparation, flag readout, reset and
fixture visit counts. Bright pulses, multiple modes and parallel testers
can reduce windows only under a priced flux/hardware model and the
appropriate correlation law. Such a test certifies the survival statistic,
not the surviving production map.

Consequently the hard geometric inventory is the residual pool after
ordinary loss/noise/public-mode qualification. If observed loss already
reveals which devices are bad, a hard-prior lower bound on $M$ opaque
geometry candidates cannot be charged to those easily rejected devices.
A native geometry certificate also cannot supply the missing lossy code.
The next physical candidate must first furnish a production-law certificate
and an erasure-aware, all-attempt service at its actual efficiency, then
price screening, survivor calibration, failed attempts, storage deadline
and deployment against the strongest ordinary probes. The independent-loss
calculation supplies finite failure criteria; it does not establish a
finite native architecture advantage.

