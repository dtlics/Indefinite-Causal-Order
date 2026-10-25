# Repeatable commutator diagnostics: physical ports and decision costs

<a id="nr-r06-commutator-apparatus"></a>

This is a proof component of [NR-R06](../architecture-baselines.md#nr-r06-pauli-physical-ports),
which remains the sole result owner. The known unitary three-call
construction, its restricted passive-loss extension, measured clocks and
a concrete model-reuse task are kept together so that a scalar signal is
compared with the strongest available ordinary service. No practical
architecture advantage is established.

<a id="nr-r06-commutator-ports"></a>

## Known compiler and actual optical ports

**Stable-unitary compiler (under 180 words).**
[Bavaresco et al., Nature Communications 16, 10216 (2025)](https://doi.org/10.1038/s41467-025-64996-6),
[arXiv:2409.18202v2](https://arxiv.org/html/2409.18202v2), Section II,
"Go theorem", Eqs. (4)--(5), explicitly give the fixed chronological word
ABA. For unitary inputs the auxiliary transformation factors identically
from control and target for **any auxiliary input state**; discarding it
therefore reproduces the full SWITCH. The source attributes this circuit
to the original SWITCH paper. Theorem 1, Eq. (7), extends the construction
to a repeated bipartite unitary A and a general bipartite B. The same
discussion and Appendix B distinguish access to a dilation from an
inaccessible discarded environment: the circuit is not a simulator for
arbitrary noisy channels. This is a known construction, not a new result.

**Actual native optical ports (under 180 words).**
[Stromberg et al., PRL 131, 060803 (2023)](https://doi.org/10.1103/PhysRevLett.131.060803),
[arXiv:2211.12540v2](https://arxiv.org/html/2211.12540v2), Fig. 3 and
Eqs. (1)--(15), use a heralded single photon, path control, polarization
target, a balanced directional coupler, two specially constructed
reciprocal SU(2) gadgets, a circulator and two output measurement stations.
Figure 1 and the paragraph preceding Eq. (2) explicitly distinguish an
ordinary backward gadget action P U^T P-dagger from U. The palindromic
gadget in Eq. (10) enforces the required equal forward/backward action;
its angles are calculated for a requested unitary. The experiment
process-tomographs both directions for 100 random settings. Polarization
dependent detection efficiencies and output differential loss are corrected.
Each of 52 gate pairs is measured for 60 seconds in each of six runs,
with downtime for rotating waveplates. Thus it demonstrates a stable
qubit router, not a measured fast-refresh unknown multimode gate service.

**Classical field readout port (under 100 words).**
[Popoff et al., PRL 104, 100601 (2010)](https://doi.org/10.1103/PhysRevLett.104.100601),
[arXiv:0910.5436](https://arxiv.org/abs/0910.5436), experimentally characterize
a random optical medium using spatial phase modulation and full-field
interferometric camera measurement. That supplies an actual classical
complex-field characterization port. It does not establish a particular
two-module, two-order scalar experiment or its refresh time.

<a id="nr-r06-passive-erasure"></a>

## Passive lossy maps: an exact coarse-erasure ordinary comparator

This is an analytic comparison, not a physical rate or advantage
certificate. A and B are stationary d-mode contractions in common
orthonormal, photon-flux-normalized retained mode bases, each implemented by a passive
number-preserving linear optical dilation with vacuum loss inputs. No
photon is added; vacuum produces vacuum, and a surviving single photon
leaves every loss environment in its unique vacuum. Vacuum-relative
phases, input/output mode bases and all routed clocks must be stationary
or separately calibrated. Each visit is a closed specified temporal/mode
service: discarded ports do not feed a later visit and no residual
internal excitation or memory couples visits outside the declared model.
Fresh vacuum loss ports or a supplied compositional dilation suffice.
Arbitrary noisy quantum channels are outside this amplitude-map model.

### All-launched instrument and a precise decision

Put X=BA, Y=AB and S=Pi_0 tensor X+Pi_1 tensor Y. This is the successful
one-photon control/target operator. For launched |+><+| tensor rho,
measuring the surviving order control in the X basis gives operators

$$
\begin{aligned}
 K_\pm&=(X\pm Y)/2,&
 p_\pm&=(s_X+s_Y\pm2c)/4,\\
 s_X&=\operatorname{Tr}(X\rho X^\dagger),&
 s_Y&=\operatorname{Tr}(Y\rho Y^\dagger),\\
 c&=\operatorname{Re}\operatorname{Tr}(X\rho Y^\dagger),&
 p_{\rm click}&=(s_X+s_Y)/2,\qquad
 p_{\rm erasure}=1-p_{\rm click}.
\end{aligned}\tag{P1}
$$

Thus score +1/-1/0 for plus/minus/erasure has mean c and variance
p_click-c^2 per launch. Normalizing successful counts instead estimates
c/p_click. In particular the nonnegative all-launch minus probability is

$$
 w=p_-=\frac14\operatorname{Tr}\!\left[(BA-AB)\rho(BA-AB)^\dagger\right].
 \tag{P2}
$$

It can trigger recalibration when the ensemble-weighted transmitted-field
mismatch exceeds a specified threshold; it is not a worst-input operator
norm certificate. Extinction also makes w small, so a production rule
must retain p_click (and any required individual-order throughput).
Mode-dependent loss alone does not fake P2 in the stationary matched-map
implementation. An uncalibrated path phase or unequal clock-dependent
maps does change it: for commuting X=Y and relative phase phi,
w_phi=s_X sin^2(phi/2). With additive order-map errors whose difference
has norm at most delta, |w_actual-w|<=delta sqrt(w)+delta^2/4.

For independent stationary rounds, thresholding the observed minus rate
between w<=theta-Delta and w>=theta+Delta has error at most delta_conf
with N>=log(2/delta_conf)/(2 Delta^2) launches (Hoeffding). Under the ideal
promise w=0 versus w>=epsilon, observing any minus has zero false positives
and miss probability <=(1-epsilon)^N. Detector backgrounds, phase and
drift uncertainties need their own calibration budget. The same finite
tests apply to the ordinary construction below, not only the SWITCH.

### A three-slot ordinary construction matches this whole service

Supply one d-mode buffer R initially in vacuum, a payload register Q,
and coherent conditional swaps C_0,C_1 of Q/R for control 0/1. A acts
only on Q in slots 0 and 2; B acts on Q in slot 1. Chronologically use

$$
 C_1\longrightarrow A_Q\longrightarrow C_1\longrightarrow B_Q
 \longrightarrow C_0\longrightarrow A_Q\longrightarrow C_0.
 \tag{P3}
$$

On control 0 the occupied payload visits A_0 then B_1 and is stored in R
through the final A slot. On control 1 it is stored in R through A_0 and
then visits B_1 and A_2. The final target is Q in both histories. The
extra A visit is vacuum in each history. If its vacuum amplitude is v_A,
both successful histories have the same overall factor v_A, |v_A|=1;
after this irrelevant common phase, the exact successful operator is S.
All buffer and loss outputs on success are vacuum. This is equality of
the successful control/target/reference CP map on every joint input, not
just an equality of P1 for a known rho. Four conditional swaps and all
their routing/buffer ports are supplied, priced premises.

Define the failed output to be a SINGLE erasure symbol: discard every
failed target and control output, while retaining an untouched reference.
If chi_(QD,R_ref) is any input with untouched reference R_ref, the
erased-reference block is

$$
 |{\rm er}\rangle\langle{\rm er}|\otimes
 \operatorname{Tr}_{QD}\!\left[(F\otimes I_{\rm ref})\chi_{QD R_{\rm ref}}\right],
 \qquad F=I_{QD}-S^\dagger S.
 \tag{P4}
$$

P4 is the unique complementary measurement effect after all failed
outputs are discarded; a square-root sandwich inside the partial trace
is an equivalent positive representation. Trace preservation plus the
common successful S therefore proves EXACT equality of the full
successful-control/target OR single-erasure/reference instrument. Apply
the same X-control measurement on success to obtain P1, including every
launch and no-click. If path control is encoded in the same lost photon,
this coarse erasure is a natural accessible endpoint; external surviving
control must be explicitly discarded to use P4.

No equality of lost environments or retained lost control follows.
Choose A=I and B=sqrt(eta)I, with independent Markov loss time modes.
In an actual two-slot native schedule B is in slot 0 or 1, so on loss its
external control is (1-eta)I_D/2. In P3 B is in the common middle slot,
so its lost control is (1-eta)|+><+|. Success is sqrt(eta)I with control
plus and coarse erasure mass is 1-eta in both. A retained control-X
measurement on no-click distinguishes them. Conversely, for an abstract
query SWITCH pairing the same absorber-A Kraus label across histories,
A=complete absorber,B=I preserves |+> on loss, while fresh first/last-A
compiler loss ports dephase it. That abstract example requires its
module-labelled dilation; an actual timed native bath can itself record
the A visit. These are explicit limits on P4, not arbitrary-channel
SWITCH simulators or assumptions that physical clock records are absent.

### What ordinary field records do and do not buy

Two separate ordinary order experiments with ideal common-LO heterodyne
readout give z_X=sqrt(E)X psi+xi and z_Y=sqrt(E)Y psi+nu, where E is the
mean launched sample photon number in EACH run and xi,nu are independent
CN(0,I_d) noise. The unbiased scalar H=Re(z_X^dagger z_Y)/E obeys exactly

$$
 \operatorname{Var}(H\mid\psi)=
 \frac{\|X\psi\|^2+\|Y\psi\|^2}{2E}+\frac{d}{2E^2}.
 \tag{P5}
$$

A shared random pure probe from a known ensemble with mean projector rho
makes E[H]=c, adding at most 1 to this variance. No full matrix is learned.
At E=sqrt(d), bounded variance costs 2sqrt(d) launched sample photons and
2d complex field records per paired round. At fixed E this estimator pays
d in variance. These are this specified detector model's costs, not a
lower bound against better ordinary strategies. Reference photons,
wavefront preparation, two quadratures, mode registration, detector or
serial-readout clock, dynamic range and relative phase calibration count.

Without a common relative field phase, even infinite separate order
density-channel records need not identify c. Let Z=diag(1,-1) and let F
be the Pauli bit flip.
The pairs (A,B)=(I,Z) and (F,ZF) have X=Z,Y=+/-Z respectively, so both
individual completed-order channels are rho->Z rho Z for every rho, but
c=+1/-1. This excludes neither additional individual-module process
learning nor coherent reuse; those are additional experiments/ports.
Independent unknown LO phases have the same sign ambiguity. Native path
phase is an analogous nuisance, not a free clock certificate.

If a paid coherent output-overlap port is admitted, total coherent probe
energy E split between the two orders and a balanced recombiner yield
Poisson count means E p_+, E p_-. Their difference/E has variance
p_click/E and no d-channel readout. A delayed d-mode field, parallel
modules or other physical routing supplies that port; it is not just
electronic multiplication of independent common-LO records. More strongly,
P3 already gives exactly the single-photon P1 distribution with a vacuum
buffer and no LO or d-mode field measurement. Thus no dimension advantage
survives the strongest ordinary coherent-buffer comparator from these
fixed passive maps alone. A finite measured advantage could only follow
from the paid routing, delay, loss, drift, calibration and launch rates.

Native has two nominal module slots; P3 has A,B,A and a d-mode coherent
vacuum buffer plus four conditional swaps. Both histories contain one
occupied passage through each module, so there is no automatic extra
module-absorption cost for P3. The extra routing and storage can still
lose photons or distort modes; all such losses remain erasures, never
renormalized away. Passive rounds may pipeline, so slot count alone is
not a launch-rate divisor. Neither matched ideal query statistics nor
P5 supplies those actual apparatus costs.

The [multimode-fiber primary source](https://pmc.ncbi.nlm.nih.gov/articles/PMC13539527/)
uses polarization-resolved interferometric field measurement and explicit
input/output basis registration; it gives round-trip matrices related by
transpose reciprocity. Those facts motivate a large-mode test, but do not
implement P3's coherent forward routing or certify a native matched-map
router. Five-second full-matrix acquisition is not a lower bound for P5.

<a id="nr-r06-commutator-clocks"></a>

## Clock drift and information per launched round

### Retiming changes the statistic in both implementations

For static U,V on dimension d the target is
`f=Re kappa`, `kappa=Tr(U^dagger V^dagger U V)/d`.
Let U_j,V_j denote actual full-amplitude unitaries at clock times t_j.
The native two-window histories are `K_0=V_1 U_0`, `K_1=U_1 V_0`, so

```
kappa_N=Tr(U_0^dagger V_1^dagger U_1 V_0)/d.
```

For the ordinary U_0,V_1,U_2 compiler, let R initially have arbitrary
normalized state sigma, independent of the input/control. Its branches are
`(V_1 U_0)_Q tensor U_2,R` and `(U_2 V_1)_Q tensor U_0,R`. On Q=I/d,

```
kappa_O = a b,
a=Tr(sigma U_2^dagger U_0),
b=Tr(U_0^dagger V_1^dagger U_2 V_1)/d.
```

This is a retained cross-history kernel, not a product of reduced-channel
tomographies. Static U makes a=1 and recovers kappa exactly. A dirty R
does not need fresh pure initialization: after a static round it factors
as U sigma U^dagger and remains a valid next-round dummy. I/d is unchanged.
During routing it can hold the unknown input coherently, so its actual
storage/error and controlled-SWAP costs remain.

Suppose full operator-norm drift satisfies `||U(t)-U(t*)||<=L_U |t-t*|`
and similarly for V. For two native windows separated by Delta and
reference t* at their midpoint, telescoping the four unitary factors gives
`|kappa_N-kappa(t*)|<=(L_U+L_V)Delta`.
For three equally spaced ordinary windows and reference t*=t_1, both
`|a-1|` and `|b-kappa(t_1)|` are at most `2 L_U Delta`, so
`|kappa_O-kappa(t_1)|<=4 L_U Delta`. Repeating V instead gives the
corresponding `4 L_V Delta` bound. These are sufficient drift budgets,
not tight relative lower bounds or a measured source clock. They show why
an unpriced claim that drift excludes ordinary reuse is inadequate:
the native fringe also requires a retiming certificate.

Full-amplitude qualification matters. If U_j and V_j differ only by
scalar phases from fixed U,V, the native kernel is multiplied by
`exp(i[(alpha_1-alpha_0)-(beta_1-beta_0)])`. Identical reduced unitary
channels do not constrain that factor. In the full-register ordinary
compiler, arbitrary scalar phases of U_0,U_2 cancel between a and b.
For an empty optical bypass R is instead vacuum, outside the d-dimensional
target sector; its vacuum-relative phase need not track the one-photon
global phase. Static cancellation works, but drift must be qualified in
that physical sector. This is not a free full-register phase reference.

### Compare measured information rates, not nominal slot counts

As a deliberately conditional model, suppose each launched round has an
observed erasure independent of f, with survival eta. On survivors the
phase-calibrated X sign has probabilities `(1+/-v f)/2`, with known
contrast v. Then its Fisher information about f per launch is

```
I_f = eta v^2/(1-v^2 f^2),   |v f|<1.
```

This is the regular interior model, not a regular Cramer--Rao claim at a
support-changing noiseless endpoint. At measured launch rate R, the
information rate is `R I_f`. Native and
ordinary share the ideal f, so this expression supplies a concrete
same-apparatus comparison after their eta,v,R and calibration uncertainty
are measured. A three-window latency does not automatically divide the
launch rate by 3/2: passive linear optical rounds may pipeline. A controller
that admits only one active round must instead include that occupancy.
Mode-dependent losses, f-dependent erasures, correlated drift, uncertain
contrast or an unknown fringe phase require their full instrument and
nuisance-parameter analysis, not this binary model or a fitted divisor.
Every launch, rejected event and calibration/pilot round counts.

In the stationary one-photon vacuum compiler, each occupied history visits
U and V once; the additional nominal U slot is empty on that branch.
Thus there is no automatic extra occupied module-absorption penalty.
Extra loops, mode-preserving delay, routing boundaries and time records
can still be decisive. Equality of selected survivors is not equality of
all erased bath/control outputs. Measure the actual accepted/rejected
instrument appropriate to the calibration endpoint.

<a id="nr-r06-multimode-model-reuse"></a>

## Multimode model reuse has a direct ordinary field-pilot test

The useful production decision is whether to reuse a stored first-order
dispersion model over a declared frequency band after a change in fiber
compression. The inspected source makes that task concrete, but does not
supply a unitary order-controlled instrument or a complete native rate.
Its normality metric alone is not a universal certificate for this decision.

### Primary facts and actual access

[Bharadwaj et al., APL Photonics 11, 096101 (2026)](https://doi.org/10.1063/5.0337399),
[open primary](https://pmc.ncbi.nlm.nih.gov/articles/PMC13539527/),
Sec. III, Eq. (20), define

$$\eta(T)=\frac{\sum_i|\lambda_i(T)|^2}{\|T\|_F^2}.$$

This is Schur diagonal-energy fraction, not a measured commutator norm.
Under static compression, the reported half-correlation bandwidth of a
first-order dispersion model decreases from about 2.60 THz to 0.11 THz
as $\eta$ decreases from 0.85 to 0.39. Sec. II and Appendices A–B use a
one-meter fiber supporting about 170 modes per polarization, scanned
focused spots, polarization-resolved off-axis holography and explicit
basis registration. The source reports about five seconds per full
matrix, 20-microsecond camera exposure and maximum 120-Hz frame rate.
A fixed reference spot is revisited after each input mode for phase
tracking. Symmetry corrections, phase-conjugate products and dispersion
models are computed from measured complex matrices. No complete
two-reflector order-router loss/phase/throughput ledger is given.

### Why the commutator interpretation needs a different port

Every unitary $T$ is normal and has $\eta(T)=1$. Thus replacing the
measured non-normal transmission block by an assumed complete unitary
changes the proposed diagnostic. Omitted modes, collection and losses
must be included before any quantum-channel interpretation. An all-input
unitary dilation's commutator is not automatically the normality of the
observed block.

Reciprocity gives a backward transpose, $T_{\rm bw}=T_{\rm fw}^T$,
in the appropriate matched physical bases. It does not give an executable
adjoint $T^\dagger$. Complex conjugating a measured classical field in
software does not supply an adjoint operation on an unknown quantum
payload. Likewise, the paper's computational basis-registration and
aberration corrections are not demonstrated coherent mode converters in
an order loop. The strongest ordinary comparison receives any such
physical converters once supplied.

For a nonzero square contraction $T$, a hypothetical executable pair
$A=T$, $B=T^\dagger$ and $\rho=I/d$ would give

$$
 w=\frac{\|TT^\dagger-T^\dagger T\|_F^2}{4d}.
$$

This vanishes exactly when $T$ is normal. To see the relation to the
source metric, write its unitary Schur form as $D+N$, with $D$ diagonal
and $N$ strictly upper triangular. Frobenius orthogonality gives
$\|T\|_F^2=\sum_i|\lambda_i|^2+\|N\|_F^2$, so $\eta=1$ exactly when
$N=0$, equivalently normality. This zero-test does not identify
the finite value of $\eta$ from $w$ or certify a bandwidth. The physical
adjoint port and power normalization remain unprovided by that source.


There is also an elementary target distinction. Take the passive
two-mode family

$$T(\delta)=\operatorname{diag}(e^{iK\delta^2},e^{-iK\delta^2}),
  \qquad T(0)=I.$$

All members are unitary, normal and mutually commuting. Its first
derivative at the reference frequency vanishes, so the first-order model
is $M(\delta)=I$. Yet at $K\delta^2=\pi/2$ its normalized complex-field
overlap with that model is $|\operatorname{Tr}T|/2=0$ and its average
squared field residual is two. Neither normality nor frequency-pair order
commutation alone gives a universal bandwidth certificate. This does not
contradict the source's empirical relationship within its controlled
fixed-dispersion compression study.

### A paid stored-model scalar criterion

Fix the output field coordinates, phase convention and calibrated
power norm. The pilot can retain the original rectangular spot-to-camera
coordinates: the actual field and stored prediction use the same output
representation, and no physical $W$ mode converter is required for this
direct residual. Let $M(\omega)$ be the actual stored prediction, obtained
through paid prior calibration; its acquisition, storage, fitting and
amortization are common production costs. Choose an input spot index
$j$ uniformly from a declared orthonormal calibrated input set of size
$D$. The existing spot scanner supplies individual columns, so this
pilot does not assume random coherent superposition preparation. Measure

$$y_j=T(\omega)e_j,\qquad p_j=M(\omega)e_j,\qquad
  r_j=y_j-p_j.$$

Then the ordinary scalar mean is exactly

$$R(\omega)=\mathbb E_j\|r_j\|^2
   =\frac{\|T(\omega)-M(\omega)\|_F^2}{D}.$$

For a known production distribution of input spots, sample that
distribution instead and obtain its weighted average residual. This
qualifies a declared global RMS task, not worst-case error on arbitrary
quantum inputs or unseen input subspaces. If the spot coordinates are
not orthonormal, their measured Gram/power metric must replace an
unjustified Euclidean norm. Output registration and its calibration
errors also remain part of the experiment.

Suppose a declared, independently qualified power bound gives
$0\le\|r_j\|^2\le B$ for all sampled columns. This is a premise to
measure or justify in calibrated units, not a bound inferred from the
paper's normalized plots. With independent column choices and noiseless
readout, $n\ge B^2\log(2/\alpha)/(2\epsilon^2)$ samples suffice for
$|\widehat R-R|\le\epsilon$ except with probability $\alpha$.
Prespecify a useful threshold $R_*$ and a guard band. Reuse the model
when the upper confidence endpoint is below $R_*$; recalibrate when the
lower endpoint exceeds it; unresolved data require more probes or a
conservative production choice. This is a direct decision criterion,
not a lower bound based on complete matrix tomography.

The residual is power-sensitive: retain raw calibrated output amplitudes
and losses. Renormalizing every surviving field would silently change
the endpoint. If production permits ignoring an overall phase, define
that different metric explicitly and estimate its phase on independent
data; fitting it freely on test data changes the decision statistic.

The confidence statement above is per frequency. For a declared finite
grid of $L$ test frequencies, allocate error probability $\alpha/L$ to
each point for a simultaneous grid decision. Certification between grid
points additionally requires an independently qualified spectral
regularity bound, with its interpolation error included in the guard
band. Without that premise, the verdict concerns tested frequencies
only; a good sampled grid is not a continuous-band guarantee.

### Optional noise-unbiased two-record readout

For a fixed $j$, take two phase-aligned records
$\widetilde y_s=y_j+\varepsilon_s$ and keep $p_j$ fixed. Assume the
two errors are independent, centered and proper circular complex,
with $\mathbb E\varepsilon_s\varepsilon_s^\dagger=\nu I_{D_o}$.
Define

$$Y_j=\operatorname{Re}\langle\widetilde y_1-p_j,
                                  \widetilde y_2-p_j\rangle.$$

Expansion gives

$$\mathbb EY_j=\|r_j\|^2,\qquad
  \operatorname{Var}(Y_j\mid j)=\nu\|r_j\|^2+D_o\nu^2/2.$$

Indeed, the two linear real terms each have variance
$\nu\|r_j\|^2/2$; the independent-error bilinear real term has variance
$D_o\nu^2/2$, and their cross covariances vanish. Gaussianity is not
needed for this identity. Across random columns, add
$\operatorname{Var}_j\|r_j\|^2$. Under the qualified bound above this
is at most $B^2/4+\nu B+D_o\nu^2/2$. A sample mean of independent
record pairs therefore has variance at most that quantity divided by
$n$. This noisy product need not be bounded; the preceding noiseless
Hoeffding formula cannot be applied to it. A finite-variance confidence
procedure or a separately justified bounded readout model is required.
For colored proper readout noise with known covariance $\Sigma$, the
conditional variance becomes $r_j^\dagger\Sigma r_j+
\operatorname{Tr}(\Sigma^2)/2$.

These are conditional measurement identities, not a noise model fitted
to this source. Reference drift, shared phase errors, correlated repeats
or prediction updates can violate their premises. Their calibration and
uncertainty must enter the actual confidence statement.

### Complete experiment and stopping criterion

Measure a stored model's held-out residual over the declared frequency
band and a compression sequence, with every pilot and reference repeat,
galvo/polarization settling, wavelength tuning, complex-field readout,
processing and input optical energy charged. The camera's maximum frame
rate and exposure alone do not determine complete pilot throughput.
Nor is five-second full-matrix acquisition a scalar-test lower bound.
Output detector-mode count and the stored matrix's classical cost remain
real, even though the pilot does not learn a fresh matrix.

An order-sensitive candidate must predict this same production decision
more accurately or sooner under those measured costs. It must first
supply its physical pair of operations, matched bases, coherent phases,
mode-dependent loss completion and actual all-launch yield. A static
compression scan is not a measured fast-refresh deadline. Discard the
present source as evidence for a native normality/commutator advantage;
retain it as a concrete ordinary model-reuse experiment. A future layout
could change that comparison, but the inspected source does not provide
the missing interface or its competing rate.
