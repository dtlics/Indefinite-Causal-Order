# Remote spin phase gates and ordinary photon-bus controls

This is a conditional-output proof component of
[NR-R11](../communication.md#nr-r11). It compares a specified switched
spin–photon construction with ordinary operations on the same stationary
spin payload. The
[exact finite checker](../checks/architecture/verify_remote_spin_phase.py)
replays the complete detected spin instruments, an explicit
lost-carrier counterexample for the first ordinary compiler, and a
stronger all-outcome compiler under a declared erasure dilation. It also
states a microscopic bright-loss obstruction for unencoded data and an
entanglement-first ordinary baseline with explicit extra resources. A scalar
reflected-sector comparison gives an exact average-concurrence closure and
a certified narrow Bell-yield interval. Native
routing, clocks, general cavity loss and optimal fault-tolerant rates
remain separate. An arbitrary-purifying-helper argument below extends the
Bell-yield formula to pure finite-pulse states, and a separate
[validated continuum checker](../checks/architecture/verify_remote_spin_pulse.py)
certifies one ordinary Gaussian-pulse lower bound. This comparison has
not been formalized in Lean. For fixed coherent controls, the full-pulse
ordinary factory also has the exact four-mode reduction and marginal SDP
below. A separate eigenstate-source construction matches complete coherent
survivors without assuming frequency-independent reflection amplitudes.
A stronger decorated eight-mode interface attains independent coherent
order programs; its same-port ordinary compiler uses four global windows,
with a separately qualified three-window merged-port option.
An exact projector-reflection certificate below gives a restricted
two-encounter gate gap while retaining those stronger ordinary comparators.

## Physical task and declared interfaces

Two remote stationary qubits $A,B$ hold arbitrary unknown input,
possibly entangled with an untouched reference $R$. A photon interacts
with each spin and is then detected; the spins are the retained output.
The target is a physical controlled phase

$$
\operatorname{CS}_{AB}=\operatorname{diag}(1,1,1,i),
$$

rather than preparation of one selected known spin state. Photon
detection may consume the carrier, while the spin data must remain
available on the declared branch.

The native ideal interaction is a spin–polarization controlled $Z$.
Known photon rotations and known local spin rotations are additional
controls, with their synthesis, duration and errors charged. This is a
model motivated by cavity gates, rather than a claim that every cavity
supplies the ideal interface. [Daiss et al., Science **371**, 614–617
(2021)](https://doi.org/10.1126/science.abe3150) demonstrate a remote gate
using sequential reflections from two atom–cavity modules connected by
60 m of fiber, polarization detection and conditional atomic control.
Their [primary manuscript and supplement](https://arxiv.org/pdf/2103.13095)
describe the spin-dependent reflection phase and local Raman rotations.
The experiment uses weak coherent pulses, has substantial loss, and
does not implement the switch or the four-mode port assumed below.

For the switched construction let $D$ denote photon polarization and
$C$ its route/order qubit. Photon Hadamards around the $A$ interaction
define

$$
G_A=|0\rangle\!\langle0|_A\otimes I_D
       +|1\rangle\!\langle1|_A\otimes X_D,
\qquad
G_B=|0\rangle\!\langle0|_B\otimes I_D
       +|1\rangle\!\langle1|_B\otimes Z_D.
\tag{RS1}
$$

The coherent interface must supply histories $G_BG_A$ for $C=0$
and $G_AG_B$ for $C=1$, with the required phase and environment
coherence. Knowing the two reduced gates alone does not supply that
router. The ordinary comparisons below specify their own native ports;
one of them needs only a single polarization bus.

## Complete detected switch instrument

Initialize $C,D$ in $+$. For spin label $a,b\in\{0,1\}$, the
output carrier state is

$$
|\phi_{ab}\rangle
=Z_D^b|+\rangle_D\otimes
 \frac{|0\rangle_C+(-1)^{ab}|1\rangle_C}{\sqrt2}.
\tag{RS2}
$$

Indeed $X^a|+\rangle=|+\rangle$, whereas
$X^aZ^b|+\rangle=(-1)^{ab}Z^b|+\rangle$. Measuring $D$ in $Z$
with result $d$, and $C$ in $Y$ with eigenvalue $s=\pm1$, gives
the diagonal spin Kraus amplitude

$$
K^S_{d,s}(a,b)
=\frac{(-1)^{bd}[1-is(-1)^{ab}]}{2\sqrt2}.
$$

Consequently, up to a branch-global phase,

$$
K^S_{d,s}=\frac12 Z_B^d\operatorname{CS}_{AB}^{s},
\qquad (K^S_{d,s})^\dagger K^S_{d,s}=I_{AB}/4.
\tag{RS3}
$$

Every $(d,s)$ outcome has probability $1/4$ for every input,
including reference-entangled input. Correcting $Z_B^d$ leaves
$\operatorname{CS}$ or $\operatorname{CS}^{\dagger}$, each with
probability $1/2$. These are all detected branches. Turning the latter
into a physical $\operatorname{CS}$ needs
$\operatorname{CZ}_{AB}$, since
$\operatorname{CS}^2=\operatorname{CZ}$. That is a nonlocal correction;
a proposed frame convention or repeat-until-success procedure must
state how it is handled and count its cost.

## An ordinary single-polarization bus matches the instrument

Use the native fixed-order sequence
$\operatorname{CZ}_{AD}$ followed by
$\operatorname{CZ}_{BD}$. No route qubit is needed. Prepare

$$
|\psi_\alpha\rangle_D
=\cos\alpha|0\rangle+\sin\alpha|1\rangle,
\qquad \alpha=\pi/8,
$$

and measure $D$ in $Y$, with eigenvalue $y=\pm1$. Its complete
spin instrument has Kraus operators

$$
K^F_y
=\frac{\cos\alpha\, I-iy\sin\alpha\,Z_AZ_B}{\sqrt2}
=\frac{e^{-iy\alpha Z_AZ_B}}{\sqrt2}.
\tag{RS4}
$$

Thus $p_y=1/2$, independently of the unknown spin state. Apply the
known **local** spin correction

$$
L_y=e^{iy\alpha Z_A}e^{iy\alpha Z_B}.
$$

On $00,01,10$, the combined phase is $e^{iy\alpha}$; on $11$
it is $e^{-3iy\alpha}$. Therefore

$$
L_yK^F_y
=\frac{e^{iy\alpha}}{\sqrt2}
  \operatorname{CS}_{AB}^{-y}.
\tag{RS5}
$$

Relabelling $s=-y$ reproduces the switch's corrected two-outcome
instrument. To reproduce its raw four-outcome dictionary, sample an
independent fair $d$ and apply $Z_B^d$. The ordinary branch Kraus
operator is

$$
\widetilde K^F_{d,s}
=\frac1{\sqrt2}Z_B^d L_{-s}K^F_{-s}.
\tag{RS6}
$$

Equations (RS3),(RS5) show that this equals $K^S_{d,s}$ up to a
branch-global phase. Hence every classical flag and the full retained
spin CP map agree on arbitrary $ABR$. This is equality of the
detected conditional quantum output, rather than only a scalar fringe,
gate fidelity or average output population.

The ordinary circuit uses the same two occupied native spin–photon
interactions, one photon, one polarization preparation/readout and
classically communicated local rotations. It does not require coherent
four-mode propagation or a third interaction window. In the convention
$R_z(\theta)=e^{-i\theta Z/2}$, the local corrections have rotation
angle magnitude $\pi/4$. Their calibration and duration, and the
nonstabilizer photon preparation, are real costs. They are ordinary
known controls for the declared atomic architecture, but cannot be
treated as free protected operations in a Clifford-only topological
model. The switch separately pays for its route coherence, route-specific
photon controls, second photon-degree readout and spin storage.

This construction uses established ancilla-mediated phase-control
ingredients. The elementary instrument comparison makes no claim of a
new ordinary gate mechanism or a demonstrated performance ordering.

## A deterministic four-mode alternative needs stronger ports

Suppose the two photon degrees $C,D$ are retained, and both stations
can apply $I_C\otimes G_A$ or $I_C\otimes G_B$ identically and
coherently on all $C$ alternatives. Prepare their known Bell state
$\Phi_{CD}$. Fixed order $G_A$ then $G_B$ sends spin label $ab$
to the photon state

$$
|\beta_{ab}\rangle
=(I_C\otimes Z_D^bX_D^a)|\Phi\rangle.
$$

The four states are orthonormal. For any desired known diagonal spin
unitary $U=\operatorname{diag}(u_{ab})$, $|u_{ab}|=1$, measure the
photon in the orthonormal basis

$$
|m_{uv}\rangle
=\frac12\sum_{a,b}u_{ab}^*(-1)^{ua+vb}|\beta_{ab}\rangle,
\qquad u,v\in\{0,1\}.
\tag{RS7}
$$

Its spin branch is

$$
K_{uv}=\frac12 Z_A^uZ_B^v U.
\tag{RS8}
$$

All four outcomes have probability $1/4$; local Pauli corrections
give $U$ deterministically in the ideal model. This includes
$\operatorname{CS}$. The photon source entangles two degrees of
freedom of one carrier, rather than supplying preshared $A$–$B$
entanglement. Source preparation, four-mode decoding, phase control and
readout still count.

The known unitary in (RS7) acts on one photon's four modes. It needs
no nonlinear gate between independent photons. Arbitrary path–polarization
unitaries and basis measurements are described by
[Englert, Kurtsiefer and Weinfurter, PRA **63**, 032303
(2001)](https://doi.org/10.1103/PhysRevA.63.032303), within the general
[linear-optical mode decomposition of Reck et al., PRL **73**, 58
(1994)](https://doi.org/10.1103/PhysRevLett.73.58).

This optical-control fact does **not** establish the station interface.
A two-polarization cavity with one spatial port need not preserve a
second rail or frequency/time-bin label with the same interaction. A
mode converter, matched coupling ports or a justified time-bin scheme
must supply $I_C\otimes G$. For example, histories $A_1B_2$ and
$A_2B_3$, aligned at the output, use three global windows and a longer
storage interval than switched histories $A_1B_2,B_1A_2$. Both have
two occupied interactions; that does not imply equal clocks, loss or
routing hardware. The single-polarization match (RS4)–(RS6) does not
need this stronger port.

### Balanced attenuation attains the accepted reflected-gate ceiling

The same construction closes a whole lossy family. Suppose the two
surviving reflections are a known ideal controlled π phase times a
common scalar at each station: the dark/bright amplitudes are
$\alpha,-\alpha$ at $A$ and $\beta,-\beta$ at $B$. Known photon
wrappers put the ideal parts into the $X,Z$ convention above. Then
(RS7)–(RS8) are simply multiplied by $\alpha\beta$:
$$
K_{uv}=\frac{\alpha\beta}{2}Z_A^uZ_B^v U,
\qquad p_0=|\alpha\beta|^2.
\tag{RS8a}
$$
Thus every prescribed known diagonal unitary on arbitrary unknown $ABR$
is attained with joint launch probability $p_0$. All four surviving
outcomes are accepted after local Pauli corrections; physical missing
photons still count as failures. This is a single-attempt gate weight;
rejected spins may be damaged, so it is not a harmless-retry rate.

This also gives an upper bound for any switch in the declared one-pass
diagonal-reflection architecture whose accepted flags require a surviving
reflected carrier. On the dark–dark spin input $00$,
each history is $\alpha\beta$ times normalized photon evolution,
even for an entangled control–polarization source or an accessible source
purifier. Total surviving weight is $p_0$. Every accepted unitary flag
has the same probability on every input, so its total accepted yield
is at most $p_0$. The ordinary construction saturates this bound, including
any prescribed mixture of diagonal-unitary flags by choosing the known
readout basis with the required classical probabilities. This is an
accepted reflected-gate ceiling, not an equality of no-click spin states.
No-click acceptance is outside this bound. It assumes
one visit to each station, no free bypass and no intermediate data-spin
encoding or control that changes the diagonal interaction model.

If the same balanced relation holds **pointwise** over a pulse, with
common factors $\alpha(\nu),\beta(\nu)$ and frequency-preserving optics,
replace $p_0$ by $\int|f(\nu)\alpha(\nu)\beta(\nu)|^2d\nu$.
The surviving spectral envelope is common to all four photon labels,
so the constant spatial-mode basis (RS7) suffices; this family requires
no additional coherent spectral sorter. Frequency conversion changes
the frequencies encountered by the stations and needs its own bound.

There is a physical single-frequency balancing line in the resonant
input–output model (RS19). For cooperativity
$C=g^2/(\kappa\gamma)>0$, set
$$
\frac{\kappa_r}{\kappa}=\frac{C+1}{C+2},\qquad
r_0=1-2\frac{\kappa_r}{\kappa}=-\frac{C}{C+2},\qquad
r_1=1-\frac{2\kappa_r/\kappa}{1+C}=+\frac{C}{C+2}.
\tag{RS8b}
$$
Here $\kappa,\gamma$ are the amplitude decay rates used in (RS19),
and $\kappa-\kappa_r=\kappa/(C+2)>0$. This is a resonance condition
on model parameters; it neither asserts that the measured modules lie
on that line nor extends their equality to a finite-bandwidth cavity
pulse. General routed loss/emission records and actual optical, local
control and storage costs remain separate.

The photon readout can close a larger **single-frequency** opposite-phase
family without data-spin filters. Write the two amplitudes at station
$j$ as $-u_j,+v_j$, with $0<u_j,v_j\le1$, after removing a known common
phase. Give each station a fresh independently addressable two-state
register of the same four-mode photon, using the preserved ports and
a known between-station mode swap. In that register choose
bright-projector population $x_j=u_j/(u_j+v_j)$. The two spin-conditioned
photon vectors are
$$
|f_{j0}\rangle=-u_j\bigl(\sqrt{1-x_j}|0\rangle+\sqrt{x_j}|1\rangle\bigr),
\qquad
|f_{j1}\rangle=-u_j\sqrt{1-x_j}|0\rangle+v_j\sqrt{x_j}|1\rangle.
$$
Their inner product vanishes, and their squared norms are
$d_{j0}=u_j^2$, $d_{j1}=u_jv_j$. Thus the four joint vectors are
$|f_{ab}\rangle=\sqrt{d_{Aa}d_{Bb}}\,|e_{ab}\rangle$ for an
orthonormal photon basis. Set
$p=\min_{ab}d_{Aa}d_{Bb}$, and for target phases $t_{ab}$, $|t_{ab}|=1$,
use the four photon measurement vectors
$$
|m_{rs}\rangle=\sum_{a,b}
 \frac{\sqrt p\,t_{ab}^*(-1)^{ra+sb}}
      {2\sqrt{d_{Aa}d_{Bb}}}|e_{ab}\rangle.
\tag{RS8c}
$$
Their effects sum to $\operatorname{diag}_{e}(p/(d_{Aa}d_{Bb}))\preceq I$;
the positive complement supplies reflected failure outcomes. Every
success branch is $\sqrt p\,Z_A^rZ_B^s\operatorname{diag}(t_{ab})/2$,
so local Pauli feedback gives the exact target on arbitrary $ABR$ with
total launch probability $p$. When $v_j\ge u_j$ at both stations,
$p=u_A^2u_B^2$ saturates the same accepted reflected-gate ceiling.
Indeed the dark–dark input has exactly that total surviving weight,
which bounds every input-independent accepted unitary instrument.
In (RS19) this includes the resonant range
$1/2<\kappa_r/\kappa\le(C+1)/(C+2)$, not just its balanced endpoint.
The two independently addressed photon registers and generalized
measurement require the declared four-mode interface, calibrated source
and readout, additional failure ports and their losses. A polarization-only
module does not supply them. Frequency-dependent amplitude ratios require
different source balances; (RS8c) alone is not a finite-pulse compiler.
No-click branches remain excluded and rejected spin data need not survive.

## A common diagonal bath preserves the detected comparison

A limited correlated-noise extension is exact. Let a common spin/bath
evolution over the same total duration be

$$
N=\sum_{a,b}|ab\rangle\!\langle ab|\otimes V_{ab}.
\tag{RS9}
$$

This includes time-ordered Hamiltonians diagonal in the spin basis,
with arbitrary quantum bath dynamics, spatial correlations and memory.
Assume this evolution is independent of the photon route/polarization.
It commutes with the spin-controlled photon gates, photon-only controls
and local $Z$ corrections, so it can be placed at a common end of
each circuit. Equations (RS3)–(RS6) then agree on the full $ABER$
input and output, including later bath readout. No classical-bath or
Markov assumption is used.

This requires the same elapsed bath evolution and the stated commuting
interaction. It does not cover spin relaxation, scattering-induced bath
changes, photon-dependent bath dynamics, route-clock records or
spin-dependent loss. Such faults need their actual joint dilation.
Matching a marginal noise rate is insufficient.

## The first compiler's lost-carrier counterexample

The detected-instrument match (RS4)–(RS6) alone is not an optical
erasure-completion theorem. Suppose the photon is erased after the
interactions but before readout, with its optical state retained in an
inaccessible environment. The rejected spin map is the Schur multiplier
determined by the carrier Gram matrix.

For (RS2), the overlap is zero unless both $b$ and $ab$ agree.
In particular $|00\rangle\!\langle10|$ is retained with factor one.
For the ordinary circuit (RS4), before its outcome-dependent correction,
the carrier is
$$
|\gamma_{ab}\rangle
=\cos\alpha|0\rangle+(-1)^{a+b}\sin\alpha|1\rangle.
$$
Opposite parities have overlap $\cos(2\alpha)=1/\sqrt2$, so the
same spin coherence has factor $1/\sqrt2$. Known phase conventions
cannot change its magnitude. These no-click spin states therefore
differ. The four-mode Bell-label carrier instead loses every
off-diagonal $ab$ coherence when erased.

This is a counterexample to promoting those particular detected
identities to a full loss simulation. It is not an ordinary impossibility
result: the stronger compiler below matches the observed rejected map
as well. None of these classical-instrument comparisons asserts equality
of an unmeasured coherent route/polarization output.

## An ordinary compiler for the complete observed erasure instrument

Consider the following explicit optical loss model. In both circuits,
each native ideal spin–photon interaction is followed by a
**spin- and polarization-independent erasure**. Its surviving component
is the ideal gate with scalar survival amplitude; its lost component
transfers the whole incident carrier to a fresh inaccessible optical
mode and leaves vacuum. The two photon degrees, including the route,
are lost together. Loss modes distinguish station, route and time and
are traced; their records are not coherently erased. The vacuum
extension of a later spin interaction acts trivially on the spin.

Let the survival factors be:

| Port | Survival |
| --- | --- |
| Unmonitored propagation before the first encounter | $\tau_0$ |
| Module $A$, after its ideal interaction | $\tau_A$ |
| Module $B$, after its ideal interaction | $\tau_B$ |
| Intermodule link, in either direction | $\tau_L$ |
| After the second encounter, including detection efficiency | $\tau_D$ |

All factors lie in $[0,1]$. The link and optical implementation must
supply the same declared factors in both directions/order arms.
Different module efficiencies $\tau_A,\tau_B$ are allowed. Success
preserves the intended photon modes. Fresh loss ports, calibrated
parameters and reciprocal propagation are assumptions about the
physical dilation, not consequences of an observed terminal success
probability. The accessible output distinguishes detected outcomes from
one final vacuum/no-click flag; loss location is not an accessible
output. A separate source herald is retained and handled separately.

The common photon-detection probability is
$$
s=\tau_0\tau_A\tau_B\tau_L\tau_D,\qquad F=1-s.
\tag{RS10}
$$
The ordinary circuit now starts $D$ in $+$, visits $B$ first with a
controlled photon Hadamard, then $A$ with controlled photon $X$.
Both use the same native controlled-$Z$ encounters: with
$W=e^{-i\pi Y_D/8}$, $WZ_DW^\dagger=H_D$; photon Hadamards conjugate
$Z_D$ to $X_D$. These are known polarization wrappers, not controlled
unknown channels or four-mode-preserving cavity ports.

Its carrier states after $B$ are $+$ for $b=0$ and $0$ for $b=1$.
After $A$ they are
$$
|\gamma_{00}\rangle=|\gamma_{10}\rangle=|+\rangle,\qquad
|\gamma_{01}\rangle=|0\rangle,\quad
|\gamma_{11}\rangle=|1\rangle.
\tag{RS11}
$$
On detection, measure $Y_D$ with eigenvalue $y$ and correct spin $B$ by
$$
Q_y=|0\rangle\!\langle0|+
                   e^{-iy\pi/4}|1\rangle\!\langle1|.
$$
The amplitudes $\langle y|+\rangle=(1-iy)/2$,
$\langle y|0\rangle=1/\sqrt2$ and
$\langle y|1\rangle=-iy/\sqrt2$ give
$$
Q_yK^G_y=\frac{e^{-iy\pi/4}}{\sqrt2}
                       \operatorname{CS}^{-y}.
\tag{RS12}
$$
Relabel $s_{\rm flag}=-y$ and, if the raw switch dictionary is desired,
sample the independent fair $d$ and apply $Z_B^d$ as in (RS6).
Every detected spin CP map, including its scalar detection weight,
then equals the switch's. This stronger compiler needs only one local
spin phase correction, although its photon wrappers differ from (RS4).

**All loss histories.** A lost carrier produces a Schur map on the
spin matrix units. For one switch arm with first module $j$ and second
$k$, its four loss weights after the pre-first segment are
$$
\frac{\tau_0}{2}(1-\tau_j),\quad
\frac{\tau_0\tau_j}{2}(1-\tau_L),\quad
\frac{\tau_0\tau_j\tau_L}{2}(1-\tau_k),\quad
\frac{\tau_0\tau_j\tau_L\tau_k}{2}(1-\tau_D).
\tag{RS13}
$$
The first two use the photon state after the first ideal gate; the
last two use its state after both. The unmonitored pre-first loss contribution is
$(1-\tau_0)\operatorname{id}$.

In the $A$-first arm, the first $X^a$ acts trivially on $+$; after
both encounters the carrier is $Z^b|+\rangle$. In the $B$-first arm
it is $Z^b|+\rangle$ after the first encounter and
$(-1)^{ab}Z^b|+\rangle$ after both. The erased route modes are
orthogonal, so their rejected contributions add rather than interfere.
Summing (RS13) gives the switch's complete rejected coefficient
$$
G_S(ab,a'b')=
\begin{cases}
F,&b=b'=0\ \text{or }(a,b)=(a',b'),\\
h,&b=b'=1,\ a\ne a',\\
g_S,&b\ne b',
\end{cases}
$$
where
$$
h=1-\tau_0\tau_B\tau_L,\qquad
g_S=(1-\tau_0)+\frac{\tau_0}{2}(1-\tau_A\tau_L).
\tag{RS14}
$$
For example, the $b=1$ off-diagonal first-stage contribution is
$$
1-\tau_0+\frac{\tau_0}{2}
       [\,2-\tau_A\tau_L-\tau_B\tau_L\,].
$$
Its second-module loss contribution is
$\tau_0\tau_L[\tau_A(1-\tau_B)-\tau_B(1-\tau_A)]/2$,
and the post-second contributions cancel. Their sum is $h$. This
cancellation matters when the module efficiencies differ.

For the ordinary $B$-first circuit, any loss after $B$ has cross-$b$
overlap $1/\sqrt2$, both before and after $A$, by (RS11). At $b=1$,
the two $a$ states become orthogonal only when $A$ acts. Its complete
reject coefficient therefore has the **same** two within-$b$ cases,
while
$$
G_G(ab,a'b')=g_G\quad(b\ne b'),\qquad
g_G=(1-\tau_0)+\frac{\tau_0}{\sqrt2}
                 (1-\tau_A\tau_B\tau_L\tau_D).
\tag{RS15}
$$
These are complete subnormalized CP maps: every diagonal equals $F$,
and every spin matrix unit is specified.

**A local reject correction.** If $g_G>0$, set $r=g_S/g_G$. Write
$z=\tau_A\tau_L$ and
$w=\tau_A\tau_B\tau_L\tau_D\le z$. Then
$$
g_G-g_S=\tau_0\left[
 \left(\frac1{\sqrt2}-\frac12\right)(1-z)
 +\frac{z-w}{\sqrt2}\right]\ge0.
$$
Thus $0\le r\le1$. Upon final no-click, apply only the local channel
$$
\mathcal D_{B,r}(\rho)
 =\frac{1+r}{2}\rho+\frac{1-r}{2}Z_B\rho Z_B.
\tag{RS16}
$$
It leaves the within-$b$ coefficients unchanged and multiplies the
cross-$b$ coefficients by $r$. Consequently
$$
\mathcal D_{B,r}\circ\mathcal R_G=\mathcal R_S.
\tag{RS17}
$$
If $g_G=0$, the declared transmissions imply $F=0$, so its value is
irrelevant. Combined with (RS12), this is equality of **all observed
detected/vacuum branches and retained spin states** for arbitrary
unknown $ABR$ input. It is an ordinary two-encounter construction with
randomized local spin control after rejection.

## Calibration, clocks and what the erasure comparison excludes

The corrector $r$ depends on supplied or calibrated loss parameters.
Their monitoring access, statistical confidence, precision and validated
reuse interval must be charged. Terminal counts alone identify a
transmission product and need not identify the individual factors in
$g_S$. There is no universal unknown-transmission simulator here.
Clip an approximate corrector $\widehat r$ into $[0,1]$. Its reject-map difference is
$$
g_G(\widehat r-r)\,\mathcal P_{\rm cross,B},\qquad
\mathcal P_{\rm cross,B}=(\operatorname{id}-\operatorname{Ad}_{Z_B})/2.
$$
This projection has diamond norm one: the triangle inequality gives
the upper bound, and a $|+\rangle_B$ input attains it. Thus the
half-diamond error of the entire observed instrument is
$$
\frac12\,|g_G\widehat r-g_S|.
\tag{RS18}
$$
Bound the subnormalized coefficient rather than an unstable fitted
ratio. For negligible $g_G$, omitting dephasing has error at most
$g_G/2$; a small rejected branch need not be calibrated by division.

Both circuits count every launch, attempted encounter, source event,
photon control, detection and classical feedback. The ordinary schedule
also includes the local $B$ phase or reject dephaser and their errors.
Ideal polarization wrappers are unconditional photon unitaries, so
their placement preserves the lost-carrier Gram products used above.
Their extra optical loss, duration and control errors in a physical
implementation must still be included in the matched budget; ideal
unitary wrappers do not supply free lossless optics.
A statement about equal occupied gates is not a statement about equal
optical routers, pulse durations or wall time. Spin storage and noise
over the complete feedback interval must be matched explicitly. The
common diagonal-bath argument (RS9) applies when both use the same
elapsed bath evolution and the erasure ports are independent of that
bath. General idling or relaxation cannot be discarded as a visibility.

Under those matched interface/clock premises, any code, recovery or
adaptive repeat controller receiving these flags and spin outputs sees
the same instrument after substitution of the ordinary compiler.
The equality is input/reference inclusive, so composition does not
assume fresh known spin data. Independent fresh optical loss ports and
the declared calibrated module behavior must remain valid across
attempts. This excludes an error-corrected benefit derived solely from
the first ordinary compiler's poorer no-click state in this erasure
model; it is not an optimal ordinary-rate theorem.

The excluded physical effects are substantial. Actual cavity reflection
and missing-photon amplitudes can depend on spin, polarization,
frequency and detuning; loss may occur during the interaction rather
than after a perfect gate. Direction-dependent paths, monitored loss
locations, external retained order controls, nonorthogonal loss records,
photon-dependent bath changes or dark counts need new dilations.
One cannot trace a record available to the receiver solely to enforce
this model. Known source-herald outcomes are retained as separate
branches, rather than hidden in a fitted erasure parameter.

A known-input resource factory may reset after rejection. A supplied
unknown input can be irreversibly damaged on no-click, so retrying
requires the specified physical code or recovery; neither circuit gets
that recovery free. The following microscopic loss obstruction and
ordinary factory baseline sharpen that distinction. A larger detected
gate fidelity or control fringe does not settle complete encoded
performance; a substantial native gate or rate advantage remains open.

The checker uses exact arithmetic in
$\mathbb Q[e^{i\pi/8}]=\mathbb Q[x]/(x^8+1)$. It checks every spin
matrix-unit coefficient of the four raw instrument branches, four-mode
readout orthogonality and complete branches for finite phase choices,
the first compiler's lost-carrier obstruction, and all-history rejected
maps at 73 erasure-parameter cases including unequal modules and
boundary values. It also checks the stronger compiler's four detected
branches and the corrector's positivity decomposition. These are full
corresponding Choi-map checks; all-dimensional native-port, calibration,
composition and clock arguments remain the proofs above.

## Spin-dependent cavity loss and an unencoded recovery obstruction

The preceding all-loss compiler is scoped to post-unitary,
state-independent erasure. A cavity reflection can violate that premise
before routing costs enter. A useful minimal extension is the linear,
one-excitation, closed-cycling input–output model used in
[Hacker et al., Nature Photonics **13**, 110–115 (2019), Methods and supplement](https://arxiv.org/pdf/1812.09604).
The formulas below are the corresponding one-excitation solution, not
a full experimental fit. Set
$D_c(\omega)=\kappa+i(\omega_c-\omega)$,
$D_a(\omega)=\gamma+i(\omega_a-\omega)$ and
$\Delta_g=D_cD_a+|g|^2$, where $\kappa,\gamma$ are **amplitude**
decay rates and $\kappa=\kappa_r+\kappa_\ell$; choose $g$ real by a
fixed phase convention. A photon entering the
monitored reflection port has amplitudes
$$
r_g=1-\frac{2\kappa_rD_a}{\Delta_g},\qquad
\ell_g=-\frac{2\sqrt{\kappa_r\kappa_\ell}\,D_a}{\Delta_g},\qquad
e_g=\frac{2ig\sqrt{\kappa_r\gamma}}{\Delta_g}.
\tag{RS19}
$$
The output modes are reflected light, intrinsic cavity loss and atomic
spontaneous emission, respectively. They are orthogonal reservoirs in
this declared model, and
$|r_g|^2+|\ell_g|^2+|e_g|^2=1$ for real frequency. Indeed
$\operatorname{Re}(\Delta_gD_a^*)=\kappa|D_a|^2+\gamma g^2$, so
$$
|\Delta_g|^2-|\Delta_g-2\kappa_rD_a|^2
=4\kappa_r[\kappa_\ell|D_a|^2+\gamma g^2],
$$
which is exactly the sum of the two loss numerators.
For spin label $a$ and polarization $p$, take $g_{1,R}=g$ and the
other $g_{a,p}=0$. The isometry retains the atomic basis label and
sends $|p,\omega\rangle$ into those three modes with amplitudes
(RS19). Spontaneous emission is nonzero only in the bright spin and
$R$ polarization. This assumes a closed transition returning to the
same qubit state; Raman leakage, motion and extra levels require more
output channels.

[Daiss et al., primary manuscript and supplement](https://arxiv.org/pdf/2103.13095)
give $(g,\kappa,\kappa_r,\gamma)/(2\pi)$ in MHz as
$(7.6,2.5,2.3,3)$ and $(7.6,2.8,2.4,3)$ for their two modules,
and use an input–output simulation. Substitution into (RS19) at
resonance gives dark/bright reflected amplitudes approximately
$(-0.8400,0.7885)$ and $(-0.7143,0.7823)$. Thus even the minimal
mode-matched model has spin- and polarization-dependent survival.
These derived amplitudes are an illustration from the reported
parameters, not a fit of the experiment or a measured switch rate.
The experiment's weak coherent source also allows multiple incident
photons, including lost-photon records on a detected attempt; the
one-photon model does not include those events.

For a normalizable pulse $\int|f(\omega)|^2d\omega=1$, retain the
frequency and emission modes in the dilation. A frequency-unresolved
detection gives a Kraus integral, not the operator obtained by replacing
$r_g(\omega)$ with its average. In particular, if history $h$ has loss
amplitude $F^z_{h,\mu}(\omega)$ for spin label $z$, its overlap with
history $h'$ is
$$
\Gamma^{z,z'}_{h,h'}=
 \sum_\mu\int d\omega\,
 F^z_{h,\mu}(\omega)
 F^{z'}_{h',\mu}(\omega)^*.
\tag{RS20}
$$
Here $F$ includes the pulse, all preceding reflection amplitudes,
propagation delays and the actual router's mode transformations.
Relative time shifts supply frequency-dependent phases. Scalar
reflectivities do not determine (RS20). Neither orthogonal time
records nor their coherent erasure follows just from a fiber length
and a pulse duration. The native router and accessible records must be
specified before assigning the switch a complete no-click instrument.

There is nevertheless a recovery obstruction that does not require
orthogonal order-history records. Let $\mathcal J$ be an unresolved
no-click CP map from the **unencoded** $AB$ data space to the same
space, with only that flag and $AB$ accessible afterwards. Suppose
some Kraus representation contains a nonzero operator $K_*$ of rank
less than four. There is no subsequent trace-nonincreasing recovery
$\mathcal R$ on those data such that
$$
\mathcal R\circ\mathcal J=p\operatorname{Ad}_U,
\qquad p>0,
\tag{RS21}
$$
for a unitary $U$ on arbitrary $ABR$.

To prove this, write the recovery Kraus operators as square matrices
$L_\ell$. The output Choi operator in (RS21) has rank one, so every
$L_\ell K_j$ must be zero or a scalar multiple of $U$. Because $p>0$,
some $L_{\ell_0}K_{j_0}$ has full rank. Thus $L_{\ell_0}$ is
invertible. But $L_{\ell_0}K_*$ is nonzero and rank deficient,
a contradiction. Fresh clean recovery ancillas followed by readout or
tracing still give square effective Kraus operators $L_\ell$ and do
not change this argument. It includes a heralded recovery, rather than
only deterministic feedback.

In the spin-diagonal direct constructions above, an emission from
module $A$ has right support in
$P_{A,1}=|1\rangle\!\langle1|_A\otimes I_B$, hence rank at most
two. All photon rotations and the other diagonal spin interaction
preserve that support. Coherent sums of early/late emission amplitudes
with the same bright-spin support retain the bound, so the argument
allows arbitrary initial route/polarization states. A common spin
pre-rotation merely rotates the right support. This application assumes
independent local radiation reservoirs and no route-dependent spin
basis controls coherently combining different supports. General
interventions must be tested from their actual Kraus operators.

A quantitative version holds for a trace-preserving recovery after
the aggregate flag. Define the accepted weight of that flag on
$\Phi_4$ as $p_J$, and let $w$ be the weight of the rank-at-most-two
emission constituents. With $q_J$ its overlap with the desired
unitary Choi state after recovery,
$$
q_J\le p_J-\frac{w}{2}.
\tag{RS22}
$$
Indeed $|\operatorname{Tr}(U^\dagger K)|^2\le
\operatorname{rank}(K)\operatorname{Tr}(K^\dagger K)$, by the
trace-norm and Hilbert–Schmidt inequalities. Every recovered emission
constituent still has rank at most two. A trace-preserving recovery
preserves their summed probability $w$; the other constituents have
$q\le p$. Integrating over continuous emission records gives (RS22).
This is a subnormalized all-input Choi bound, not a worst-input
conditional-fidelity guarantee.

The obstruction concerns restoring an unknown full-space data state
following one unresolved flag. It does not exclude encoding into extra
physical qubits, backup quantum memory, a smaller code space, or an
additional accessible syndrome identifying a different output sector.
If emission has a separately accessible flag, aborting that destructive
branch is distinct from repairing it. No claim about all encoded
repeat-until-success schemes follows.

<a id="nr-r11-parity-failure"></a>

### Balanced reflection does not make an online parity retry harmless

Use the closed-cycling dilation (RS19), independent unobserved intrinsic
and spontaneous reservoirs, and a fresh input-independent bath on every
attempt. The balanced carrier setting (RP19) has
$r_0=-r,r_1=r$, $s=\sqrt{1+C_i}$, $r=(s-1)/(s+1)$ and
$q=1-r^2$. Here $\kappa_{\rm ex}=\kappa_r$ and
$\kappa_{\rm in}=\kappa_i=\kappa_\ell$ denote the same amplitude widths.
Its intrinsic amplitudes satisfy
$\ell_1/\ell_0=1/s$ and $\ell_0\ell_1^*=q/s$.
Only intrinsic loss contributes to the atomic off-diagonal term;
closed-cycling spontaneous emission has right support $|1\rangle$.
Normalization in (RS19) therefore gives the **unresolved** local failure map

$$
\mathcal F_j=q\left[\frac{1+\lambda}{2}\operatorname{id}
       +\frac{1-\lambda}{2}\operatorname{Ad}_{Z_j}\right],
\qquad \lambda=1/s.
\tag{PF1}
$$

Its input-independent probability $q$ does not make its conditional data
channel identity. This uses the declared cycling branch, not merely a
reflected amplitude and total linewidth. For example, a spontaneous
branch returning to $|0\rangle$ with the same norm instead changes the
failed populations; auxiliary-state decay enlarges the output space.
The [ordinary architecture comparison](../architecture.md) does not
supply those missing branching fractions or a native loss router.

Keep the photon bypass at unit amplitude and prepare photon $|+\rangle$.
Apply node $A$, photon $X$ (vacuum fixed), node $B$, then photon $X$
readout. This bypass choice differs from attenuating an individual node
to a scalar CZ. With $R_j=-rZ_j$, the accepted operators are

$$
L_\pm=\frac{R_A\pm R_B}{2}
 =-rZ_A\Pi_{\rm even/odd},\qquad
\Pi_t=\frac{I+(-1)^tZ_AZ_B}{2}.
\tag{PF2}
$$

Known $-Z_A$ feedback gives $r\Pi_t$, so their total accepted effect is
$pI$, $p=r^2$. Initial $V$ interacts with $A$ and then bypasses $B$;
initial $H$ bypasses $A$ and interacts with $B$. Thus a loss at $B$ on
its occupied branch has no earlier unobserved interaction with $A$.
Distinct node loss records give the complete failed map on arbitrary
unknown $ABR$,

$$
\mathcal F=\frac12(\mathcal F_A\otimes\operatorname{id}_B+
                    \operatorname{id}_A\otimes\mathcal F_B).
\tag{PF3}
$$

The accepted and failed maps together are trace preserving. This is a
parity measurement, not a full-space unitary. Either parity encoding
$\{|00\rangle,|11\rangle\}$ or
$\{|01\rangle,|10\rangle\}$ has conditional failure coherence
$\lambda$. Coherences differing in only one bit instead have multiplier
$(1+\lambda)/2$; the full map is not uniform global dephasing.

For an exact carrier fixture take
$\kappa_{\rm in}=\gamma=1$, $\kappa_{\rm ex}=3$, $|g|^2=8$.
Then $s=3,r=1/2$ and

$$
\mathcal F_j=\tfrac12\operatorname{id}+\tfrac14\operatorname{Ad}_{Z_j},
\qquad
\mathcal F=\tfrac12\operatorname{id}
 +\tfrac18\operatorname{Ad}_{Z_A}+\tfrac18\operatorname{Ad}_{Z_B}.
\tag{PF4}
$$

Its probability is $3/4$, with conditional logical visibility $1/3$.
For comparison, changing only the declared spontaneous final state to
$|0\rangle$ gives the local failed map $(3/4)\operatorname{AD}_{1/3}$,
where the subscript denotes survival **amplitude**: the normalized
output $|1\rangle$ population is $1/9$. These are different completions
of the same guided response, not fitted device parameters.

With ideal detection, stationary independent attempts and no waiting
noise, $n$ failures then success has population weight $pq^n$ and
logical coherence weight $p(q\lambda)^n$. At most $J$ attempts give

$$
P_J=1-q^J,\qquad
c_J=\frac{p[1-(q\lambda)^J]}{1-q\lambda},\qquad
\mathcal J_{\rm reject}=\mathcal F^J.
\tag{PF5}
$$

Here $c_J$ is unnormalized coherence; its accepted visibility is
$c_J/P_J$. For eventual success,
$c_\infty=p/(1-q\lambda)=(s-1)/(s+3)$, logical entanglement fidelity
is $(s+1)/(s+3)$, and mean attempts are $1/p$.
At (PF4), four mean attempts still give visibility $1/3$ and fidelity
$2/3$, despite an ideal accepted parity operator on every attempt.
A known phase cannot undo unobserved random dephasing. For the resulting
logical dephasing channel, arbitrary CPTP recovery cannot exceed
$(1+c_\infty)/2$: Pauli Parseval gives
$\sum_{\ell,P}|\operatorname{Tr}(R_\ell P)|^2=4$ for recovery Kraus
operators, so its weighted Bell overlap is at most the larger Pauli
probability; identity attains it. This optimizes recovery for these
encodings and records, not an enlarged error-correcting code or bath access.

External loss has a different placement and data map. For transmission
$\eta$ after node $B$ but before destructive readout, with orthogonal
lost-polarization records, add

$$
\mathcal F_{\rm ext}=\frac{1-\eta}{2}
   (\operatorname{Ad}_{R_A}+\operatorname{Ad}_{R_B}).
\tag{PF6}
$$

At (PF4), unresolved internal plus external loss is
$\tfrac12\operatorname{id}+(2-\eta)
(\operatorname{Ad}_{Z_A}+\operatorname{Ad}_{Z_B})/8$ and success is
$\eta/4$. Its intra-parity failure coherence coefficient is $\eta/4$,
so eventual retry visibility is $\eta/(4-\eta)$ under the same assumptions.
If external loss were separately identified, its within-parity logical
$Z$ could be corrected; a coarse no-click flag does not provide that
record. Loss between nodes, source vacuum, false heralds, missed clicks,
spectral processing, spin flips, leakage and storage need their actual
maps and clocks. An ideal no-interaction source-vacuum branch alone
changes the launch count but does not remove the internal retry penalty.

The commuting elastic survivor does not determine native no-click
behavior. Orthogonal order-record loss subspaces imply an ordinary
classical mixture of history failures, but photon loss or Markov baths
alone do not imply that premise. For routed loss Kraus maps, column
orthogonality constrains $\sum_\mu K_{0\mu}^\dagger K_{1\mu}=0$;
it need not imply
$\sum_\mu K_{0\mu}\rho K_{1\mu}^\dagger=0$.
Physical clocks, ports and inaccessible record overlaps must complete
the native dilation before a full-channel comparison or safe retry is
claimed. This warning grants no receiver access to those records.

## Entanglement first: the ordinary baseline with spare matter qubits

If the architecture supplies a separate communication qubit $a,b$ at
each node, the strongest baseline should isolate optical failures from
the unknown data. Initialize $a,b,D$ in $+$, use ordinary
$\operatorname{CZ}_{aD}$ followed by $\operatorname{CZ}_{bD}$,
and read $D$ in $X$. In the ideal model, result $x$ applies
$$
J_x=\frac{I+(-1)^xZ_aZ_b}{2},\qquad
J_x|++\rangle=
\begin{cases}
 (|00\rangle+|11\rangle)/2,&x=0,\\
 (|01\rangle+|10\rangle)/2,&x=1.
\end{cases}
\tag{RS23}
$$
Thus a local $X_b^x$ supplies $\Phi_2$ on every detected attempt.
In the preceding ideal erasure model, its yield is $s$ from (RS10).
Any failed factory branch acts on $a,b$ and the optical environment,
while the arbitrary $ABR$ state factors unchanged. More generally this
factorization is exact for **any** factory scattering instrument if the
whole factory and its initial environment are independent of $ABR$
and physically isolated from it. Shared baths, reset crosstalk and
storage errors violate that premise and must be charged. For real
cavities, optical detection is not automatically a perfect Bell herald.

One known Bell pair implements $\operatorname{CS}_{AB}$ on arbitrary
input by ordinary LOCC. Bell-assisted controlled-unitary constructions
are established by
[Eisert et al., Phys. Rev. A **62**, 052317 (2000)](https://doi.org/10.1103/PhysRevA.62.052317).
A stronger sufficient local ledger for this phase gate follows directly
from two local controlled-$Z$ gates. Prepare
$(|00\rangle+i|11\rangle)_{ab}/\sqrt2$ by a local $S_b$ on the
factory Bell pair. Apply $\operatorname{CZ}_{aA}$ and
$\operatorname{CZ}_{bB}$, set $P=Z_AZ_B$, and measure $a$ in $X$
with eigenvalue $m=\pm1$. For arbitrary $ABR$ input the remaining
operator-valued state is
$$
\frac{|0\rangle_b I+i m|1\rangle_b P}{2}.
$$
Send $m$ to Bob. With $c=\cos\beta$, $s_\beta=\sin\beta$, Bob
measures the orthonormal basis
$c|0\rangle+m s_\beta|1\rangle$,
$-m s_\beta|0\rangle+c|1\rangle$. The two data Kraus operators are
$$
K_{m,0}=\frac12U_\beta,\qquad
K_{m,1}=\frac{i m}{2}P U_\beta,\qquad
U_\beta=e^{i\beta Z_AZ_B}.
\tag{RS24}
$$
Every joint record has probability $1/4$, independently of $ABR$.
For the second outcome Bob applies $Z_B$ and sends that outcome bit to
Alice for $Z_A$. At $\beta=\pi/8$, the two local data rotations obey
$$
(T_A\otimes T_B)U_{\pi/8}=e^{i\pi/8}\operatorname{CS}_{AB}.
$$
This proves the full arbitrary-input/reference channel, rather than a
known-state factory identity. All four records are usable, with no
inverse-CS output needing a nonlocal correction.

The stronger online cost is two local matter–matter CZ gates, two data
$T$ rotations, a single $T$-equivalent $R_y(\pi/4)$ measurement-basis
rotation on $b$, Pauli feedback, and one classical bit in each
direction. Alice's bit changes Bob's basis by a known Pauli $Z$;
readout, resource phase $S_b$, Bell readiness and storage are additional.
An alternative generic controlled-unitary construction uses one local
CNOT and a local CS synthesized by two CNOTs plus three $T/T^\dagger$
phases. That three-CNOT count is sufficient, but is not the strongest
phase-gate comparator here. Neither ledger treats non-Clifford control
or local entangling gates as free hardware.

A primary recent context is
[Liu, Zheng, Yin and Wei, New J. Phys. **28**, 034506 (2026)](https://doi.org/10.1088/1367-2630/ae4a44),
whose [primary protocol](https://inspirehep.net/files/ffad4269b5939382009116652d0d3624)
uses the phase-Bell resource and two local switches of known
single-qubit gates. The ordinary reduction can be checked explicitly.
For anticommuting known Pauli operators $P_0,Q_0$, let
$R=e^{-i\pi P_0/4}$ and
$W=|0\rangle\!\langle0|\otimes Q_0R+
|1\rangle\!\langle1|\otimes RQ_0$. Since
$Q_0RQ_0=R^\dagger$,
$$
(Q_0R)^\dagger RQ_0=R^{-2}=iP_0,\qquad
W=(I\otimes Q_0R)(S\otimes I)\operatorname{C}(P_0).
\tag{RS24a}
$$
Here $\operatorname{C}(P_0)$ is controlled Pauli $P_0$, locally
Clifford-equivalent to CZ. Thus the specified ideal local switch is
itself a known entangling gate under a change of local Clifford frame.
For a general known rotation axis the corresponding equivalence uses
known local basis rotations, whose synthesis must be counted.
Equations (RS24)–(RS24a) are an ordinary comparator, not a claim that
the primary paper demonstrates a matter-gate implementation or that a
physical router and a synthesized CZ have identical noise and timing.
Native errors, coherent-mode access and durations still determine the
actual architecture comparison.

For the exact ideal-resource statement, let $s_{\rm Bell}$ be the
perfect Bell-pair yield per fresh independent factory attempt, including
its filters and source heralds. A hard maximum of $K$ attempts gives
the data instrument
$$
[1-(1-s_{\rm Bell})^K]\operatorname{Ad}_{\rm CS}
 \quad\hbox{or}\quad
(1-s_{\rm Bell})^K\operatorname{id}_{AB}.
\tag{RS25}
$$
The mean launch count is $[1-(1-s_{\rm Bell})^K]/s_{\rm Bell}$,
with a hard $K$ cap; without a cutoff it is $1/s_{\rm Bell}$ if
$s_{\rm Bell}>0$. Two commanded station windows are counted per
launch, even when loss prevents a visit. In the ideal $a$-then-$b$
erasure model, the mean occupied visits per launch are
$\tau_0(1+\tau_A\tau_L)$; multiply this by the same expected
attempt count. The online classical round trip, local gates, resets,
Bell storage and data idling are additional. The geometric equalities
need the stated conditional stationary success probability; marginal
one-use success alone does not imply them with bath memory.

For an imperfect but data-independent normalized resource $\sigma$,
use the same deterministic protocol. Contractivity under that LOCC map
for every input and reference proves
$$
\frac12\|\mathcal G_\sigma-\operatorname{Ad}_{\rm CS}\|_\diamond
 \le\frac12\|\sigma-\Phi_2\|_1.
\tag{RS26}
$$
Keep available accepted-resource labels and apply the bound to their
flagged corrected state; false heralds belong in that state. The
factory's optical click probability must not replace $s_{\rm Bell}$
without a quality/yield justification.

For example, a known pure monochromatic reflected branch has an
unnormalized two-spin coefficient matrix $M_y$. Its local singular
vector rotations and a Schmidt filter give a Bell pair with yield
$2\sigma_{\min}(M_y)^2$, counted before normalization. This is the
two-qubit instance of pure-state entanglement conversion
([Vidal, Phys. Rev. Lett. **83**, 1046 (1999)](https://doi.org/10.1103/PhysRevLett.83.1046)).
The filter's local meter, readout, herald and failures are real costs.
For a finite unresolved bandwidth the state is instead generally
$\int |f(\omega)|^2|M_y(\omega)\rangle\!\langle M_y(\omega)|d\omega$.
Its average amplitude cannot be inserted into the pure-state formula;
exact filtering at a monochromatic, nonnormalizable limit is not an
exact finite-pulse factory claim.

This architecture adds **two** independently addressable matter
qubits and local data–communication entangling gates. The Daiss
experiment has one qubit atom per cavity; it does not supply this
spare-register architecture automatically. If entanglement is prepared
before data arrival, factory waiting can be moved offline, while Bell
storage remains a cost. With data already present, their coherence
must last through the waiting and online feedback time. Thus this is a
stronger ordinary baseline when the node supplies those resources,
not a measured rate ordering or a two-atom-only simulation.

For a **known resource-state** task there is an additional ordinary
baseline without two extra remote stationary qubits. A Bell pair on
the two output spins can be converted deterministically by LOCC into
$\operatorname{CS}|++\rangle$. Its squared Schmidt coefficients are
$\lambda_\pm=(1\pm1/\sqrt2)/2$. In Schmidt bases, apply the local
POVM
$$
M_0=\operatorname{diag}(\sqrt{\lambda_+},\sqrt{\lambda_-}),\qquad
M_1=\operatorname{diag}(\sqrt{\lambda_-},\sqrt{\lambda_+}).
\tag{RS27}
$$
Each outcome has probability $1/2$ on $\Phi_2$; on outcome one,
$X\otimes X$ gives the same Schmidt state, followed by known local
basis rotations. A local helper or weak meter, readout and feedback
are required for this POVM; it is not a local unitary. Moreover,
$(I\otimes S)X_A\operatorname{CS}^{\dagger}|++\rangle
=\operatorname{CS}|++\rangle$.
This locally Clifford equivalence concerns those known states and does
not correct the inverse-CS gate on an arbitrary unknown input.

A measured ordinary memory-transfer endpoint is supplied by
[Stas et al., Nature **651**, 326–332 (2026), Eqs. (3)–(5)](https://www.nature.com/articles/s41586-026-10171-w).
They combine SiV electron/nuclear registers, photon-mode erasure and
electron heralds to retain a weak optical signal's phase in matter.
To distinguish that endpoint from preserving the flying photon, take
their idealized one-photon circuit, with common reflected amplitude
$\alpha$, early/late input $F$, electron $E$ and initialized nuclear
memory $N$. Its normalized branch before photon erasure is
$|e\rangle\mapsto|e\rangle|\downarrow\rangle_E|+\rangle_N$ and
$|l\rangle\mapsto|l\rangle
(|\downarrow\downarrow\rangle+|\uparrow\uparrow\rangle)_{EN}/\sqrt2$.
A fine erasure bra $w_e\langle e|+w_l\langle l|$, followed by the
electron $\langle-|$ herald, therefore has

$$
K_m=\frac{\alpha}{\sqrt2}H\operatorname{diag}(w_e,w_l),\qquad
p_{m,\rm balanced}=\frac{|\alpha|^2}{2}
                       \min\{|w_e|^2,|w_l|^2\}.
\tag{RS27a}
$$

Direct contraction sends the early/late inputs to
$w_e|+\rangle/\sqrt2,w_l|-\rangle/\sqrt2$. Hence this is an
operator identity on every $FR$. Equal magnitudes give a scalar
known unitary after phase correction. Otherwise a nuclear filter
balances the two singular values to their minimum, proving the
all-attempt weight in (RS27a); its failure, meter and feedback are
paid. This consumes the photon and initialized memory resources; it
does not implement a gate preserving pre-existing unknown $ABF$.
Incident vacuum has electron $|+\rangle$ and is rejected in this ideal
circuit. An input photon lost **after** spin interaction can instead
leave a non-plus electron and falsely herald with local-oscillator
clicks. For unresolved records $\mu$, every corrected $K_{m\mu}$ must
be proportional to the same isometry for an exact storage branch.
The measured phase-ensemble visibility is not a full unknown-input
process certificate. In the two-station experiment, event-ready
memory entanglement permits local signal collection without transporting
that signal between stations. Its preparation, storage and erasure
records are charged ordinary resources; a direct flying-payload
proposal must compare its actual link cost with that option. Neither
the matter-transfer endpoint nor its photon consumption supplies a
nondestructive flying-qubit branch meter for the gate below.

<a id="nr-r11-offline-parity"></a>

### A Bell resource gives a complete ordinary parity instrument

The isolated-factory premise of (RS23) also gives a stronger parity
comparator. Supply communication qubits $a,b$ in
$\Phi^+_{ab}=(|00\rangle+|11\rangle)/\sqrt2$, independent of unknown
$ABR$ and factory records. Apply local CNOTs $A\to a$, $B\to b$,
then $Z$ readouts $u,v$. For computational data $i,j$, the resource bit
$k$ becomes $u=k\mathbin\oplus i$, $v=k\mathbin\oplus j$; exactly one
$k$ contributes when $i\mathbin\oplus j=u\mathbin\oplus v$. Thus

$$
K_{uv}=\frac{\Pi_{u\oplus v}}{\sqrt2}.
\tag{PB1}
$$

This proves the full unknown-input/reference instrument. Coarse graining
the redundant uniform bit gives $\Pi_t\rho\Pi_t$ without learning a
logical value inside that parity sector. All four records are useful.
The protocol consumes one Bell pair, two local CNOTs and two readouts.
One endpoint needs the other endpoint's bit; both can exchange their
bits in one simultaneous classical round. Parity-dependent operations
wait for the actual causal delivery. Under Bell resources and LOCC,
an exact parity instrument can create one ebit from $|++\rangle$ and
therefore requires that net shared entanglement on this input. This
does not exclude direct quantum transmission or flying parity meters.

For a Bell-diagonal accepted resource, retain its correlated weights:

$$
\rho_{ab}=\sum_{x,z}w_{xz}|\beta_{xz}\rangle\!\langle\beta_{xz}|,
\qquad |\beta_{xz}\rangle=(I\otimes X^xZ^z)|\Phi^+\rangle.
\tag{PB2}
$$

Its expansion $\sum_k(-1)^{zk}|k,k\oplus x\rangle/\sqrt2$ and
$k=u\oplus i$ give every fine operator and the reported-parity map:

$$
K_{uv}^{xz}=\frac{(-1)^{zu}}{\sqrt2}
 Z_A^z\Pi_{u\oplus v\oplus x},\qquad
\Gamma_t(\rho)=\sum_{x,z}w_{xz}
 Z_A^z\Pi_{t\oplus x}\rho\Pi_{t\oplus x}Z_A^z.
\tag{PB3}
$$

An $x$ error flips the announced parity; a $z$ error adds a data phase.
The correlation $w_{11}$ is not two independent error rates. Keeping
$u,v$ divides each coarse term into two equal fine records.

Let $\mathcal M_w$ output $AB$ and the actual syndrome, or the full
$u,v$ pair. With ideal local operations, its exact completed-instrument
distance from a perfect-resource $\mathcal M_0$ is

$$
\frac12\|\mathcal M_w-\mathcal M_0\|_\diamond=1-w_{00}.
\tag{PB4}
$$

Convexity and the unit upper bound for channels prove $\le$.
For the lower bound use normalized $\Phi_4$ on $AB:R$. In a common
classical block the error Choi-vector overlaps are proportional to
$\operatorname{Tr}[\Pi_{t\oplus x}Z_A^{z\oplus z'}
\Pi_{t\oplus x'}]$. Distinct $x$ have orthogonal parity support;
equal $x$ and distinct $z$ have zero trace because
$\operatorname{Tr}(Z_A\Pi_t)=0$. Hence the four normalized error Choi
states have mutually orthogonal supports, also with fine records.
Their half trace distance is exactly $1-w_{00}$, attaining the bound.

For an arbitrary resource, CPTP contraction of this fixed circuit instead
gives

$$
\frac12\|\mathcal M_\rho-\mathcal M_0\|_\diamond
 \le\frac12\|\rho-\Phi^+\|_1\le\sqrt{1-F_B}.
\tag{PB5}
$$

A paid bilateral Pauli twirl preserves $F_B$ and makes the averaged
resource Bell diagonal. Its random seed must be discarded for (PB4);
retaining it need not leave conditionally Bell-diagonal resources.
Retained source flags $f$ require the actual conditional corrected state:
if each is Bell diagonal, (PB4) averages to
$\sum_fp_f(1-F_f)$; otherwise (PB5) gives
$\sum_fp_f\sqrt{1-F_f}\le\sqrt{1-F_{\rm average}}$.
The ideal comparator retains the same public flag distribution.
False heralds belong in the accepted resource, not an omitted loss term.

Local gates, readout, frames, reset crosstalk and storage remain paid
ports. Separately certified half-diamond errors $\epsilon_\ell$ give
$\delta_{\rm parity}\le\delta_{\rm resource}+
\sum_\ell\epsilon_\ell$, clipped at one, by telescoping. An average
gate infidelity or prepared-state stabilizer statistic is not one of
these channel certificates. Correlated noise needs a joint bound.
The [architecture comparison](../architecture.md) supplies the physical
baseline context, not a grant of free extra processor qubits or controls.

For stationary independent factory attempts, let $p_B>0$ be qualified
delivery probability and $q_B=1-p_B$. The duration $\tau_B$ includes
source, propagation, herald/timeout, reset and required cooling. If $n$
attempts fit before local readout and required syndrome communication,

$$
a_n=1-q_B^n,\qquad
\mathbb E\min(N,n)=\frac{1-q_B^n}{p_B},\qquad
\mathbb E C_{\rm node}=\frac{2(1-q_B^n)}{p_B},\qquad
\mathbb E C_{\rm CNOT}=\mathbb E C_{\rm read}=2a_n.
\tag{PB6}
$$

The node count is for a two-opportunity factory, not automatically two
occupied interactions per optical amplitude. For identical serial
attempts, $n=\max(0,\lfloor(T-t_{\rm local}-t_{\rm classical})/
\tau_B\rfloor)$; overlapped schedules need their actual event times.
The public attempt count and reject output complete the instrument:

$$
\Gamma_{k,u,v}=p_Bq_B^{k-1}\mathcal M_{uv}^{(k)}\circ\mathcal W_k,
\quad1\le k\le n,\qquad
\Gamma_{\rm reject}=q_B^n\mathcal W_{\rm reject}.
\tag{PB7}
$$

Here $\mathcal W_k$ is the actual TP data-waiting channel, independent
of qualification, and $\mathcal M_{uv}^{(k)}$ includes the delivered
resource's age and local operations. Reject returns the actual stored
data without a parity answer, not a free input reset. Data/factory
crosstalk or shared-bath correlations require joint CP history maps
instead of this factorization. Identical source/storage quality is
needed before replacing the successful part by $a_n$ times one map.
Pipelining, distillation and buffered pre-arrival Bell pairs may improve
the frontier, with their extra interfaces, preparation and storage paid.

Applying the (PF4) parity factory to fresh communication qubits in $++$
gives a perfect Bell pair after accepted detection and its known frame,
with probability $1/4$ in that carrier fixture. After mean four attempts,
(PB1) measures arbitrary data parity without exposing the data to (PF4).
It pays two spare memories, local operations and the full waiting clock.
Thus direct-retry fidelity alone is not an architecture advantage; the
native comparison must beat this resource/deadline frontier with the
same physical isolation, controls and records.

The separate [parity checker](../checks/architecture/parity_failure_baselines.py)
replays the literal vacuum-extended contact composition, all accepted
and loss flags, downstream attenuation and capped logical retries.
Its second API checks the Bell-error/readout instrument once, fine and
coarse Choi orthogonality, mixture weights and capped factory ledgers.
General diamond/recovery proofs and physical continuum, branching,
router, storage and clock premises remain the arguments above; these
finite fixtures establish neither a native optimum nor a hardware rate.

The exact checker replays resonant scattering-kernel normalization,
finite rank-loss examples, the ideal factory and remote-gate Kraus
identities, local controlled-phase synthesis and the resource-state
POVM. It does not fit finite-bandwidth data or verify a native router.
A remaining positive target must specify the real scattering and
record dilation, support arbitrary data/reference input and compare
encoded recovery, ancilla factories, optical loss and complete elapsed
clocks. No native switch advantage is established here.

## Scalar elastic reflections: exact average-concurrence comparison

For the pure reflected sector, retain generic complex dark amplitudes
$\alpha,\beta$ and bright contrasts $\Delta_A,\Delta_B$. In the
native polarization basis,
$$
R_A(a)=\alpha I+a\Delta_A P,\qquad
R_B(b)=\beta I+b\Delta_B Q,\quad a,b\in\{0,1\},
\tag{RS28}
$$
with rank-one photon projectors $P,Q$ and
$|\alpha|,|\alpha+\Delta_A|,|\beta|,|\beta+\Delta_B|\le1$.
Fixed photon wrappers may occur
on both sides of each reflection; they need not be inverse
conjugations. Every selected surviving history visits each module
exactly once. Arbitrary initial route/polarization states, known
photon routing and generalized photon readout are allowed. Spin
preparation is a product, with no preshared matter entanglement or
route-controlled spin-basis interventions. The optical network's
additional modes, controls and clocks must be supplied and charged;
allowing them for an upper bound does not establish a native router.

The metric is concurrence multiplied by each branch's probability,
summed per **launched** model photon. It scores reflected-photon
heralds; no-click states are retained as separate physical outcomes,
and are not declared useless or bounded as entanglement resources by
this result. For a pure unnormalized two-spin coefficient matrix $M$,
its contribution is $2|\det M|$. A generalized detector can be refined
into rank-one branches; forgetting records cannot increase mixed-state
concurrence.

For spin input $++$, the four surviving photon vectors have the
multilinear form
$$
v_{ab}=\alpha\beta w_0+a\beta\Delta_A w_A
 +b\alpha\Delta_B w_B+ab\Delta_A\Delta_B w_{AB}.
\tag{RS29}
$$
The $w$ vectors include the source, router and all known photon
wrappers. They do not depend on the four scalar amplitudes. This
remains true when the dark action of a wrapped station contains a
known nontrivial rotation: expand each station's scalar and contrast
terms before composing the two histories. For a readout bra $m_y$,
put $t_j=\langle m_y|w_j\rangle$ and
$M_y(a,b)=\langle m_y|v_{ab}\rangle/2$. Expansion gives
$$
\det M_y=\frac{D}{4}(t_0t_{AB}-t_At_B),\qquad
D=\alpha\beta\Delta_A\Delta_B.
\tag{RS30}
$$

Replace the scalar module values by
$\alpha=\beta=1$, $\Delta_A=\Delta_B=-2$, while keeping exactly
the same source, wrappers, routing and readout. The native reflections
are now the unitaries $I-2P,I-2Q$. Thus the ideal comparison has
$\sum_y p_y C_y\le\sum_y p_y\le1$, including any optical
postselection. Branchwise, (RS30) scales every determinant by $D/4$
relative to that comparison. Consequently
$$
\sum_y p_y C_y\le\frac{|D|}{4}.
\tag{RS31}
$$
This requires no optimized-switch solver or assumed measurement basis.

More precisely, for a fixed product spin input with coefficients
$u_av_b$, the ideal circuit preserves each spin-basis population
$|u_av_b|^2$. Triangle inequality followed by Cauchy–Schwarz gives
$$
\sum_y2|\det M_y|
\le2\sum_y(|M_{00}M_{11}|+|M_{01}M_{10}|)
\le4|u_0u_1v_0v_1|.
$$
Optical postselection can only reduce the population sums used in this
inequality. The physical bound is therefore
$|D|\,|u_0u_1v_0v_1|$, at most $|D|/4$.
Mixed optical preparations and separable spin preparations follow by
refining their mixtures and using convexity.

An ordinary **two-polarization-mode** bus attains the bound. Use bare
$R_A$, any known intermediate polarization unitary $U$, then bare
$R_B$. For input photon $\chi$ and rank-one output POVM vectors $m_y$,
a two-by-two determinant expansion gives, up to a fixed sign,
$$
\det M_y=\frac{D}{4}\det(U)\,
 \chi_R\chi_L\,m_{y,R}^*m_{y,L}^*.
\tag{RS32}
$$
Hence
$$
\sum_y2|\det M_y|
=\frac{|D|}{2}|\chi_R\chi_L|
 \sum_y|m_{y,R}m_{y,L}|\le\frac{|D|}{4}.
\tag{RS33}
$$
The bounds use $|\chi_R\chi_L|\le1/2$ and POVM completeness plus
Cauchy–Schwarz. A balanced photon and any equatorial projective
polarization readout attain both inequalities; $|\det U|=1$.
For fixed product spin coefficients the same construction attains the
refined bound above. Thus even arbitrary extra order modes do not
improve this metric over the ordinary polarization-only port. This
neither compiles every switched flagged instrument nor proves equality
for every other resource measure. For a diagonal gate Kraus operator,
the same coefficient matrix describes its Choi state in the local
spans $\{|00\rangle,|11\rangle\}$ of each node's input/output
pair, so it also bounds that process-entanglement measure; it is not
a gate-fidelity or all-task simulation statement.

Local feedback and filters cannot evade the average-concurrence
comparison. A local Kraus operator $L$ multiplies $2|\det M|$ by
$|\det L|$, and
$\sum_j|\det L_j|\le\frac12\sum_j\operatorname{Tr}(L_j^\dagger L_j)
\le1$ for a local instrument. Iterate over local rounds and both
nodes, counting filter failures. The determinant and assistance
mechanisms are established tools: see
[Gour, Meyer and Sanders, Phys. Rev. A **72**, 042329 (2005)](https://arxiv.org/pdf/quant-ph/0505091),
whose Theorem 1 treats concurrence of assistance for $2\times2\times n$
pure states, and the related one-sided-channel factorization law of
[Konrad et al., Nature Physics **4**, 99–102 (2008)](https://doi.org/10.1038/nphys885).
The circuit-specific comparison (RS29)–(RS33) is derived here without
a priority claim for those mechanisms.

## A certified narrow Bell-yield interval at the resonant scalar point

A Bell branch has concurrence one, so (RS31) bounds its total
reflected-herald yield. Equality of average concurrence is not equality
of Bell yield: extracting a Bell pair from a nonmaximal pure branch
can lose probability. A stronger ordinary factory closes most of that
possible gap at the resonant scalar values derived from Table S1.

Write the real opposite-phase amplitudes as
$r_{A,0}=-a$, $r_{A,1}=b$, $r_{B,0}=-c$, $r_{B,1}=d$, with all four
letters positive. Prepare the bright probabilities of spins $A,B$ as
$u,v$, and the photon's $R$ probability as $x$. After the first
reflection its photon marginal has trace and determinant
$$
T=a^2+(b^2-a^2)ux,\qquad
h=a^2(a+b)^2u(1-u)x(1-x).
\tag{RS34}
$$
An arbitrary known intermediate photon unitary can give its $R$
population any $z$ with $0\le z\le T$ and $h\le z(T-z)$;
these are precisely the interval between the two eigenvalues of that
marginal. Directly tracing the pure reflected three-qubit state gives
the common trace $P$ and spin-marginal determinants
$$
\begin{aligned}
P&=c^2T+v(d^2-c^2)z,\\
D_A&=h c^2[c^2+v(d^2-c^2)],\\
D_B&=v(1-v)c^2(c+d)^2z(T-z).
\end{aligned}
\tag{RS35}
$$
For example, if $N$ is the first spin–photon coefficient matrix,
$\det(N^\dagger N)=h$. Tracing the second spin inserts the photon
effect $\operatorname{diag}(c^2+v(d^2-c^2),c^2)$ between $N$ and
$N^\dagger$, proving $D_A$. Expanding the second spin's two-by-two
marginal proves $D_B$ and its trace $P$.

For a pure $2\times2\times2$ state, Theorem 1 of
[Pollock, Wang and Chitambar, Phys. Rev. A **103**, 032428 (2021)](https://arxiv.org/abs/2010.11431)
states that helper measurement followed by local filtering can attain
the smaller of the two single-copy Bell-probability cut bounds. Applied
to these **unnormalized** marginals, the attainable yield is exactly
$$
Y=P-\sqrt{P^2-4\min(D_A,D_B)}.
\tag{RS36}
$$
This invocation requires a pure scalar reflected state and the
prescribed helper measurement and local Schmidt filters. Their local
meters or ancillas, feedforward and failed branches are charged. The
three-qubit theorem alone does not establish the analogous formula for
a larger helper. The fixed-marginal argument below proves that extension
when the entire purifying helper is accessible. An arbitrary mixed
finite-bandwidth state with inaccessible records remains outside it.

An exact rational lower witness is
$$
(a,b,c,d)=\left(\frac{21}{25},\frac{2573}{3263},
 \frac57,\frac{647}{827}\right),\quad
u=x=\frac{499457255181911835}{10^{18}},\quad
v=\frac{4135}{8664},\quad z=vT.
$$
The checker verifies with fractions that $h\le z(T-z)$,
$D_A\le D_B$, $P>L$ and
$4\min(D_A,D_B)>2PL-L^2$, where $L=36521957/10^8$.
Since $P-L>0$, squaring proves $Y>L$ in (RS36) without trusting a
floating optimizer or inferring an exact Bell pair from nearly
maximally mixed marginals. The witness explicitly includes local
Schmidt filtering.

At the same scalar point the universal switch upper bound is
$$
C_{\max}=\frac{|r_{A,0}r_{B,0}
 (r_{A,1}-r_{A,0})(r_{B,1}-r_{B,0})|}{4}
=\frac{863246304}{2361188375}.
$$
Thus, writing $Y_{\rm ord}^{\star}$ for the best ordinary factory yield
with these controls, every compared switch satisfies
$$
Y_{\rm sw}-Y_{\rm ord}^{\star}
 <\frac{379}{10^6},\qquad
\frac{Y_{\rm sw}-Y_{\rm ord}^{\star}}{Y_{\rm ord}^{\star}}
 <\frac{13}{12500}=0.104\%.
\tag{RS37}
$$
The second inequality follows from $(C_{\max}-L)/L<13/12500$;
no global ordinary optimizer is needed. These are per-launch bounds
for the scalar elastic/heralded-photon task, before additional
optical losses, not a measured probability or complete-loss-model
advantage. Known spin/source imbalance, the intermediate unitary and
the filters require calibrated amplitudes and controls. The 18-digit
fraction is an arithmetic witness, not a claim of free physical
precision: uncertain amplitudes or preparation need a stated
approximate-Bell tolerance and an error budget. No such robustness
claim is supplied by the exact inequality alone.

## Spectral records and the remaining physical test

If frequency is first resolved or dephased, (RS31) applies pointwise;
tracing unresolved frequency then bounds mixed-state concurrence by
convexity. With a frequency-resolving readout, the ordinary balanced
photon and equatorial polarization measurement attain the corresponding
pointwise average. Frequency resolution, finite bin width, pulse
shaping, control bandwidth and their loss/time costs remain physical
resources. A time-resolved detector instead implements coherent
frequency integrals conditional on its timestamp. It is not the same
instrument as tracing frequency, and an available timestamp cannot be
deleted solely to weaken the ordinary baseline.

There is no universal integral-of-pointwise-contrasts bound for
**coherent** spectral readout. An exact two-mode counterexample makes
this distinction explicit. In spectral mode zero let only $A$ apply
$Z_A$; in mode one let only $B$ apply $Z_B$. Both stations are visited,
and these native controlled operations commute. The pointwise contrast
products vanish in each mode. Yet a balanced coherent spectral input
and its $\pm$ readout give
$$
K_\pm=\frac{Z_A\pm Z_B}{2}.
\tag{RS38}
$$
On $++$ each outcome is a Bell state with probability $1/2$.
Ordinary fixed order already realizes the entire instrument; no switch
advantage is asserted. The example shows why a scalar proof cannot
silently be applied after coherent spectral erasure. It is a minimal
scope guard, not a claim that a particular cavity supplies these ideal
mode selectivities.

## Bell assistance with an arbitrary accessible purifying helper

Let $|\Psi\rangle_{ABF}$ be a pure, possibly unnormalized reflected
state, where $A,B$ are qubits and $F$ contains **every accessible
purifying mode**. Set $\rho=\operatorname{Tr}_F|\Psi\rangle\!\langle\Psi|$,
$p=\operatorname{Tr}\rho\le1$, and let $\rho_A,\rho_B$ be its
unnormalized spin marginals. One generalized measurement on $F$, broadcast
of its outcome, and outcome-dependent local spin filters and unitaries
can produce a known exact Bell pair with maximum joint probability
$$
Y(\rho)=2\min\{\lambda_{\min}(\rho_A),
                    \lambda_{\min}(\rho_B)\}.
\tag{RS39}
$$
All normalization and reflection weights are inside $\rho$: the yield
per reflected photon is $Y/p$ when $p>0$, and $Y=0$ when $p=0$.
Filter failures and all other rejected launches are counted. This is a
resource-factory statement, not an unknown-input remote-gate compiler.

Here is a proof for arbitrary helper dimension, rather than an invocation
of the three-qubit theorem beyond its domain. For an unnormalized pure
two-qubit vector $v$, the optimal exact Bell-conversion weight is
$e_2(v)=2\lambda_{\min}(\operatorname{Tr}_B|v\rangle\!\langle v|)$.
If its Schmidt weights are $\lambda_+\ge\lambda_-$, a local filter
attenuating the larger Schmidt amplitude gives Bell success $2\lambda_-$.
Optimality follows from the smaller-Schmidt-weight monotone; see
[Vidal, Phys. Rev. Lett. **83**, 1046 (1999)](https://doi.org/10.1103/PhysRevLett.83.1046).
Refining a helper measurement gives a pure ensemble of $\rho$, and
every such ensemble is realizable on a purification by the
[Hughston–Jozsa–Wootters theorem, Phys. Lett. A **183**, 14–18 (1993)](https://doi.org/10.1016/0375-9601(93)90880-9).
Thus the optimization is
$\max_{\rho=\sum_k v_kv_k^\dagger}\sum_k e_2(v_k)$.
For positive matrices $X_k$,
$\sum_k\lambda_{\min}(X_k)\le\lambda_{\min}(\sum_kX_k)$.
Apply this to both marginal ensembles to obtain the upper bound (RS39).
Equivalently, the two qubit-versus-rest cut monotones bound even general
LOCC collaboration, not just the helper-first protocol used for attainment.

For the matching lower bound normalize $\rho$ to trace one. If its rank
is $r\ge3$, Hermitian operators supported on its range form a real
space of dimension $r^2\ge9$. The map
$X\mapsto(\operatorname{Tr}_B X,\operatorname{Tr}_A X)$ has image
dimension at most $4+4-1=7$, because its two traces agree. There is
therefore a nonzero supported Hermitian $X$ with both partial traces zero.
It is traceless and indefinite. Positivity of $\rho$ on its support
makes $\{t:\rho+tX\succeq0\}$ a bounded closed interval
$[t_-,t_+]$, with $t_-<0<t_+$. Both endpoint states lose rank and keep
both marginals, and
$$
\rho=\frac{-t_-}{t_+-t_-}(\rho+t_+X)
      +\frac{t_+}{t_+-t_-}(\rho+t_-X).
\tag{RS40}
$$
Each endpoint would remain positive beyond the endpoint if it were still
full rank on the old support, proving the rank drop. Starting from rank
at most four, at most two splits along each branch give at most four
rank-at-most-two states $\sigma_j$, all with the **same two marginal
matrices** as $\rho$. This is the elementary two-qubit fixed-marginal
rank argument underlying the extremal-rank bound in
[Parthasarathy, Ann. Inst. H. Poincaré Probab. Statist. **41**, 257–268 (2005), Theorem 2.5](https://www.numdam.org/article/AIHPB_2005__41_3_257_0.pdf).

For each $\sigma_j$, [Pollock–Wang–Chitambar's rank-two theorem and its
proof](https://arxiv.org/html/2010.11431v2) supply
an ensemble of at most two pure vectors whose total Bell yield is the
right side of (RS39). That value is the same for every $j$, precisely
because (RS40) preserved both marginals. Combining their weighted
ensembles gives at most eight vectors of $\rho$ with that yield. HJW
implements this ensemble by one measurement on the original $F$; it
need not physically realize the intermediate mixed-state decomposition.
Then apply each vector's optimal local filter. This proves (RS39),
including its unnormalized form. The extension is a derived combination
of the cited fixed-marginal and rank-two results; no priority claim is
made for that combination.

The eight rank-one helper effects sum to the identity **on the occupied
Schmidt support**, whose dimension is at most four. On a larger or
infinite $F$, add the zero-probability complementary effect, giving at
most nine total effects, or absorb that complement into an old effect,
which then need not be rank one on the full space. Eight counts nonzero
helper outcomes, not later filter success/failure leaves. A general POVM
may require additional analyzer modes or a local Naimark ancilla. Knowing
the two marginals gives the optimum value, not the calibrated optical
mode functions needed to implement it.

In particular,
$$
Y=p\quad\Longleftrightarrow\quad
\rho_A=\rho_B=\frac p2 I.
\tag{RS41}
$$
Sufficiency also has a direct construction. A normalized two-qubit state
with these marginals is
$(I\otimes I+\sum_{ij}T_{ij}\sigma_i\otimes\sigma_j)/4$, with real
$T$. A real singular-value decomposition, absorbing reflection signs
into its diagonal, is implemented by proper rotations from local spin
unitaries. It makes the state Bell diagonal. Its Bell eigenensemble is
obtained by measuring the corresponding orthonormal Schmidt modes of any
purification. At most four nonzero projective helper outcomes suffice
in this special case; known local corrections fix the Bell frame, and
no lossy local filter is needed. This does not say that an unmeasured
spin marginal is a pure Bell state.

Purity and full access are essential. An inaccessible source mixture,
motion, recoil, weak-pulse extra photons or bath records can make $ABF$
mixed. For example, $I_{AB}/4$ independent of $F$ has both marginals
maximally mixed but no helper-created entanglement. A bucket detector or
a restricted polarization/time-bin readout also need not realize the
optimal coherent mode POVM. In either case (RS39)'s marginal expression
remains a cut upper bound; the attainment claim does not apply.

## Exact reduction of the pure finite-pulse optimization

For a normalized incident spectral amplitude $f(\nu)$, write a pure
elastic reflected state as
$$
|\Psi\rangle=\sum_{ab}c_{ab}|ab\rangle
       \int d\nu\, f(\nu)|v_{ab}(\nu),\nu\rangle_F,
\qquad
\rho_{ab,a'b'}=c_{ab}c_{a'b'}^*
 \int d\nu\,|f(\nu)|^2
    \langle v_{a'b'}(\nu)|v_{ab}(\nu)\rangle.
\tag{RS42}
$$
The helper can contain polarization, frequency, temporal and orthogonal
order modes. Despite its infinite dimension, the spin Gram matrix has
rank at most four, so (RS39) applies. For an ordinary $AB$ route,
$v_{ab}(\nu)=R_{B,b}(\nu)U(\nu)R_{A,a}(\nu)\chi(\nu)$.
Only the two integrated two-by-two marginals are needed to evaluate the
optimal helper/filter yield. No average-amplitude replacement is made.

For fixed $\rho$, this has the exact small SDP and dual
$$
\begin{aligned}
Y&=\max_y\{y:\rho_A-\tfrac y2I\succeq0,
                    \ \rho_B-\tfrac y2I\succeq0\}\\
 &=\min_{Y_A,Y_B\succeq0,\ \operatorname{Tr}Y_A+
             \operatorname{Tr}Y_B=1}
  2\operatorname{Tr}(Y_A\rho_A)+2\operatorname{Tr}(Y_B\rho_B).
\end{aligned}
\tag{RS43}
$$
The projector onto the smaller marginal eigenvalue on the limiting side,
and zero on the other side, attains the dual. For a qubit marginal
$\rho_j=(pI+\mathbf r_j\cdot\boldsymbol\sigma)/2$, this is equivalently
$Y=p-\max_j\|\mathbf r_j\|$. An affine source search is an attainable
SDP only if every feasible source setting still gives a pure or
accessibly purified $ABF$ state. Coherently prepared spectral intensities
can meet that premise; an uncontrolled classical source mixture cannot
be substituted as though its inaccessible label were a free helper.
Spin preparations and optical-unitary choices can leave a nonconvex
outer optimization, and floating grids do not certify its optimum.

The same reduction supplies a strong switch comparator without searching
over every helper POVM. At fixed source and optical controls, let its
pure state be
$\sqrt w|0\rangle_C|\psi_{AB}\rangle+
e^{i\varphi}\sqrt{1-w}|1\rangle_C|\psi_{BA}\rangle$.
Tracing the orthogonal order labels gives
$\rho_j(w)=w\rho_j^{AB}+(1-w)\rho_j^{BA}$ for each spin.
Consequently its optimum full-helper Bell yield is a one-dimensional
concave function $p(w)-\max_j\|\mathbf r_j(w)\|$, or a small
second-order-cone optimization in $w\in[0,1]$. A known relative phase
$\varphi$ is a local unitary on the helper and does not change that
optimum. The interior can exceed both endpoint yields: it retains a
coherent purifying order label, while an ordinary classical lottery only
gives the average of its branch yields. This is a comparison method,
not an ordinary domination theorem or a native advantage claim.

## A validated ordinary Gaussian-pulse Bell yield

An explicit normalizable finite-bandwidth example uses the pure
one-photon elastic model (RS19), the reported Table S1 rates, and only
an ordinary $AB$ route with frequency-independent real controls. Let
$\nu=(\omega-\omega_0)/(2\pi)$ in MHz and express each amplitude
decay rate in the same units, so the common $2\pi$ cancels. Define
$$
r_{j,a}(\nu)=1-
 \frac{2\kappa_{r,j}(\gamma_j-i\nu)}
 { (\kappa_j-i\nu)(\gamma_j-i\nu)+a g_j^2},\qquad
R_{j,a}(\nu)=\operatorname{diag}(r_{j,a}(\nu),r_{j,0}(\nu)),
\tag{RS44}
$$
with $a=1$ bright and $a=0$ dark. The exact parameter tuples
$(g,\kappa,\kappa_r,\gamma)$ are
$(38/5,5/2,23/10,3)$ for $A$ and
$(38/5,14/5,12/5,3)$ for $B$, in MHz. These are the parameter-model
values cited above, not new measured yields or a model of all cavity
imperfections.

Prepare each spin as $\cos\alpha_j|0\rangle+\sin\alpha_j|1\rangle$,
the photon polarization as
$\chi=(\cos\chi_0,\sin\chi_0)^{\mathsf T}$, and between the two
reflections apply
$U_\theta=\begin{pmatrix}\cos\theta&\sin\theta\\-
\sin\theta&\cos\theta\end{pmatrix}$.
The exact angles in radians and incident spectral intensity are
$$
\begin{gathered}
(\alpha_A,\alpha_B,\chi_0,\theta)=\frac1{10^{16}}
(8005482133044127,7631314280924895,
 7885503202769666,31166396848875224),\qquad
\sigma=\frac{11993}{64000}\ \mathrm{MHz},\\
|f(\nu)|^2=\frac{e^{-\nu^2/(2\sigma^2)}}{\sqrt{2\pi}\sigma}.
\end{gathered}
\tag{RS45}
$$
The eight components of the complete spin–polarization vector are
$w_{ab,\ell}(\nu)=
 (\cos\alpha_A,\sin\alpha_A)_a
 (\cos\alpha_B,\sin\alpha_B)_b
 [R_{B,b}(\nu)U_\theta R_{A,a}(\nu)\chi]_\ell$.
The Gaussian intensity FWHM in time is
$\sqrt{2\ln2}/(2\pi\sigma)$, approximately $1\,\mu\mathrm s$;
it is not a compact temporal support or a complete protocol clock.

The [continuum interval checker](../checks/architecture/verify_remote_spin_pulse.py)
proves, with rational outward rounding and an analytic integration error,
$$
0.36675027396793<p<0.36675027396795,
\qquad
Y_{\mathrm{ord}}>\frac{36675027}{10^8}=0.36675027
\quad\text{per launched photon}.
\tag{RS46}
$$
It bounds every integrated $X,Z$ Bloch component in absolute value by
$2\times10^{-15}$. All preparations and optics are real and
$r(-\nu)=r(\nu)^*$, so $w(-\nu)=w(\nu)^*$.
The integrated spin $Y$ components are exactly zero by oddness. The
last inequality follows from (RS43), using
$\|(r_x,0,r_z)\|\le |r_x|+|r_z|$ and the certified lower bound on
$p$. It does **not** infer exact Bell states from nearly mixed
marginals: the arbitrary-helper theorem and its outcome-dependent
Schmidt filters supply exact Bell states and include filter rejection.
No exact locally-maximally-mixed root or numerical optimizer is assumed.

For completeness, the continuum error used in this replay has a direct
bound. Put $G(z)=e^{-z^2/(2\sigma^2)}$ and use the analytic strip
$|\operatorname{Im}z|\le a=1/10$ MHz. Equation (RS44) is analytic
there, because
$$
\operatorname{Re}\!\left(\kappa_j-iz+
              \frac{a' g_j^2}{\gamma_j-iz}\right)
 \ge\kappa_j-\frac1{10}>0\qquad(a'\in\{0,1\}).
$$
It also gives $|r_{j,a'}(z)|\le1+2\kappa_{r,j}/(\kappa_j-1/10)<3$
for both stations. The two-reflection vector therefore has
$\|w(z)\|\le9$ throughout the strip, as does $w(-z)$.
For $O=I,Z_A,X_A,Z_B,X_B$ the continuation of the real-frequency
kernel is $w(-z)^{\mathsf T}O w(z)$, of absolute value at most $81$.
This treats the conjugate factor analytically, rather than treating a
nonanalytic $|r(z)|^2$ as holomorphic. The normalization kernel $1$
satisfies the same loose bound.

On **each** boundary, the absolute integral of a Gaussian-weighted
kernel is at most
$81e^{a^2/(2\sigma^2)}\sqrt{2\pi}\sigma<243$.
Indeed $0.18<\sigma<0.19$, $\pi<4$ give
$\sqrt{2\pi}\sigma<1$, and $a^2/(2\sigma^2)<1$ with $e<3$.
Contour shifting, or equivalently applying the Poisson formula and
bounding each nonzero Fourier mode by the appropriate boundary integral,
gives infinite trapezoid error at spacing $h=1/100$ MHz bounded by
$$
\frac{243+243}{e^{2\pi a/h}-1}
 <\frac{486}{2^{60}-1}.
\tag{RS47}
$$
Here $2\pi a/h=20\pi>60>60\ln2$, using $\pi>3$ and
$\ln2<1$; no decimal approximation to that exponential is trusted.

The finite sum keeps the 601 nodes $kh$, $-300\le k\le300$.
On the real axis the reflection is contractive: writing its denominator
as $d=\kappa-i\nu+a'g^2/(\gamma-i\nu)$ gives
$\operatorname{Re}d\ge\kappa\ge\kappa_r$ and hence
$|1-2\kappa_r/d|\le1$. Thus every real kernel above has absolute
value at most one. Beyond $3$ MHz the Gaussian is less than $2^{-113}$,
since $9/(2\sigma^2)>113$ and $e>2$. The ratio of successive omitted
node weights is less than $2/3$: its exponent is at least
$601h^2/(2\sigma^2)>1/2$, and $e^{1/2}>3/2$.
The omitted **discrete** two-sided tail is consequently less than
$2h\,2^{-113}/(1-2/3)<2^{-100}$. Combined with (RS47), the uniform
absolute error for each unnormalized integral is
$E=486/(2^{60}-1)+2^{-100}$.

The replay encloses the finite sums on a $10^{-28}$ rational grid with
outward rounding for every operation. Sine/cosine and the Gaussian use
40-term alternating Taylor sums with the first omitted term as an error
bound; for $e^{-x}$ it first reduces $0\le x<256$ by $256$ and
squares eight times. All Gaussian nodes and reflection real/imaginary
parts are rational. It widens the normalization integral and every
numerator by $E$, proves the normalization interval is positive, and
only then divides intervals. Positive-frequency doubling is justified
by the real-control conjugation symmetry above. These steps certify the
continuum inequalities, rather than interpreting agreement between
quadrature cutoffs as a proof.

## Four modes saturate the fixed coherent ordinary bus

The larger optical-control comparison can be reduced exactly, with a
stronger port assumption than polarization alone. Fix normalized product
spin amplitudes $a=(a_0,a_1)^{\mathsf T}$ and
$b=(b_0,b_1)^{\mathsf T}$, a pure factorized incident pulse
$f(\nu)\phi$, and strictly chronological $A$ then $B$. Both stations
preserve four photon modes and have scalar responses
$A_a(\nu)=\alpha(\nu)I+a\delta(\nu)P_A$ and
$B_b(\nu)=\beta(\nu)I+b\epsilon(\nu)P_B$, where $P_A,P_B$ are
known frequency-independent rank-two bright projectors. This includes
(RS44) with a second preserved photon degree of freedom. Known
frequency-independent photon rotations before, between and after the
encounters are allowed. There is no inter-encounter measurement,
postselected filter, recorded feedforward, adaptive spin preparation or
extra device call. After both encounters, allow the full purifying-helper
readout and local spin filters of (RS39).

In this class, all source and intermediate optical controls reduce to
five real variables: $x\in[0,1]$ and a Hermitian two-by-two $Y$ obeying
$0\preceq Y\preceq D_x=\operatorname{diag}(x,1-x)$.
To prove necessity, absorb the source optics into $\phi$, put
$x=\|P_A\phi\|^2$, and for $0<x<1$ choose
$e_0=P_A\phi/\sqrt x$, $e_1=(I-P_A)\phi/\sqrt{1-x}$.
These are orthonormal and independent of frequency. At an endpoint
complete the occupied source direction with any unused vector in the
appropriate bright or dark sector. In this basis the first-encounter
photon coefficient rows and their spin marginal are
$$
\begin{gathered}
N(\nu)=\begin{pmatrix}
a_0\alpha(\nu)&a_0\alpha(\nu)\\
a_1[\alpha(\nu)+\delta(\nu)]&a_1\alpha(\nu)
\end{pmatrix},\qquad S_x=\sqrt{D_x},\qquad T(\nu)=N(\nu)D_xN(\nu)^\dagger,\\
Q=U^\dagger P_B U,\qquad K_{ij}=\langle e_i|Q|e_j\rangle,
\qquad Y=S_xK^{\mathsf T}S_x,\qquad
X(\nu)=N(\nu)YN(\nu)^\dagger.
\end{gathered}
\tag{RS48}
$$
Here $U$ is the intermediate photon unitary; a terminal $U^\dagger$
can be absorbed in the helper measurement. The compression satisfies
$0\preceq K\preceq I$, so $0\preceq Y\preceq D_x$.
The transpose is required by the row convention: the selected spin
matrix entry is $\langle h_{a'}|Q|h_a\rangle$.
It cannot be dropped for a complex compression. The same $Y$ applies
at every frequency because the pre-$B$ photon vectors always lie in the
fixed span of $P_A\phi$ and $(I-P_A)\phi$.

Put
$h_0(\nu)=\beta(\nu)(b_0,b_1)^{\mathsf T}$ and
$h_1(\nu)=(\beta(\nu)b_0,[\beta(\nu)+\epsilon(\nu)]b_1)^{\mathsf T}$.
Tracing the orthogonal $Q$ and $I-Q$ photon sectors gives the exact
unnormalized spin state
$$
\rho_{AB}(x,Y)=\int d\nu\,|f(\nu)|^2
\left\{N(D_x-Y)N^\dagger\otimes h_0h_0^\dagger
             +NYN^\dagger\otimes h_1h_1^\dagger\right\}.
\tag{RS49}
$$
Every frequency-dependent factor remains inside this integral; it is
affine in $x,Y$. Pointwise first-encounter Schmidt weights are the
eigenvalues of $T(\nu)$, while those of the entire pulse are the
eigenvalues of $\int|f|^2T(\nu)d\nu$. These operations cannot be
interchanged. In particular, pointwise rank one at $x=1$ does not
exclude spin–frequency entanglement of the full pulse.

Conversely every feasible $x,Y$ is attained with four preserved photon
modes and one constant $U$. On the occupied source support set
$K=(S_x^+YS_x^+)^{\mathsf T}$ and extend by zero on an unused direction.
The inequalities on $Y$ force its off-support entries to vanish, so this
also handles $x=0,1$ without inverting a zero amplitude. Then
$0\preceq K\preceq I$, and commuting positive square roots give
$$
V_K=\begin{pmatrix}\sqrt K&-\sqrt{I-K}\\
                    \sqrt{I-K}&\sqrt K\end{pmatrix},\qquad
Q_K=V_K\begin{pmatrix}I_2&0\\0&0\end{pmatrix}V_K^\dagger
=\begin{pmatrix}K&\sqrt{K(I-K)}\\
                 \sqrt{K(I-K)}&I-K\end{pmatrix}.
\tag{RS50}
$$
$V_K$ is unitary and $Q_K$ is a rank-two projector with compression $K$.
In the physical basis whose first two vectors are $e_0,e_1$, any native
rank-two $P_B$ is unitarily equivalent to $Q_K$. Thus a known constant
$U(4)$ realizes $U^\dagger P_BU=Q_K$. Prepare the pure source
$\sqrt x e_0+\sqrt{1-x}e_1$. This realizes (RS49) at every frequency
with the same source and unitary, including singular effects.

This proves saturation of any larger coherent photonic program space
in this class. A larger pure source still populates only the same two
source directions before $B$; only a positive two-by-two compression
enters (RS49), and (RS50) already realizes every such compression.
It is not necessary to assign an uncontrolled source mixture or a new
physical ancilla to each feasible point.

Let $L_A=\operatorname{Tr}_B\rho_{AB}$ and
$L_B=\operatorname{Tr}_A\rho_{AB}$. By (RS39), the exact fixed-spin,
fixed-pulse optical-control optimum in this class is the small SDP
$$
\begin{aligned}
\max_{x,Y,z}\quad &z\\
\text{subject to}\quad&0\le x\le1,\quad
 0\preceq Y\preceq\operatorname{diag}(x,1-x),\\
&L_A(x,Y)-\tfrac z2 I\succeq0,\qquad
 L_B(x,Y)-\tfrac z2 I\succeq0.
\end{aligned}
\tag{RS51}
$$
There are five real optical-control variables plus the scalar objective.
Every primal optical point has the pure four-mode realization above;
(RS39) supplies its terminal POVM and local filters. Exact integral
coefficients and feasible primal/dual witnesses can certify values;
unvalidated quadrature and floating solver output cannot. The reverse
definite order follows by exchanging the stations. Spin populations,
pulse shape and response functions remain separate outer choices.

This is not an upper bound for all ordinary protocols. Intermediate
spin measurement or filtering with a retained flag can steer the photon
and adapt later optics or the second spin's preparation. Other valid
ordinary comparisons include photon instruments, extra calls, ancillary
memories and frequency-dependent or frequency-converting controls.
A factorized source and a fixed $U$ cannot be replaced by independent
$Y(\nu)$ without supplying that additional interface. Stronger ordinary
strategies can only raise the benchmark. The four-mode station ports,
coherent mode readout and clocks remain the paid assumptions discussed
after (RS8), not consequences of the mathematical reduction.

## An eigenstate source has an exact reverse-order survivor compiler

A useful subset permits equality of complete conditional quantum outputs,
with no optimization over their Bell yield. Let $P,Q$ be known rank-one
polarization bright projectors. For each spin label use
$A_a=\alpha I+a\delta P$, $B_b=\beta I+b\epsilon Q$, allowing all four
scalar functions to depend on frequency. With a pure order control
$|c\rangle=c_0|0\rangle+c_1|1\rangle$ and source polarization $\psi$,
the switch's surviving photon vector at spin label $ab$ is
$$
\begin{gathered}
v_{ab}=\alpha\beta x+a\delta\beta y+
                 b\alpha\epsilon z+ab\delta\epsilon w,\\
x=|c\rangle\psi,\quad y=|c\rangle P\psi,\quad
z=|c\rangle Q\psi,\quad
w=c_0|0\rangle QP\psi+c_1|1\rangle PQ\psi.
\end{gathered}
\tag{RS52}
$$
The $C=0$ history is $BA$ and $C=1$ is $AB$.

Suppose first that $P\psi=\psi$. Then $y=x$ and
$z-w=c_1|1\rangle(I-P)Q\psi$ is orthogonal to both $x$ and $w$.
Choose a rank-two projector $P'$ on the four photon modes whose range
contains $\operatorname{span}\{x,w\}$ and whose kernel contains
$z-w$. Such a projector exists: the first span has dimension at most
two and is orthogonal to the excluded vector; pad its range in the
remaining orthogonal directions if needed. With $Q'=I_C\otimes Q$,
$$
P'x=x,
\qquad Q'x=z,
\qquad P'Q'x=P'z=w.
\tag{RS53}
$$
The strictly chronological reverse word $B(Q')$ then $A(P')$ has the
same four polynomial coefficients in (RS52), hence the same surviving
vector $v_{ab}$ for every $ab$ and every complex
$\alpha,\beta,\delta,\epsilon$.

If $P\psi=0$, then $y=0$ and
$w=c_1|1\rangle PQ\psi$ is orthogonal to both $x$ and $z-w$.
Choose a rank-two $P'$ containing $w$ and excluding
$\operatorname{span}\{x,z-w\}$. Its orthogonal complement has dimension
at least two, so padding is again possible. Now $P'x=0$, $Q'x=z$ and
$P'Q'x=w$, proving the same reverse-word identity. Exchanging the
stations and relabelling the two order-control states gives the
forward-word construction for a $Q$-eigenstate source.
The usual plus-polarization source with an $X$-axis bright projector in
(RS1) is in this eigenstate class.

Both $P'$ and $Q'$ have rank two, so known four-mode conjugating optics
implement them with one encounter at each native station. The compiler
depends on the known projectors and source, **not** the reflection
coefficients. It therefore holds pointwise for arbitrary calibrated or
unknown scalar spectral functions in the stated two-eigenvalue model.
Multiplying by any common incident pulse and retaining the frequency
register preserves equality of the entire coherent surviving linear operator.
Linearity in the four spin basis labels proves equality for arbitrary
unknown $ABR$ inputs and every terminal photon measurement, including
coherent spectral readout and its conditional spin outputs.

This is survivor equality in the declared four-preserved-mode interface.
The reverse route must realize the same station responses; direction,
phase and temporal access cannot be changed silently. Optical wrappers,
propagation, storage and readout need their actual losses and duration.
Physical spontaneous-emission, lost-route and no-click records are not
identified by (RS52)–(RS53), so this is not a complete-erasure or harmless
retry theorem. The separate all-loss comparison (RS10)–(RS18) retains
its narrower erasure-dilation assumptions. For an ideal deterministic
diagonal gate, (RS7)–(RS8) already provide the stronger endpoint check
under four-mode ports; no additional remote query or nonlinear
interaction between independent photons is hidden in that readout.

## Exact accepted diagonal-gate instruments and local phase corrections

The gate task can be tested directly on unknown data, instead of
optimizing a known-state factory. Index spin labels by $j=00,01,10,11$.
Let $v_j$ be the pure surviving photon vector, including every accessible
frequency, path and polarization mode, for that label. Use the
**Kraus covariance**
$G_{jk}=\langle v_k|v_j\rangle$, so tracing the photon multiplies
the spin matrix unit $|j\rangle\!\langle k|$ by $G_{jk}$.
This is the transpose of the conventional column Gram $V^\dagger V$.
For a photon readout with diagonal spin Kraus vectors $k_m$,
$G=\sum_m k_mk_m^\dagger$. Equivalently $G=4\rho_{++}$ for the
unnormalized output of the same channel on the dummy input $++$.
That identity computes the channel; it does not reset or prepare the
unknown payload. No normalization by reflected-photon probability is made.
Accepted flags in this section require a surviving reflected carrier;
physical no-click outcomes are not accepted by this model.

For continuous local $Z$ phases define
$q(\theta_A,\theta_B)=(1,e^{i\theta_B},e^{i\theta_A},
e^{i(\theta_A+\theta_B)})^{\mathsf T}$.
Their conic covariance hull $\mathcal K$ has the exact description
$$
\begin{gathered}
\Omega\succeq0,\qquad \Omega^{T_B}\succeq0,\qquad
\operatorname{diag}\Omega=p(1,1,1,1),\\
\Omega_{01}=\Omega_{23},\qquad \Omega_{02}=\Omega_{13},
\qquad p=\frac{\operatorname{Tr}\Omega}{4},
\qquad
\mathcal K=\left\{\sum_r w_r q_rq_r^\dagger:w_r\ge0\right\}.
\end{gathered}
\tag{RS54}
$$
The two equalities are complex, with zero-based indices. Necessity
follows from each product phase vector. For sufficiency, when $p>0$,
$\Omega/(4p)$ is a two-qubit PPT state and therefore separable by
[Horodecki, Horodecki and Horodecki, Phys. Lett. A **223**, 1–8 (1996)](https://arxiv.org/abs/quant-ph/9605038).
The linear equalities in (RS54) remove every Pauli coefficient containing
$Z$, leaving the nine-dimensional real space
$\mathcal E=\operatorname{span}\{I,X,Y\}^{\otimes2}$.
In a separable product decomposition, project each local Bloch vector
onto its $XY$ disk. This leaves $\Omega$ unchanged, and each disk state
is a mixture of pure equatorial states. This is a decomposition argument,
not an assumed physical flattening channel. It gives the asserted phase
vectors; at $p=0$ positivity forces $\Omega=0$. At most nine phase
atoms suffice per flag by Carathéodory in the normalized eight-dimensional
affine hull. The reflected positive remainder needs at most four
rank-one vectors on the occupied helper support, with a zero-probability
complement effect if the full helper is larger. These counts exclude
physical loss records. Four Pauli masks alone do not describe this cone.

Fix the accepted flag dictionary **before** optimization: flag $\ell$
is the known diagonal unitary $U_\ell=D_{u_\ell}$, with
$|u_{\ell,j}|=1$. With arbitrary terminal photon measurement and only
output local phase corrections, the exact accepted maps
$p_\ell\operatorname{Ad}_{U_\ell}$ are achievable if and only if
$$
G-\sum_\ell D_{u_\ell}\Omega_\ell D_{u_\ell}^\dagger\succeq0,
\qquad \Omega_\ell\in\mathcal K,
\qquad\operatorname{diag}\Omega_\ell=p_\ell(1,1,1,1).
\tag{RS55}
$$
For necessity, a successful corrected unitary channel has rank-one
Choi matrix, so every hidden corrected success Kraus operator is a
scalar multiple of $U_\ell$. Before its inverse local phase correction,
its vector is a scalar multiple of $D_{u_\ell}q_r$. These vectors sum
to the displayed covariances; the other photon outcomes add a positive
remainder. For sufficiency, decompose every $\Omega_\ell$ into phase
atoms and the positive remainder into vectors. Together they factor
the actual $G$. The same purification/ensemble correspondence used in
(RS39) realizes these vectors by a POVM on the pure accessible photon
program. Applying each inverse local phase gives exactly the prescribed
diagonal Kraus operators. Equality on all spin matrix units proves
the maps on every unknown $ABR$. The success probability is the
input-independent $\sum_\ell p_\ell$ per launch, including reflection
and readout rejection. Prescribed relative weights require the additional
constraints $p_\ell=r_\ell p$; they must not be optimized away.
In particular, $\operatorname{CS}$ and $\operatorname{CS}^\dagger$
are different unknown-input gates, not one target related by a free
output local phase.

The positive remainder supplies rejected **reflected** readout maps.
Physical no-reflection spin states and emission records require their
actual dilation and are not determined by this covariance. Counting
their probability as failure does not make an unknown rejected payload
repairable or justify repeat-until-success. An inaccessible source
mixture also invalidates the attainment proof; a classical lottery
between orders cannot be given a coherent cross-order purifier by merely
summing its Gram matrices. Such a lottery has separate readout constraints
for each order and shared launch probabilities. An aggregated covariance
can be used as an upper relaxation only when that additional access has
not been physically supplied.

For a single uncorrected target branch the specialization is
$$
G-puu^\dagger\succeq0,
\qquad
p_{\max}=\frac1{u^\dagger G^+u}\quad
\text{if }u\in\operatorname{ran}G;
\qquad p_{\max}=0\text{ otherwise}.
\tag{RS56}
$$
The range condition also holds for every refined phase vector in (RS55).
It matters for rank-deficient programs and cannot be replaced by a
finite Pauli-only test. A genuinely complex covariance must not be
transposed while keeping the target vectors unchanged.

There are simple exact upper witnesses, independent of a solver's status.
For a weighted accepted payoff $\sum_\ell w_\ell p_\ell$, let $Z\succeq0$
and, for each flag, give a decomposition
$$
D_{u_\ell}^\dagger ZD_{u_\ell}-\frac{w_\ell}{4}I
 =A_\ell+(B_\ell)^{T_B}+W_\ell,
\qquad A_\ell,B_\ell\succeq0,\quad W_\ell\perp\mathcal E.
\tag{RS57}
$$
Taking traces against $\Omega_\ell$ in (RS54) and then using the
positive remainder in (RS55) proves
$\sum_\ell w_\ell p_\ell\le\operatorname{Tr}(ZG)$.
For total unitary yield, $Z=|00\rangle\!\langle00|$ and
$W=Z-I/4\perp\mathcal E$ give
$\sum p_\ell\le G_{00}$, precisely the dark–dark witness in (RS8a).
No claimed numerical optimizer or small eigenvalue tolerance enters
this weak-duality proof.

Substituting $G(x,Y)=4\rho_{++}(x,Y)$ from (RS49) into (RS55) yields
an exact finite SDP over all source, constant four-mode optics, terminal
readout and local phase feedback in that declared coherent-bus class.
The dummy spin preparation is fixed, so there is no gate-task outer
optimization over data populations. Both chronological words remain
ordinary comparisons. Extra intermediate data controls, encodings,
memories, bypass paths, local nonunitary filters and different temporal
or spectral interfaces are not upper-bounded by this restricted SDP.
Their availability and costs must be included in a practical comparison.

## Eight preserved modes attain two independent coherent-order programs

The two ordinary moment cones can be combined exactly in a stronger
**decorated** coherent-order interface. Let $F$ be a four-dimensional
photon program space and $C$ a distinct order qubit: eight actual
preserved photon modes are supplied. At station $j=A,B$, assume the
same native spin-controlled reflected operator in both visit windows,

$$
\mathsf R_j(\nu)=\sum_{s=0}^1|s\rangle\!\langle s|_j\otimes
 [\alpha_j(\nu)I_F+s\delta_j(\nu)\Pi_j],
\qquad \operatorname{rank}\Pi_j=\operatorname{rank}(I-\Pi_j)=2.
\tag{RS58}
$$

All scalar response functions are common to the two order arms.
They are not independent design variables. For each arm $o$, known
frequency-independent photon wrappers $V_{j,o}$ can realize any
rank-two $P_{j,o}=V_{j,o}^\dagger\Pi_jV_{j,o}$. Indeed conjugating
$\mathsf R_j$ by $I_j\otimes V_{j,o}$ gives exactly
$\sum_s|s\rangle\langle s|_j\otimes
[\alpha_jI_F+s\delta_jP_{j,o}]$. This is an operator identity on
unknown spin/reference inputs. It neither replaces the unknown
spin interaction by a known photon matrix nor controls a copied spin.
The branch-dependent known optics are additional controls around the
same physical scattering slot, not part of a bare four-mode switch.

Use homogeneous ordinary variables
$\gamma_o\ge0$, $0\le x_o\le\gamma_o$ and
$0\preceq Y_o\preceq\operatorname{diag}(x_o,\gamma_o-x_o)$,
with $\gamma_0+\gamma_1=1$. Let $\Phi_{AB}(\gamma,x,Y)$ denote the
linear Kraus-covariance map obtained from (RS49) on the dummy $++$
input, multiplied by four, with
$D_x=\operatorname{diag}(x,\gamma-x)$; define $\Phi_{BA}$ by the
physical reverse word. The dummy input only computes the channel.
Actual unknown data are not prepared in $++$.

For $\gamma_o>0$, (RS50) supplies a pure source $\phi_o\in F$
and rank-two station projectors realizing
$(x_o/\gamma_o,Y_o/\gamma_o)$. At $\gamma_o=0$ the inequalities
force $x_o=Y_o=0$. Prepare the single pure photon
$\sum_o\sqrt{\gamma_o}e^{i\chi_o}|o\rangle_C\phi_o$
with one common spectral envelope $f(\nu)$.
The two reflected words and their complete pure photon program are

$$
\begin{aligned}
K_{0,ab}&=(\alpha_BI+b\delta_BP_{B,0})
          (\alpha_AI+a\delta_AP_{A,0}),\\
K_{1,ab}&=(\alpha_AI+a\delta_AP_{A,1})
          (\alpha_BI+b\delta_BP_{B,1}),\\
g_{ab}&=\int d\nu\,f(\nu)|\nu\rangle
 \sum_{o=0}^1\sqrt{\gamma_o}e^{i\chi_o}
 |o\rangle_C K_{o,ab}(\nu)\phi_o,\\
G&=\Phi_{AB}(\gamma_0,x_0,Y_0)+
   \Phi_{BA}(\gamma_1,x_1,Y_1).
\end{aligned}
\tag{RS59}
$$

There is no second launch-weight factor in the homogeneous maps.
Orthogonality of the order labels proves the last line, including
all finite-pulse integrals. Its channel action on every spin matrix
unit is multiplication by $G_{jk}$, so it covers arbitrary unknown
$ABR$. Independent branch choices of projectors are legitimate
because known block-diagonal photon optics implement their independent
conjugations of the same native $\Pi_j$.

For this pure fully accessible photon program, (RS55) with one
aggregate residual is exact: decompose each accepted phase-cone
covariance and the positive remainder, and realize that ensemble by
the terminal photon POVM on the actual purification. Local phase
feedback then gives every prescribed unitary flag on unknown $ABR$.
Consequently the two independent homogeneous moment programs are
attainable in this declared eight-mode interface. A classical order
lottery can have the same reduced $G$ but lacks its coherent purifier;
it retains separate per-order readout constraints and shared launch
probabilities. The summed residual alone does not establish classical
attainment.

Giving a fixed-order ordinary processor eight or more modes does not
enlarge its constant-control class. Before its second encounter the
source occupies only the two fixed directions $P_A\phi$ and
$(I-P_A)\phi$. Its second bright projector enters through a
two-dimensional effect compression, already realized by (RS50) in four
modes. Matching the four feature-vector Gram matrices gives one
frequency-independent support isometry for all scalar response
combinations, including cross-frequency blocks. Terminal readout
absorbs that isometry. This proves saturation of a *single fixed word*;
it does not merge the two different word cones into one.

### Same ports, physical windows and the stronger ordinary schedule

If each station truly has simultaneous $F4$ ports, the decorated
native schedule has two encounter macro-windows: in the first,
$C=0$ visits $A$ and $C=1$ visits $B$; in the second, their
destinations are exchanged. A station sees only one order alternative
per window. Sources, branch-specific wrappers, interstation routes,
output holds and coherent joint readout must all preserve the eight
external modes.

The same per-visit $F4$ hardware has a safe definite-order repeated
schedule

$$
\begin{array}{c|cccc}
&1&2&3&4\\ \hline
C=0&A_0&B_0&\text{hold}&\text{hold}\\
C=1&\text{hold}&\text{hold}&B_1&A_1 .
\end{array}
\tag{RS60}
$$

Only one four-mode arm enters a station at a time. Place precisely the
desired branch wrappers at its occupied visits, coherently delay the
other arm and align both at one common finish. Each history occupies
one $A$ and one $B$ encounter; there are four global query
opportunities, rather than two. With the same reflected operators in
the common spin/path frame, its entire survivor is exactly (RS59).
Every terminal photon measurement and its retained-spin CP map
therefore agree on arbitrary $ABR$, not just their scalar yield.

The generic full-joint argument is owned by
[(MC4)--(MC5)](../architecture-baselines.md#nr-r08-material-pointer-clock).
In its interaction-picture notation, (RS60) replaces the second
ordinary word by $G_A(3\tau)G_B(2\tau)$, while the two-window
word is $G_A(\tau)G_B(0)$, both followed by the same actual idle
evolution to the common finish. Time-independent joint writes and
vacuum opportunities with no extra preparation/reset/slot record
are sufficient for equality of complete instruments.
Merely equal reflected scalar responses establish only the survivor
identity here. Emission fields, route-dependent bath evolution,
noncommuting spin idle, timestamps and mandatory resets need their
actual dilation. Known compensation pulses are additional data
controls, not implicit photon wrappers.

A direct three-window $A_0$--$B_{\rm middle}$--$A_1$ survivor compiler
needs an important port qualification: both order branches meet $B$ in its
middle window, whereas the native schedule exposes only one $F4$
arm per station/window. Across a generic finite pulse its pre-$B$
feature span is three-dimensional: the two $C=0$ directions after
$A$, plus the unvisited $C=1$ source direction. Its required bright
compression can be

$$
K=K_0\oplus k_1=\tfrac12 I_3,\qquad
\operatorname{rank}K=\operatorname{rank}(I-K)=3.
\tag{RS61}
$$

For a frequency-independent isometric compression of this prescribed
pre-$B$ program, any physical rank-two bright/rank-two dark
projector has both ranks at most two. Thus (RS61) cannot fit that
four-mode station port. In general a compression $K$ can be
embedded into two bright and two dark modes exactly when both
ranks are at most two: stack square roots of $K$ and $I-K$ in
their respective ranges to obtain an isometry. The example needs
at least six modes; an actual replicated $C2\otimes F4$ middle
port is sufficient. External bypass modes alone do not increase
the rank of a single native spin-dependent scattering difference.

| Direct survivor compiler | Additional condition beyond one $F4$ port per visit |
|---|---|
| Four windows (RS60) | Coherent input/output holds and repeatable common-frame survivor |
| Three windows, constant controls | A sufficient merged port, or the proved bright/dark rank condition |
| One calibrated monochromatic point | The actual two pre-$B$ spin-conditional vectors span at most two; bespoke four-mode compression may suffice |
| Finite-pulse frequency-dependent compression | A separately supplied causal spectral processor, with its bandwidth, calibration, loss and latency |

The monochromatic case is not a normalizable finite-duration pulse.
At that calibrated point the combined pre-$B$ vectors
$v_a=\sqrt{\gamma_0}|0\rangle A_a\phi_0+
\sqrt{\gamma_1}|1\rangle\phi_1$ span a space $W$ of dimension
at most two. The desired projector $P_{B,\rm total}$ then has
$\dim(W+P_{B,\rm total}W)\le4$; its two-dimensional compression
admits the rank-two dilation (RS50). Known photon isometries before
and after the actual $B$ encounter can restore the prescribed
survivor without learning the unknown spin. These optics depend
on the calibrated program, not on its actual spin label.
For finite pulses with nonconstant $\alpha_A(\nu)$ and nontrivial
$\delta_A(\nu)$, the constant-control three-dimensional feature span
can occur, so that case cannot be substituted silently.
Serializing the two middle visits in time avoids merged simultaneous
ports but pays their physical sub-windows; renaming them one macro
does not remove that clock.
This port obstruction concerns that direct response-uniform survivor
compiler. It is not a lower bound against every three-window algorithm
or a different program with covariance-equivalent terminal instruments.
External quantum program storage and controlled photon–memory transfer
are additional resources not bounded by this port argument.

### Station and readout interfaces remain physical assumptions

A single spatial cavity port with two polarizations does not supply
(RS58) merely by adding a bypass rail. Its spin-dependent difference
on polarization has rank one; padding with unaffected modes preserves
that rank. Known conjugations cannot turn it into the required
rank-two difference on $F4$, and bypass has a different dark scalar
response. Duplicating cavities with independent spins likewise does
not duplicate an unknown payload without paid coherent data transfer
or encoding.

A time-bin spectator through the same input mirror is a possible
realization of $I_{\rm time}\otimes R_j$ only with a preserved
orthogonal modal encoding, identical spin frames and scalar kernels.
Delayed pulses $f(\nu)$ and $e^{i\nu\Delta}f(\nu)$ are not automatically
independent copies of a frequency register. Their accepted
cross-spin/bin overlap is
$\int d\nu\,|f(\nu)|^2r_a(\nu)^*r_b(\nu)e^{i\nu\Delta}$,
which need not vanish from identical bin settings or input-bin
orthogonality. The full temporal encoding and scattering must
preserve the required orthogonality, or retain an overlap/tail error
budget. General $U(4)$ mixing between early
and late bins requires causal buffering: an early output depending
on a late input must wait at least their separation. Passive edge
bins cannot be discarded while calling the wrapper deterministic.
Pulse width, cavity ringdown, router switching and guard intervals
then split each encounter macro into physical arrival windows.
If order and internal program are both temporal labels they need
four distinct orthogonal bins, not two labels reused as two tensor
factors. A demonstrated
[time-bin/polarization switch](https://arxiv.org/abs/2305.19386)
supplies evidence for coherent routing techniques; it does not
demonstrate this shared-spin four- or eight-mode station interface.

The accepted reflected photon must also remain a pure accessible
program. Photon survival does not by itself rule out unobserved
motion, phonon, fluorescence, pump or timing records correlated
with spin, arm or internal mode. If such records are inaccessible,
their covariance decomposition is not necessarily attainable by a
photon-only POVM. Joint spectral readout, any additional Naimark
ports/detectors, phase locking and stored-spin local feedback
remain charged. The stronger ordinary comparisons also include
actual intermediate instruments, data controls, spare memories
and entanglement-first payload-safe routes when the device supplies
them; the fixed-word SDP is not their universal upper bound.

For a specified attempt/failure-handling protocol, write its model
accepted weights as $p_S,p_F$ and its additional transmissions and
complete cycle times as $\eta_o,\tau_o$. Necessary comparisons are

$$
R_S=\frac{p_S\eta_S}{\tau_S},\qquad
R_F=\frac{p_F\eta_F}{\tau_F},\qquad
R_4=\frac{p_S\eta_4}{\tau_4},
\tag{RS62}
$$

with a corresponding $R_3$ only when its merged-port/compression
premise is supplied. The repeated schedule matches the ideal survivor
weight $p_S$ but has its own losses and clock. Even a strict ideal
two-window versus fixed-word yield gap is therefore not a gate-rate
advantage. Rejected unknown data may be damaged, so these expressions
do not establish harmless retries. No measured native implementation,
all-loss compiler or strongest-ordinary optimum follows from this
eight-mode attainment theorem.
For illustrative equal transmissions, $p_S>0$, $t>0$ and common
overhead $T_0\ge0$, set
$\tau_S=T_0+2t$ and $\tau_4=T_0+4t$: then
$R_S/R_4=(T_0+4t)/(T_0+2t)$, so a $20\%$ rate increase requires
$T_0\le8t$.
For the qualified three-window comparator
$\tau_3=T_0+3t$, the same illustrative threshold is $T_0\le3t$;
these are conditional clock sensitivities, not fitted device claims.

## An exact restricted gate gap for projector reflections

A rational checkpoint separates the coherent two-arm cone from both
fixed words and their recorded classical lotteries. The scalar kernel
is $A_a=I-aP$, $B_b=I-bQ$: dark reflection is one and bright
reflection is zero. The prescribed accepted gate is
$D=\operatorname{CZ}=\operatorname{diag}(1,1,1,-1)$ on unknown
$ABR$. The coherent attainment uses local output $Z$-phase corrections.
The ordinary upper below permits an arbitrary complete photon POVM followed
by a terminal trace-nonincreasing separable correction, including local
filters and LOCC. All rejected launches are counted;
physical no-click branches are not accepted.

For the conventional feature Gram of
$(\phi,P\phi,Q\phi,QP\phi)$, every ordinary moment has the form

$$
H(\gamma,x,q,t,c)=
\begin{pmatrix}
\gamma&x&q&c\\
x&x&c^*&t\\
q&c&q&c\\
c^*&t&c^*&t
\end{pmatrix}\succeq0,\qquad
x,q,t\in\mathbb R,\quad c\in\mathbb C.
\tag{RS63}
$$

Here $\gamma=1$ for a normalized source and is the launch weight
in a homogeneous arm. This condition is also sufficient in four
modes: factor $H$ into vectors $(v_0,v_1,v_2,v_3)$.
Its identities give
$\operatorname{span}\{v_2,v_3\}\perp
\operatorname{span}\{v_0-v_2,v_1-v_3\}$.
A rank-two $Q$ includes the first span and excludes the second,
padding unused directions when necessary. Similarly
$v_1\perp v_0-v_1$ permits a rank-two $P$ with $Pv_0=v_1$.
Then $Qv_0=v_2$, $Qv_1=v_3$, as required.
At $\gamma=0$ positivity forces $x=q=c=t=0$.

Define $J$ to exchange coordinates 1 and 2 (zero-based) and put

$$
L=\begin{pmatrix}
1&0&0&0\\1&0&-1&0\\1&-1&0&0\\1&-1&-1&1
\end{pmatrix},\qquad
G_{AB}=LH^{\mathsf T}L^{\mathsf T},\qquad
L_{BA}=JL=LJ.
\tag{RS64}
$$

The transpose is essential for complex $c$: $H$ is the conventional
column Gram, whereas $G$ is the Kraus covariance of (RS54)–(RS55).
The two equal station kernels allow station-label exchange for the
reverse word; this is a relabelling, not a physical data-spin swap.

The selected
[rational certificate](../checks/architecture/projector_gate_gap.json)
contains the normalized moment and phase covariance

$$
H_*=\frac1{1000}
\begin{pmatrix}
1000&313&922&278\\
313&313&278&87\\
922&278&922&278\\
278&87&278&87
\end{pmatrix},\qquad
\Omega_*=\frac1{1000}
\begin{pmatrix}
175&-30&-30&174\\
-30&175&-164&-30\\
-30&-164&175&-30\\
174&-30&-30&175
\end{pmatrix}.
\tag{RS65}
$$

Use the equal coherent arm moments $H_*/2$ and $H_*/2$.
Their total covariance is
$G_*=\tfrac12 L(H_*+JH_*J)L^{\mathsf T}$.
Exact principal-minor checks prove
$H_*\succ0$, $\Omega_*\succ0$,
$\Omega_*^{T_B}\succ0$ and
$G_*-D\Omega_*D\succ0$.
The diagonal of $\Omega_*$ is $7/40$ and its complex phase-cone
equalities in (RS54) hold. Thus (RS55) and the pure eight-mode
attainment (RS59) give the exact accepted map
$(7/40)\operatorname{Ad}_{\rm CZ}$ on every unknown $ABR$.
The source, projectors and POVM exist by the displayed Gram
construction and covariance factorization; no numerical
eigenvalue or near-unitarity tolerance supplies them.

For the ordinary upper, the same certificate specifies four rational
real symmetric matrices $Z,A,B,S$, with common denominator $60000$.
They satisfy $Z,A,B,S\succeq I/2000$. With
$\mathcal E=\operatorname{span}_{\mathbb R}\{I,X,Y\}^{\otimes2}$
and $\langle X,Y\rangle=\operatorname{Tr}(XY)$, their exact
identities are

$$
\begin{aligned}
W&=DZD-A-B^{T_B}-I/4\ \perp\mathcal E,\\
\Lambda&=L^{\mathsf T}ZL+S,\qquad
\Lambda_{00}=1/6,\qquad
\langle\Lambda,H_i\rangle=0\quad(i=1,\ldots,5).
\end{aligned}
\tag{RS66}
$$

The $H_i$ are all five real coefficient directions in (RS63),
including $\operatorname{Im}c$. The replay tests all nine real
Pauli directions of $\mathcal E$, including their imaginary
entries, and all five moment directions. These are not restrictions
to real ordinary programs or a finite Pauli correction dictionary.

For the local-phase-feedback subclass, feasible $H,\Omega$, positivity,
PPT and the reflected residual yield the weak-duality chain

$$
\begin{aligned}
p
&=\langle I/4,\Omega\rangle
 \le\langle Z,D\Omega D\rangle
 \le\langle Z,LH^{\mathsf T}L^{\mathsf T}\rangle\\
&=\langle L^{\mathsf T}ZL,H\rangle
 \le\langle\Lambda,H\rangle
 =\gamma/6 .
\end{aligned}
\tag{RS67}
$$

The first inequality subtracts the nonnegative pairings with
$A,\Omega$ and $B,\Omega^{T_B}$; $W$ pairs to zero.
The transpose in the middle equality can be dropped because
$L^{\mathsf T}ZL$ is real symmetric, even when $H$ is complex.
The next inequality uses $S,H\succeq0$.
For $BA$, conjugate $Z,A,B$ by $J$, keep $S$ and use $L_{BA}$.
The certificate checks all identities again, including partial
transpose. Homogeneity bounds each recorded order arm by
$\gamma_o/6$, hence their lottery by $1/6$ when
$\sum_o\gamma_o=1$. It does not grant a classical lottery the
coherent pooled purifier.

<a id="nr-r11-terminal-separable-gate"></a>

The same upper extends to **any terminal separable correction after complete
photon readout**. This includes local unentangled ancillas, amplitude filters,
phases, LOCC and recorded failures. It excludes spin operations before or
interleaved with the photon readout, shared entangled resources and retained
quantum processing of the photon after a spin filter.

Refine the photon measurement mathematically and write one raw spin Kraus
operator as $K=\operatorname{diag}(k)$. If its accepted separable correction
has product Kraus operators $Q_l=A_l\otimes B_l$, exact CZ on every unknown
$ABR$ implies

$$
Q_lK=c_lD,\qquad
p_k=\sum_l|c_l|^2\le\min_{a,b}|k_{ab}|^2.
\tag{RS67a}
$$

The accepted unitary channel has rank-one Choi matrix, so each refined
successful history must be proportional to $D$. For nonzero $c_l$, $K$ is
invertible and $Q_l=c_lDK^{-1}$ is a diagonal product. Consequently
$k=D(u\otimes v)$ for two nonzero complex vectors. Completeness
$\sum_lQ_l^\dagger Q_l\preceq I$ proves the probability bound in (RS67a)
entry by entry. A zero component of $k$ precludes nonzero full-space CZ
success. For an allowed product atom the bound is attained by the local
contractions $\operatorname{diag}(m_u/u_a)$ and
$\operatorname{diag}(m_v/v_b)$, where $m_u=\min_a|u_a|$ and
$m_v=\min_b|v_b|$. Their complementary filter outcomes are failures;
multiple success records share this one budget.

Put $C=DZD$ for the same ordinary dual $Z$ as in (RS66). The
[shared rational certificate](../checks/architecture/projector_gate_gap.json)
also supplies four sector decompositions. Set
$S_0=\operatorname{diag}(-1,1)$, $S_1=\operatorname{diag}(1,-1)$ and
$E_{ij}=|ij\rangle\langle ij|$. For each $i,j\in\{0,1\}$ it gives
real symmetric positive-definite matrices $A_{ij},B_{ij}$ of size four
and $M_{A,ij},M_{B,ij}$ of size two, with denominator $6000000$, such that

$$
C-E_{ij}=A_{ij}+B_{ij}^{T_B}
       +S_i\otimes M_{B,ij}+M_{A,ij}\otimes S_j.
\tag{RS67b}
$$

Tensor indices are $2a+b$ and
$(B^{T_B})_{ab,cd}=B_{ad,cb}$. The exact replay checks all 64 entry
identities and all 48 positive leading principal minors. Sylvester's
criterion proves positivity without a numerical tolerance. In the sector
where $|u_i|=\min_a|u_a|$ and $|v_j|=\min_b|v_b|$, both $S$ expectations
are nonnegative. The partially transposed term on $u\otimes v$ is the
expectation of $B_{ij}$ on $u\otimes\overline v$, and is also nonnegative.
Thus the four sectors, including ties and zero-minimum endpoints, prove

$$
(u\otimes v)^\dagger C(u\otimes v)
 \ge\min_a|u_a|^2\min_b|v_b|^2
\quad(u,v\in\mathbb C^2).
\tag{RS67c}
$$

Real certificate matrices do not restrict the amplitudes or phases.
Let $G$ be the unnormalized raw photon-readout covariance. Its accepted
raw atoms satisfy $G-\sum_k kk^\dagger\succeq0$. Equations (RS67a)–(RS67c)
and $Z\succeq0$ now give

$$
p_{\rm CZ}\le\sum_k k^\dagger Zk
 \le\operatorname{Tr}(ZG_{AB})\le\gamma/6.
\tag{RS67d}
$$

The last inequality uses the unchanged moment dual of (RS66), with
$G_{AB}=LH^{\mathsf T}L^{\mathsf T}$; no phase-cone restriction on the
accepted atoms remains. For $BA$, use $JZJ$: $D$ commutes with $J$ and
$J(u\otimes v)=v\otimes u$, so (RS67c) also bounds that dual. Recorded
classical order lotteries again sum their separate launch weights. Photon
and filter rejections have not been renormalized away. This is an exact
unknown-input gate statement, including passive references, rather than a
known-input entanglement-factory fidelity.

Consequently the exact restricted optima obey

$$
\operatorname{OPT}_{\rm coherent,8}\ge\frac7{40},\qquad
\operatorname{OPT}_{\rm fixed\ word/recorded\ lottery}\le\frac16,
\qquad
\Delta_{\rm OPT}\ge\frac1{120},\qquad
\frac{\operatorname{OPT}_{\rm coherent,8}}
 {\operatorname{OPT}_{\rm fixed\ word/recorded\ lottery}}
\ge\frac{21}{20}.
\tag{RS68}
$$

The ordinary optimum is positive: $H_*\succ0$ is ordinary-realizable,
$L$ is invertible and (RS56) gives a positive uncorrected CZ
weight. Neither optimum, nor their actual difference, is asserted
equal to these bounds.

There is a checked scalar correspondence with (RS44). At one
frequency, set its decay rate $\gamma=\kappa$, $\kappa_r=\kappa$,
$g^2=2\kappa^2$ and $\nu=\kappa$; direct substitution gives
$r_{\rm dark}=-i$, $r_{\rm bright}=0$. A common station phase $i$
gives the projector kernel. This is a single-frequency model point,
not a fit to the measured modules, a normalizable finite-pulse
certificate or evidence for the required four/eight-mode ports.

This checkpoint concerns the specified CZ flag and the fixed-word
two-encounter class with terminal separable correction after complete
photon readout. Intermediate data controls, spin operations before or
interleaved with that readout, encodings, shared entangled resources,
protected data bypasses, spare payload memories, entanglement-first protocols,
extra calls and different spectral or no-click interfaces are
outside the ordinary dual. The safe four-window survivor compiler,
or the qualified calibrated three-window construction, matches
the pooled instrument when its premises are supplied. Thus (RS68)
is an exact restricted-interface gate separation, not a practical
rate or hardware advantage, a harmless-retry theorem, or a
priority claim. The port, purity, timing and strongest-ordinary
resource tests above remain necessary.

The broader mechanisms have established antecedents.
[Simonov et al., Proposition 2](https://arxiv.org/html/2311.13654v4)
give deterministic CZ by switching product unitaries on the data
register, with ancilla measurement and local preprocessing/feedback;
those slots differ from the spin-controlled photon contractions here.
[Duan, Wang and Kimble](https://arxiv.org/pdf/quant-ph/0505054)
already give ordinary sequential cavity-photon remote gates with
photon detection and local phase feedback. This checkpoint certifies
the specified probability optimization, without a new-mechanism or
priority claim.

<a id="nr-r11-retained-photon-gate"></a>
## Retaining the unknown flying photon: gate, controllers and loss

This subsection changes the output task: **both spins and the incoming
photon qubit are unknown data**. Write them as $A,B,F$, with an arbitrary
untouched reference $R$. The same $F$ must remain quantum output. A final
photon counter, a known-input spin factory and a fresh replacement photon
do not implement this service. The following ideal identities, restricted
ordinary bounds and physical-instrument conditions do not establish a
native hardware advantage or a new gate-generation mechanism.

### Ideal complete instrument and strong ordinary circuits

Set $P=Z_FZ_A$, $Q=X_FZ_B$, and
$U_A(\theta)=e^{-i\theta P}$, $U_B(\phi)=e^{-i\phi Q}$.
Since $P,Q$ are Hermitian involutions with $PQ=-QP$, a supplied coherent
order interface, initialized in $+$ and read in $X$, has Kraus operators

$$
\begin{aligned}
K_+&=\cos\theta\cos\phi I-i\sin\theta\cos\phi P
                         -i\cos\theta\sin\phi Q,\\
K_-&=\sin\theta\sin\phi\,PQ.
\end{aligned}
\qquad
\theta=\phi=\frac\pi4:
\quad K_+=\frac{\sqrt3}{2}G,\quad K_-=\frac12PQ,
\quad G=\frac{I-iP-iQ}{\sqrt3}.
\tag{RP1}
$$

The minus sign convention can change with the order labels. Here
$G^\dagger G=I$ and $PQ=iY_FZ_AZ_B$ is a product of local Paulis.
After reading a **surviving** minus without consuming $F$, its inverse
restores all of $ABFR$. The corrected classical instrument is exactly
$\{(3/4)\operatorname{Ad}_G,(1/4)\operatorname{Id}\}$.
This is a legitimate ideal repeat branch. Photon loss is not such a
branch. Where the plus probability is nonzero, at a common drifting
angle its normalized gate becomes, up to a global phase,
$[\cos\theta I-i\sin\theta(P+Q)]/\sqrt{1+\sin^2\theta}$;
equal drift therefore does not preserve the fixed target $G$.

A different service forwards the **designated plus output port** and
dumps minus, without measuring the surviving photon or waiting for a
classical result. Its accepted map is $(3/4)\operatorname{Ad}_G$ in
the lossless ideal model. It needs no QND order readout or measurement-
decision storage, but gives no online occupancy herald or same-input
retry. The full device still includes vacuum: dumping ideal minus
alone gives the remaining-spin map
$\tfrac14\operatorname{Tr}_F[PQ\rho(PQ)^\dagger]$ in that sector.
Other optical losses have their own spin/reference maps. The ordinary
$9/16$ construction below can likewise forward its selected helper
port, apply its fixed known spin-phase correction unconditionally and
dump the complement, with no QND readout. Neither architecture receives
late receiver postselection as exclusive access.

One ideal cavity CZ and known local phases implement each $\pi/4$
Ising rotation; a photon Hadamard changes its $Z_F$ axis to $X_F$.
Those phases, rotations and coherent routes are supplied controls with
their own cost. [Daiss et al.](https://doi.org/10.1126/science.abe3150)
demonstrate sequential cavity reflections, photon detection and atomic
feedback for retained **spin** data. That experiment supplies neither
this coherent order interface nor its retained-photon branch readout.
The product-unitary switch mechanism also has the antecedents cited
above, including [Simonov et al.](https://arxiv.org/html/2311.13654v4).

Several ordinary constructions preclude comparing (RP1) only with an
uncontrolled two-contact word.

* **Four contacts, no helper readout.** With
  $S=\operatorname{CNOT}_{A\to F}\operatorname{CZ}_{BF}$ and
  $g_F=(I-iZ_F-iX_F)/\sqrt3$,

  $$
  SZ_FS^\dagger=P,\qquad SX_FS^\dagger=Q,\qquad
  G=Sg_FS^\dagger.
  \tag{RP2}
  $$

  The chronological node visits are $A,B,g_F,B,A$; photon Hadamards
  wrap each $A$ CZ. This is an operator identity on every $ABFR$.
  Revisits, links and storage are paid. Four contacts remain necessary
  with **arbitrary clean photonic ancillas in a unitary-only circuit**.
  The physical stationary data are qubits $A,B$; their only couplings to
  other registers are counted exact CZ encounters. Allow arbitrary
  photon/ancilla unitaries and local unitaries on those physical spin
  qubits, but no extra matter encoding, pre-shared node resource,
  measurement, postselection, record-conditioned feedback or additional
  nonlocal primitive. The target must be unconditional $G$ on every
  $ABFR$, with all photonic ancillas returned to a fixed state independent
  of that input. A unitary dilation with exactly this reduced channel
  automatically has such a pure, input-independent environment output;
  merely discarding its final environment does not evade the premise.

  Suppose there is only one $B$ encounter. Across $B|\text{rest}$, all
  pre-encounter controls give a local spin unitary and a rest-source
  isometry $E$ from $AF$; all later controls give a local spin unitary
  and a rest unitary $V$. The two spin factors are independent rank-one
  matrices $R_j=b_{\rm out}|j\rangle\langle j|b_{\rm in}$, and the
  rest maps are $VE,VJE$, where $J=J^\dagger$, $J^2=I$ is the CZ's
  relative photon operator, including all ancillary identities.
  The target's $B$ operator-Schmidt span is precisely
  $\operatorname{span}\{|0\rangle\langle0|,|1\rangle\langle1|\}$.
  Each $R_j$ must therefore be diagonal; its rank one forces a
  computational projector. Unitary $b_{\rm in/out}$ leave only matched
  bit permutations and phases. Consequently, up to inversion and a
  common phase,

  $$
  E^\dagger JE=e^{i\delta}G_+^\dagger G_-,\qquad
  G_b=\frac{I-iP-i bX_F}{\sqrt3},\quad P=Z_AZ_F.
  \tag{RP2a}
  $$

  The compression on the left is Hermitian, whereas the right is
  unitary. Hence its eigenvalues must be $\pm1$. Equivalently, exact
  clean return makes the source code invariant: with
  $C=E^\dagger JE$,
  $E^\dagger J^\dagger(I-EE^\dagger)JE=I-C^\dagger C=0$, so
  $JE=EC$. But anticommutation gives

  $$
  G_+^\dagger G_-=\frac{I+2iX_F-2PX_F}{3}
  =\frac13I+i\frac{2\sqrt2}{3}H,\qquad
  H=\frac{X_F+iPX_F}{\sqrt2},\quad H^\dagger=H,\quad H^2=I.
  \tag{RP2b}
  $$

  Its eigenvalues $e^{\pm i\theta}$, each twice, have
  $\cos\theta=1/3$ and ratio $-7/9+i4\sqrt2/9$. No common phase
  makes them both real, including after inversion. Thus one $B$
  encounter is impossible; zero has insufficient spin Schmidt rank.
  Station relabelling and a photon Hadamard give the same obstruction
  at $A$. Two contacts per node are necessary, and (RP2) attains four.
  This proves no lower bound for measured/feedforward circuits such as
  (RP3), selected ports or spin filters, extra matter encodings,
  fractional interactions, or controlled-vacuum opportunity calls.
  The latter's occupied counts in (RP4) are not counts of fixed CZ
  gates, so that construction is also consistent with the bound.

* **Two contacts, two photon helpers.** Supply eight preserved photon
  modes $F,H_A,H_B$, prepare both helpers in $+$, and use one
  $\operatorname{CZ}_{A,H_A}$ and one $\operatorname{CZ}_{B,H_B}$.
  Known mode swaps can assign the interacting degree while preserving
  the other two; that spectator-mode station extension is a premise.
  For a spin label $a,b$, the helper states are $H|a\rangle,H|b\rangle$.
  Apply helper Hadamards before the computationally controlled known
  photon unitary
  $V=\sum_{ab}|ab\rangle\langle ab|\otimes
  (I-i(-1)^aZ_F-i(-1)^bX_F)/\sqrt3$.
  The four helper-$X$ outcomes have operators

  $$
  J_{mn}=\frac12Z_A^mZ_B^nG,\qquad m,n\in\{0,1\}.
  \tag{RP3}
  $$

  Local spin-$Z$ feedback gives deterministic $G$. Both helper bits
  must be read **without absorbing the photon carrying $F$**; a specified
  joint four-outcome meter is an alternative to two binary readouts.
  There is no minimum-two-devices or minimum-two-periods claim. Known
  $U(8)$ synthesis, extra modes, readout, feedback and delay are paid.
  For terminal Pauli or compatible fixed-Clifford continuations, one
  may instead defer the helper keys until final helper/photon detection
  and use all four results by classical Pauli-frame postprocessing.
  That can remove the readout/return requirement for those workloads;
  it does not deliver an arbitrary reusable fixed-frame $ABF$ gate
  before those keys are accessible.
  With an independent $3/4$ coin this circuit, or identity contacts on
  helpers prepared in $0$, also reproduces the corrected classical
  instrument in (RP1). It does not reproduce unspecified loss branches
  or the unread coherent order output.

* **Three contacts, one reusable helper.** A helper $C=+$, one
  $\operatorname{CZ}_{AC}$, the known photon operation
  $e^{-i\alpha X_CZ_F}$ and computational QND helper readout give
  $K_0=e^{-i\alpha P}/\sqrt2$, $K_1=Z_AK_0$.
  Spin feedback and a real reset make an arbitrary $P$ rotation
  deterministic. The same construction uses $X_F$ for $Q$. Thus
  $e^{-i\pi P/8}e^{-i\beta Q}e^{-i\pi P/8}=G$ for
  $\sin\beta=1/\sqrt3$, using three contacts and three actual helper
  read/reset cycles on four modes. Expansion in $I,P,Q$ proves the
  identity: $\cos\beta\cos(\pi/4)=
  \cos\beta\sin(\pi/4)=\sin\beta=1/\sqrt3$.
  It explicitly lies outside the lower bound following (RP2).

* **Coherent return instead of helper measurement.** Before reading
  (RP3), a known helper basis conversion gives
  $\frac12\sum_{mn}|mn\rangle Z_A^mZ_B^nG|\psi\rangle$.
  Two CZ revisits cancel both byproducts and leave $|++\rangle G|\psi\rangle$.
  If an additional coherent vacuum/idle port bypasses the return node
  when its key is zero, there are four potential contact windows with
  lossless mean occupied contacts three. For state-independent surviving
  contact amplitude $\sqrt t$ and lossless bypass, the survivor is

  $$
  t\left(\frac{|0\rangle+\sqrt t|1\rangle}{\sqrt2}\right)^{\!\otimes2}
     \otimes G|\psi\rangle,
  \qquad p_{\rm return}=\frac{t^2(1+t)^2}{4}.
  \tag{RP4}
  $$

  This factorization includes every reference. It needs eight-mode
  return routing, storage and correct vacuum-relative spin phases;
  local equivalence of an occupied Ising gate to CZ does not prove its
  idle block. It is not a hard three-query protocol or a complete loss
  instrument. No helper readout is needed for correction; a promised
  online photon-arrival herald remains a separate resource.

These are known-control flying-program constructions, related to the
ordinary gate-teleportation/program baselines in
[NR-R11](../communication.md#nr-r11), rather than claims of mechanism
priority. Arbitrary joint processing of one photon's modes is a control
assumption, not a free unknown gate or a demonstration that each module
preserves those spectator modes.

### Two occupied contacts with controlled-vacuum opportunity calls

The fixed-two-query bounds below must also be distinguished from the
vacuum-extended schedules in (RS58)–(RS62). For the retained photon
there is a direct same-local-port specialization. Write
$\Pi_c=|c\rangle\langle c|$ on the coherent route label. For any
operators $A,B$ on the retained payload, let
$A_0=\Pi_0\otimes A+\Pi_1\otimes I$,
$A_1=\Pi_0\otimes I+\Pi_1\otimes A$ and define $B_0,B_1$ analogously.
Then the chronological four-opportunity word $A_0,B_0,B_1,A_1$ obeys

$$
A_1B_1B_0A_0
=\Pi_0\otimes BA+\Pi_1\otimes AB
=A_1(I_C\otimes B)A_0.
\tag{RP4a}
$$

Each surviving history occupies one $A$ and one $B$ contact; the
inactive alternative is coherently stored/bypassed. This is a
constructive four-encounter-window serialization using the original
local $F$ port, not four occupied contacts. A three-window version
uses the right-hand expression only when the middle node supplies
$I_C\otimes B$ on both alternatives simultaneously. Its modal port,
storage, phase and timing are substantive premises. Calling two
sequential $B$ subvisits one macro-window does not remove their pulse,
switching and cavity-tail guard times.

The known initial $C=+$ does not generally compress that middle input
to a single $F$ qubit. For already wrapped Ising $A$ the pre-middle
graphs are
$(|0\rangle e^{-i\pi aZ_F/4}|f\rangle+|1\rangle|f\rangle)/\sqrt2$,
$a=\pm1$; their span is four because the two upper blocks differ by
$-i\sqrt2 Z_F$. With the physical spin phase deferred as below, the
photon-only blocks are instead $R_{A,+}=S_F$ and $R_{A,-}=S_FZ_F$.
Their graph span is **three**, namely
$\operatorname{span}\{|+\rangle_C|0\rangle_F,
|0\rangle_C|1\rangle_F,|1\rangle_C|1\rangle_F\}$.
Both exceed a single two-dimensional arrival port. No four-dimensional
projector-rank conclusion is inferred for the deferred three-dimensional
span. A genuine spectator-path extension, additional coherent modes or
memory, or timed subvisits can supply a different interface and must
be modeled rather than excluded by dimension terminology alone.

The spin phases must be implemented in the correct vacuum frame.
Using $S=\operatorname{diag}(1,i)$,

$$
U_A=e^{-i\pi/4}S_FS_A\operatorname{CZ}_{AF},\qquad
U_B=e^{-i\pi/4}(H_FS_FH_F)S_B
                         (H_F\operatorname{CZ}_{BF}H_F).
\tag{RP4b}
$$

$S_A,S_B$ commute with both contacts and all photon wrappers. Attach
the photon factors to the occupied routed visits and apply each spin
phase **once** at a common finish. The two omitted scalar phases are
the same in each complete surviving history. Applying $S_A$
unconditionally at both possible $A$ windows would rotate even the
empty alternative twice and give the wrong gate. Real phases on
failed/vacuum branches and their leakage-space extension remain part
of the full device. Free spin evolution must be matched or compensated;
extra idle dephasing is a physical cost.

For stationary frequency-diagonal **actual coherent survivor** kernels
$R_A(\omega),R_B(\omega)$, the same multiplication matches
$\Pi_0 R_BR_A+\Pi_1 R_AR_B$ pointwise, even when the raw kernels are
complex, nonunitary, spin dependent and include auxiliary polarization.
Matched output delays and known wrappers therefore give the same
accepted map on every $ABFR$, with spectral coherence retained. The
kernel must describe the actual selected Kraus amplitude with matched
purified environmental records, not just a thermally averaged or
measured mean reflection amplitude. Inelastic reflected light,
zero-energy dephasing, motion and nonstationary records require their
own cross-history completion. Retiming elastic products does not
retime the complete vacuum/loss/bath instrument.

If $A,B$ are fixed joint dilations and controlled idle is literally
identity in that same frame, (RP4a) holds before any environment is
traced. This stronger statement needs its declared independent
controller/vacuum extension. A photon's path label disappears on loss;
stationary reduced channels do not by themselves fix the emitted-time
records or the bath's intervening free evolution. Actual full-channel
equality needs an argument from the complete physical network/dilation,
not a scalar reflectivity or an event diagram.

Nor is four serialization windows a latency lower bound. At the
controlled-event level, $A_0$ commutes with $B_1$, $B_0$ with $A_1$,
and $B_0$ with $B_1$. Thus the same four opportunity operations can
form the two layers $(A_0\parallel B_1)$ and
$(B_0\parallel A_1)$ if the actual coherent routing/bypass access
permits them. Giving a comparator that same network gives the same
physical realization, including its full channel when the hardware
is identical. This is enlarged vacuum-controlled access, **not** a
two-opaque-query fixed-order simulation or a proof of causal
separability. The distinction between time-controlled circuits and
time-delocalized local operations is discussed by
[Oreshkov, Quantum **3**, 206 (2019)](https://arxiv.org/html/1801.07594v4);
[Simonov et al.](https://arxiv.org/html/2311.13654v4) explicitly use
vacuum extensions in this setting. A practical timing comparison must
specify the allowed opportunity calls, network, common-finish modes,
storage and idle noise. A topology count alone proves neither a
two-versus-four latency gap nor an occupied-contact advantage.

### What exactly two CZ contacts and one terminal flag can do

There is also a useful restricted exact comparison. Consider one fixed
$A$ CZ followed by one fixed $B$ CZ, arbitrary photon unitaries before
and between the contacts, one clean photon helper, no intermediate
instruments or extra station ancillas,
and arbitrary terminal photon instruments retaining $F$. Arbitrary local
spin unitaries before/after their sole contact and record-dependent local
unitary corrections are allowed. This class contains an exact $G$ flag
of weight $9/16$; the **total** weight of all its exact locally corrected
$G$ records is at most $9/16$. Its projective two-outcome completion
cannot turn the other outcome into either $G$ or a harmless local-product
retry. This is not an upper bound on all ordinary controllers: larger
photon helpers, middle measurements and local data filters change
this fixed-unitary model; the extensions below retain their distinct
assumptions.

Here is the reduction including local spin controls. Across $A|BF$, the
branch's spin factors are $U_A|i\rangle\langle i|V_A$. Target $G$ has
operator-Schmidt rank two and spin span $\operatorname{span}\{I,Z_A\}$,
so the two independent rank-one factors must be diagonal. A rank-one
diagonal matrix is a computational projector times a scalar. Thus the
allowed controls reduce to matched input/output bit flips and spin
phases. Apply the same argument to $B$. Common input/output photon
unitaries are absorbed into its encoder/decoder. This reduction needs
the stated one-contact/no-spin-instrument conditions.

Let $a,b=\pm1$ be spin $Z$ eigenvalues and write each CZ on the photon
as $D(a)=\Pi_0+a\Pi_1$. With source isometry $E$, middle photon unitary
$W$ and accepted contraction $M$, the Fourier matrix has blocks

$$
C_{ji}=M_jW_{ji}E_i,\quad E_i=\Pi_iE,\quad M_j=M\Pi_j,
\quad\sum_iE_i^\dagger E_i=I,\quad\sum_jM_jM_j^\dagger\le I.
\qquad
C=\frac{\sqrt p}{\sqrt3}(R_\beta\otimes I)C_0(R_\alpha\otimes I),
\quad C_0=\begin{pmatrix}I&-iZ\\-iX&0\end{pmatrix},
\quad R_\gamma=e^{i\gamma X}.
\tag{RP5}
$$

The $R$ matrices act on Fourier **block indices**, not extra physical
helpers. They express the local spin phases. Pauli matrices within each
block act on $F$. For any finite photon-helper dimension, stack the block
source/row as $L=\operatorname{diag}(E_i)$,
$T=\operatorname{diag}(M_j)$. Then $C=TWL$,
$\|L\|_{\rm HS}^2=2$, $\|T\|_{\rm HS}^2\le2$.
Schatten Hölder gives $\|C\|_*\le2$, even if the two query-projector
sectors have unequal dimensions.
The eigenvalues of $C_0^\dagger C_0$ are
$(3\pm\sqrt5)/2$, each twice, and hence

$$
\|C_0/\sqrt3\|_*=2\sqrt{5/3},\qquad p\le\frac35.
\tag{RP6}
$$

This elementary dimension-independent lemma applies to one fine flag.
The stronger dual below improves its single-flag probability bound to
$9/16$; the nuclear-norm lemma remains useful when terminal spin filters
are allowed. Both single-flag arguments also apply to a coarse exact
map $p\operatorname{Ad}_G$ with **one common
visible spin correction**: rank-one Choi support forces every hidden
Kraus operator to be $\lambda_rG$. Dilate the photon filter and contract
its hidden register onto $\sum_r\lambda_r|r\rangle/\sqrt p$ to obtain
one photon contraction with Kraus $\sqrt pG$. This is an upper-bound
reduction, not a free physical record eraser. Distinct visible spin
corrections cannot be compressed this way by photon-only processing.

In fact an arbitrary finite photon helper cannot increase the optimum
of that one corrected flag beyond $9/16$. Here is an explicit all-phase
dual, independent of a numerical optimizer. Denote the normalized target
Fourier matrix by
$\widehat C=(R_\beta\otimes I)(C_0/\sqrt3)(R_\alpha\otimes I)$,
so the physical coefficient matrix is $t\widehat C$, $t=\sqrt p$.
Let $A_i=E_i^\dagger E_i$, $B_j=M_jM_j^\dagger$. The physical
factorization in (RP5) gives the necessary positive Gram matrix

$$
\mathcal M=
\begin{pmatrix}
 \operatorname{diag}(B_0,B_1)&t\widehat C\\
 t\widehat C^\dagger&\operatorname{diag}(A_0,A_1)
\end{pmatrix}\succeq0,
\qquad A_0+A_1=I,\quad B_0+B_1\preceq I.
\tag{RP6a}
$$

It follows by taking the Gram product of the stacked block maps
$\operatorname{diag}(M_j)$ and
$\operatorname{diag}(E_i)^\dagger W^\dagger$.
If necessary add the positive deficit to $B_0$; this preserves
$\mathcal M\succeq0$ and permits $B_0+B_1=I$ in the upper-bound
argument. No realizability of that padded point is required.

Use $\tau_x,\tau_y,\tau_z$ for Pauli matrices on the block index,
distinct from physical photon $X,Y,Z$. Put
$s_a=\sin2\alpha$, $c_a=\cos2\alpha$, $q=c_a^2$ and
$s_b=\sin2\beta$, $c_b=\cos2\beta$, $r=c_b^2$, and define

$$
\begin{gathered}
a_*=\frac{2+\sqrt2}{2\sqrt3},\qquad
b_*=\frac{2-\sqrt2}{2\sqrt3},\qquad
a_*^2+b_*^2=1,\quad 2a_*b_*=1/3,\\
K_A=a_*I+b_*\tau_y\otimes(-s_aI+2c_aZ),\qquad
K_B=a_*I+b_*\tau_y\otimes(s_bI-2c_bX).
\end{gathered}
\tag{RP6b}
$$

Each square has equal diagonal blocks:
$H_A=(1+3b_*^2q)I-4b_*^2s_ac_aZ$ and
$H_B=(1+3b_*^2r)I-4b_*^2s_bc_bX$.
Consequently the total diagonal dual cost on (RP6a) is exactly
$\mathcal D=\operatorname{Tr}H_A+\operatorname{Tr}H_B
=4+6b_*^2(q+r)$ after padding.
The following gauges and index matrices fix every normalization:

$$
\begin{gathered}
U_L=\operatorname{diag}(I,iX),\quad
U_R=\operatorname{diag}(I,iZ),\quad
F_0=\frac1{\sqrt3}\begin{pmatrix}1&1\\1&0\end{pmatrix},\quad
O=\frac{\tau_z+\sqrt2\tau_x}{\sqrt3},\\
V_0=U_L^\dagger(O\otimes I)U_R^\dagger,\qquad
V=(R_\beta\otimes I)V_0(R_\alpha\otimes I),\qquad
U_L(C_0/\sqrt3)U_R=F_0\otimes I.
\end{gathered}
\tag{RP6c}
$$

$O^2=I$, so $V$ is unitary. The dual block matrix
$\mathcal Y=\bigl(\begin{smallmatrix}
K_B^2&-K_BVK_A\\-K_AV^\dagger K_B&K_A^2
\end{smallmatrix}\bigr)$ is positive: it is a congruence of
$\bigl(\begin{smallmatrix}I&-V\\-V^\dagger&I\end{smallmatrix}\bigr)$
by $\operatorname{diag}(K_B,K_A)$. Positivity of its pairing with
$\mathcal M$ gives
$2t\ell\le\mathcal D$, where
$\ell=\operatorname{Re}\operatorname{Tr}(V^\dagger K_B\widehat C K_A)$.

This trace has a short exact reduction. Let
$N(x)=a_*I+b_*[2x\tau_x+(1-x)\tau_z]$. Direct Pauli multiplication
gives

$$
\begin{aligned}
U_R^\dagger(R_\alpha\otimes I)K_A(R_\alpha^\dagger\otimes I)U_R
 &=N(q)\otimes I-b_*s_ac_a(\tau_x+2\tau_z)\otimes Z,\\
U_L(R_\beta^\dagger\otimes I)K_B(R_\beta\otimes I)U_L^\dagger
 &=N(r)\otimes I-b_*s_bc_b(\tau_x+2\tau_z)\otimes X.
\end{aligned}
\tag{RP6d}
$$

Every nonidentity physical term in the trace vanishes because
$\operatorname{Tr}X=\operatorname{Tr}Z=\operatorname{Tr}XZ=0$.
Thus $\ell=2\mathcal T$, with

$$
\begin{aligned}
\mathcal T&=\operatorname{Tr}[O N(r)F_0N(q)]\\
 &=\frac43+\frac{4(\sqrt2-1)}9(q+r)
             +\frac{28\sqrt2-41}{18}qr,\\
3\mathcal T-\mathcal D
 &=\frac{10\sqrt2-13}{3}[q(1-r)+r(1-q)]
   +\frac{68\sqrt2-93}{6}qr\ \ge0.
\end{aligned}
\tag{RP6e}
$$

Both displayed constant coefficients are positive (square
$10\sqrt2>13$ and $68\sqrt2>93$), and $q,r\in[0,1]$.
Since $\mathcal D>0$, also $\mathcal T>0$. Weak duality therefore
gives the sharp dimension-independent single-flag bound

$$
\sqrt p=t\le\frac{\mathcal D}{4\mathcal T}\le\frac34,
\qquad p\le\frac9{16}.
\tag{RP6f}
$$

The inequality is strict away from $q=r=0$; the four-mode construction
in (RP10) attains equality. This proof requires only the necessary
Gram condition and the explicit positive dual, not SDP sufficiency or
strong duality. It covers one fine flag, or one coarse exact map with
the common correction reduction above. It does not bound several
visible records with different spin corrections for an arbitrary
larger helper; (RP3) already has total unit yield in that larger model.

Now restrict the photon through the two contacts to four dimensions,
one data qubit and a two-level helper, while allowing one arbitrary
accepted terminal contraction $M:C F\to F$.
The full target $C$ is invertible. In a four-dimensional photon space
this forces both query sectors to have dimension two: each block
source and row must have rank at least two and their dimensions sum
to four. Thus all the $E_i,M_j$ in (RP5) are square and invertible,
even when an individual target block is singular. Put
$\kappa=\sqrt{p/3}$, $H_j=(M_jM_j^\dagger)^{-1}>0$ and
$K_i=E_i^\dagger E_i$. Unitarity of $W$ gives the necessary balance
conditions

$$
H_0^{-1}+H_1^{-1}\le I,\qquad
C^\dagger\operatorname{diag}(H_0,H_1)C
 =\operatorname{diag}(K_0,K_1),\qquad K_0+K_1=I.
\tag{RP7}
$$

The first relation is equality for a terminal projective helper outcome.
Conversely these conditions construct the source, row and middle
unitary: choose positive square roots $E_i=\sqrt{K_i}$,
$M_j=\sqrt{H_j^{-1}}$ and
$W=\operatorname{diag}(M_j)^{-1}C\operatorname{diag}(E_i)^{-1}$.
Then $W^\dagger W=I$. The source isometry and a coisometric terminal
row extend to $U(4)$ controls in the equality case; the inequality
permits a trace-decreasing terminal filter.

For completeness the balance bound includes all spin phases and their
singular limits. First suppose $\sin2\alpha\sin2\beta\ne0$, and put
$u=\cot2\alpha$, $v=\cot2\beta$,
$A_0=\cos^2\beta H_0+\sin^2\beta H_1$,
$T_0=\sin\beta\cos\beta(H_0-H_1)$ and $A_1=A_0-2vT_0$.
The conjugated weight is
$\bigl(\begin{smallmatrix}A_0&iT_0\\-iT_0&A_1\end{smallmatrix}\bigr)$.
Writing its $C_0$ congruence as $B$ gives
$B_{00}=A_0+\{T_0,X\}+XA_1X$,
$B_{01}=-i(A_0+XT_0)Z$, $B_{11}=ZA_0Z$.
The off-diagonal balance and scalar block sum imply

$$
\begin{gathered}
A_0=hI-t_0X+h_zZ,\qquad T_0=t_0I+t_xX+t_zZ,\qquad h>0,\\
t_0=2vt_x,\quad h_z=-2vt_z,\quad
S:=\kappa^{-2}=3h+(2-4v^2)t_x,\\
h=(12v^2-2)t_x,\qquad ut_z=-2vt_x,\qquad
u(h+t_x)=2vt_z.
\tag{RP8}
\end{gathered}
$$

Indeed $B_{01}+B_{10}=0$ forces the first line;
$B_{00}+B_{11}=SI$ gives the second; and
$B_{00}-B_{11}=2u[h_zI+t_zX+(h+t_x)Z]$ gives the third.
If $v\ne0$, write $s=v^2$, $q=-t_x>0$, $L=2-12s$ and
$z=|v|\sqrt L$. The last line gives
$0<s<1/12$, $u^2=4s/(1-12s)$ and
$t_z^2=(1-12s)q^2$. The positive $H_0,H_1$ commute, and

$$
\begin{aligned}
H_0+H_1&=q[(4-20s)I-6v\sqrt L\,N],\\
H_0H_1&=2q^2(1-8s)[I-4v\sqrt L\,N],\qquad N^2=I.
\end{aligned}
\tag{RP9}
$$

Positive product requires $z<1/4$, equivalently $s<1/24$ in this
interval. The inverse-sum eigenvalues are
$(4-20s\mp6z)/[2q(1-8s)(1\mp4z)]$.
Their difference is $10z/[q(1-16z^2)]>0$, with the upper-minus-sign
fraction the larger. Requiring that eigenvalue to be at most one and
using $S=4q(1-8s)$ gives
$S\ge2(4-20s-6z)/(1-4z)\ge8$.
The last inequality is equivalent to $z\ge2s$, which follows from
$z^2-4s^2=2s(1-8s)>0$. Thus this whole generic branch has
$p=3/S\le3/8$. In the projective case the two inverse-sum eigenvalues
would both equal one; their nonzero difference rules out every
$v\ne0$ solution entirely.

If $v=0$, (RP8) forces $u=0$ and, up to swapping the two blocks,
$H_0=hI+T_0$, $H_1=hI-T_0$ with
$T_0=-hX/2+t_zZ$. The inverse-sum inequality becomes
$2h/(3h^2/4-t_z^2)\le1$, so $h\ge8/3$ and
$p=3/(2h)\le9/16$.
There are two remaining angle cases. If $\sin2\beta=0$, the weight
is block diagonal with positive blocks $A_0,A_1$. For
$\sin2\alpha=0$, $B_{01}=-iA_0Z$ cannot vanish. Otherwise the
conditions give $A_0=hI+z_0Z$, $A_1=h_1I+2z_0Z$,
$z_0=-uh$, $h_1=2uz_0=-2u^2h\le0$, contradicting positivity.
If $\sin2\beta\ne0$ but $\sin2\alpha=0$, they give
$A_0=-XT_0$, $t_x=-h$, $t_0=-2vh$, $h_z=t_z=0$;
then $B_{11}=h(I-2vX)$ and $B_{00}=h(4v^2I+2vX)$.
Positivity requires simultaneously $|v|<1/2$ and $|v|>1/2$.
This exhausts the singular cases without dividing by a vanishing sine.

The sharp value is attained at $\alpha=\beta=\pi/4$, $t_z=0$:

$$
\begin{gathered}
H_0=\tfrac83I-\tfrac43X,\qquad H_1=\tfrac83I+\tfrac43X,
\qquad K_0=\tfrac12I+\tfrac14Z,\quad K_1=\tfrac12I-\tfrac14Z,\\
M_0M_0^\dagger=\tfrac12I+\tfrac14X,\qquad
M_1M_1^\dagger=\tfrac12I-\tfrac14X,
\qquad\kappa=\tfrac{\sqrt3}{4},\qquad p=\tfrac9{16}.
\tag{RP10}
\end{gathered}
$$

The construction after (RP7) supplies exact $U(4)$ controls and local
spin-phase correction. This proves the sharp single-contraction bound
$9/16$ in four photon dimensions, and attains it with a projective
helper outcome. It does not yet multiply or sum leaf bounds across
an arbitrary instrument; the fixed-circuit argument below is needed
for that conclusion.

The projective complement is also constrained. Every feasible projective
solution has $u=v=0$. Put $\rho=t_z/h$, so
$\rho^2=3/4-4p/3$. Up to common input/output photon unitaries, bit flips
and spin phases, choose the orthogonal row $[-M_1,M_0]$.
After removing the accepted branch's spin phases its sector operators are

$$
D_{ab}=\frac12\left[i(\rho a+b/2)I-X/2
                   -(a/2+\rho b)Y+(ab-\rho)Z\right],
\quad D_{ab}^\dagger D_{ab}=(1-p)I.
\tag{RP11}
$$

The real quaternion inner products, or direct Pauli multiplication, give

$$
\begin{aligned}
\frac{\operatorname{Tr}(D_{ab}^\dagger D_{-a,b})}{2(1-p)}
 =\frac{\operatorname{Tr}(D_{ab}^\dagger D_{a,-b})}{2(1-p)}
 &=-\frac{p}{3(1-p)},\\
\frac{\operatorname{Tr}(D_{ab}^\dagger D_{-a,-b})}{2(1-p)}
 &=\frac{p/3-\rho ab}{1-p}.
\end{aligned}
\tag{RP12}
$$

For target $G_{ab}=(I-iaZ-ibX)/\sqrt3$ the corresponding absolute
half-traces are all $1/3$. Photon pre/post unitaries preserve these
overlaps, spin phases preserve their magnitudes and matched flips permute
the same pairs. A complement locally equivalent to $G$ would therefore
require $p=1/2$ from a neighboring pair. Then
$\rho=\pm1/\sqrt{12}$ and the opposite-pair values have magnitudes
$|1/3\pm1/\sqrt3|\ne1/3$, a contradiction.
A local-product rejected unitary would require all sector photon
operators proportional, so the neighboring magnitude would be one;
that requires $p=3/4>9/16$. Thus neither a second corrected $G$ nor a
harmless local retry completes this projective one-helper circuit.
For these diagonal unitary branches, arbitrary local pre/post spin
operations again reduce to matched flips and phases by the rank-one
spin-factor argument above. Additional contacts, station ancillas,
middle instruments, larger helpers and general corrections remain
outside this projective-complement argument. Terminal filters and
middle photon instruments are treated separately below.
At most one of the two projective outcomes can therefore be a locally
corrected $G$ flag. A zero-weight branch cannot evade the single-branch
bound by putting deterministic $G$ in its complement.

The stronger total-terminal-instrument statement uses the **same source
and middle unitary for all records**. Refine its accepted records to
photon rows $M_m$ with $\sum_mM_m^\dagger M_m\le I_4$, absorbing
each known photon output correction into its row. For the fixed circuit,
the matched spin flips are fixed by its common pre-contact spin bases;
absorb them once. The remaining accepted corrections are spin phases.
Every nonzero corrected-$G$ Fourier matrix is invertible, and hence

$$
C_mC_n^{-1}
=\operatorname{diag}(M_{m0}M_{n0}^{-1},M_{m1}M_{n1}^{-1})
\quad\hbox{is block diagonal}.
\tag{RP12a}
$$

The square block cancellation uses four dimensions and the common
$W,E_i$; it fails for a general larger helper or a changed intermediate
history. Common photon output unitaries multiply this test by block
diagonal matrices and do not alter its vanishing off-diagonal blocks.
For $\delta=\alpha_m-\alpha_n$, put $c=\cos\delta$, $s=\sin\delta$.
Direct multiplication gives

$$
C_0^{-1}=\begin{pmatrix}0&iX\\iZ&iY\end{pmatrix},\qquad
C_0R_\delta C_0^{-1}
=I\otimes(cI-sZ)+sJ\otimes Y,\qquad
J=\begin{pmatrix}0&-2\\1&0\end{pmatrix}
  =-X/2-3iY/2.
\tag{RP12b}
$$

Thus the ratio test is $R_{\beta_m}[I\otimes(cI-sZ)+sJ\otimes Y]
R_{-\beta_n}$. Its physical-$I$ and physical-$Z$ off-diagonal
coefficients are respectively
$ci\sin(\beta_m-\beta_n)X$ and
$-si\sin(\beta_m-\beta_n)X$. Since $c,s$ cannot both vanish,
$\sin(\beta_m-\beta_n)=0$. The remaining physical-$Y$ coefficient
contains $sR_{\beta_n}JR_{-\beta_n}$ up to sign. Conjugation about
$X$ preserves its nonzero $X$ coefficient $-1/2$, so it cannot be
diagonal. Therefore $\sin(\alpha_m-\alpha_n)=0$ too.
All accepted records require the same spin phases modulo global signs.

After that common correction, rank-one Choi support forces every
accepted fine Kraus to be $\lambda_mG$, including hidden records.
Stack its photon rows into $M_{\rm stack}$ and contract the record
onto $\sum_m\lambda_m|m\rangle/\sqrt p$, where
$p=\sum_m|\lambda_m|^2$. This gives one photon contraction with
Kraus $\sqrt pG$, to which (RP7)–(RP10) apply. Consequently

$$
\sum_{\text{accepted exact locally corrected }G\text{ records}}p_m
\le\frac9{16}.
\tag{RP12c}
$$

This mathematical compression does not grant a free physical record
eraser. Intermediate readout can change $E,W$, local nonunitary spin
filters change the phase factors, and extra spin ancillas change the
rank-one spin argument. None is covered by (RP12c). In particular it
does not constrain the four differently corrected eight-mode records
of (RP3).
The reverse fixed word has the same cap by relabelling the two stations
and conjugating the photon by a Hadamard. This is a mathematical change
of labels/basis, not a physical remote spin SWAP. A recorded classical
lottery over either word and over pre-chosen sources/middle circuits is
also bounded by convexity. Its record may select $E,W$ before the
contacts; intermediate measurement-dependent changes are outside this
fixed-circuit proof. The purely photon middle-instrument model is
bounded separately in (RP12g)–(RP12n).

There is a separate, weaker **total** bound allowing terminal local
spin filters in four photon dimensions. Keep the same fixed source
isometry and middle $U(4)$, no intermediate records or pre-contact
spin-ancilla encodings, and no additional shared ancillary quantum
resource beyond the arbitrary supplied $ABFR$ input.
After the last contact allow any terminal separable instrument, hence
any terminal LOCC with local workspaces, filtering and classical
communication. Fine-grain its successful Kraus operators as
$M_m\otimes L_{A,m}\otimes L_{B,m}$, with their sum of positive
effects at most identity on the full post-contact Hilbert space.
The target on each accepted leaf is $\lambda_mG$.

Across either spin cut the two factors are
$L_{A,m}|i\rangle\langle i|V_A$, where $V_A$ is the common pre-contact
spin unitary. Target invertibility excludes rank-one local filters.
The diagonal target Schmidt span again forces each rank-one factor
diagonal, so $V_A,V_B$ are monomial with common matched permutations.
Absorb them once. Every successful spin filter is an invertible
diagonal $D_{A,m}\otimes D_{B,m}$. With normalized two-point
Hadamard $H$, division by its diagonal entries becomes the invertible
circulant $T_{A,m}=H D_{A,m}^{-1}H$, and similarly for $B$.
The Fourier matrix is, up to its scalar,
$(T_{B,m}\otimes I)C_0(T_{A,m}\otimes I)$.
The same square-factor ratio (RP12a) applies.

To check compatibility for complex filters, write
$T_{A,m}T_{A,n}^{-1}=aI+b\tau_x$, with complex $a,b$ not both zero.
From (RP12b),

$$
C_0[(aI+b\tau_x)\otimes I]C_0^{-1}
 =aI+ibI\otimes Z-ibJ\otimes Y.
\tag{RP12d}
$$

Its physical-$I,Z$ parts force
$T_{B,m}T_{B,n}^{-1}$ to be both circulant and diagonal, hence
scalar. The remaining part is proportional to
$bTJT^{-1}$ for an invertible circulant $T$. Since $T$ commutes with
$\tau_x$,
$\operatorname{Tr}(\tau_xTJT^{-1})
=\operatorname{Tr}(\tau_xJ)=-1$;
a diagonal matrix has zero such trace. Thus $b=0$ too.
All successful spin product filters are proportional to one common
invertible product $D=D_A\otimes D_B$:
$D_{A,m}\otimes D_{B,m}=c_mD$.
Normalize $\|D_A\|_{\rm op}=\|D_B\|_{\rm op}=1$ by absorbing
their scales into $c_m$.

Now the **global** terminal success-effect budget implies

$$
\left(\sum_m|c_m|^2M_m^\dagger M_m\right)\otimes D^\dagger D
\preceq I,
\qquad \sum_m|c_m|^2M_m^\dagger M_m\preceq I_4.
\tag{RP12e}
$$

The second inequality follows by evaluating the spin factor on a
maximal eigenvector of $D^\dagger D$, whose largest eigenvalue is one.
This is not an unjustified independent photon-POVM budget for unrelated
branch filters: the compatibility proof has first made their spin
factor common. Stack the rows $c_mM_m$ and compress their record onto
the successful $|\lambda\rangle/\sqrt p$ as before. The resulting
photon contraction, followed by $D$, implements $\sqrt pG$.
Before $D$, its Fourier matrix is
$C_{\rm eff}=\sqrt p(T_B\otimes I)(C_0/\sqrt3)(T_A\otimes I)$,
where $T_A=HD_A^{-1}H$, $T_B=HD_B^{-1}H$ have smallest singular
values at least one. Therefore

$$
2\sqrt{5p/3}\le\|C_{\rm eff}\|_*\le2,
\qquad
\sum_{\text{terminal-LOCC exact }G\text{ leaves}}|\lambda_m|^2
\le\frac35.
\tag{RP12f}
$$

The lower norm inequality follows by applying nuclear-norm
submultiplicativity to the two inverse matrices; the upper is the
physical factorization in (RP6). This is a valid, potentially loose
filter bound, not a $9/16$ claim for filters. It includes terminal
local ancillary workspaces by Kraus refinement. The extension below
also allows arbitrary middle photon records. Middle spin filters,
coherent spin-ancilla encoding before a contact, extra node visits
and pre-shared auxiliary entanglement remain outside these bounds
and require their own physical accounting.

### An intermediate photon instrument has a different optimum

Keep four photon dimensions, the fixed source isometry, exactly one
$A$ CZ followed by one $B$ CZ, and retained unknown $ABFR$.
Now permit an arbitrary **photon** instrument between the contacts,
record-dependent photon controls, arbitrary terminal photon instruments
and local spin-unitary feedback. Several adaptive photon operations
between the contacts are included by collecting their full records
into one instrument. No spin filtering or coherent spin-ancilla encoding
is allowed before or between the contacts, and there is no extra shared
auxiliary entanglement. A transient meter may be read or discarded;
retaining and coherently reusing it after the second contact adds
quantum memory outside this four-dimensional model.

In this class the optimal total exact-$G$ probability is
$3/(3+\sqrt5)\approx0.572949$, slightly above $9/16$ and below
the native ideal $3/4$. The following proof gives both the global
upper bound and a matching partial-measurement construction.

Fine-grain the surviving middle photon instrument, including hidden
and reset records, into Kraus operators $T_h:\mathbb C^4\to\mathbb C^4$
with $\sum_hT_h^\dagger T_h\preceq I_4$. Loss and other discarded
outcomes remain in the positive completeness deficit; they cannot
replace unknown $F$. Conditional photon unitaries are included in
$T_h$. Write $L=\operatorname{diag}(E_0,E_1)$,
so $\operatorname{Tr}L^\dagger L=2$. A successful terminal fine row has
Fourier matrix $C_{hm}=\operatorname{diag}(M_{hm,0},M_{hm,1})T_hL$.
It is invertible, so every square factor is invertible. Consequently
a singular $T_h$ has **zero** exact-$G$ success. A complete helper
projective measurement, or its fine-grained measure-and-reset channel,
has rank at most two per record; appending a fresh helper afterwards
does not restore that rank.

For a fixed nonsingular $h$, the ratio cancellation (RP12a) uses only
invertibility of the middle matrix, so (RP12b) still makes all
successful terminal spin phases equal. Compress these terminal rows
to one contraction $M_h$ and let $p_h$ be their total success weight.
The input $A$ basis and its matched flip are fixed before its contact.
Any conditional $B$ input basis on a successful leaf is monomial by
the same rank-one spin-factor argument. Its matched bit flip inserts
a known photon $Z$ at the $B$ query, which can be absorbed on the left
of $T_h$ without changing $T_h^\dagger T_h$. Spin phases commute with
the queries. Thus this feedback preserves the instrument budget and
the target form below. Absorb photon output corrections into $M_h$,
put $H_{hj}=(M_{hj}M_{hj}^\dagger)^{-1}$ and
$\mathcal R_\theta=R_\theta\otimes I$. Then

$$
\begin{aligned}
C_h&=\sqrt{p_h/3}\,\mathcal R_{\beta_h}C_0\mathcal R_{\alpha_h},
&H_{h0}^{-1}+H_{h1}^{-1}&\preceq I,\\
C_h^\dagger\operatorname{diag}(H_{h0},H_{h1})C_h
 &=L^\dagger T_h^\dagger T_hL,
&\sum_h\operatorname{Tr}
 [C_h^\dagger\operatorname{diag}(H_{h0},H_{h1})C_h]&\le2.
\end{aligned}
\tag{RP12g}
$$

The last inequality is the **joint** Kraus budget. It does not sum
unrelated single-branch probability bounds. Exact rank-one Choi support
justifies refining hidden terminal records before the compression.

To minimize each trace cost, drop its unitary right phase, put
$c=\cos2\beta$, $s=\sin2\beta$, and omit the history index.
The diagonal blocks of
$\mathcal R_\beta C_0C_0^\dagger\mathcal R_\beta^\dagger$ are
$B_0=(3+c)I/2+sX$ and $B_1=(3-c)I/2-sX$.
They commute and are positive: their determinants are
$(5c^2\pm6c+5)/4=[5(c\pm3/5)^2+16/5]/4>0$ and their traces
are $3\pm c\ge2$. Set $Q_j=H_j^{-1}$, with $Q_0+Q_1\preceq I$.
Pinching $Q_j$ in their common $X$ eigenbasis cannot increase the
objective $\sum_j\operatorname{Tr}(B_jQ_j^{-1})$.
Equivalently, Cauchy--Schwarz gives
$\langle x|Q_j^{-1}|x\rangle\ge1/\langle x|Q_j|x\rangle$.
For each eigenvalue $x=\pm1$, writing these positive diagonal entries
as $q_{jx}$, the scalar constraint $q_{0x}+q_{1x}\le1$ gives
$b_{0x}/q_{0x}+b_{1x}/q_{1x}\ge(\sqrt{b_{0x}}+\sqrt{b_{1x}})^2$.
Hence

$$
\operatorname{Tr}(H_0B_0+H_1B_1)
\ge6+2\bigl(\sqrt{d+cs}+\sqrt{d-cs}\bigr),
\qquad d=\frac{5+3c^2}{4}.
\tag{RP12h}
$$

Since $d\ge5/4$ and the following polynomial is at least $25/16$,
the squared root sum is
$2d+2\sqrt{d^2-c^2s^2}\ge5$. Combining with (RP12g) yields

$$
d^2-c^2s^2=\frac{25+14c^2+25c^4}{16},\qquad
\frac{6+2\sqrt5}{3}\sum_hp_h\le2,
\qquad
p_\star=\max\sum_hp_h=\frac3{3+\sqrt5}.
\tag{RP12i}
$$

Here is an exact two-history construction attaining the bound. Let
$r=\sqrt5$, $p_\star=3/(3+r)$, $\gamma=(3-r)/4$, and choose positive
square roots in

$$
\begin{aligned}
Q_0&=I/2+\gamma X,& Q_1&=I/2-\gamma X,
&\mathsf R&=\operatorname{diag}(\sqrt{Q_0},\sqrt{Q_1}),
&L&=I_4/\sqrt2,\\
\beta&=\pi/4,& \alpha_\pm&=\pm\pi/4,
&C_\pm&=\sqrt{p_\star/6}\,\mathcal R_\beta C_0\mathcal R_{\alpha_\pm},
&T_\pm&=\mathsf R^{-1}C_\pm L^{-1}.
\end{aligned}
\tag{RP12j}
$$

The eigenvalues of each $Q_j$ are $(5-r)/4,(r-1)/4$, strictly
between zero and one, and $Q_0+Q_1=I$.
The balanced source has block rows $E_0=E_1=I/\sqrt2$.
Write $Q_0^{-1}=hI-tX$, $Q_1^{-1}=hI+tX$, where
$h=1+3r/5$, $t=2r/5$, so $3h-2t=3+r$. Direct multiplication gives

$$
\begin{aligned}
A&=C_0^\dagger\mathcal R_\beta^\dagger
       \operatorname{diag}(Q_0^{-1},Q_1^{-1})
       \mathcal R_\beta C_0\\
 &=\frac{3h-2t}{2}I_4
   +\frac{h-2t}{2}\tau_z\otimes I
   +(h-t)\tau_y\otimes Z,\\
T_+^\dagger T_++T_-^\dagger T_-
 &=\frac{p_\star}{3}(3h-2t)I_4=I_4.
\end{aligned}
\tag{RP12k}
$$

The $\alpha_\pm$ conjugations cancel the last two terms of $A$ in
their sum, proving the middle instrument is complete. Use the common
terminal coisometry $M=[\sqrt{Q_0},\sqrt{Q_1}]$, which extends to a
four-mode unitary followed by one projective helper outcome. Its
accepted Kraus in each middle history is

$$
K_\pm=\sqrt{p_\star/2}\,
 e^{i\alpha_\pm Z_A+i\beta Z_B}G.
\tag{RP12l}
$$

Local spin phases therefore give exact $G$ with total weight $p_\star$.
These are full operator identities on arbitrary $ABFR$, rather than
known-input scores. The terminal rejected branches have not been
shown to be harmless retries.

The required middle primitive is a **full-rank weak measurement**.
Put $a_0=(h-2t)/2=(5-r)/10$, $b_0=h-t=(5+r)/5$ and
$D=-a_0\tau_y\otimes I+b_0\tau_z\otimes Z$.
Its two Pauli terms anticommute, so $D^2=(a_0^2+b_0^2)I$.
The middle effects and strength satisfy

$$
T_\pm^\dagger T_\pm
 =\frac I2\pm\frac{D}{3+r}
 =\frac{I\pm\nu S}{2},\qquad
S=\frac D{\sqrt{a_0^2+b_0^2}},\quad
\nu^2=3-\frac{6r}{5}\in(0,3/5),\qquad
(T_+^\dagger T_+)(T_-^\dagger T_-)
 =\frac{3r-5}{10}I\succ0.
\tag{RP12m}
$$

Both records have probability exactly $1/2$ for every input/reference:
the normalized photon source in spin sector $z=\pm1$ is
$[I;zI]/\sqrt2$, whose compression of both terms of $D$ is zero.
No complete projective helper read/reset can replace this weak
instrument. One implementation uses a four-mode basis change, an
unsharp QND meter and the conditional polar-decomposition unitaries
of $T_\pm$. It requires that readout before its conditional pulse;
a direct joint-meter implementation is a distinct supplied primitive.
The middle record and terminal good/bad record may reuse a meter only
with its actual reset, storage and readout time. The spin-phase
correction can be deferred to the output, so no extra $A$ quantum visit
is required. Destructive detection of this same photon loses $F$.
Meter survival, false heralds, unobserved fields, feedback latency and
the four-mode controls all remain paid resources.

There is also a weaker bound including **terminal** separable spin
filters after arbitrary middle photon records. Apply (RP12d)--(RP12e)
separately for each nonsingular $T_h$. Its successful filters share
a normalized product factor $D_h$, and their weighted photon rows
compress to a contraction. The inverse-filter circulants cannot
decrease the target nuclear norm. With
$S_h=\operatorname{diag}(M_{h0},M_{h1})$ this gives

$$
\frac{20}{3}\sum_hp_h
 \le\sum_h\|C_{h,\mathrm{eff}}\|_*^2
 \le2\sum_h\|T_hL\|_{\rm HS}^2\le4,
\qquad \sum_hp_h\le\frac35.
\tag{RP12n}
$$

The sharp value in (RP12i) is only for unitary spin feedback; (RP12n)
does not assert a sharp filtered optimum. Middle spin filters change
the photon-only Kraus budget, and pre-contact spin-ancilla encoding
changes the rank-one spin factors. Neither is covered. Extra contacts,
larger preserved quantum spaces and coherent reuse of a meter remain
separate ordinary resources in the physical comparison.

### A sequence bound with four persistent photon modes

Consider $n$ fresh unknown spin pairs $(A_i,B_i)$, the same unknown
retained photon qubit $F$, and arbitrary passive references. Put

$$
G_i=\frac{I-iZ_FZ_{A_i}-iX_FZ_{B_i}}{\sqrt3},\qquad
U_n=G_n\cdots G_1.
\tag{RP23}
$$

An ordinary circuit in the following restricted class has an exact
accepted full-input channel $p\operatorname{Ad}_{U_n}$ only if

$$
p\le\left(\frac35\right)^n.
\tag{RP24}
$$

The photon workspace has dimension four, including its one persistent
helper, at every query boundary. Each spin has exactly one complete CZ
encounter; a classically adaptive query permutation is allowed. Known
photon instruments, discarded fresh environments, classical records and
feedback, local spin-unitary controls, and photon/classical
postselection are allowed. No additional persistent quantum workspace,
spin ancilla/instrument, joint spin operation, preloaded auxiliary
entanglement, or extra controlled-vacuum encounter is supplied. The
complete unknown input is present before these calls. An environment
retained coherently for a later measurement counts as extra quantum
workspace even if it never recouples unitarily. This is an upper bound,
not a claimed optimum: the single-pair optimum (RP12i) is not being
multiplied. The ideal native all-plus port has weight $(3/4)^n$, but
both probabilities vanish with $n$.

**This is not an expected-cost or architectural separation.** The
deterministic, ancilla-free four-contact compiler (RP2) implements
$U_n$ with $4n$ encounters and no helper readout. Run it with classical
probability $1/2$ and otherwise abort before touching the input. Its
accepted channel is $\tfrac12\operatorname{Ad}_{U_n}$ at mean $2n$
contacts, exceeding $(3/4)^n$ for $n\ge3$. Under the separately supplied
eight-mode, lossless coherent-return interface (RP4), the $n$-pair
circuit has mean $3n$ **occupied** contacts and returns its helpers.
Running it with probability $2/3$ gives
$\tfrac23\operatorname{Ad}_{U_n}$ at mean $2n$ occupied contacts,
exceeding the native one-pass weight for $n\ge2$. Its $4n$ potential
opportunity calls are not $3n$ opaque queries. The controlled-vacuum
compiler (RP4a) is another mandatory comparator: with the enlarged path
interface, the same two occupied contacts per pair can reproduce the
native survivor and can admit the same two physical time layers. Thus
(RP24) supplies no occupied-contact, latency, loss, or delivered-rate
advantage over those interfaces. It also gives no bound for approximate
gates or terminal spin filtering.

**Query order and actual boundary ranks.** Refine observed records and
each discarded environment to fine Kraus histories, fixing that
refinement when its instrument is applied. Rank-one unitary Choi
support makes every nonzero successful fine history a scalar multiple
of $U_n$ after its permitted correction. On a fixed history, local
unitaries on a leaf before its unique encounter can be moved immediately
before it; all later leaf unitaries can be moved after it. They commute
with operations on other systems. The target spin-side Schmidt span is
$\operatorname{span}\{I,Z\}$ and has rank two for every leaf. Its
rank-one factors force matched pre/post bit permutations and phases.
These give invertible local changes of the two Fourier indices, which
do not alter any matricization rank. They do not permit arbitrary
spin filters or encodings.

Remove these local gauges and write the target's Fourier coefficients
in the spin $Z$ labels. For one pair, apart from $1/\sqrt3$, they are
$g_{00}=I$, $g_{10}=-iZ$, $g_{01}=-iX$, $g_{11}=0$. For a queried
leaf set $S$, let $T_S$ have columns indexed by its Fourier bits and
$F_{\rm in}$, and rows by the complementary bits and $F_{\rm out}$.
A four-mode fine history factors through its photon workspace at every
cut, so $\operatorname{rank}T_S\le4$.

For two pairs, use bit order $(A_1,B_1,A_2,B_2)$ and entries
$(g_{\epsilon_2}g_{\epsilon_1})_{F_{\rm out},F_{\rm in}}$,
omitting the common $1/3$. Direct exact multiplication gives

$$
\begin{array}{c|c}
S&\operatorname{rank}T_S\\ \hline
\{A_1,B_1\}&2\\
\{A_2,B_2\}&6\\
\{A_1,A_2\},\{A_1,B_2\},\{B_1,A_2\},\{B_1,B_2\}&8
\end{array}
\tag{RP25}
$$

Each mixed $8\times8$ determinant is $1$. In the reversed-pair case
the last two rows and columns vanish and the leading $6\times6$
minor has determinant $16$. Every one-/three-leaf cut has rank four.
For arbitrary $n$, set the Fourier bits of all but two selected pairs
to $00$. These are **Fourier slices**, not physical input choices:
each removed coefficient is $I/\sqrt3$, so no intervening photon
rotation remains. A slice cannot increase rank. Mixed cuts therefore
forbid two simultaneously open pairs, and reversed cuts forbid
finishing a later pair before an untouched earlier one. Every nonzero
successful history must visit pairs $1,\ldots,n$ in order, with either
internal order and adjacent encounters within each pair.

Let $J$ be the combined photon Kraus map in a gap between complete
pairs, including every operation and record in that gap. Write the
target matricization as $\lambda T=\mathcal A J\mathcal B$.
The target has rank two: its past and future coefficient stacks factor
through $F$, and Parseval and unitarity make those stacks full row and
column rank two. To infer the rank of $J$, the physical stacks
$\mathcal B,\mathcal A$ must instead have full rank four.

Fix all physical spin $Z$ labels except one pair. Its target Fourier
matrix is the invertible matrix
$C_0/\sqrt3$, multiplied by invertible common photon matrices and local
index gauges, where

$$
C_0=\begin{pmatrix}I&-iZ\\-iX&0\end{pmatrix}.
\tag{RP26}
$$

Its physical factorization is
$\operatorname{diag}(M_0,M_1)V\operatorname{diag}(E_0,E_1)$,
where the source and terminal sector blocks are $2\times2$ and $V$
is the combined map between that pair's encounters. Invertibility
forces all five factors invertible. For the prefix after the second
encounter, the four maps $\Pi_lV\Pi_kE$ have a positive-definite
horizontal-stack Gram matrix: it is the sector pinching of
$V\operatorname{diag}(E_0E_0^\dagger,E_1E_1^\dagger)V^\dagger$.
Thus the full prefix stack has row rank four. The time-reversed
argument gives suffix column rank four. Consequently
$\operatorname{rank}J=\operatorname{rank}(\mathcal A J\mathcal B)=2$.
This is a statement about the **combined gap**, not each constituent
Kraus map. In particular a unitary-only interpair gap cannot work.

**A determinant-normalized norm inequality.** For invertible complex
$2\times2$ matrices $R,T$, the nucleus obeys

$$
\|(I_\tau\otimes R)C_0(I_\tau\otimes T)\|_*
\ge2\sqrt5\sqrt{|\det R\det T|},
\tag{RP27}
$$

where $\|\cdot\|_*$ is the nuclear norm and $\tau$ is the block
index. Here is a complete argument. Set
$A_L=C_0C_0^\dagger$ and $A_R=C_0^\dagger C_0$. Multiplication gives

$$
A_L=\begin{pmatrix}2I&iX\\-iX&I\end{pmatrix},\quad
A_R=\begin{pmatrix}2I&-iZ\\iZ&I\end{pmatrix},\quad
A_\bullet^2-3A_\bullet+I_4=0.
\tag{RP28}
$$

They are positive definite because $C_0$ is invertible. Hence
$\sqrt{A_\bullet}=(A_\bullet+I_4)/\sqrt5$,
$\operatorname{Tr}_\tau\sqrt{A_\bullet}=\sqrt5 I$, and
$\|C_0\|_*=2\sqrt5$.

For Hermitian $L,M$, the function
$t\mapsto\log\|e^{tL}Ce^{tM}\|_*$ is convex. Indeed
$F(z)=e^{zL}Ce^{zM}$ is entire and uniformly bounded on every finite
vertical strip: its imaginary exponential factors are exterior
unitaries. For every fixed $D$ with $\|D\|_{\rm op}\le1$,
$\operatorname{Tr}(D^\dagger F(z))$ is bounded analytic, with boundary
moduli at most the two boundary nuclear norms. The scalar three-lines
inequality and nuclear/operator-norm duality give log convexity. For
completeness, three-lines follows by rescaling to $0\le\Re z\le1$,
dividing the scalar function by
$\exp[(1-z)\log m_0+z\log m_1]$, multiplying by
$e^{\epsilon z^2-\epsilon}$, and applying the maximum principle on
large rectangles. The horizontal-edge contribution tends to zero;
then let $\epsilon\downarrow0$. The positive boundary bounds $m_j$
exist because invertible exponentials preserve nonzero $C$.

For traceless Hermitian $H,K$, put $L=I_\tau\otimes H$ and
$M=I_\tau\otimes K$. The derivative of the nuclear norm at the
invertible $C_0$ is

$$
\left.\frac{d}{dt}\|e^{tL}C_0e^{tM}\|_*\right|_{t=0}
=\operatorname{Tr}(L\sqrt{A_L})+
 \operatorname{Tr}(M\sqrt{A_R})=0.
\tag{RP29}
$$

One obtains this formula directly by differentiating
$S(t)^2=C(t)^\dagger C(t)$ for its positive square root, multiplying
the resulting Sylvester equation by $S^{-1}$ and taking a trace.
Thus the convex logarithm has its global minimum at zero. Finally use
the polar orientations $R=U_RP$ and $T=QU_T$, with $P,Q>0$; the
unitaries are exterior, so no unitary is moved through $C_0$.
Writing $P=\sqrt{|\det R|}e^H$ and
$Q=\sqrt{|\det T|}e^K$ gives traceless Hermitian logarithms and proves
(RP27). Singular filters have the trivial zero lower bound. Query-index
phases $R_\alpha=e^{i\alpha X_\tau}$ commute with the $F$ filters
and can be removed by norm invariance. Reversing internal encounter
order interchanges $X,Z$ and is unitarily equivalent via the photon
Hadamard, so the same inequality applies.

**Actual recorded frontiers and their metric.** A viable frontier is an
actual circuit prefix immediately before the next pair's first query,
including the entire preceding gap, with nonzero conditional accepted
CP weight. It is not a complete successful future relabelled as a
prefix. Rank-two factorization and its uniqueness give its corrected
prefix operator as

$$
(I_{\rm past}\otimes E_vH_v)U_{\rm past},\qquad
E_v^\dagger E_v=I_2,\quad H_v\text{ invertible},\qquad
w_v=|\det H_v|.
\tag{RP30}
$$

At the root $H=I$; arbitrary source instruments may be included in the
first stage. At terminal success $H=\lambda I$ up to a photon unitary,
so $w=|\lambda|^2$. Changing the isometric gauge of $E_v$ does not
change $w_v$.

This determinant weight is established entanglement machinery:
$|\det H|$ is the unnormalized qubit $G$-concurrence of
$(H\otimes I)|\Phi_2\rangle$. [Gour, PRA **71**, 012318
(2005), Eqs. (19), (21)–(22) and (45)](https://arxiv.org/html/quant-ph/0410148v2)
gives determinant scaling and average product bounds for chains of
independent shared states under LOCC. Those results do not supply the
present fixed-CZ, four-mode coefficient: that needs the query-order,
common-phase and physical-budget arguments here. No new determinant
monotone or general product-bound technique is claimed.

The past-spin frame cannot secretly depend on the future continuation.
Choose one continuation to fix a frame $D_v$. A second has past
correction $D_w$ and suffix $F_w$ acting only on the photon and future
spins. Cancelling $U_{\rm past}$ on the **input side** gives

$$
(D_wD_v^\dagger)_{\rm past}\otimes(F_wE_vH_v)
=\lambda_w I_{\rm past}\otimes U_{\rm future}.
\tag{RP31}
$$

Both factors are nonzero, so $D_wD_v^\dagger$ is scalar. This covers
matched flips as well as phases. There is also an intrinsic measurable
definition of $w_v$, requiring no measurable choice of a future frame.
Fix past computational labels $z_0$ and let $P_v(z_0)$ be the actual
prefix map from $F$ to all past-spin outputs and the four photon modes.
Equation (RP30) gives
$w_v=\sqrt{\det[P_v(z_0)^\dagger P_v(z_0)]}$, independent of $z_0$.
Unvisited-spin pre-unitaries can be deferred to their own query; they
commute with this prefix.

**The complete two-encounter budget.** At a viable parent with metric
$H_{\rm in}$, let $S_r:\mathbb C^2\to\mathbb C^4$ be the source/
preparation maps, including the parent's isometric embedding, and
$V_{rh}$ the middle photon maps. Their genuine Kraus budgets give
$\sum_rS_r^\dagger S_r\le I_2$ and
$\sum_hV_{rh}^\dagger V_{rh}\le I_4$. In sector coordinates put
$L_r=\operatorname{diag}(E_{r0},E_{r1})$, so
$\sum_r\operatorname{Tr}L_r^\dagger L_r\le2$.
For fixed $r,h$, each viable child's combined boundary map is
$K_m=E_mM_m$ with $E_m$ isometric and
$\sum_mM_m^\dagger M_m\le I_4$. Dead records are positive terms
that may be omitted. A terminal $2\times4$ output row can be embedded
isometrically in four modes. The child's Fourier factorization is

$$
\begin{aligned}
C_m&=\operatorname{diag}(M_{m0},M_{m1})V_{rh}L_r\\
&=(I_\tau\otimes H_m)R_{\beta_m}
  \frac{C_0}{\sqrt3}R_{\alpha_m}
  (I_\tau\otimes H_{\rm in}^{-1}).
\end{aligned}
\tag{RP32}
$$

It is invertible for every viable child. Hence $V_{rh}$ and each
sector block are invertible. For an $A$-first history, its input basis
and matched bit permutation are fixed by $r$ before the first query;
$B$'s are fixed by $r,h$ before its query. The rank-one spin-factor
argument forces all viable children's output permutations to match
these same input permutations. They can be absorbed at $r$ or $r,h$
without changing the shared $V_{rh}L_r$ or its budget. There is no
child-dependent source/middle relabelling. Only diagonal spin phases
can still vary with $m$; the reversed internal order is identical.

For two such children, $C_mC_k^{-1}$ is block diagonal in $\tau$.
The invertible exterior $F$ filters cannot remove an off-diagonal
block, and $H_{\rm in}$ cancels. Therefore this condition is exactly
block diagonality of
$R_{\beta_m}C_0R_{\alpha_m-\alpha_k}C_0^{-1}R_{-\beta_k}$.
With $J=\left(\begin{smallmatrix}0&-2\\1&0\end{smallmatrix}\right)$,
direct multiplication gives

$$
C_0(aI+bX_\tau)C_0^{-1}
=aI+i b I_\tau\otimes Z-i b J\otimes Y.
\tag{RP33}
$$

The independent physical $I,Z$ terms require
$\sin(\beta_m-\beta_k)=0$. The remaining $Y$ term requires
$\sin(\alpha_m-\alpha_k)=0$: otherwise its $X_\tau$ trace is
$\operatorname{Tr}(X_\tau R_\beta J R_{-\beta})
=\operatorname{Tr}(X_\tau J)=-1$, inconsistent with a diagonal
matrix. Thus the phases agree modulo $\pi$. Absorb the resulting
scalar signs into $H_m$. Invertibility of the common $V_{rh}L_r$
then gives a single row $M_{\rm base}$ with
$M_m=H_mM_{\rm base}$ for all these children.

Let $S=\sum_mH_m^\dagger H_m$ and $T=\sqrt S$.
The true terminal budget says $M_{\rm base}^\dagger S M_{\rm base}
\le I$, so $M_{\rm tot}=TM_{\rm base}$ is a contraction. The sum is
bounded because $M_{\rm base}$ has a right inverse. The replacement
row has the same source/middle factorization and Fourier matrix
$C_{\rm tot}=(I_\tau\otimes T)R_\beta(C_0/\sqrt3)R_\alpha
(I_\tau\otimes H_{\rm in}^{-1})$.
This is a feasible row for a norm inequality, not an equality of the
original flagged CP instruments. The $2\times2$ Minkowski determinant
inequality, (RP27), and Schatten Cauchy–Schwarz give

$$
\begin{aligned}
\sum_m|\det H_m|&\le\det T,\\
\frac{20}{3}\frac{\det T}{|\det H_{\rm in}|}
&\le\|C_{\rm tot}\|_*^2
\le2\|V_{rh}L_r\|_{\rm HS}^2,\\
\sum_{r,h}\|V_{rh}L_r\|_{\rm HS}^2
&\le\sum_r\operatorname{Tr}L_r^\dagger L_r\le2.
\end{aligned}
\tag{RP34}
$$

The terminal factor two is its $2\times4$ contraction's squared
Hilbert–Schmidt norm bound. For completeness, Minkowski for two
positive $2\times2$ matrices follows by conjugating one to $I$ and
using $\operatorname{Tr}B\ge2\sqrt{\det B}$; induction and continuity
give finite/countable sums. Thus (RP34), summed over the actual source
and middle records, proves

$$
\sum_{\text{viable children }m}w_m\le\frac35 w_v.
\tag{RP35}
$$

There is no independent per-leaf terminal budget or multiplicity factor.
For standard Borel continuous records, use finite-dimensional Kraus
densities relative to a scalar control measure. The budgets become
integrals. Integral Minkowski follows from concavity and homogeneity
of $\sqrt{\det}$: for $S=\int A\,d\mu$ of nonzero trace use
$d\nu=(\operatorname{Tr}A/\operatorname{Tr}S)d\mu$ and
$B=A\operatorname{Tr}S/\operatorname{Tr}A$. Then $B$ has constant
trace, is bounded, and $S=\int B\,d\nu$; Jensen gives
$\sqrt{\det S}\ge\int\sqrt{\det A}\,d\mu$. The zero case is
immediate. Integrability follows from the same row right inverse.
Phase agreement holds almost everywhere against a viable reference
record, while the intrinsic potential is measurable. Nonnegative
Tonelli and induction through the $n$ actual pair frontiers now give
$p=\sum_{\rm terminal}|\lambda_v|^2\le(3/5)^n$.
Dead/wrong-order histories and nontermination contribute no accepted
mass. Anisotropic intermediate $H_v^\dagger H_v$ are fully included;
neither scalar stage yields nor independent acceptance were assumed.

Exact Choi rank and exact tensor minors are essential here. Small
approximation error can change those ranks, so this argument supplies
no error-dependent extension. It does not cover terminal spin filters,
middle spin instruments, spare coherent memories, pre-contact node
encodings, extra encounters, or the larger vacuum-controlled hardware
interfaces. Those exclusions, the mean-cost countercomparisons next
to (RP24), and the actual source/router/storage/readout/loss costs
remain part of every application of the bound.


### Coherent retries and an exit-time correction key

A different service can remove per-round nondestructive readout without
delivering an unkeyed fixed gate. Put $S=Z_AZ_B$, so $S^2=I$ and
$[S,G]=0$. On minus, the photon-only correction $-iY_F$ turns
$K_-=iY_FS/2$ into $S/2$. If the full vacuum/idle and clock completion
permits these same base attempts, coherent routing with hard cap $N$
gives the exact isometry on every $ABFR$

$$
W_N=\sum_{j=1}^N\frac{\sqrt3}{2^j}|\mathrm{exit}_j\rangle
                  S^{j-1}G
       +2^{-N}|\mathrm{fail}_N\rangle S^N.
\tag{RP36}
$$

The orthogonal time/route labels retain the physical relative phases.
Each live pass either exits once or continues, so multiplication of
$\sqrt3G/2$ by $(S/2)^{j-1}$ proves the formula. Exit probabilities
are $3/4^j$, accepted mass is $1-4^{-N}$, and lossless mean occupied
data contacts are $(8/3)(1-4^{-N})$. These are not hard-window or
wall-time counts. If all labels remain coherently stored, the
one-photon code has at least $2(N+1)$ modes including $F$ and the
residual route, or an explicit released-output stream with its own cost.

A later classical $j$ permits local correction $S^{j-1}$ if intervening
operations are compatible. For terminal Pauli measurements it can
simply relabel the appropriate $X/Y$ signs. Before that key is read or
coherently corrected, however, it is a quantum register entangled with
the payload. Its off-diagonal time blocks can depend on $\rho$.
Discarding it in the formal infinite ideal process gives

$$
\mathcal C_{\rm untracked}
=\frac45\operatorname{Ad}_G+\frac15\operatorname{Ad}_{SG},
\qquad
G(PQ)G^\dagger=\frac{-PQ+2iP-2iQ}{3}.
\tag{RP37}
$$

The first identity sums odd/even exit probabilities; it is not
$\operatorname{Ad}_G$. The second shows why omitting the minus-route
photon $Y$ is substantive: propagating that uncorrected fault through
$G$ gives a sum of Pauli words, not a Pauli frame. A final destructive
photon record can reveal the exit time for a terminal sampling task;
keeping optical $F$ with an online herald instead needs an actual
nondestructive arrival/key port, coherent correction, or a specified
matter-transfer interface such as (RS27a) with all its resources.

The declared raw CZ completion has a different frame. With
$\mathsf S_j=\operatorname{diag}(1,i)$ and
$T=\mathsf S_A\mathsf S_B$, the literal occupied photon wrappers obey
$R_A=e^{i\pi/4}\mathsf S_A^\dagger U_A$ and the analogous $R_B$.
Thus raw flags are $iT^\dagger K_\pm$. Choose a physical photon-only
output gauge: phase $-i$ on plus and operation $-Y_F$ on minus.
Since $T^2=S$, the round maps and their finite-cap composition are

$$
\begin{aligned}
A_{\rm raw}&=\frac{\sqrt3}{2}T^\dagger G,
&B_{\rm raw}&=\frac12T,\\
W_{N,\rm raw}
&=\sum_{j=1}^N\frac{\sqrt3}{2^j}|\mathrm{exit}_j\rangle
                        T^{j-2}G
 +2^{-N}|\mathrm{fail}_N\rangle T^N.
\end{aligned}
\tag{RP38}
$$

All $T$ factors commute with $G$. Without that specified output gauge,
retaining the literal flags and applying only $-iY_F$ on minus gives
additional $i^j$ and $i^N$ phases on exits and residual; coherent time
labels do not permit dropping them. A single unconditional finish can
shift every spin power together, but cannot remove its $j$ dependence.
The raw key is $j\bmod4$, a local Clifford frame, not merely parity.
A photon-only operation confined to one minus route cannot remove its
spin $T$ factor. This excludes neither recombining exit times nor
selecting a frame subset, which changes the instrument and yield.

When $j$ is known **before** terminal basis choice, Clifford frames
only change Pauli measurement bases. Late sign relabelling cannot in
general repair a previously fixed $X$ result: $\mathsf S_A$ changes
the relevant basis to $Y$, and inputs $|+\rangle,|-\rangle$ become
indistinguishable by that fixed $X$ measurement. Specify basis
feedforward, a compatible task such as spin-$Z$ readout, or active
compensation. All later unconditional spin pulses and free evolution
also act on already-exited spins and must be included at a common
finite-cap finish. No infinite-duration online service is inferred.

Loss needs the full exit/continue maps $\widehat A,\widehat B$ on
one-photon **and vacuum**, with their controller, bath and time records.
At cap $N$ the ordered exits are $\widehat A\widehat B^{j-1}$ and
the residual is $\widehat B^N$, or the actual nonstationary products.
Without a meter there may be no early loss stop: empty windows, spin
idling and false terminal arrival records still count. Only a declared
stationary scalar survivor with unit plus bypass gives
$a=3t^2/4$, $b=t^2r/4$ and delivered mass
$a(1-b^N)/(1-b)$, where $r$ includes the photon correction/return.
It is not fitted by detector efficiency or mean polarization fidelity.

The same supplied full timed controlled-vacuum interface lets the
ordinary serialized/qualified-parallel circuit (RP4a) append exactly
this minus-$Y$ route and loop, matching all exit and loss records.
Retimed elastic products alone do not prove that premise. Also the
two-helper ordinary state $\tfrac12\sum_{mn}|mn\rangle
Z_A^mZ_B^nG|\psi\rangle$ in (RP3) needs no internal QND readout if
the endpoint allows those terminal keys and deferred Pauli frames.
For such sampling, its ideal scalar weight $t^2$ is at least
$3t^2/(4-t^2)$; protected eight-mode processing and all terminal access
remain paid. Coherent native exit bins must not be free while ordinary
temporal labels are excluded. The fixed four-CZ and adjustable-angle
ordinary gates remain further comparators. Endpoint-dependent meter
removal therefore establishes no native hardware advantage.

### A physical meter is a complete instrument, not one efficiency

This readout/retry discussion concerns the online classical-flag
service. The designated one-shot output port following (RP1), and its
ordinary selected-port and serialized comparisons, do not require this
meter or its measurement-decision hold.

After a path interferometer, plus and minus occupy different rails.
Reading that label destructively absorbs the photon carrying $F$.
An unmeasured output rail is a quantum key, not an available classical
spin-feedback signal. A common-rail presence measurement also does not
distinguish plus from minus. One can compose ideal rail-selective
occupancy meters to resolve $\{+, -,\mathrm{vacuum}\}$, or specify a
time-multiplexed meter with its reset/readout/delay; neither interface
follows just from coherent routing. Monitoring a discarded minus port
and accepting silence retains plus in an exactly lossless model, but
consumes the minus photon and therefore gives no same-$F$ retry. Under
loss, silence also includes vacuum.

[Niemietz et al., Nature **591**, 570–574
(2021)](https://doi.org/10.1038/s41586-021-03290-z) demonstrate a
polarization-preserving nondestructive photon detector using an atom and
two crossed cavities. Their [primary manuscript, Methods and
supplement](https://arxiv.org/html/2103.14677) report, for the stated
weak-coherent-pulse experiment, surviving-photon herald probability
$\Pr(H\mid S)=0.79\pm0.03$, survival $0.31\pm0.01$, and conditional
mean polarization fidelity $0.962\pm0.003$. The $79\%$ is not
$\Pr(S\mid H)$. Vacuum/multiphoton priors, dark heralds, loss and
atomic readout remain separate records. These averages do not specify
an arbitrary-reference conditional channel. Microwave $\pi/2$ pulses
and fluorescence take about $5.8$ and $7.5\,\mu\mathrm{s}$ respectively;
the complete control sequence and feedback delay must be included.
The actual presence primitive supports a physical investigation, but is
not a demonstrated path-$X$/survival meter for (RP1).

The following scalar ledger is conditional on its stated ideal
instruments. Let each occupied node contact survive with probability
$t$, independent of data/history, with the exact surviving CZ; let a
correct helper measurement have survival $m$ and per-round routing and
storage survival $r$. Put $q=t^2mr$. With a genuine fatal-erasure flag,
a native round gives good exit $3q/4$, identity retry $q/4$, and fatal
loss $1-q$. Hence

$$
D_N=\frac{3q}{4-q},\qquad
\mathbb E N_{\rm rounds}=\frac4{4-q},\qquad
D_4=t^4r_4,\quad D_8=t^2m^2o,\quad D_3=(tm)^3r_3.
\tag{RP13}
$$

$r_4,o,r_3$ include each ordinary circuit's own optics/holds; $D_8$
assumes two independent binary-meter survivals, not a joint meter.
The mean number of scheduled native node contacts is $8/(4-q)$,
equal to $8/3$ at $q=1$. If each round also uses one cavity meter,
its lossless total mean is four cavity encounters. This mean does
not order survival against four fixed contacts. Actual occupied
counts require the locations of losses rather than $q$ alone.
With $r_4=1$, $D_N\ge D_4$ exactly when
$mr\ge4t^2/(3+t^4)$. For $t,m>0$, $D_N\ge D_8$ exactly when
$r(3+t^2m^2o)\ge4mo$.
At $m=t$, $r=o=r_4=1$ these inequalities hold because
$t^4-4t+3=(t-1)^2(t^2+2t+3)\ge0$; equal mean contact count does not
by itself order survival. Conversely a supplied joint four-outcome
meter with the same $m,r$ gives ordinary delivery $q\ge D_N$.
At $m=0.31$ the common-survival model cannot both beat $t^4$ and
deliver $0.1$: the first inequality gives $t^2\le mr$, so
$D_N\le3m^2/(4-m^2)=961/13013<0.1$.
This rejection is **not** valid when plus bypasses the lossy meter.

There is a stronger closure of this same **common reliable-meter toy**
when the separately priced coherent-return ports of (RP4) are supplied.
Set $r=1$ and the ordinary extra routing losses to zero for this
declared comparison. Then

$$
\begin{aligned}
D_C-D_N
&=\frac{t^2 N(t,m)}{4(4-mt^2)},\qquad
D_C=\frac{t^2(1+t)^2}{4},\\
N(t,m)
&=\frac t3\bigl[24+8t+t(1-t)(t+3)\bigr]
 +\left(\frac13-m\right)\bigl[t^2(1+t)^2+12\bigr]\ge0
\quad(0\le t\le1,\ 0\le m\le1/3).
\end{aligned}
\tag{RP13a}
$$

Expansion gives $N=4(1+t)^2-m[t^2(1+t)^2+12]$ and the denominator
is positive. Thus $m=.31$ is dominated at every $t$ in this toy;
both deliveries vanish at $t=0$, and the inequality is strict for
$t>0$. This uses protected spectator modes, coherent returns, the
correct vacuum-relative spin phases and lossless extra ordinary optics.
It does not cover the plus-bypass instrument below, false flags,
unequal route transfers, timed reservoir records or actual device
statistics. It is not universal ordinary hardware dominance.

If plus survival is $\ell_+$ and corrected-minus return survival is
$\ell_-$, with otherwise ideal flags, the correct sum is instead

$$
D_{N,\rm asym}=\frac{t^2p\ell_+}{1-t^2(1-p)\ell_-},
\qquad p=3/4.
\tag{RP14}
$$

The optimistic $\ell_+=1$, $\ell_-=m$ gives
$3t^2/(4-t^2m)$. Plus may still need to wait for atomic readout and
branch-conditioned spin control; its delay loss belongs in $\ell_+$.
For one concrete hold implementation this is decisive. The
[Niemietz Methods, Appendix D](https://arxiv.org/html/2103.14677)
uses fiber attenuation $4\,\mathrm{dB/km}$ near $780\,\mathrm{nm}$.
Its post-reflection microwave $\pi/2$ and fluorescence components give
a nominal $5.8+7.5=13.3\,\mu\mathrm{s}$, not a measured total latency;
electronics and gaps add time. Assuming group velocity
$2\times10^8\,\mathrm{m/s}$, a fiber-only hold needs $2.66\,\mathrm{km}$,
or $10.64\,\mathrm{dB}$, with survival
$b_{\rm delay}=10^{-1.064}\approx0.0863$.
If **every accepted plus** waits in that spool for the clean-$G$
dark-hit-dump and spin-feedback policy, $\ell_+\le b_{\rm delay}$, $\ell_-\le1$
and $t\le1$ in (RP14) imply $D_{N,\rm asym}\le b_{\rm delay}<0.1$.
This excludes that particular hold implementation, not faster meters,
frequency conversion or matter storage. Those change the instrument
and cost and must also be offered to ordinary protocols.
Immediate plus forwarding with later dark-hit spin errors, deferred
flags or a different frame policy is a different service; this cap
does not exclude it.
Ordinary helper meters must receive the same bypass option: with
independent uniform helper bits, survival one on zero and $m$ on one
gives $D_{8,\rm asym}=t^2(1+m)^2o/4$. The readout-free coherent return
has (RP4). These are comparator points, not optimal ordinary frontiers.

To expose false/missed heralds without fitting a quantum map from mean
numbers, consider the following **defined** classical-instrument model.
Let $\eta=\Pr(H\mid\text{surviving minus})$, $d$ be an empty-bypass
dark-hit probability, $b_+$ the plus bypass survival, and
$r_M,r_R,r_W$ the minus pre-decision, repeat-return and wrong-exit
transmissions. Suppose all survivors preserve $F$ exactly. Pass plus on
atomic zero, dump plus on atomic one, and correct/return minus on atomic
one. The good exit, true surviving repeat and missed-minus wrong exit
weights are

$$
a=t^2p b_+(1-d),\qquad
b=t^2(1-p)r_Mm\eta r_R,\qquad
w=t^2(1-p)r_Mm(1-\eta)r_W.
\tag{RP15}
$$

If atomic-zero survivors from both paths are delivered, good/wrong
weights are $a/(1-b)$ and $w/(1-b)$.
Because $\operatorname{Tr}(G^\dagger PQ)=0$, their conditional
entanglement fidelity is $a/(a+w)$. With the illustrative
$m=.31$, $\eta=.79$, $d=0$ and other transmissions one, it is about
$0.9788$; this is not a source-certified channel prediction or a
universal $79\%$ fidelity cap.
An additional path-resolved output switch can dump minus on atomic
zero, converting surviving misses into erasures; the good delivery
remains $a/(1-b)$ in this model. That switch, optical storage and
feedback are paid. Plus must wait to be dumped on a dark hit before an
erroneous global spin correction; releasing it early changes the
instrument. Ordinary path-gated helper readout similarly has per-bit
good surviving weight $[b_+(1-d)+m\eta]/2$, and the independent
two-bit comparator is its square times $t^2o$.

The $b$ in (RP15) counts true surviving repeats, not every announced
repeat. A lost photon can produce a hit and cause further empty rounds.
Such histories cannot deliver the old unknown $F$, but they consume
calls/reset/time. Their costs cannot be inferred from $1/(1-b)$.
A delivered-output service may score vacuum zero; an **online heralded**
gate must also bound false accepted vacuum. A common final-arrival
check applies to ordinary outputs too, while native same-photon retry
requires its additional branch record. No-click selection is not
recovery of a lost $FR$ state.

For the real instrument let $T$ be the corrected true surviving-repeat
CP map, $A$ the clean exit, and $W$ a wrong exit if delivered. Then

$$
\mathcal C_{\rm delivered}=\sum_{j\ge0}A\circ T^j
\quad\text{or}\quad\sum_{j\ge0}(A+W)\circ T^j.
\tag{RP16}
$$

For stopping and cost, use full maps $\widehat T,\widehat A$ on
one-photon **and vacuum**, including all retained records; the complete
accepted map is $\sum_j\widehat A\circ\widehat T^j$ and mean rounds
are $\sum_j\operatorname{Tr}\widehat T^j(\rho)$.
Persistent bath/controller memory belongs in that state; otherwise
use the actual nonstationary products instead of a fixed power.
A scalar geometric reduction requires the corresponding scalar map
identities, not mean polarization fidelity. If $T=b\Lambda$ with
$\Lambda$ TP, $A=a\operatorname{Ad}_G$ and
$\tfrac12\|\Lambda-\operatorname{Id}\|_\diamond\le\delta$, the
normalized delivered map differs from $\operatorname{Ad}_G$ by at most
$b\delta/(1-b)$ in half diamond norm: telescope
$\|\Lambda^j-\operatorname{Id}\|_\diamond/2\le j\delta$ and sum
$(1-b)\sum_jb^jj=b/(1-b)$.
This reference-inclusive bound is conditional on constant $b$ and a
uniform channel error; the measured six-state mean does not supply it.

### Microwave number readout and the retained-qubit port

[Kono et al., *Quantum non-demolition detection of an itinerant
microwave photon*](https://doi.org/10.1038/s41567-018-0066-3),
[primary v1, Figs. 1–4, Methods and supplement](https://arxiv.org/html/1711.05479v1),
report detection efficiency $0.84\pm0.02$ from the weak-input
qubit-flip slope, survival $0.87\pm0.03$ from reflected/input mean
photon number in corrected tomography, and no-input flip probability
$0.0147\pm0.0005$. These are not survival conditioned on a hit.
Their one-coaxial-pulse apparatus uses $25\,\mathrm{ns}$ qubit pulses,
$500\,\mathrm{ns}$ readout, a $650\,\mathrm{ns}$ amplifier pump and
a $500\,\mathrm{ns}$ Gaussian input width. Ramsey intervals are
$800\,\mathrm{ns}$, or $1100\,\mathrm{ns}$ for tomography;
initialization uses readout postselection. These components are not
an end-to-end restart clock, and their final quadrature measurement
is not a demonstrated coherent-return loop.

The known weak coherent pulse used to characterize that detector must
not be identified with the present arbitrary unknown $FR$ payload.
If one **chooses** a hypothetical logical encoding
$c_0|0\rangle+c_1|1\rangle$ in a single pulse mode, reading its
number measures $F$ itself and removes that logical coherence. A
one-photon dual-rail or time-bin encoding instead needs a common
total-occupancy instrument on
$\operatorname{span}\{|10\rangle,|01\rangle\}$, with identical
meter and unresolved-reservoir states on the two alternatives.
Otherwise which-rail information dephases $F$ and can destroy its
coherence with $R$.
The single-mode measurements do not specify this extension. Sending
both bins through one unreset ancilla before a final read is a
conditional design, requiring matched complex transfer, retained
meter coherence across the separation, orthogonal outgoing bins and
a newly characterized longer clock. Retained $F$ and order $C$ need
four preserved one-photon modes; (RP3) needs its larger supplied
program/spectator ports. Ordinary schemes receive the same ports.

A minimal stationary dispersive reflection model illustrates why an
interaction Hamiltonian does not supply a free itinerant gate angle.
In the source's energy-decay convention put
$a=(\kappa_{\rm ex}+\kappa_{\rm in})/2$ and let the two spin
detunings be $\delta-s\chi$, $s=\pm1$. The elastic and internal-loss
columns can be written

$$
r_s(\delta)=1-\frac{\kappa_{\rm ex}}{a-i(\delta-s\chi)},
\quad l_s(\delta)=\frac{-\sqrt{\kappa_{\rm ex}\kappa_{\rm in}}}
 {a-i(\delta-s\chi)},\qquad
|r_s|^2=1-\frac{\kappa_{\rm ex}\kappa_{\rm in}}
 {a^2+(\delta-s\chi)^2}.
\tag{RP16a}
$$

Their squared norms sum to one. For
$\chi\kappa_{\rm ex}\kappa_{\rm in}\ne0$, subtraction gives
$|r_+|=|r_-|$ exactly when $\delta=0$. Moving the carrier therefore
generically changes spin-dependent survival as well as phase. The
lossless case is all-pass but still has finite-bandwidth phase and
bypass-matching requirements. This is a diagnostic of a specified
no-spin-flip model, not a device fit or a converse against tunable
hardware; relaxation, dephasing and additional output records need
their own dilation.

If the device additionally provides exact adjustable retained-qubit
Ising interactions $e^{-i\theta P},e^{-i\phi Q}$, the ordinary
three-rotation identity already proved above is mandatory. Its total
$P$ area is $\pi/4$ and $Q$ area is
$\beta=\arcsin(1/\sqrt3)$. Ideal corrected native retry uses mean
area $\pi/3$ on each axis. With hypothetical constant Hamiltonian
rates $g_P,g_Q$ and no other costs,

$$
T_N-T_E=\frac{\pi}{12g_P}+
 \frac{\pi/3-\beta}{g_Q}>0.
\tag{RP16b}
$$

This is an adjustable-Hamiltonian comparison, not a claim that an
itinerant reflection angle equals $\chi$ times a selectable pulse
duration. Loading, holding and releasing a photon with a controlled
dwell supplies a different memory interface. Per-visit overheads,
rail conversions and dissipation can change the time comparison.
Conversely a demonstrated number meter does not prove those exact
angle controls for either architecture.

For a real retained-photon retry, the full maps in (RP16), including
vacuum, dark hits, missed hits, lost fields and all feedback records,
remain necessary. A surviving repeat must preserve the entire unknown
$ABFR$ after its correction; a hit after absorption cannot return $F$.
Meter preparation may occur before input arrival, but repeated attempts
still require a real reset, storage/return and compatible readout
pulses. Neither $.87$ nor the other two statistics specifies those
maps. A plus-only output-port service avoids this meter for both
architectures. The concrete next component to characterize is a
which-rail-erasing occupancy instrument and its complete finite-pulse
return channel, compared with the same-control ordinary circuits;
no native performance claim follows from the reported scalars alone.

**The missing two-rail instrument has a precise test.** Use the full
time-ordered detector/field dilation, with input-independent prepared
detector/bath states purified,
cavity memory retained, and every readout/loss record. On the
vacuum-plus-code input its full Kraus family satisfies
$\sum K^\dagger K=I_3$. For flag $h$, let $K^S_{h\mu}$ be the
unresolved surviving-code Kraus operators. A scalar known-isometry
branch on every $FR$ is equivalent to

$$
K^S_{h\mu}=c_{h\mu}U_h\quad\text{for every }\mu,\qquad
\sum_\mu|c_{h\mu}|^2=s_h.
\tag{RP16c}
$$

This is necessary by rank-one Choi support and sufficient after tensoring
with $I_R$. For rail-preserving maps it says that the two complete
unobserved record vectors have equal norm $\sqrt{s_h}$ and overlap
modulus $s_h$, with their relative phase known. Equal rail efficiencies
alone do not fix that overlap. A lost-photon flag instead has some
effect $E_h^L$ on $F$ and output
$|\mathrm{vac}\rangle\langle\mathrm{vac}|\otimes
\operatorname{Tr}_F[(E_h^L\otimes I_R)\rho]$; only
$E_h^L=\ell_h I$ is state-independent erasure. Incident-vacuum dark
maps and vacuum/code coherences are additional data. Projecting onto
output sectors does not license replacing their coherent sum by a
pinched instrument without an actual record.

A concrete diagnostic sends both bins through one unreset meter.
Let its initial state be $|+\rangle$, each occupied bin apply $Z$,
and the common physical gap have Kraus $L_\mu$. Then
$W_\mu=|e\rangle\langle e|\otimes L_\mu Z+
|l\rangle\langle l|\otimes ZL_\mu$.
Commutation $L_\mu Z=ZL_\mu$ record by record suffices to preserve
$F$; covariance of the reduced gap alone does not. For amplitude
damping $L_0=\operatorname{diag}(1,a)$,
$L_1=\sqrt\gamma|g\rangle\langle e|$, $a=\sqrt{1-\gamma}$,
the no-jump vectors coincide, while early/late jumps have opposite
signs. Thus any final meter effect $E$ gives

$$
\Phi_E=A_E\operatorname{Id}_F+B_E\operatorname{Ad}_{Z_F},\qquad
A_E=\langle v_-|E|v_-\rangle,\quad
B_E=\frac\gamma2\langle g|E|g\rangle,\quad
v_-=\frac{|g\rangle-a|e\rangle}{\sqrt2}.
\tag{RP16d}
$$

For $0<\gamma<1$, a nonzero known-unitary branch requires $A_EB_E=0$.
Positivity then restricts $E$ to the ray $|e\rangle\langle e|$ or
$|w\rangle\langle w|$, where
$w=(a|g\rangle+|e\rangle)/\sqrt{1+a^2}$. The latter ray has
strictly positive real off-diagonal entries and the former has zero;
their nonnegative sum cannot be $I$. No complete terminal meter-only
POVM makes every occupied flag clean; monitoring the jump bath is a
different port. Selected clean sub-POVMs remain
possible: $E=|e\rangle\langle e|$ rejects jumps, with both occupied
and incident-vacuum weight $a^2/2$; the $w$ ray isolates a correctable
$Z_F$ branch. Rejected effects and false heralds still count.

For Ramsey $X$ flags $h=\pm1$, the same dilation gives the **full**
vacuum/early/late Kraus operators and occupied maps

$$
\begin{aligned}
K_{h0}&=\tfrac12\operatorname{diag}(1+ha,1-ha,1-ha),&
K_{h1}&=\tfrac{\sqrt\gamma}{2}\operatorname{diag}(1,-1,1),\\
\Phi_h&=\tfrac{(1-ha)^2}{4}\operatorname{Id}_F
             +\tfrac\gamma4\operatorname{Ad}_{Z_F},&
p_h&=(1-ha)/2.
\end{aligned}
\tag{RP16e}
$$

Summing $K_{h\mu}^\dagger K_{h\mu}$ gives $I_3$, retaining the
vacuum/code cross terms. The usual hit $h=-1$ has conditional
$Z_F$ error $(1-a)/2$, entanglement fidelity $(1+a)/2$, and **full**
diamond norm $1-a$ from identity; incident-vacuum false hits occur
with probability $(1-a)/2$. A corrected other flag has the same
residual error. At $\gamma=0$ the ideal detector returns; at
$\gamma=1$ nonzero occupied effects fully dephase the code.
These are exact ideal-kick/gap formulas, not bounds fitted to Kono's
finite-pulse device. Diagonal pure-dephasing Kraus commute with $Z$
and instead change flags without this rail error. Actual pulses,
cavity tails, ladder jumps and driven intervals require the full
dilation, not only a gap rate. A genuinely simultaneous coupling
$N_{\rm total}\otimes B_M(t)$ factors from $F$ because
$N_{\rm total}=I$ on its one-photon code; sequential bins with this
relaxation gap are not that protected interface.

A stored coherent probe exhibits a different record tradeoff. In a
defined model a photon in either bin rotates $|\alpha_p\rangle$ by
$\phi$, with one probe pure-loss channel $\eta$ between the kicks.
Both occupied histories leave the same kept probe
$|\sqrt\eta\alpha_pe^{i\phi}\rangle$, but their lost states have
amplitudes $\sqrt{1-\eta}\alpha_pe^{i\phi}$ and
$\sqrt{1-\eta}\alpha_p$. Their coherent-state overlap gives, after
a known rail phase correction,

$$
\begin{aligned}
V&=e^{-(1-\eta)z},\qquad z=|\alpha_p|^2(1-\cos\phi),\\
\Phi_h&=q_h\left[\frac{1+V}{2}\operatorname{Id}_F
                 +\frac{1-V}{2}\operatorname{Ad}_{Z_F}\right],\\
d_h=0&\ \Longrightarrow\quad
q_h\le1-e^{-2\eta z}=1-V^{2\eta/(1-\eta)}
\quad(0<\eta<1).
\end{aligned}
\tag{RP16f}
$$

Every probe-only flag has the same normalized dephasing; postselecting
the kept probe cannot remove the hidden loss record. Here $q_h$ and
$d_h$ are its occupied and incident-vacuum probabilities. Positivity
and $d_h=0$ force its effect to annihilate the vacuum-input probe
$|\sqrt\eta\alpha_p\rangle$; projection onto its orthogonal complement
proves and attains the displayed bound. The full diamond norm from identity is
$1-V$ and its $Z_F$ error is $(1-V)/2$. At $\eta=1$ this record
leakage vanishes; at $\eta=0$ the retained probe has no occupancy
information. Loss before both kicks or after both has common
occupied loss states and does not cause this particular mechanism.

[Sinclair et al., Nature Communications **7**, 13454 (2016),
primary proposal/experiment](https://arxiv.org/html/1510.01164v1)
motivate such a stored-probe approach, but their proof of principle
uses macroscopic signal pulses. Its total probe recall does not
determine the isolated inter-bin $\eta$ in (RP16f), nor establish a
single-mode pure-loss model of the ensemble. The diagnostic supplies
no universal optical-QND converse or native gate benefit. A practical
comparison must measure the timed full instrument and offer its
protected modes, probes, memory, clocks and all readout records to
the ordinary return/Euler/deferred-frame controllers too.

### Preparing the meter and balancing the cavity response

In a scalar atom-preserving reflection model take atom amplitudes
$r_0=A>0$, $r_1=-B<0$. Preparation
$|\psi_z\rangle=\sqrt z|0\rangle+\sqrt{1-z}|1\rangle$ gives a
surviving atomic vector
$A\sqrt z|0\rangle-B\sqrt{1-z}|1\rangle$.
Choosing $z=B/(A+B)$ makes it orthogonal to the bypass atom and gives
survival $AB$. The source's illustrative intensities $A^2=.50$,
$B^2=.117$ would give about $.242$ in this derived ideal setting,
not a newly measured operating point. For complex amplitudes,
$zr_0+(1-z)r_1=0$ requires antipodal phases; an initial atomic
relative phase cancels from this condition. For a finite pulse it
must hold as an operator on the occupied frequency/polarization
support, not only for one averaged amplitude.

Improving the conditional hit fraction in this way does not maximize
true surviving-hit mass. More generally suppose the full interaction
preserves atomic labels,
$V=|0\rangle\langle0|\otimes V_0+|1\rangle\langle1|\otimes V_1$,
with the same retained/lost outputs in both terms. The orthogonal hit
bra gives

$$
K_H(z)=\sqrt{z(1-z)}(V_0-V_1),\qquad
\mathcal H_z=4z(1-z)\mathcal H_{1/2}.
\tag{RP17}
$$

The identity holds on every passive reference, including loss if the
full controlled dilation holds. A selected diagonal elastic block
$R_0,R_1$ alone proves it only for that block; it does not cover lost
atomic flips or other reflected inelastic records. Normalized nonzero
hit output is independent of $z$. For the scalar example the hit mass
is $z(1-z)(A+B)^2$, maximized at $z=1/2$; it exceeds $AB$ by
$(A-B)^2/4$. With the illustrative intensities it is about $.275$.
Thus perfect conditional survivor discrimination can reduce useful
repeat mass. If only $T$ changes to $cT$, $c=4z(1-z)$, while $A$ and
all other controls are fixed and misses are dumped, each finite sum
$\sum_{j<K}c^jA\circ T^j$ increases in CP order with $c$.
Balanced preparation maximizes every positive linear all-launch output
payoff in this model. It need not maximize fidelity, signed utility or
payoff per query/time, and actual preparation-dependent errors may
invalidate its hypotheses.

There is a distinct physical route to equal elastic amplitudes at a
node. The projected architecture of
[Arwas et al., *Blueprint for a fault-tolerant compound photon–atom
quantum architecture*, Sec. II.3](https://arxiv.org/html/2606.30385v1)
uses a single reflection with symmetric polarization preparation and
orthogonal polarization selection. Its Eqs. (8)–(13) give the selected
interacting-rail amplitudes $+r_{\rm sym}$ and $-r_{\rm sym}$, with
$r_{\rm sym}=(r_a-r_c)/2=(\kappa_e/\kappa)C/(1+C)$.
There is no additional two-pass requirement in that construction.
However its other logical spatial rail bypasses the atom. To obtain
the survivor premise $\alpha(\omega)\operatorname{CZ}$ used in this
subsection, the **full complex bypass transfer** must equal the
selected interacting transfer throughout the occupied band, after
calibrated phases and all path losses. Equal atomic-state amplitudes
or equal average rail intensities alone do not prove this. Auxiliary
polarization selection must not consume the unknown $F$; reencoding
$F$ into spatial/temporal rails, extra order/helper modes, filters and
their failure/loss records are additional resources. The source states
that its device parameters are projected. Neither its scalar efficiency
nor its cluster-state protocols demonstrate this retained-$F$ switch,
its QND order readout or matched ordinary modal ports.
In particular its efficiency quoted for incident $|+\rangle$ with an
ideal bypass is not a state-independent whole-gate survival scalar.

### Raw cavity ports and a finite-pulse certificate

The local loss-complete closed-cycling model is already given in
(RS19): reflected, intrinsic-loss and spontaneous-emission amplitudes
are orthogonal one-excitation outputs with squared norms summing to
one. Raman flips, motion, extra levels and inelastic reflected records
need additional columns; these formulas are not an experimental fit.
For the symmetric two-polarization extension, let $p$ denote its
auxiliary polarization, distinct from retained logical $F$. At spin
eigenvalue $z=\pm1$ its **raw** reflected operator and two linear
polarization modes are

$$
R_z=mI_p+zdZ_p,\qquad
m=\frac{r_g+r_0}{2},\quad d=\frac{r_g-r_0}{2}
 =\frac{\kappa_r g^2}{D_c(D_cD_a+g^2)},\qquad
u=\frac{\sigma_++\sigma_-}{\sqrt2},\quad
v=\frac{\sigma_+-\sigma_-}{\sqrt2}.
\tag{RP18}
$$

Thus $R_zu=mu+zdv$. The selected $v$ output gives $dZ_{\rm spin}$;
the other reflected $u$ output gives $mI_{\rm spin}$. It remains a
coherent accessible port until actually dumped. The complete selected
logical node is
$b(\omega)|0\rangle\langle0|_F\otimes I+
d(\omega)|1\rangle\langle1|_F\otimes Z_{\rm spin}$,
so a scalar CZ survivor requires $b=d$ as full complex transfers,
including delays. A matched filter must have its causal realization,
reservoir phases, loss and timing specified; equal moduli alone do not
provide it.

Spatial logical $F$, order/program label $C$ and this auxiliary
polarization normally mean **eight raw optical modes**, despite four
kept logical code modes. Ordinary processors must receive the same raw
ports, including $m$, rather than have them discarded by definition.
The fixed-CZ bounds do not by themselves upper-bound this general raw
finite-cooperativity kernel. On a band where $r_g=-r_0$, a known
photon phase conditioned on the interacting rail removes $Z_p$ from
the raw $zdZ_p$ action and leaves $p$ as a spectator. Away from that
condition the extra $m$ term remains. Whether such a raw interface
supplies the middle spectator port in (RP4a) is an actual operator/
mode test, not an inference from the four kept modes.

A direct one-polarization node avoids the auxiliary selection and has
a useful explicit bandwidth bound. In the amplitude-decay convention
of (RS19), take $\kappa_i=\kappa-\kappa_r>0$,
$C_i=g^2/(\kappa_i\gamma)$, $s=\sqrt{1+C_i}$ and choose

$$
\kappa_r=\kappa_i s,\qquad \kappa=\kappa_i(1+s),\qquad
\alpha_0=\frac{s-1}{s+1}.
\tag{RP19}
$$

At common cavity/atomic resonance, $r_g(0)=\alpha_0$ and
$r_0(0)=-\alpha_0$. A bypass with carrier amplitude $\alpha_0$
therefore gives $\alpha_0\operatorname{CZ}$ on the carrier. A
constant attenuator and its beamsplitter loss port specify one such
bypass; this does not make the node exactly broadband. Set
$\delta=\omega-\omega_0$, $D_0=\kappa\gamma+g^2$.
Subtraction of the rational amplitudes in (RS19) gives exactly

$$
\begin{aligned}
|r_0(\delta)-r_0(0)|
 &=\frac{2\kappa_r|\delta|}{\kappa\sqrt{\kappa^2+\delta^2}},\\
|r_g(\delta)-r_g(0)|
 &=\frac{2\kappa_r|\delta|
       \sqrt{(\gamma^2-g^2)^2+\gamma^2\delta^2}}
 {D_0\sqrt{(D_0-\delta^2)^2+\delta^2(\kappa+\gamma)^2}}.
\end{aligned}
\tag{RP20}
$$

For $|\delta|\le B$ with $B^2<D_0$, bound the first expression by
its value at $B$ and the second by
$2\kappa_rB\sqrt{(\gamma^2-g^2)^2+\gamma^2B^2}/[D_0(D_0-B^2)]$.
Let $\epsilon_j$ bound the **full wrapped-node operator** residual
from $\alpha_{j0}U_j$ on that band. With ideal known wrappers this is
the maximum of the two diagonal residuals and
$|b_j(\delta)-\alpha_{j0}|$; known unitary wrappers preserve operator
norm, while calibrated wrapper errors must be added. For contraction
nodes and an otherwise ideal equal-history router, telescoping each
two-node product and averaging the two histories gives

$$
\left\|K_+(\omega)
 -\frac{\sqrt3}{2}\alpha_{A0}\alpha_{B0}G\right\|_{\mathrm{op}}
\le\epsilon_A+\epsilon_B.
\tag{RP21}
$$

Take a normalized **known** incident pulse $f$ independent of logical
$ABFR$, and let $q_{\rm tail}$ be its intensity outside the band.
Outside it both accepted operators have norm at most one, so their
difference is at most two. The accepted Stinespring-operator error is
at most
$e=\epsilon_A+\epsilon_B+2\sqrt{q_{\rm tail}}$.
The two Stinespring operators are contractions, hence the full
diamond distance of their subnormalized CP maps is at most
$\min\{2,2e\}$. This follows from expanding
$V\rho V^\dagger-W\rho W^\dagger$ into the two terms containing
$V-W$ and tensors with every passive reference. The ideal comparison
map is $(3/4)|\alpha_{A0}\alpha_{B0}|^2\operatorname{Ad}_G$.
Add calibrated router error at the Stinespring level. This is an
all-launch absolute bound; conditional fidelity at small yield needs
a separate normalization/yield bound. No numerical bandwidth or rate
is asserted without actual parameters, pulse, bypass and routing.

More generally, matched scalar node transfers and equal history
transfer $h$ give the exact factorization

$$
V_+|\psi\rangle
=\frac{\sqrt3}{2}G|\psi\rangle\otimes
  \int f(\omega)h(\omega)\alpha_A(\omega)\alpha_B(\omega)
                      |\omega\rangle\,d\omega,
\quad
\mathcal A_+=\frac34\eta\operatorname{Ad}_G,\quad
\eta=\int|fh\alpha_A\alpha_B|^2d\omega.
\tag{RP22}
$$

Literal weight $3/4$ per launched pulse requires $\eta=1$ in this
prescription. If spectrum is correlated with logical data, retain the
common spectral filter in the declared output rather than replace it
by a scalar. For a general scattering device, exact accepted
$p\operatorname{Ad}_G$ requires every unresolved accepted frequency/
reservoir Kraus to be a scalar multiple of the same $G$, by rank-one
Choi support. A mean reflection amplitude or one polarization fringe
does not certify that condition.

The next physical comparison must specify a complete node/router/clock
dilation on unknown $ABFR$, with pulse tails, raw ports, vacuum and
all accessible records. Its endpoint must distinguish immediate
delivered output from an online herald, harmless retry or a deferred
Pauli-frame workload. It must include the same-two-occupied-contact
serialization in (RP4a), its qualified parallel hardware access,
(RP2)–(RP4), middle instruments (RP12j)–(RP12m), spare-matter gates,
ordinary raw-mode processing and reusable calibration. The fixed-two-
query bounds remain valid for their specified call interfaces; they
exclude neither four controlled-vacuum opportunities nor an identical
supplied hardware route. No best-ordinary physical rate, universal
latency gap or native architecture advantage follows from them or
from the scalar break-even curves.


The [exact finite replay](../checks/architecture/verify_remote_spin_phase.py)
checks the literal native corrected flags and ordinary two-helper,
reused-helper and classical-coin instruments on every $ABF$ matrix
unit; an actual pre/CZ/middle/CZ/post four-mode circuit realizes (RP10)
and its complementary map. It also checks polynomial complement-Gram
identities, the phase-ratio and complex-circulant ingredients, explicit
terminal product-effect/compression budgets, coherent-return occupation
and rational scalar-ledger cases. Its imported
[dual component](../checks/architecture/retained_photon_dual.py)
checks the formal all-phase matrices, trace polynomial and balanced
attainment without an optimizer. The imported
[middle-instrument component](../checks/architecture/retained_photon_middle.py)
checks the exact $\mathbb Q(\sqrt5,i)$ Gram construction, positive
effects, midpoint probabilities, all 64 corrected channel matrix
units and the all-angle trace-cost polynomial ingredients. Positive
$Q_j$ supply the square-root existence; no expanded radical Kraus
entries or formalized pinching/minimization proof are claimed.
The imported
[serial-survivor component](../checks/architecture/retained_photon_serial.py)
checks the complete retained-input survivor and both output maps,
one-time spin wrappers, nonunitary raw kernels, retained auxiliary
polarization, coherent frequency inputs and the two middle-input
spans. It also guards the commuting-event layering and the rational
local-response identities underlying the finite-pulse certificate.
Its additional polynomial and matrix guards cover the common-meter
identity (RP13a), the energy-decay reflection algebra (RP16a), and the
relative-sector trace/determinant in (RP2b). The general clean-ancilla
obstruction and missing physical readout instrument remain analytic.
Its finite $N=2,3$ fixtures also retain coherent exit/residual cross
blocks, the raw-CZ time gauge and all vacuum/one-photon matrix units
of the damping diagnostic, with pure-dephasing comparison cases.
The general Stas transfer reduction, complete-POVM obstruction and
coherent-probe tradeoff remain analytic, not finite-replay certificates.
Retiming unresolved reservoir histories is not certified. The general
norm, causal-interface and continuum error arguments remain analytic;
no physical port or clock is supplied by these replays.
The imported
[sequence component](../checks/architecture/retained_photon_chain.py)
guards the exact Fourier-cut ranks and slices, the phase-ratio identity,
nucleus moment identities, and a genuinely complex anisotropic
multi-record boundary contraction on full input matrix units. Its
finite algebra does not enumerate all controllers or prove complex
interpolation, continuous-record integration or the general
determinant-potential theorem (RP24). Those remain analytic arguments.
These finite/formal algebra checks support the general analytic
proofs; they do not enumerate arbitrary
controller instruments, establish the optical ports, reconstruct the
physical meter/loss channel or verify a hardware rate. This retained-
photon comparison has not been formalized in Lean.

## Physical resources and verification scope

The arbitrary-helper protocol assumes a pure incident photon and the
complete reflected polarization–frequency purifier. Generalized coherent
measurement on its at-most-four-dimensional occupied Schmidt span can
require calibrated temporal/spectral mode conversion, phase references,
additional detector ports, quantum memory and feedforward. The
Bell-assistance proof (RS39) allows at most eight nonzero helper outcomes
and then
local filters with their own success/failure records. Mathematical mode
compression does not establish that a given cavity/router preserves
those modes or that ordinary timestamp detection implements the POVM.
The fixed Gaussian witness uses no exact-LMM claim and retains these
filter costs. Supplying only a more restricted detector leaves a
different optimization.

The yield (RS46) includes the two model reflection probabilities and the
filter failures. It excludes unmodeled source, fiber, mode-matching,
detector, wrapper and local-control losses. Their measured costs and the
source/filter calibration precision must be added before claiming a
physical rate. A Gaussian has temporal tails; finite readout windows
require a separate truncation/error budget. The cavity's actual spectral
and loss-record dilation, available classical timestamps, local spare
qubits, storage over the entire analysis/feedback time, and the strongest
ordinary spectral controls must be matched. No universal finite-bandwidth
comparison, native gate advantage, hardware yield or fault-tolerant
throughput follows from this declared ideal-model factory bound.

The existing exact finite replay covers (RS30), ordinary saturation, the
rational scalar Bell-yield witness, the known-gate compiler and online
two-CZ protocol, and (RS38). Its additional Gaussian-rational example
checks a rank-four state, two rank-three and four rank-two same-marginal
endpoints, an explicit complete eight-outcome helper POVM, exact Bell
filtering of joint weight $2/5$, and filter failure $3/5$. It guards
normalization and nontrivial complex marginals; the dimension-count proof
and the cited rank-two theorem establish (RS39) in general. The separate
continuum replay certifies only (RS46) in the stated scattering model.
Neither replay validates a native coherent mode analyzer, optimizes every
switched flagged instrument, or formalizes these arguments in Lean.
The finite replay also checks (RS48)–(RS50) on nine coherent two-frequency
examples, including complex compressions, zero/one source occupancy,
singular effects and all spin-state entries. Exact coefficient-vector and
coherent-frequency guards check the eigenstate-source compiler. These
finite cases also guard complex gate-covariance orientation, continuous
local phases versus a Pauli-only restriction, separate accepted gate flags,
the exact dark–dark dual witness, and the balanced and orthogonal-tag
reflected-gate constructions. They support the general proofs; they do not
supply native
four-mode ports, an adaptive ordinary upper bound or a physical loss and
clock completion. A further native gate comparison must retain arbitrary
unknown $ABR$, the complete rejected instrument, and the strongest paid
ordinary source, optics, local controls and memory resources.
The added decorated-bus guards check independent same-spin projector
conjugations, pure eight-mode sources, full coherent two-frequency
spin/reference matrix units and joint photon-readout CP coefficients.
They match the safe four-window survivor and the three-window variant
with its explicitly supplied eight-mode middle port. A three-dimensional
bright/dark compression fixture guards the generic six-mode requirement;
padding polarization with bypass modes guards the rank-one obstruction.
These finite identities support (RS58)–(RS62); physical station ports,
surviving-bath purity, time-bin wrappers, common-finish dynamics and
actual gate rates remain the stated analytic and device premises.
The selected projector-kernel certificate additionally checks its
primal PSD/PPT and reflected rejection matrices, both ordinary duals
with a positive rational margin, every real/imaginary moment and
phase direction, transpose conventions and homogeneous lottery
weights. Its [terminal-filter component](../checks/architecture/projector_filter_dual.py)
additionally checks four all-complex-product sector decompositions with
64 integer entry identities and 48 strictly positive leading minors.
The Choi-rank, separable-correction and completeness argument above connects
that certificate to all terminal LOCC after complete photon readout;
it does not cover premeasurement or interleaved controls.
Its checked scalar cavity point is single-frequency.
These exact tests establish the bounds in (RS68), not either optimum,
a finite-pulse rate or a physical separation from the longer or
entanglement-first ordinary protocols.
