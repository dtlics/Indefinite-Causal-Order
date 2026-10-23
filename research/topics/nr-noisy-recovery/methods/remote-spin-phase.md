# Remote spin phase gates and ordinary photon-bus controls

This is a conditional-output proof component of
[NR-R11](../communication.md#nr-r11). It compares a specified switched
spin–photon construction with ordinary operations on the same stationary
spin payload. The
[exact finite checker](../checks/architecture/verify_remote_spin_phase.py)
replays the complete detected spin instruments, an explicit
lost-carrier counterexample for the first ordinary compiler, and a
stronger all-outcome compiler under a declared erasure dilation. Native
routing, clocks, general cavity loss and optimal fault-tolerant rates
remain separate. This comparison has not been formalized in Lean.

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
that recovery free. The next falsifiable model is the full calibrated
spin-dependent scattering dilation, with optimized ordinary
preparation, wrappers, readout, local phases and qualified mode-assisted
controls, evaluated in an actual clocked encoded task. A larger detected
gate fidelity or control fringe does not settle that comparison. A
substantial native gate or rate advantage remains open.

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
