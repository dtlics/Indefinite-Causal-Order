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
not been formalized in Lean.

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

## Physical resources and verification scope

The arbitrary-helper protocol assumes a pure incident photon and the
complete reflected polarization–frequency purifier. Generalized coherent
measurement on its at-most-four-dimensional occupied Schmidt span can
require calibrated temporal/spectral mode conversion, phase references,
additional detector ports, quantum memory and feedforward. The arbitrary
helper proof allows at most eight nonzero measurement outcomes and then
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
