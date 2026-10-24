# Moving-atom CAPS: retained outputs, passive bounds and ordinary comparators

<a id="nr-r11-moving-caps"></a>

This proof component of [NR-R11](../communication.md#nr-r11) supplies a
microscopic model for its retained-inelastic optical question. Two local
moving scatterers can fail to commute because a sideband produced at the
first changes the photon frequency seen by the second. The results below
give an all-cutoff passive-resolvent bound, a source-specific minus-port
recovery budget, and a finite-packet diagnostic. They establish no native
hardware advantage. The displayed plus-only protocol has an ordinary
random-order CP completion with at least its all-launch target-good mass.
The reflected sector alone does not specify the lost-photon data channel.

## Model, source and required quantum output

[Kikura et al., *Scattering theory for cavity-assisted spin-motion-photon
interactions*, arXiv:2606.26542v1, 25 June 2026](https://arxiv.org/html/2606.26542v1),
Eqs. (3)–(8), (12)–(16) and Fig. 2, develop a stationary joint
motion/photon reflection model, including standing/running-wave coupling
and unequal trapping potentials. Fig. 2(a) gives a polarization/spin CZ
interface; Fig. 2(b) instead detects a photon polarization and tests an
atomic $Z$. The source supplies neither matched routed nodes nor a
coherent-order helper or measured complete loss instrument. The
composition, bounds and comparisons here are deductions within the
declared model, not an experimental switch result.

The data are an unknown photon polarization $P$ and two unknown atomic
spins $A,B$, jointly entangled with any passive reference. Their input
dimension is $D=8$. The required gate and output temporal mode are fixed
before optimization:

$$
U=|H\rangle\langle H|_P\otimes I_{AB}
 +|V\rangle\langle V|_P\otimes Z_AZ_B,\qquad
V_\star|\psi\rangle=|f_\star\rangle\otimes U|\psi\rangle.
\tag{MC1}
$$

Both the polarization and spins must be returned as quantum data.
The input temporal state is a specified normalizable wavepacket,
independent of the data and initial motion; it is not an arbitrary
unknown temporal payload. A known product-state Bell factory or
destructive photon tomography does not implement (MC1).
An accepted output optical port can preserve polarization without
certifying photon presence. A nondestructive herald, independent
measured helper, or downstream presence test is an additional port.
Lost photons, false flags and rejected unknown data remain in the
full service specification.

The retained reflected model preserves each spin basis value. State
$0$ is dark; state $1$ couples to the cavity. For equal harmonic
ground/excited traps, write $N=b^\dagger b$, $Q=b+b^\dagger$ and

$$
\begin{aligned}
C(z)&=(z+i\kappa-\mu N)^{-1},&
A(z)&=(z-\Delta_a+i\gamma-\mu N)^{-1},\\
R(z)&=[I-g^2C(z)d^\dagger A(z)d]^{-1},&
s(w)|n\rangle&=|n\rangle-
 \frac{2\kappa_{\rm ex}}{\kappa-iw}R(w+n\mu)|n\rangle,\\
r_{\rm dark}(w)&=1-\frac{2\kappa_{\rm ex}}{\kappa-iw},&
\kappa&=\kappa_{\rm ex}+\kappa_{\rm in}.
\end{aligned}
\tag{MC2}
$$

The standing-wave antinode uses $d=\cos(\eta Q)$; the running-wave
model uses $d=e^{i\eta Q}$ and its true complex adjoint in (MC2).
The dark column is $r_{\rm dark}(w)\delta_{mn}$.
The operator proof below also permits a different selfadjoint
excited-trap Hamiltonian.

The selected finite diagnostic duplicates a single-node nominal
parameter set,
$(g,\kappa_{\rm in},\gamma,\mu)/(2\pi)
=(7.6,0.2,3,0.138)$ MHz and $\eta=0.17$, at both nodes. It sets
$\Delta_a=0$ and
$\kappa_{\rm ex}=\kappa_{\rm in}
\sqrt{1+g^2/(\kappa_{\rm in}\gamma)}$.
These are hypothetical identical nodes, not a fit to a measured
two-node apparatus. Frequencies in the numerical code are divided by
the common $2\pi\,{\rm MHz}$ unit. At fixed mass and optical
wavenumber, $\eta\propto\mu^{-1/2}$; it is not an independent trap knob.

## Energy shifts, paired histories and their clock

For initial motion $\boldsymbol n=(n_A,n_B)$ and final motion
$\boldsymbol m=(m_A,m_B)$, let
$E_j=(m_j-n_j)\mu_j$. The two reflected words have amplitudes

$$
\begin{aligned}
T_{AB}(w)&=s_B^{m_Bn_B}(w-E_A)s_A^{m_An_A}(w),\\
T_{BA}(w)&=s_A^{m_An_A}(w-E_B)s_B^{m_Bn_B}(w).
\end{aligned}
\tag{MC3}
$$

They reach the same final motion and photon frequency
$\nu=w-E_A-E_B$ and are diagonal in the two spin labels.
The local motion spaces are independent, but the common field makes
the frequency arguments order dependent. For example, from ground
motion the $(m_A,m_B)=(2,0)$ difference is
$s_A^{20}(w)[s_B^{00}(w-2\mu_A)-s_B^{00}(w)]$.
Noncommuting local motional matrices by themselves would not show
noncommutation between spatially separated nodes.

These amplitudes assume the actual route histories are the phase-aligned
single-pass products in one scattering frame, with the same initial
environment. A complete route must preserve the field, spin, motion
and helper records needed for that pairing. Equal final arrival time
does not establish it: pre/post propagation, direction-dependent
couplings, dispersion, finite windows and the $H$ reference arm must
be specified. Reversing a running wave generally replaces $d$ by
$d^\dagger$, not the identical oriented operation.

Each stationary contact conserves total free energy
$H_{\rm ph}+\mu_AN_A+\mu_BN_B$. Equal-duration nondispersive free
waits can therefore be commuted to a common finish. Keeping only a
motional phase during a wait is wrong: its photon sideband carries
the compensating propagation phase. Unequal routes, nonlinear
dispersion, spin drift and physical loss-record overlaps still need
their actual operators. A relative route phase of $\pi$, even for
commuting elastic contacts, interchanges the sum/difference ports;
energy-transfer bounds for the aligned difference cannot cover that
changed instrument.

The native $X$ flags use $(T_{AB}\pm T_{BA})/2$.
The common bypass contributes only to plus and only for unchanged
motion. At a standing-wave antinode all transitions are even, so a
motional parity check misses the first sidebands. For ground motion
and exactly monochromatic input, positive trap frequencies imply that
only unchanged motion can retain the carrier frequency. Its full
spin/polarization operator is identical in native plus and ordinary
serial scattering:
$|H\rangle\langle H|\otimes I+
 |V\rangle\langle V|\otimes
 \operatorname{diag}_{AB}[s_A^{00}(w)s_B^{00}(w)]$.
This sector identity is not a result for finite packets, thermal
zero-net-energy exchange or all loss records.

## A passive resolvent bound without an oscillator cutoff

Let the asymptotic ground Hamiltonian be $H_g=\mu N$, $\mu>0$,
and let $H_e$ be any selfadjoint excited-sector Hamiltonian,
including detuning or a different trap. For bounded $d$, set

$$
H_0=\begin{pmatrix}H_g&g d^\dagger\\gd&H_e\end{pmatrix},
\quad
\Gamma=\kappa P_c^\dagger P_c+\gamma P_e^\dagger P_e,
\quad \delta=\min\{\kappa,\gamma\}>0.
$$

Here $P_c,P_e$ extract the cavity and excited blocks,
$\kappa=\kappa_{\rm ex}+\kappa_{\rm in}>0$,
$\gamma>0$, and $\kappa_{\rm ex},\kappa_{\rm in}\ge0$.
The rates are amplitude decay rates. Take $g$ real, or conjugate
off-diagonal entries for complex $g$. Bounded coupling makes $H_0$
selfadjoint on
$D(H_g)\oplus D(H_e)$. The source's cosine and exponential are bounded;
no commutation with $N$ or equality of the traps is required.
All frequency fibers use the same flux normalization.

For real total energy $E$, define
$G(E)=(E-H_0+i\Gamma)^{-1}$. It exists and

$$
\|G(E)\|\le\delta^{-1}.
\tag{MR1}
$$

To include an unbounded trap, work first on $D(H_0)$.
The imaginary part of
$\langle\psi,(E-H_0+i\Gamma)\psi\rangle$ is at least
$\delta\|\psi\|^2$. Cauchy–Schwarz gives
$\|(E-H_0+i\Gamma)\psi\|\ge\delta\|\psi\|$.
This closed operator has closed range. Its adjoint
$E-H_0-i\Gamma$ has the same lower bound and zero kernel, so
the original range is dense. It is therefore all of the two-block
Hilbert space, proving invertibility and (MR1).

The resolvent identity
$G(E-e)-G(E)=eG(E-e)G(E)$ then gives, for the reflected fiber,

$$
S_{\rm ref}(E)=I-2i\kappa_{\rm ex}P_cG(E)P_c^\dagger,\qquad
\|S_{\rm ref}(E-e)-S_{\rm ref}(E)\|
\le L|e|,\quad L=\frac{2\kappa_{\rm ex}}{\delta^2}.
\tag{MR2}
$$

Passivity supplies more than a sampled singular-value check.
The bounded resolvents obey
$G-G^\dagger=-2iG^\dagger\Gamma G=-2iG\Gamma G^\dagger$.
Expanding the reflected product yields

$$
I-S_{\rm ref}^\dagger S_{\rm ref}
=4\kappa_{\rm ex}P_cG^\dagger
 [\kappa_{\rm in}P_c^\dagger P_c+\gamma P_e^\dagger P_e]
 GP_c^\dagger\ge0.
\tag{MR3}
$$

Thus every real-energy reflected fiber is a contraction.
For the declared Markov completion, stack the rows
$\sqrt{2\kappa_{\rm ex}}P_c$,
$\sqrt{2\kappa_{\rm in}}P_c$ and $\sqrt{2\gamma}P_e$ into $W$.
Since $W^\dagger W=2\Gamma$, the same identity makes
$S_{\rm full}=I-iWG(E)W^\dagger$ unitary.
This is a mathematical passive optical completion, not identification
of an actual spontaneous final atomic level, recoil direction,
lost-photon wavepacket or receiver record. Those determine failed
unknown-data maps and remain necessary for the physical service.

The physical column is
$s_{mn}(w)=\langle m|S_{\rm ref}(w+n\mu)|n\rangle$, and

$$
T|w,n\rangle
=\sum_m s_{mn}(w)|w-(m-n)\mu,m\rangle.
\tag{MR4}
$$

It is $S_{\rm ref}(E)$, not the column-dependent array at one incident
$w$ treated as a motional matrix, to which (MR3) applies.
Indeed $(J\psi)(E)_n=\psi_n(E-n\mu)$ is a unitary change of variables
on $L^2(\mathbb R;\mathcal H_m)$, and $JTJ^\dagger$ is multiplication
by $S_{\rm ref}(E)$. This proves contraction of the physical frequency-
shifting operator in the stationary linearized Markov model.

### Energy-transfer moments control the aligned minus branch

Fix initial number states $n_A,n_B$. Abbreviate the entries in (MC3)
by $a(w)=s_A^{m_An_A}(w)$, $b(w)=s_B^{m_Bn_B}(w)$.
The exact difference is

$$
\begin{aligned}
d_{m_A,m_B}(w)
&=a(w)b(w-E_A)-b(w)a(w-E_B)\\
&=a(w)[b(w-E_A)-b(w)]
 +b(w)[a(w)-a(w-E_B)].
\end{aligned}
\tag{MR5}
$$

The prepared and measured balanced helper gives
$p_-(V;w,n_A,n_B)=\frac14\sum_{m_A,m_B}|d_{m_A,m_B}(w)|^2$.
It is an **all-launch reflected minus probability**, not a
survival-conditioned probability and not the total rejection/no-click
probability.
Define the unnormalized reflected second moment

$$
M_{2,j}(w,n)=\sum_m[(m-n)\mu_j]^2|s_j^{mn}(w)|^2
=\|(H_{g,j}-n\mu_j)S_{{\rm ref},j}(w+n\mu_j)|n\rangle\|^2.
$$

The last expression is an extended quadratic form; it may be infinite.
For the first term of (MR5), fix $m_A$ and apply (MR2) to the entire
$B$ column:
$\sum_{m_B}|b(w-E_A)-b(w)|^2\le L_B^2E_A^2$.
Weight by $|a(w)|^2$ and sum over $m_A$ to obtain $L_B^2M_{2,A}$.
The second term analogously contributes $L_A^2M_{2,B}$.
The Hilbert-space inequality
$\|x+y\|^2\le2\|x\|^2+2\|y\|^2$ proves

$$
p_-(V;w,n_A,n_B)
\le\frac12\left[
 L_B^2M_{2,A}(w,n_A)+L_A^2M_{2,B}(w,n_B)\right].
\tag{MR6}
$$

Clip the bound at one if useful. Infinite moments give a valid but
uninformative right side. Neither $L$ nor this argument uses a finite
Fock cutoff.

For any normalized packet $f$ independent of the number labels, trace
the full output motion and field:
$p_-(V;f,\boldsymbol n)=
\int |f(w)|^2p_-(V;w,\boldsymbol n)\,dw$.
For fixed final motions the map
$w\mapsto w-E_A-E_B$ is injective with Jacobian one; different final
motions are orthogonal. No coherent spectral overlap has been
replaced by a classical average. Integrating (MR6) is therefore valid
for arbitrary $L^2$ packets. Average next over initial number-diagonal
motion, including correlated diagonal mixtures; product thermal states
are sufficient. Coherent initial motion or input-correlated quantum
environment programs require their cross terms and are not bounded
by these diagonal moments alone.

Because retained CAPS preserves the spin labels, tracing spins and
reference weights the scalar probability by the corresponding
diagonal input spin populations and branch moments. It is not a full
spin-gate identity. If $H$ follows the common commuting bypass, its
minus amplitude vanishes. An independent polarization $|+\rangle$,
or a Bell probe with polarization marginal $I/2$, contributes exactly
one half of the $V$-only weight; the spin Choi average is separate.
A common field-only TNI filter cannot increase this unfiltered minus
probability. Its coherently selected probability need not itself
equal the displayed $|f|^2$ integral. Control-dependent filters or
different helper measurements are different instruments.

Equal finish time alone is insufficient for (MR5)–(MR6). With $d=I$
and diagonal $H_e$, the transfer moments vanish and the two elastic
products commute. An inserted relative route phase $\pi$ nevertheless
makes the nominal minus operator their nonzero sum. Constant-phase
calibration can restore alignment, but its control and stability are
paid; residual frequency/spin-dependent phases require their actual
operator treatment.

A finite Fock sum is generally a lower partial sum of $M_2$, not an
upper bound on its tail. A normalized conditional sideband moment
must also be multiplied by reflection probability. Neither empirical
finite moments of unbounded shifts nor narrowband pilots give a
distribution-free confidence upper bound without energy/tail
assumptions. A useful physical application of (MR6) needs a validated
stationary model, upper-tail control, frequency scans, preparation and
drift calibration. This bound may be loose and does not by itself
certify numerical oscillator truncation.

## Scores, ordinary completion and a limited recovery budget

For the fixed target isometry $V_\star$, define the accepted Choi
mass and unnormalized target-good mass of fine maps $K_\lambda$ by

$$
p=\frac18\sum_\lambda\operatorname{Tr}K_\lambda^\dagger K_\lambda,
\qquad
g=\frac1{64}\sum_\lambda
 |\operatorname{Tr}(V_\star^\dagger K_\lambda)|^2,
\qquad F=g/p\quad(p>0).
\tag{MC4}
$$

These are normalized maximally entangled $PAB:R$ probe scores.
Acceptance need not be input independent, and $F$ is not a
worst-input diamond guarantee. For packets and thermal motion,
$K_{\boldsymbol n,\boldsymbol m}(\nu)$ includes
$f(\nu+E_A+E_B)$; the trace overlap in $g$ is
$\int d\nu\, f_\star^*(\nu)
\operatorname{Tr}[U^\dagger K_{\boldsymbol n,\boldsymbol m}(\nu)]$.
The integral is **inside** its absolute square.
Initial thermal labels and final motion are summed afterward.
A frequency measurement would be a different output service.

For paired reflected Kraus maps $X_\lambda,Y_\lambda$ of the two
orders, $K_{\pm,\lambda}=(X_\lambda\pm Y_\lambda)/2$.
The elementary expansion underlying
[FC2](final-flag-completion.md) gives

$$
\mathcal O_{\rm ref}=\tfrac12(\mathcal X+\mathcal Y)
=\Gamma_++\Gamma_-,
\qquad
p_O=p_++p_-,\quad g_O=g_++g_-.
\tag{MC5}
$$

This is an actually supplied random-order reflected comparator with
the same common decoder. The CP identity suffices for positive-score
ordering even though these reflection maps are TNI. It is not a
completed physical CPTP/diamond conclusion: intrinsic/spontaneous
loss, false heralds and rejected data records are not supplied.
For positive branch probabilities,

$$
F_+-F_O=\frac{p_-}{p_++p_-}(F_+-F_-)
\le\frac{p_-}{p_++p_-}.
\tag{MC6}
$$

At $p_-=0$ the two conditional scores agree when defined.
Rejecting bad mass can raise conditional quality without creating
more correct all-launch output.

Every common allowed payload decoder preserves (MC5). For any
chosen native plus decoder available to ordinary processing at the
same paid resources, ordinary random order using it has $g_O\ge g_+$.
Optimizing plus decoding within that shared family cannot evade
this comparison. It does not reproduce the native flag record.
For the scalar $H/V$ phase plate used below, minus has no $H$
amplitude, so its good mass is phase independent; the cross term of
the ordinary mixture equals that of plus. Thus even the optimized
identity is $g_{O,\rm opt}=g_{+,\rm opt}+g_-$.
Common attenuation or delay is covered pointwise. Retaining the
ordinary random seed may permit still stronger branch-specific
ordinary calibration.

The source gives a further input-support fact. Minus annihilates
all $H$ inputs and also $|V00\rangle$: both dark cavity responses
are commuting scalar frequency multipliers with no motion change.
For every frequency and initial/final motion, therefore,

$$
K_{-,\lambda}=K_{-,\lambda}\Pi,\qquad
\Pi=|V\rangle\langle V|\otimes
 (I_{AB}-|00\rangle\langle00|),\qquad \operatorname{rank}\Pi=3.
$$

Any subsequent CP decoder or accepted TNI instrument keeps this
input support. Applying the [rank/Choi argument SG3](../communication.md#nr-r11-bare-swap-gate)
to the fixed $D=8$ isometric target gives

$$
g_{-,\rm decoded}\le\frac38p_{-,\rm decoded}
\le\frac38p_-.
\tag{MC7}
$$

Equivalently the decoded Choi operator is supported on
$I_{\rm out}\otimes\Pi^T$, where the normalized target vector has
squared projection $3/8$. Positivity yields (MC7).
Auxiliary outputs, accessible motion records and accepted output
processing cannot restore input sectors already killed.
This concerns measured/dephased order flags with separate payload
decoders. It does not bound a protocol retaining coherent control
and later jointly processing both histories, preencoding into extra
input-bearing registers, a lower input code or a known-state target.

### A minus-only atomic Bell endpoint

Changing the task to atomic Bell preparation does not make this bare
measured minus branch useful on product atoms. Take a fixed photon
state independent of $ABR$, number-diagonal initial motion independent
of the data, and trace final motion. Refine every branch by initial
and final local numbers $\boldsymbol n,\boldsymbol m$ and the fine
photon-only terminal CP/readout record. If neither local number changes,
the stationary same-frequency contacts are diagonal in the common
polarization and commute, so minus is zero. If only $A$ changes,
its spin must be bright $1$; the atomic Kraus operator has form
$P_{1,A}\otimes D_B$ with $D_B$ diagonal. Only $B$ changing gives
$D_A\otimes P_{1,B}$, and both changing gives
$cP_{1,A}\otimes P_{1,B}$, including zero-total-energy exchange.
Arbitrary terminal photon processing can coherently integrate the
coefficients within a fine branch without changing these product forms.

Positive summation over initial thermal labels, discarded motion and
hidden photon records therefore gives a separable atomic operation.
Grouping visible outcomes and local spin feedforward preserve it;
no accepted outcome can entangle initially product atoms.
This is a separate minus-only atomic-output endpoint, not the full
retained-$PAB$ task, an all-flag bound or a statement about coherent
control recovery. It excludes initial coherent/entangled motion,
motional erasure, extra unread bath inelasticity in an unchanged-number
sector, an intermediate photon converter and joint spin operations.
The common phase/clock and actual stationary-contact assumptions remain
essential.

### A uniform route-loss budget

Fix a plus decoder shared with ordinary processing, giving $g_+,g_-$
in (MC5), and grant native any separate minus decoder. Its total
good mass is at most $g_++3p_-/8$.
If extra native routing loss is only a uniform input-, branch-,
frequency- and port-independent transmission $0\le\eta\le1$,
a necessary condition to beat the ordinary comparator is

$$
\eta>\frac{g_O}{g_++3p_-/8},
\qquad
1-\eta<
\frac{3p_-/8-g_-}{g_++3p_-/8},
\tag{MC8}
$$

when the denominator and right side are positive. A nonpositive
right side leaves no advantage even at $\eta=1$. Plus-only service
has no additional-loss allowance in all-launch good mass.
Nonuniform route loss requires its actual CP model. A numerical
partial moment or truncated $p_-$ cannot certify this physical
threshold; one needs compatible rigorous upper bounds such as (MR6)
with certified full moments. No minus recovery optimum is asserted.

## Finite-packet diagnostic and stronger ordinary processing

The optional numerical model uses independent geometric thermal
mixtures $p_n=(1-q)q^n$, $q=\bar n/(1+\bar n)$, and
$f(w)=(2\pi\sigma^2)^{-1/4}e^{-w^2/(4\sigma^2)}$.
It fixes the output Gaussian, with any common target-arrival
translation declared for both strategies.
The motionless-design carrier sets the common paid $H$ amplitude
$h=r_{\rm dark}(0)^2\approx0.6656575598$.
Its $H$-arm rejection probability is $1-h^2\approx0.5569000131$;
the unused attenuator port is not discarded from the physical ledger.
Finite-$\eta$ bright carriers may mismatch that balance.
Keeping an avoidable unit $H$ amplitude would not be a fair test of
motion-induced error. Static polarization phase is optimized per
accepted port for both protocols, with the target temporal mode fixed.

An ordinary two-port delay filter acts on both polarizations:
$F_\pm(\nu)=[1\pm e^{i\nu\tau}]/2$.
After their common mean delay, the two amplitudes are
$\cos(\nu\tau/2)$ and $\sin(\nu\tau/2)$ up to a known phase.
The delay, rejected port, phase locks and packet reshaping are paid.
For standing-wave first sidebands $\pm2\mu$,
$\tau_0=\pi/(2\mu)\approx1.811594\,\mu{\rm s}$;
running-wave first sidebands $\pm\mu$ instead require
$\pi/\mu\approx3.623188\,\mu{\rm s}$.
For an undistorted Gaussian target with $z=\sigma^2\tau^2$,

$$
p_{\cos}=(1+e^{-z/2})/2,\quad g_{\cos}=e^{-z/4},\quad
p_{\sin}=(1-e^{-z/2})/2,\quad g_{\sin}=0,\quad
F_{\cos}=\operatorname{sech}(z/4).
\tag{MC9}
$$

The two port probabilities sum to the unfiltered probability.
Their good masses need not sum to the original good mass: forgetting
the port dephases delayed field components. Accepting both output
wires requires supplying them to the actual endpoint, not relabelling
them as one nondestructively heralded wire.

The selected calculation uses
$\sigma/(2\pi)=0.01$ MHz, output cutoff 20, initial cutoff 12,
and 240 trapezoidal intervals over $[-8.5\sigma,8.5\sigma]$.
The following rounded values are finite-model **reflection-sector**
scores with optimized static $H/V$ phase, not physical tail-certified
gate errors or an optimized ordinary frontier:

| Geometry / $\bar n$ | Protocol | $g$ | $p$ | $1-g/p$ |
| --- | --- | --- | --- | --- |
| Standing / 0 | Native plus | 0.4403411450 | 0.4404042511 | $1.43291245\,10^{-4}$ |
| Standing / 0 | Ordinary random | 0.4403411450 | 0.4404044393 | $1.43718580\,10^{-4}$ |
| Standing / 0 | Ordinary selected $\tau_0$ filter | 0.4389172626 | 0.4389639491 | $1.06356166\,10^{-4}$ |
| Standing / 0.1 | Native plus | 0.4397640560 | 0.4398394216 | $1.71348096\,10^{-4}$ |
| Standing / 0.1 | Ordinary random | 0.4397640560 | 0.4398396630 | $1.71896721\,10^{-4}$ |
| Standing / 0.1 | Ordinary selected $\tau_0$ filter | 0.4383420397 | 0.4383958776 | $1.22806723\,10^{-4}$ |
| Standing / 0.25 | Native plus | 0.4388759669 | 0.4389755936 | $2.26952810\,10^{-4}$ |
| Standing / 0.25 | Ordinary random | 0.4388759669 | 0.4389759412 | $2.27744566\,10^{-4}$ |
| Standing / 0.25 | Ordinary selected $\tau_0$ filter | 0.4374568223 | 0.4375248056 | $1.55381539\,10^{-4}$ |
| Running / 0.25 | Native plus | 0.4430649306 | 0.4431020519 | $8.37759955\,10^{-5}$ |
| Running / 0.25 | Ordinary random | 0.4430649306 | 0.4431020540 | $8.37807054\,10^{-5}$ |

The running calculation replaces only $d$ and its true complex
adjoint at the same nominal parameters from a standing-wave apparatus.
It is a theoretical geometry comparison, not a measured running-wave
node or free retuning. Unitarity of $d$ is not recoil freedom:
$[d,N]\ne0$. Its leading
$d^\dagger A d=A+i\eta[A,Q]+O(\eta^2)$ has odd sidebands, but the
commutator also contains the motional energy difference; the label
$O(\eta)$ alone does not predict a larger effect.

At $\bar n=0.25$ the finite minus probability is about
$3.48\,10^{-7}$ for standing waves and $2.09\,10^{-9}$ for running
waves. The latter is below the omitted initial joint thermal mass
$8.192\,10^{-9}$. Thermal zero-net-energy exchange can evade a
carrier-frequency filter, but its finite minus weight here is about
$1.61\,10^{-13}$ standing and $1.08\,10^{-16}$ running.
These exchange diagnostics are below the omitted-mass scale, not certified
physical residuals. Ground motion has no nontrivial zero-net-energy
exchange.

The basic filter is not an ordinary optimum. Common relative $H$ delay,
attenuation and static phase can materially improve the unfiltered
comparison, and the same calibrations must be offered to native.
Temporal-mode projection onto the target is another benchmark only
when its mode sorter and complete ports exist. A stronger ideal
passive family has transfer
$f_k(\nu)=k^2/[k^2-\nu^2-i\sqrt2 k\nu]$ and complementary
$r_k(\nu)=i\nu^2/[k^2-\nu^2-i\sqrt2 k\nu]$.
Their symmetric two-port matrix is unitary on real frequency, with
lower-half-plane poles and group delay $\sqrt2/k$.
It illustrates that a single delay filter is not an optical-control
optimum. No optimized numerical yield from that additional model is
used here; bandwidth, insertion loss, polarization handling,
stabilization and latency must be paid.

### Convergence and what is not certified

The finite standing coupling is $\cos(\eta Q_N)$, not the projection
of the infinite-oscillator cosine. The running exponential is likewise
the unitary of a finite position matrix, not a certified projection of
the infinite displacement. Increasing cutoffs is an empirical
comparison of these finite models.
Unnormalized initial weights omit
$\epsilon_{\rm init}=1-(1-q^{N_{\rm init}})^2$.
For a true TNI channel this bounds the omitted initial contribution
to $p,g$, but not output cutoff, finite-coupling approximation,
quadrature or physical-dilation error.

For the selected standing point, doubling intervals 240 to 480
changes native $g,p$ by less than $5\,10^{-16}$ in the audited
calculation. Changing
$(N_{\rm out},N_{\rm init})=(20,12)$ to $(24,14)$ changes its
$\bar n=0.25$ scores by about
$(2.93\,10^{-9},3.07\,10^{-9})$ while reducing
$\epsilon_{\rm init}$ from $8.192\,10^{-9}$ to
$3.2768\,10^{-10}$; ground scores change below $10^{-15}$.
This joint change does not isolate output truncation.
Independent literal kernel/order evaluations agree within
$2.23\,10^{-16}$ standing and $1.12\,10^{-16}$ running in their
checked cases. Such residuals are numerical consistency tests, not
outward error enclosures.

The optional [packet code](../numerics/moving_caps_packet.py) and
[running-wave code](../numerics/moving_caps_running.py) use NumPy.
Their single [current numerical record](../numerics/moving_caps_record.json)
owns actual selected runs, source hashes, environment, settings and
convergence data. Full JSON outputs and replay logs are generated in the ignored
build directory rather than stored as scan histories. Main exact-runner
fingerprints provide integrity for these inputs; they do not execute
the NumPy calculation or certify its floating-point results.

## Remaining physical test and executable scope

A positive successor must supply the same complete oriented contacts,
coherent router/helper, initial motion state and common-clock records
for both histories. Actual intrinsic/spontaneous loss, recoil,
spin-return levels, missing-photon flags, routing dispersion,
readout/reset, storage and all rejected launches must enter its
unknown-data instrument. Fitted reflection amplitudes and equal
arrival times do not supply it. Persistent calibrated nodes are
reused; no fresh hidden frame is assumed.

Compare ordinary pulse/packet shaping, sideband filters and coherent
same-order delays, trap/cooling optimization, paid repeated routes,
and capture/process/re-emission or Bell-resource/teleportation controls
when actually available. Acoustic capture is not automatically an
optical cavity port. A changed geometry, calibrated quarter-period
motion echo or extra selector must preserve its real controls and
costs. The required endpoint may legitimately accept a heralded
quality/yield tradeoff, use different branch decoders or retain
coherent control; those cases need their own complete comparison.
No full failure-utility, accepted-service, decoder or hardware-rate
optimum is asserted.

The standard-library [resolvent replay](../checks/architecture/moving_caps_resolvent.py)
checks literal finite Gaussian-rational inversions, passive Gram and
weighted-unitarity identities, Lipschitz slacks, unwrapped energy
shifts, nonzero order differences, (MR6), phase and common-energy
clock guards. The [completion/rank replay](../checks/architecture/moving_caps_rank.py)
checks finite CP decompositions, normalized scores, CPTP/TNI decoder
and input-support fixtures. The rational finite couplers are not the
source's infinite cosine or displacement operators.
The unbounded-domain argument, general
Lipschitz/moment estimate, packet/thermal extension and source-specific
support reasoning remain the proofs above. These finite checks
certify neither a motional tail nor a physical router, total rejection
bound, empirical score or native architecture benefit.
