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

<a id="nr-r11-moving-caps-coherent-motion"></a>

## Symmetric coherent motion and a blue-band Bell factory

The number-diagonal separability statement does not cover coherent
initial motion. Consider identical standing-wave nodes, each prepared
in the same-phase local state
$(|0\rangle+\epsilon_N|2\rangle)/\sqrt{1+\epsilon_N^2}$,
with $\epsilon_N\ge0$, and atoms initially in known $|++\rangle$.
A single $V$ photon has normalized spectral envelope supported on
$[-L,L]$, $L<\mu$. Select the blue band
$[2\mu-L,2\mu+L]$ with a frequency-diagonal transmission and bucket
click, then discard the remaining photon record and all final motion.
The bands are disjoint because local standing-wave transitions are
even. Hard spectral isolation is an idealization, not a finite-time
filter certificate. Preparation, phase alignment, filtering,
detection and all other output ports are paid.

For a general packet the initial coherent number amplitudes must be
summed at fixed **final** frequency before squaring:
$K_{\boldsymbol m}(\nu)=\sum_{\boldsymbol n}
c_{\boldsymbol n}f(\nu+E_{\boldsymbol m\boldsymbol n})
T_{\boldsymbol m\boldsymbol n}(\nu+E_{\boldsymbol m\boldsymbol n})$.
The thermal probability evaluator cannot be substituted for this
sum, and a Gaussian output window does not isolate an exact transfer
sector. The compact blue band here leaves only final motions
$00,02,20$: $20$ and $02$ initial components feed $00$ coherently,
while the initial $22$ component feeds $02$ or $20$.

Put $\delta=2\mu$, $a(w)=s^{0,2}(w)$,
$\Delta_0(w)=r_{\rm dark}(w+\delta)-r_{\rm dark}(w)$,
$\Delta_2(w)=s^{2,2}(w+\delta)-s^{2,2}(w)$, $z=\epsilon_N^2$,
and
$u=\epsilon_Na\Delta_0/[2(1+z)]$,
$v=\epsilon_Na\Delta_2/[2(1+z)]$.
For native minus, the exact diagonal atomic Kraus densities, up to
overall signs and the common incident/filter amplitude, are

$$
K_{00}=u(P_{10}-P_{01}),\qquad
K_{02}=\epsilon_N(uP_{10}+vP_{11}),\qquad
K_{20}=-\epsilon_N(uP_{01}+vP_{11}),
\tag{MC10}
$$

where $P_{ij}=|ij\rangle\langle ij|$.
The $00$ bright-bright terms cancel without equating their two
frequency responses. The other two records remain distinguishable
in discarded motion and must not be deleted. Thus (MC10), integrated
over frequency as a CP Kraus sum, also specifies the full selected
map on arbitrary $ABR$. The following Bell scores use only the
factory input $++$.

Absorb any common passive frequency-diagonal blue transmission,
$|\chi(\nu)|\le1$, into
$W(w)=|f(w)|^2|\chi(w+\delta)|^2$, without renormalizing the
original normalized packet after filtering, and define
$I_0=\int W|a|^2$, $I_d=\int W|a\Delta_0|^2$,
$I_{22}=\int W|a\Delta_2|^2$.
For $I_d>0$, write $\rho=I_{22}/I_d$ and $q=I_d/I_0$.
All final motions in (MC10) give native probability and singlet-good
mass

$$
p_N=\frac{I_dz[1+(1+\rho)z]}{8(1+z)^2},\qquad
g_N=\frac{I_dz(1+z/2)}{8(1+z)^2},\qquad
F_N=\frac{1+z/2}{1+(1+\rho)z}.
\tag{MC11}
$$

At $\epsilon_N=1$, $F_N\le3/4$; small excitation approaches unit
singlet fraction while suppressing probability. Isolating only the
$00$ singlet would give the wrong selected state.

Supply an ordinary balanced coherent path that visits **only $A$**
or **only $B$**, followed by minus which-node erasure and the same
blue selection. This needs actual bypass/termination ports, not
merely the native ability to visit $AB$ or $BA$. Using the same
local preparation family with $z_O=\epsilon_O^2$ gives

$$
J_{00}=\frac{\epsilon_Oa(P_{10}-P_{01})}{2(1+z_O)},\quad
J_{02}=\frac{\epsilon_O^2aP_{1,A}}{2(1+z_O)},\quad
J_{20}=-\frac{\epsilon_O^2aP_{1,B}}{2(1+z_O)},
$$

and

$$
p_O=\frac{I_0z_O(1+2z_O)}{8(1+z_O)^2},\qquad
g_O=\frac{I_0z_O(1+z_O/2)}{8(1+z_O)^2}.
\tag{MC12}
$$

For $z>0$ and $F_N>1/2$, equivalently $\rho z<1$, the choice
$z_O=(1+2\rho)z/[3+(1-\rho)z]$ lies in $(0,1)$.
Substitution gives $F_O=F_N$ and

$$
\frac{p_O}{p_N}
=\frac{3(1+2\rho)(1+z)^2}{q[3+(2+\rho)z]^2}
\ge\frac1{3q}.
\tag{MC13}
$$

The denominator is positive. To prove the inequality, subtract its
squared positive denominators:
$9(1+2\rho)(1+z)^2-[3+(2+\rho)z]^2
=18\rho+6z+29\rho z+5z^2+14\rho z^2+\rho z(1-\rho z)\ge0$,
using $0\le\rho z<1$. If $I_d=0$ there is no native singlet-good mass.
This matches quality by changing a paid preparation amplitude; it is
not dominance at an identical fixed coherent state.

The empty-cavity response bounds $q$ without bright-kernel numbers.
For $\delta\le2\kappa$,

$$
q\le\sup_w|\Delta_0(w)|^2
=\frac{4\kappa_{\rm ex}^2\delta^2}
 {(\kappa^2+\delta^2/4)^2}<\frac{53}{1000}<\frac1{18}
\tag{MC14}
$$

at the stated nominal rates. Indeed, setting $t=w+\delta/2$ makes
the product of the two reflection denominators
$(\kappa^2+\delta^2/4)^2+
2(\kappa^2-\delta^2/4)t^2+t^4$, minimized at zero.
Here $\kappa_{\rm ex}^2=1459/375$,
$\kappa_{\rm ex}>493/250$, $\kappa>543/250$ and
$\delta=69/250$ prove the strict rational bound.
Consequently the ideal ordinary selected probability is more than
six times the native value at matched useful raw singlet quality,
independently of a Fock cutoff or a numerical bright response.

There is a separate paid extension for a common accepted photon
effect $0\le E\le I$ after blue-band isolation. At $\nu=w+\delta$,
cascade the two Lorentzian transmissions
$L_\delta(\nu)=\kappa/[\kappa-i(\nu-\delta)]$ and
$L_0(\nu)=\kappa/(\kappa-i\nu)$ with constant phase $-i$.
Each is a causal passive two-port component: at detuning $\Omega$,
its complementary amplitude is $R=-i\Omega/(\kappa-i\Omega)$
and the matrix with rows $(R,L)$, $(L,R)$ is unitary.
The product obeys
$-iL_\delta L_0=\Delta_0(w)/M'$,
$M'=2\kappa_{\rm ex}\delta/\kappa^2$.
Thus the ordinary field vector before $E$ is exactly
$fa\Delta_0/M'$. Replacing the bucket integrals by the corresponding
$E$-weighted inner products gives $I_0'=I_d/M'^2$; the same matching
algebra (MC11)–(MC13) applies with $q=M'^2$.
At the nominal rates
$M'^2<1543622000/28978644267<1/18$.
This requires two additional filter rejection ports, phase control,
dispersion/ringdown, latency and real insertion loss to be paid.
It is an analytic construction, not a claim that the source supplies
these components or that the finite helper/packet runs test it.

This is a bounded comparison of symmetric, same-phase preparations
and measured-minus blue-band factories, not all coherent-motion
protocols. Arbitrary relative preparation phases, local spin filters,
coherent red/blue erasure, photon-outcome-dependent atomic decoders
and retained-control recovery are separate optimizations.
The paid extension covers only a common accepted photon effect after
the isolated band. Actual preparation/reset,
router loss, arm overlap, phase stability, detection, latency and
rejected launches determine delivered rates. Neither two-node router
is established by the source; if bypass is absent, its availability
must be tested rather than assumed. There is no global hardware-rate
or unrestricted factory optimum claim.

### An ordinary carrier-parity witness for the Bell endpoint

The factory endpoint may destroy the photon, unlike (MC1), so a
$V$-only restriction requires an actual interface reason. Prepare
known atoms $++$ with ground motion, photon $|+\rangle$, and use
ordinary $AB$ visits with the common $H$ amplitude
$h=a=r_{\rm dark}(0)^2$. Detect both photon $X$ ports, applying
$I$ or $X_B$ to target
$\Phi^+=(|00\rangle+|11\rangle)/\sqrt2$. The joint retained-field branch
operators before detection are $(aI\pm T_{AB})/2$.
Here detection traces the photon frequency and all final motion:
these are atomic Bell scores, not the retained-$PAB$/fixed-temporal-mode
scores in (MC4).

The [finite-packet witness](../numerics/moving_caps_parity.py) uses a
normalized compact-support truncated Gaussian on
$[-8.5\sigma,8.5\sigma]$. At $\sigma/(2\pi)=0.01$ MHz, cutoff 20 and
240 trapezoidal intervals it gives the following rounded
reflected-sector, both-port totals:

| Known photon / $H$ reference | $p$ | Bell-good mass $g$ | $F=g/p$ |
| --- | --- | --- | --- |
| $|+\rangle$ / amplitude $a$ | 0.440404 | 0.440359 | 0.999896234 |
| Biased photon / unit amplitude | 0.610359 | 0.610296 | same |

The second row has an analytic normalization explanation. Supply
unit $H$ transmission and a known photon
$\alpha|H\rangle+\beta|V\rangle$ with
$\alpha=a/\sqrt{1+a^2}$, $\beta=1/\sqrt{1+a^2}$.
Its branch operators are
$(aI\pm T_{AB})/\sqrt{2(1+a^2)}$.
Every accepted atomic density, including each fine output record,
is therefore exactly $2/(1+a^2)$ times the balanced-reference
density. Both $p,g$ scale by this factor and $F$ is unchanged;
this identity does not depend on a numerical cutoff.
At the ideal motionless equal-reflection CZ carrier, both parity
flags are Pauli-correctable Bell outputs with total probability
$2a^2/(1+a^2)\approx0.614095$.

The numerical cases are $(N,\text{intervals})=(12,160),(20,240),(20,480)$:
the first refinement changes cutoff and quadrature jointly; the
last refines quadrature at fixed cutoff. Their actual results and
environment belong to the single current numerical record, not an
infinite-oscillator or outward error certificate. Destructive
photon detection is a legitimate presence herald for this factory,
but detector efficiency, false clicks, source bias, preparation/reset,
storage and the full delivery clock still need their physical model.
The known polarization bias cannot be applied to the original unknown
retained-$PAB$ payload. Higher fidelity requirements and stronger
ordinary filters, purification, local bias or memories need their own
comparisons; this is neither a factory optimum nor a hardware rate.

<a id="nr-r11-moving-caps-coherent-analyzer"></a>

### A paid coherent photon outcome can prepare an exact Bell state

The preceding raw fidelity is not an ordinary ceiling. A stronger
conditional construction uses ground motion, known atoms $++$, identical
standing-wave nodes and a normalized incident envelope $f$ supported on
$[-L,L]$, $L<\mu$. Select the **carrier** band $[-L,L]$ after ordinary
$AB$ visits. Every nonzero allowed final motion has $m_A+m_B\ge2$ and
shifts the photon by $-(m_A+m_B)\mu$, so its output band is disjoint.
Only final motion $00$ survives, on the full oscillator Hilbert space.
This energy/parity argument does not truncate virtual excursions inside
the complete ground-to-ground reflection amplitude
$r_1(w)=s^{0,0}(w)$. It requires the specified initial ground state,
individual parity, independent nodes and absence of other unread
inelastic records. A finite-time apparatus must approximate the ideal
band isolation and bound its leakage.

Write $r_0=r_{\rm dark}$ and prepare the known photon
$\alpha H+\beta V$, $|\alpha|^2+|\beta|^2=1$. The surviving joint state is

$$
|\Psi\rangle=\frac12\sum_{ij}|ij\rangle
 \bigl(|H\rangle q+|V\rangle v_{ij}\bigr),\qquad
q=\alpha hf,\quad
(v_{00},v_{01},v_{10},v_{11})
 =\beta f(r_0^2,r_0r_1,r_0r_1,r_1^2).
\tag{MC15}
$$

Here $h$ is the supplied common $H$ response and the field vectors
include their incident amplitudes. Fix a known normalized $V$ analysis
mode $\phi$, such as $f$, and set
$c_0=\langle\phi,v_{00}\rangle$,
$b=\langle\phi,v_{01}\rangle$,
$c_1=\langle\phi,v_{11}\rangle$, $H_0=\|q\|^2>0$.
An $H$ analysis vector can contribute any scalar
$\gamma=\langle\xi,q\rangle$ at minimum squared norm
$|\gamma|^2/H_0$. Define $x=c_0-b$, $y=c_1-b$ and $u=\gamma+b$.
The unnormalized atomic amplitude matrix is

$$
M=\begin{pmatrix}u+x&u\\u&u+y\end{pmatrix},\qquad
u=\frac{|y|^2-|x|^2}{2\overline{x-y}}\quad(x\ne y),
\qquad \gamma=u-b.
\tag{MC16}
$$

For $x=y\ne0$, choose $u=0$. If $x=y=0$, this chosen $\phi$ has no
entangling contrast: every $M$ is a multiple of the all-ones product
matrix. A different analysis mode may still have contrast.

To prove (MC16), put $d=x-y\ne0$ and
$t=(|y|^2-|x|^2)/(2|d|^2)\in\mathbb R$, so $u=td$.
Then
$(MM^\dagger)_{01}=2t^2|d|^2+t(|x|^2-|y|^2)=0$ and
$(MM^\dagger)_{00}-(MM^\dagger)_{11}
=2t|d|^2+|x|^2-|y|^2=0$.
Thus $MM^\dagger=s^2I$, with $s>0$ whenever $(x,y)\ne(0,0)$.
The equal-$x,y$ case has the same property directly. Moreover,
$|u|\le(|x|+|y|)/2$, so nearly equal coefficients do not force an
unbounded analyzer amplitude, although the calibrated Bell frame can
remain sensitive to small errors.

Normalize the **whole** photon outcome, including its $H$ component:

$$
\xi=\frac{\overline\gamma}{H_0}q,\qquad
\lambda=\left(1+\frac{|\gamma|^2}{H_0}\right)^{-1/2},\qquad
|\chi\rangle=\lambda\bigl(|H\rangle\xi+|V\rangle\phi\bigr).
\tag{MC17}
$$

Detection of this one unit-normalized mode gives
$\lambda\operatorname{vec}(M)/2$, with probability

$$
p_\chi=\frac{\lambda^2}{4}\operatorname{Tr}(MM^\dagger)
       =\frac{\lambda^2s^2}{2}.
\tag{MC18}
$$

The conditional atomic state is maximally entangled. The known local
unitary $M^\dagger/s$ on atom $A$ converts it to $\Phi^+$; no nonunitary
atomic filter is used in this symmetric-node construction. All
orthogonal photon outcomes are rejected here. A second useful outcome
is not counted. Nonidentical nodes need not have $v_{01}=v_{10}$ and
are outside this prescription; local SVD/concentration remains an
additional, separately paid ordinary option for a known pure output.

A stricter fixed-even-Bell family has a closed optimum. Let $P$ project
orthogonally to $v_{00}-v_{11}$ (use $P=I$ if this vector is zero),
$A=P(v_{00}-v_{01})$ and $B=Pv_{01}$. Requiring
$\phi\perp v_{00}-v_{11}$ and $\gamma=-\langle\phi,v_{01}\rangle$
gives probability
$|\langle\phi,A\rangle|^2/[2(\|\phi\|^2+
|\langle\phi,B\rangle|^2/H_0)]$.
Cauchy--Schwarz in the positive metric $I+|B\rangle\langle B|/H_0$,
followed by its rank-one inverse, gives the attained maximum

$$
p_{\rm even}=\frac12\left(\|A\|^2-
 \frac{|\langle B,A\rangle|^2}{H_0+\|B\|^2}\right).
\tag{MC19}
$$

It is positive exactly when $A\ne0$; an optimal mode is proportional to
$A-B\langle B,A\rangle/(H_0+\|B\|^2)$ before normalization (MC17).
Exact orthogonality to a small nuisance vector can remove a large
useful packet component. Allowing a known Bell-frame rotation as in
(MC16) avoids that unnecessary fixed-parity restriction.

The [exact analyzer helper](../checks/architecture/moving_caps_analyzer.py)
guards finite complex rational photon projections, complete analyzer
normalization, nonzero and degenerate Bell matrices, and the local
correction. The [optional source witness](../numerics/moving_caps_analyzer.py)
uses the normalized compact truncated Gaussian above with 160
trapezoidal intervals and virtual-motion cutoffs 12 and 16. Its
single-outcome probabilities are approximately $0.220169$ for the
balanced photon with $H$ mask, and $0.305134$ for the biased known photon
with unit $H$ reference. These finite witnesses and their actual runs
belong to the current numerical record. They certify neither an infinite
virtual-resolvent error nor device fidelity. The carrier's final-motion
isolation is the separate analytic argument above.

The moving-ground response is complex even at bare resonance: positive
virtual phonon energies invalidate the shortcut
$r_1(-w)=\overline{r_1(w)}$. Equations (MC16)--(MC18) retain that phase.
Ground cooling, carrier isolation, coherent rank-one temporal-mode
analysis, matched $H$ analysis, calibration, known local rotation,
detection, every reject, reset, insertion loss and timing are paid
requirements. Elementary polarization control or a frequency-bin mixer
does not supply an arbitrary temporal projector. Exact compact support
and exact rank-one continuum analysis are ideal limits, with no finite
clock or calibration guarantee. A native proposal granting the same
coherent photon analyzer must admit this ordinary comparator or justify
an actual interface/cost difference. No arbitrary retained-helper
recovery, full factory optimum or native hardware benefit is established.

### Frequency-resolved ordinary readout with finite response width

<a id="nr-r11-moving-caps-frequency-readout"></a>

The same ground-motion carrier sector admits a different paid readout
that does not select one coherent temporal mode. Keep the known atomic
$++$ input and all assumptions of (MC15). Write

$$
R(w)=\begin{pmatrix}r_0(w)^2&r_0(w)r_1(w)\\
 r_0(w)r_1(w)&r_1(w)^2\end{pmatrix},\qquad q_H(w)=\alpha h(w).
$$

Assume a frequency-diagonal photon instrument with response $R_j(w)\ge0$,
$\sum_jR_j(w)\le1$. Each record $j$ has a fixed unit-normalized
polarization bra $(t_{H,j},t_{V,j})$ and a known local correction $U_j$ on
atom $A$. Discard the unresolved frequency and arrival-time records.
With $\mathbf1$ denoting the two-by-two all-ones matrix, set
$B_j(w)=t_{H,j}q_H(w)\mathbf1+t_{V,j}\beta R(w)$. Its exact accepted
probability and Bell-good mass are

$$
\begin{aligned}
\rho_j&=\frac14\int |f(w)|^2R_j(w)
 |\operatorname{vec}(U_jB_j(w))\rangle
 \langle\operatorname{vec}(U_jB_j(w))|\,dw,\\
p&=\frac14\sum_j\int |f|^2R_j\|B_j\|_F^2\,dw,\qquad
g=\frac18\sum_j\int |f|^2R_j|\operatorname{Tr}(U_jB_j)|^2\,dw,
\qquad F_{\rm Bell}=g/p.
\end{aligned}\tag{MC20}
$$

This specifies the measurement instrument, not just its spectral intensity
curve. A resolved arrival-time click after a filter can contain coherent
cross-frequency amplitudes and does not automatically implement (MC20).

For an exactly known frequency and a fixed polarization analyzer, local
unitaries alone give at most

$$
F_{\rm loc}(w)=\frac{\|B(w)\|_F^2+2|\det B(w)|}{2\|B(w)\|_F^2}.
\tag{MC21}
$$

Indeed, if the singular values are $s_1,s_2$, the largest corrected trace
magnitude is $s_1+s_2$. Exact Bell therefore requires equal singular values;
knowing the frequency cannot remove a Schmidt-amplitude mismatch by rotation.
Local concentration is a separate paid filter, with resolved-frequency
Bell mass $s_{\min}(B)^2/2$, and is not used below.

At representative $w_j$, instead apply (MC16) pointwise to
$c_0=\beta r_0(w_j)^2$, $b=\beta r_0(w_j)r_1(w_j)$ and
$c_1=\beta r_1(w_j)^2$. It gives
$M_j=\gamma_j\mathbf1+\beta R(w_j)$ and
$M_jM_j^\dagger=s_j^2I$. For nonzero $q_H(w_j)$ choose

$$
\lambda_j=\left[1+|\gamma_j/q_H(w_j)|^2\right]^{-1/2},\quad
(t_{H,j},t_{V,j})=\lambda_j(\gamma_j/q_H(w_j),1),\quad
U_j=M_j^\dagger/s_j.
\tag{MC22}
$$

The center output is exactly Bell. Count only this one normalized
polarization outcome; its orthogonal output has not been proved to be
another Bell branch. Frequency sorting followed by calibrated per-bin
polarization processing is an additional port. A label obtained after a
fixed-polarization click cannot retroactively supply (MC22). The continuum
limit with its own analyzer and correction at every frequency is exact.
A finite bin is exact only if almost every corrected $B_j(w)$ is
proportional to identity, because a positive mixture is rank one only when
all its nonzero summands share the same support.

There is an analytic finite-resolution bound. Let
$P_\perp X=X-I\operatorname{Tr}(X)/2$ and suppose
$\|B_j(w)-B_j(w_j)\|_F\le D_j|w-w_j|$. The Frobenius contraction of
$P_\perp$ and unitarity of $U_j$ imply
$\|P_\perp U_jB_j(w)\|_F\le e_j+D_j|w-w_j|$, where
$e_j=\|P_\perp U_jB_j(w_j)\|_F$. For (MC22), $e_j=0$, hence

$$
Q_j=\int |f(w)|^2R_j(w)(w-w_j)^2\,dw,\qquad
p-g\le\frac14\sum_jD_j^2Q_j,\qquad
F_{\rm Bell}\ge1-\frac{\sum_jD_j^2Q_j}{4p}.
\tag{MC23}
$$

A lower confidence bound on actual $p$ may replace its denominator.
For response weight $W_j=\int|f|^2R_j$ confined within $\Delta_j$ of
$w_j$, the triangle inequality separately gives
$p\ge\sum_jW_j[\max(0,\|B_j(w_j)\|_F-D_j\Delta_j)]^2/4$.
Mislabel tails must enter the full $Q_j$; a small nominal bin width alone
does not bound them. Calibration and rotation errors enter through the
nonzero center residual $e_j$ and its displayed squared envelope.

For constant $h$, (MR2)–(MR3) supply $|r_i|\le1$ and all-cutoff
Lipschitz constants $L_0=2\kappa_{\rm ex}/\kappa^2$ and
$L_1=2\kappa_{\rm ex}/\min(\kappa,\gamma)^2$. Entrywise product
differences then give the admissible constant

$$
D_j^2=\lambda_j^2|\beta|^2
 [4L_0^2+2(L_0+L_1)^2+4L_1^2].
\tag{MC24}
$$

If $h$ varies with Lipschitz constant $L_h$, add
$2|t_{H,j}\alpha|L_h$ to the Frobenius bound for $D_j$.
A sharp bin of full width $\Delta$ centered at its midpoint has
$Q_j\le W_j\Delta^2/4$; its incident-density centroid only decreases
$Q_j$. The finite-resolution bad mass is therefore quadratic in width
under this declared measurement model. The proof does not replace the
source's complex $r_1(w)$ by a real-resonance approximation.

The [exact frequency helper](../checks/architecture/moving_caps_frequency.py)
checks normalized complex polarization projections, corrected densities and
nonzero finite-bin bad mass. The [optional source witness](../numerics/moving_caps_frequency.py)
uses 640 trapezoidal intervals, cutoffs 12 and 16,
$\sigma/(2\pi)=10\,\mathrm{kHz}$ and compact band
$[-85,85]\,\mathrm{kHz}$. For the biased known photon with unit $H$
reference, 8, 16 and 32 bins with their own analyzers give one-port
$p\simeq0.305145$ and $F\simeq0.99998594,0.99999543,0.99999878$.
Evaluating (MC23) with the finite sampled moments and $p$ gives lower
values $0.99991558,0.99997257,0.99999268$. These are empirical evaluations
of an analytic inequality, with no infinite-resolvent, quadrature or device
confidence certificate. A fixed analyzer without frequency resolution gives
$F\simeq0.99994687$; even resolved-frequency local rotations alone reach
only about $0.99997651$ for that fixed analyzer. Two fixed polarization
outputs with separate known local corrections give a distinct approximate
comparison: total $p\simeq0.610333$, $F\simeq0.99993290$ without frequency
resolution, or $F\simeq0.99997051$ with 16-bin frame corrections.

The 32-bin example has full width $5.3125\,\mathrm{kHz}$. As one explicit
cost model, a Lorentzian amplitude filter
$t(\omega)=k_f/[k_f-i(\omega-\omega_j)]$ has intensity FWHM
$\Delta\nu=k_f/\pi$, normalized impulse intensity $2k_fe^{-2k_ft}$,
mean delay $1/(2\pi\Delta\nu)$ and 99-percent impulse-energy time
$\log(100)/(2\pi\Delta\nu)$: about $30$ and $138\,\mu\mathrm{s}$ here.
This is a filter calculation, not a universal spectrometer lower bound.
A real bank needs its actual response and time instrument, insertion loss,
polarization phases, false clicks, detector efficiency, feedforward and
atomic storage, cooling/reset, carrier leakage and calibration reuse/drift.
Exact frequency resolution is not a finite-clock port.

Finally, within the specified bare two-history protocol's ground-motion
final carrier sector both orders are the same products $r_i(w)r_j(w)$,
including their complex phase. The order
helper factors into its known plus state. Every common photon/helper
analyzer therefore has the same ordinary pre-readout state available,
with an unused known helper supplied at its actual cost. Ordering gives
no additional carrier-sector readout capability under these assumptions.
Coherent red/blue erasure, retained nonzero motion, changed history frames,
other loss records and unknown-input services remain separate tests.

Ordinary which-node erasure is established by
[Cabrillo et al., PRA **59**, 1025 (1999)](https://arxiv.org/abs/quant-ph/9810013)
and the trapped-ion single-photon-interference experiment of
[Slodička et al., PRL **110**, 083603 (2013)](https://arxiv.org/abs/1207.5468v2).
Those sources do not claim this CAPS kernel or quality-matched bound.
The separate [exact factory helper](../checks/architecture/moving_caps_factory.py)
checks its algebraic ingredients. The new carrier-parity numerical
study does not test the coherent-motion blue-band construction
(MC10)–(MC14).

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
