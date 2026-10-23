# Displacement-area calibration and native ordinary controls

[Application assessment](architecture.md) · [Native ordinary baselines](architecture-baselines.md#nr-r06) · [Finite-query metrology](metrology.md#nr-r15) · [Topic](README.md)

<a id="nr-r16"></a>

## NR-R16 — Displacement-area calibration and native ordinary controls

The geometric phase of two displacement arrays is a useful calibration
output. Its quantum-switch theory and optical experiments provide a
concrete starting point. Transporting that comparison to ion, cavity or
spatial-optical hardware requires the actual control interface and energy
budget. Reusable conditional forces already admit an ordinary echo with
the same precision scaling. Classical changes of shot order also remove
an initial-energy bottleneck when later probe preparation is allowed.

The constructions below are attainable ordinary baselines under stated
access assumptions. They do not establish an optimized ordinary frontier,
a new protected holonomic gate, or a matched architecture advantage.

### Calibration endpoint and resource conventions

Use dimensionless quadratures $[X,P]=i$ and displacement modules

$$
A_j=e^{-ix_jP},\qquad B_j=e^{ip_jX},\qquad j=1,\ldots,N.
$$

Write

$$
a=\sum_jx_j=N\bar x,\qquad b=\sum_jp_j=N\bar p,
\qquad \theta=\bar x\bar p.
$$

The unknown amplitudes are fixed during acquisition of the repeated shots
used to estimate $\theta$. The two arrays need not have equal component
amplitudes. Fresh random amplitudes on later visits require a different
statistical target and noise model.

One *primitive execution* is one physical application of an individual
$A_j$ or $B_j$. The elementary switch uses $2N$ executions. A native
conditional force is a stronger interface than an uncontrolled unknown
displacement. Its pulse, control and coupling costs are counted separately;
its existence is not inferred from a channel description. A hard
one-use-per-component cap differs from expected cost, information per
execution and information per unit time, as in the
[finite-query metrology boundary](metrology.md#nr-r15).

For continuous variables use $H=X^2+P^2$, so vacuum has energy $1$ and
variances $\operatorname{Var}X=\operatorname{Var}P=1/2$. Sources using
$(X^2+P^2)/2$ assign vacuum energy $1/2$. Initial energy means energy
entering the first unknown module. Maximum intermediate energy and the
work, bandwidth or aperture required for known controls are separate
resources. None is identified merely by the number of optical photons.

### Exact switched signal

Let $A=\prod_jA_j=e^{-iaP}$ and $B=\prod_jB_j=e^{ibX}$. The Weyl relation is

$$
BA=e^{iab}AB.
$$

Equivalently, with $D(a,b)=e^{i(bX-aP)}$,
$BA=e^{iab/2}D(a,b)$ and $AB=e^{-iab/2}D(a,b)$. Thus

$$
|0\rangle\langle0|\otimes BA+|1\rangle\langle1|\otimes AB
=e^{iabZ_C/2}\otimes D(a,b).
$$

This is an operator identity. An independently prepared control therefore
factors from any initial bus/reference state. On $|+\rangle_C$ it supplies a relative phase
$ab=N^2\theta$ and control quantum Fisher information $N^4$ for local
estimation of $\theta$. A phase-resolved control measurement attains that
local information. A single cosine readout alone does not identify the
global sign or fringe number.

This is a parameter signal, not an error-cancellation theorem. For
example, common fractional force drift sends $a,b$ to
$(1+\delta)a,(1+\delta)b$, changing the phase to
$(1+\delta)^2ab$. If a numerical target phase is already known, direct
native phase synthesis is also a gate comparator. An unknown area instead
defines a calibration problem.

### Published ordinary $3N$ echo with native conditional forces

[Zhao, Yang and Chiribella](https://arxiv.org/html/1912.02449v4),
*Quantum Metrology with Indefinite Causal Order*, PRL **124**, 190503
(2020), already give the following ordinary spin-dependent-displacement
construction and point to trapped ions. The derivation here fixes signs,
retained outputs and costs explicitly.

Suppose native controls implement

$$
U_j=|0\rangle\langle0|\otimes A_j
   +|1\rangle\langle1|\otimes A_j^\dagger,
\qquad V_j=U_j^\dagger.
$$

Apply every $U_j$, then every $B_k$, then every $V_j$, in that definite
chronological order. The complete operation is

$$
\begin{aligned}
V(I\otimes B)U
&=|0\rangle\langle0|\otimes A^\dagger BA
 +|1\rangle\langle1|\otimes ABA^\dagger\\
&=e^{iabZ_C}\otimes B.
\end{aligned}
$$

Here $A^\dagger BA=e^{iab}B$ and $ABA^\dagger=e^{-iab}B$ follow directly
from the Weyl relation. The bus output is the same $B\rho B^\dagger$ in
both arms, including every passive reference. No numerical estimate of
the $x_j$ or $p_j$ is used.

This requires two repeatable $x$-force executions and one $p$-execution
per component, hence $3N$ primitive executions. Its control relative
phase is $2N^2\theta$, with local Fisher information $4N^4$. It is outside
a hard one-use-per-component cap. Before helper errors and time costs,
its control-phase information per primitive execution is $8/3$ times the
elementary switch control's. Equivalently, launching it with probability $2/3$, with a recorded
parameter-independent skip otherwise, uses expected cost $2N$ and supplies
Fisher information $(8/3)N^4$ per attempted launch. This is an attainable
baseline, not a claim of optimality or global risk at a fixed prior.

Known oscillator parity $\Pi=e^{i\pi n}$ can manufacture the conditional
sign when that coupling is actually available. Since
$\Pi A_j\Pi=A_j^\dagger$, the controlled parity
$R=|0\rangle\langle0|\otimes I+|1\rangle\langle1|\otimes\Pi$ obeys

$$
R(I\otimes A_j)R=U_j.
$$

Changing the control convention gives $V_j$. This uses forward
displacement calls and known helpers; the helpers' coupling, retention,
noise and readout remain physical costs. Native on/off controlled
displacements provide a related three-pulse Ramsey construction. If the
$x$ force is a calibrated reference and only $b$ is unknown, its two
applications are known controls and there is only one unknown $B$ exposure.

The repeat must reproduce the same displacement response. Independent
uncontrolled changes on the two visits invalidate the displayed identity.
Native conditional forces, inverse/sign control and repeated access are
not automatically supplied by a one-pass unknown optical component.

### Ordinary $4N$ loop with a returned bus

The preceding operation leaves the bus displaced by $B$. A final
implementation of $B^\dagger$ returns it:

$$
(I\otimes B^\dagger)V(I\otimes B)U=e^{iabZ_C}\otimes I.
$$

If required, parity conjugation implements each $B_j^\dagger$ using a
second forward $B_j$ execution. The resulting four-leg geometric loop
uses $4N$ primitive executions, plus native sign/control helpers. It
returns the entire bus/reference state and has the same local information
$4N^4$. A launch probability $1/2$ gives expected cost $2N$ and information
$2N^4$, with all skips included. A scalar four-displacement loop without
a quantum-conditional force only produces a global phase; that is not
the Ramsey comparator proved here.

Both ordinary loops double the signal phase relative to the elementary
switch and therefore also double phase wrapping. Global calibration must
count coarse-to-fine gain settings, phase quadratures, prior acquisition,
background-phase estimation and every launched trial. These local
information calculations do not silently supply that global analysis.

For scalar visibility $v$ and parameter-independent survival $\eta$,
including an independently flagged no-click outcome, the launched-shot
Fisher information of a signal phase $M\theta+\phi_0$ is

$$
F_{\rm launch}
=\frac{\eta v^2M^2\sin^2(M\theta+\phi_0)}
 {1-v^2\cos^2(M\theta+\phi_0)}.
$$

At quadrature, the ordinary $3N$ echo's information per execution divided
by the switch's is

$$
\frac83\frac{\eta_{\rm ord}}{\eta_{\rm sw}}
       \left(\frac{v_{\rm ord}}{v_{\rm sw}}\right)^2.
$$

Thus, for the switch to beat this competitor at matched mean executions,
the measured parameters must satisfy

$$
\eta_{\rm ord}v_{\rm ord}^2
<\frac38\eta_{\rm sw}v_{\rm sw}^2.
$$

This is a necessary comparison with one feasible
ordinary method. It is not an upper bound over all ordinary methods or a
model for arbitrary loss channels. Return delay, route loss, reset,
helper noise and actual cycle time can reverse the ideal information-rate
comparison.

These information ratios compare the displayed control readouts. The
displaced bus can carry additional parameter information, and a joint
bus/control measurement defines a different optimization. The ratios are
not upper bounds on every full-output switch protocol.

### Classical shot-order changes with constant initial energy: exact CV construction

A different ordinary construction uses every sample once per shot, no
inverse, attenuation, controlled force or reset, and different *classical*
orders for two shot families. It requires a known squeeze after one
selected first oracle and access to the remaining components in the
specified order.

In the $x$ family, first apply $B_1$ to vacuum. Apply a known squeeze $S_N$
with

$$
S_N^\dagger XS_N=X/N,\qquad S_N^\dagger PS_N=NP.
$$

Then apply all $A_j$ and all remaining $B_j$ once and homodyne $X$.
Momentum displacements affect only the conjugate mean, and reordering
the Weyl displacements adds only a global phase. Therefore exactly

$$
X_{\rm out}\sim\mathcal N\!\left(N\bar x,\frac1{2N^2}\right).
$$

The sample mean from $\nu_x$ shots, divided by $N$, is an unbiased
$\widehat{\bar x}$ with variance
$v_x=1/(2\nu_xN^4)$. The $p$ family first applies $A_1$, squeezes $P$ by
$1/N$, applies every $B_j$ and remaining $A_j$ once, and homodynes $P$.
It gives an independent unbiased $\widehat{\bar p}$ with
$v_p=1/(2\nu_pN^4)$. Their product is globally unbiased, with exact risk

$$
\mathbb E(\widehat{\bar x}\widehat{\bar p}-\theta)^2
=\bar p^{\,2}v_x+\bar x^{\,2}v_p+v_xv_p.
$$

This follows by expanding the product of two independent zero-mean
estimation errors; the mixed linear terms vanish. For bounded means and
$\nu_x,\nu_p$ proportional to the total shots $\nu$, it is
$O(1/(\nu N^4))$ without any narrow wrapped-phase prior.

Initial energy is $1$. Immediately after the $x$-family squeeze,

$$
\langle H\rangle
=\frac1{2N^2}+N^2\left(\frac12+p_1^2\right).
$$

The remaining bounded samples change means by $O(N)$, so maximum
intermediate energy remains $O(N^2)$. Squeezing after the **entire**
$N$-displacement momentum group would instead magnify an unknown $O(N)$
mean to $O(N^2)$ and can cost $O(N^4)$ energy. The location of the control
is essential. A two-bank order router alone does not imply access after
$B_1$ or $A_1$.

For a single photon's transverse spatial degree of freedom, this squeeze
can be paraxial magnification rather than nonclassical field squeezing.
A $4f$ relay has ray matrix
$\operatorname{diag}(-f_2/f_1,-f_1/f_2)$; known parity removes the signs,
and $f_2/f_1=1/N$ gives the desired canonical map. Lens implementations of
spatial symplectic squeezing are described by
[Calvo and Picón](https://arxiv.org/abs/0712.1197), PRA **77**, 012302
(2008). Numerical aperture, clipping, angular bandwidth and paraxiality
constrain usable $N$. The transverse oscillator energy can increase as
$N^2$ while the carrier-photon energy stays fixed. Neither resource is
free or interchangeable with the other.

### Exact finite-dimensional global risk with post-first preparation

The next construction proves a finite-dimensional global-risk statement
without an approximate Weyl relation. It uses explicit known
reset/preparation and measurement controls. Their efficiency and native
cost are assumptions, not consequences of the mathematical bound.

Let $d=2m+1\ge3$, $\kappa=\sqrt{2\pi/d}$, and

$$
P=\kappa\sum_{k=-m}^m k|p_k\rangle\langle p_k|,\qquad
X=\kappa\sum_{k=-m}^m k|x_k\rangle\langle x_k|,
$$

where the two bases are discrete Fourier conjugates. Define the exact
oracles $A_j=e^{-ix_jP}$, $B_j=e^{ip_jX}$ and $H=X^2+P^2$.

A constant-energy initial state exists by an elementary exact bound.
Let $L$ be the smallest odd integer at least $\sqrt d$, and prepare a
normalized sine vector on the central $L$ momentum levels, with zero
amplitudes outside that support. Then

$$
\langle P^2\rangle\le\frac{\pi(L-1)^2}{2d}
\le\frac\pi2\left(1+\frac1{\sqrt3}\right)^2.
$$

Let $T$ cyclically shift the momentum levels. Its eigenvalues in the
position basis have squared distance from $1$ equal to
$4\sin^2(\pi n/d)\ge16n^2/d^2$. The adjacent overlap of the supported
sine vector is at least $\cos[\pi/(L+1)]$; if $L=d$, the cyclic endpoint
term is additional and nonnegative. Consequently

$$
\begin{aligned}
\langle X^2\rangle
&\le\frac{\kappa^2d^2}{16}\|(T-I)\psi\|^2\\
&\le\frac{\kappa^2d^2\pi^2}{16(L+1)^2}
\le\frac{\pi^3}{8}.
\end{aligned}
$$

The initial energy is therefore less than $8$, uniformly in $d$.
This explicit known state can initialize both the probe and a clean
auxiliary. It is a constant cap, not a claim of the exact same numerical
initial energy as the approximate-ground-state switch protocol.

In $x$ shots, consume every $B_j$ first. Swap in the auxiliary's known
initial state and apply a known unitary preparing the full sine state

$$
|s_P\rangle=\sum_{k=-m}^m c_k|p_k\rangle,\qquad
c_k=\sqrt{\frac2{d+1}}\sin\!\left(\frac{(k+m+1)\pi}{d+1}\right).
$$

This preparation happens after the first unknown call. The old unknown
probe state remains in the auxiliary; no irreversible reset is necessary.
Every known pure initial state can be mapped to the displayed known
state by a unitary. That unitary's implementation and energy cost are
part of the assumed control access. The first group's parameters will
be estimated in the other shot family; no observation from that group
is assumed to survive in the new active probe.

Apply every $A_j$ once. With
$\alpha=\pi/(d+1)$ and $\phi=\kappa N\bar x$, the state is

$$
|s_\phi\rangle=\sum_{k=-m}^m c_ke^{-ik\phi}|p_k\rangle.
$$

Use a finite phase POVM with $d+1$ outcomes:

$$
y_\ell=\frac{2\pi\ell}{d+1},\qquad
E_\ell=\frac{|e_{y_\ell}\rangle\langle e_{y_\ell}|}{d+1},
\qquad |e_y\rangle=\sum_{k=-m}^m e^{-iky}|p_k\rangle,
\quad \ell=0,\ldots,d.
$$

Finite Fourier orthogonality gives $\sum_\ell E_\ell=I$ and

$$
\mathbb E e^{iY}=r e^{i\phi},\qquad
r=\sum_{k=-m}^{m-1}c_kc_{k+1}=\cos\alpha.
$$

Indeed, summing the first moment retains only Fourier differences
$1+k-k'=0$. The choice $d+1$ rather than $d$ excludes a spurious
endpoint alias at that step. Positivity and completeness make this a
known finite POVM, implementable by a known isometry and ancillary
readout with a unitary extension.

For the last identity, the vector with components $c_k$ is normalized
and obeys $c_{k-1}+c_{k+1}=2\cos\alpha\,c_k$, with zero boundary
components. Multiplying by $c_k$ and summing proves the stated overlap.
Thus the complex sample mean

$$
Z=\frac1{\nu_xr}\sum_{s=1}^{\nu_x}e^{iY_s}
$$

satisfies $\mathbb EZ=e^{i\phi}$ and
$\mathbb E|Z-e^{i\phi}|^2=\tan^2\alpha/\nu_x$.

Assume $\bar x\in[x_{\min},x_{\max}]$ and choose $d$ such that its
phase image is a known arc $I_x$ of width less than $\pi$:

$$
\kappa N(x_{\max}-x_{\min})<\pi.
$$

Project $Z$ onto its nearest point $e^{i\hat\phi}$ on that arc. Since
$e^{i\phi}$ is an eligible point, the triangle inequality gives
$|e^{i\hat\phi}-e^{i\phi}|\le2|Z-e^{i\phi}|$. Both phases lie on the
same arc shorter than $\pi$, where linear angle error is at most
$\pi/2$ times chord distance. Converting back to $\bar x$ yields the
global bound

$$
\begin{aligned}
\mathbb E(\widehat{\bar x}-\bar x)^2
&\le\frac{\pi^2\tan^2\alpha}{\nu_x\kappa^2N^2}\\
&\le\frac{\pi^3d}{\nu_xN^2(d+1)^2}
\le\frac{\pi^3}{\nu_xdN^2}.
\end{aligned}
$$

Here $\alpha\le\pi/4$, so
$\tan^2\alpha\le2\alpha^2$ follows from $\sin\alpha\le\alpha$ and
$\cos\alpha\ge1/\sqrt2$. There is no approximate-commutation error or
unknown high-gain fringe index in this proof.

The $p$ family consumes all $A_j$ first, prepares the Fourier-dual sine
state, then applies every $B_j$ and uses the dual POVM. The phase sign is
a known convention. Its bound is identical when
$\kappa N(p_{\max}-p_{\min})<\pi$.

For even total shots $\nu$ allocate $\nu_x=\nu_p=\nu/2$. The arc
projections keep estimates in their prior intervals. Put
$X_*=\max\{|x_{\min}|,|x_{\max}|\}$ and define $P_*$ similarly.
Using

$$
\widehat{\bar x}\widehat{\bar p}-\bar x\bar p
=\widehat{\bar p}(\widehat{\bar x}-\bar x)
 +\bar x(\widehat{\bar p}-\bar p)
$$

and $(u+v)^2\le2u^2+2v^2$ proves

$$
\boxed{\quad
\mathbb E(\widehat{\bar x}\widehat{\bar p}-\theta)^2
\le\frac{4\pi^3(X_*^2+P_*^2)}{\nu dN^2}.
\quad}
$$

Choose $d$ as an odd integer of order $CN^2$ with a sufficiently large
constant $C$ to meet both arc conditions. This gives
$O(1/(\nu N^4))$ global MSE with one forward use of every oracle per
shot and constant initial energy. The two shot families have different
classical orders. The result permits bias of the clipped estimates;
the displayed bound is global over the entire fixed prior rectangle.

Every active-register state has

$$
\langle H\rangle\le\|X^2+P^2\|\le2\kappa^2m^2<\pi d.
$$

The old register retained during a swap has the same bound, so a constant
number of such registers keeps total intermediate energy $O(d)=O(N^2)$.
Preparation, the finite POVM, clean auxiliaries, SWAP and their time or
loss costs must be supplied. The proof is
not an efficient hardware implementation of those controls. A pair of
indivisible array ports does not automatically provide the intermediate
preparation port used here.

### What initial-energy converses establish

[Hu et al.](https://arxiv.org/html/2610.01462v1), *Unbounded separation
between definite and indefinite causal order in finite-dimensional
quantum metrology* (2026 preprint), use $H=X^2+P^2$ and a growing finite
dimension. Their S9 initial-energy converse explicitly uses the same
fixed oracle order in every shot, allowing known interleaving controls
after the first oracle. The first unknown nuisance parameter is its
bottleneck. Their finite-sample switched construction includes a
phase-unwrapping scheme and itself reaches intermediate energy
$O(N^2)$.

The two classical shot families above are outside that fixed-order-across-
shots restriction. They can measure a parameter at high later energy in
the family where it was not the first low-energy nuisance. This does not
refute the restricted converse. It prevents using that converse as an
all-ordinary calibration bound when shot order and later preparation can
change. The finite construction also specifies its stronger preparation
and measurement access explicitly.

An equal maximum/intermediate-energy or bounded-control-work comparison
is different. In particular, Appendix D of the
[original displacement theory](https://arxiv.org/html/1912.02449v4)
separately bounds initial energy plus the sum of the known gates' worst-case
energy increases. The squeezers and post-first preparations above are
not free under such a budget. For ideal CV squeezing the unrestricted
worst-case energy increase is unbounded; on the actual probes here its
added energy is $O(N^2)$. A physical spatial-optical budget must state how
that transverse metric relates to aperture, bandwidth and optical power.

### Native evidence and remaining measurement costs

[Yin et al.](https://arxiv.org/abs/2303.17223) implement displacement-area
readout with a photonic quantum switch; the later experiment by
[Guo et al.](https://arxiv.org/abs/2505.03290) includes source/detection
inefficiency and loss in its launch-resource treatment. Such accounting
is substantive: survivor-conditioned information is not information per
launched photon. The available main-paper comparison does not by itself
provide a numerical all-ordinary bound for every transverse preparation
energy, native measurement and reusable-component API.

Native conditional-force access is demonstrated in
[trapped-ion spin-dependent-force experiments](https://arxiv.org/abs/quant-ph/0411068)
and in [multimode cavity conditional-displacement control](https://doi.org/10.1103/PhysRevX.14.011055).
The latter includes displacement-amplitude and geometric-phase calibration.
[Microwave signal processing using an analog quantum reservoir computer](https://www.nature.com/articles/s41467-024-51161-8)
uses an ordinary conditional-displacement loop to map an unknown signal's
area to an ancillary phase. These support the ordinary native-access
comparison; they do not grant those controls to arbitrary traveling
one-pass optical components.

The single-photon optical control is physically credible, but its complete
cost has not been measured by the sources below. Polarization can control
an image transformation of the same photon's transverse mode, so this
need not be a postselected interaction between two photons. The relevant
measurements have different scopes:

| Primary source | Measured or specified quantity | Limit of that evidence |
| --- | --- | --- |
| [Fiorentino and Wong, PRL **93**, 070502 (2004)](https://arxiv.org/abs/quant-ph/0402208) | A polarization Sagnac/Dove-prism spatial-qubit gate; approximately $10\%$ horizontal-polarization PBS loss, deliberately balanced by added glass; coherence visibilities $0.908\pm0.008$ and $0.917\pm0.016$ including an analyzer | No complete insertion transmission or arbitrary continuous-field controlled-parity characterization |
| [Wang et al., arXiv:1706.03937v2](https://arxiv.org/html/1706.03937v2) | One Dove prism's intensity transmissions approximately $0.987$ and $0.945$, with polarization retardance $0.159\pi$ | These are intensity coefficients; the Jones amplitudes use their square roots. Calculated sorting fidelity or rejected-port fractions are not full-echo transmission and visibility |
| [Larson, Tabiryan and Saleh, Optics Express **27**, 5685 (2019)](https://doi.org/10.1364/OE.27.005685) | Full-image common-path controlled inversion using anisotropic lens doublets, with parity-fringe visibility $0.86$ | Output powers are normalized; absolute device throughput is not reported. A typical individual-element efficiency is not the complete inverter efficiency |

An image inverter's coordinate action must match the required conjugation.
In one dimension $\Pi_x:f(x,y)\mapsto f(-x,y)$ reverses both $x$ translation
and its momentum kick. A full two-dimensional inverter gives
$\Pi_x\Pi_y$. For exactly $x$-only modules, it also works in the **paired**
conjugation construction because

$$
(\Pi_x\Pi_y)(A_x\otimes I_y)(\Pi_x\Pi_y)
=A_x^\dagger\otimes I_y.
$$

Thus the paired circuit returns even an arbitrary spectator $y$ mode and
its reference. Identifying a *single* controlled two-dimensional inversion
with controlled $\Pi_x$ instead requires, for example, a known even
spectator. Coupled transverse modes or imperfect helpers require checking
the complete two-dimensional circuit. A dual-rail truth table, OAM-sorting
efficiency or parity-basis phase mask alone does not establish this full
conjugation. [Leary, Baumgardner and Raymer](https://arxiv.org/abs/0810.2447)
explicitly distinguish one-dimensional reflection and two-dimensional parity.

The 2023 displacement experiment reports approximately $0.004$ loss per
position-plus-momentum **pair**, not an isolated parity-gate loss or the
two component losses separately. The 2025 main paper reports visibility
above $0.989$ and worst counted efficiency $0.506$, including detectors,
and charges inferred launched photons rather than only detections. Those
aggregate figures cannot be multiplied into an invented repeated-array
or helper budget. Its separately cited experimental supplement was not
available in the checked arXiv package.

For illustration only, substituting $0.506$ and $0.989$ into the threshold
gives $(3/8)\eta_{\rm sw}v_{\rm sw}^2=0.18559845975$.
This is not a certificate that an echo with a larger product wins:
the quoted worst/lower figures are not upper bounds on every actual
switch data point. The necessary experiment compares both complete
likelihoods at the same $N$, phase setting, source/herald conditioning,
mode range and uncertainty.

No checked source measures both absolute throughput and relevant phase
visibility for the entire $3N$ echo with the actual repeated unknown array.
A reverse traversal does not automatically reproduce a specified inverse:
coordinate reflections, waveplate order, birefringent walkoff and relay
phases must be derived and calibrated. Repeating nominally identical
plates is not repeating the same independently unknown sample. A return
relay must preserve the displaced and tilted mode; an intermediate
single-mode-fiber filter generally resets that spatial state rather than
implementing the loop.

Use the same source and output detectors where compatible, and record
absolute power or photon probability in every retained/rejected port and
the no-click outcome. Measure the complete phase fringe on the shifted
and tilted family, clipping versus waist/aperture, near/far-field angular
excursions, repeated-visit stability and route delay. Component data make
this a concrete experiment; they do not select a finite hardware winner.

An application claim must therefore retain all of the following in one
matched likelihood and resource model:

- Whether unknown components can be revisited with the same response,
  whether signs are controllable, and which intermediate points admit
  squeezing, reset, SWAP or measurement.
- Initial and peak transverse/oscillator energy; source photons, aperture,
  angular bandwidth, control work and helper hardware.
- Both phase quadratures or an identifiable prior; phase unwrapping,
  background-phase calibration, drift and any discarded alignment shots.
- Every launched photon, no-click/erasure outcome, detector efficiency,
  source herald, helper fault, route delay and complete cycle time.

Single-pass optical area calibration remains a plausible finite hardware
comparison when those controls have demonstrably different costs. A
significant advantage requires measured launch-normalized risk or useful
calibration rate against ordinary beam shaping, readout, classical shot
orders and any stable reusable-component loop. None is established by
these analytic baselines alone.

### Verification and attribution scope

The Weyl-loop identities, CV Gaussian statistics and finite-dimensional
global-risk argument above are analytic proofs. Their dependencies are
explicit: the indicated native controls, fixed displacement parameters,
standard quadrature statistics, the exact Fourier-defined finite
operators and the normalized finite phase POVM. The cited $3N$ echo is
established prior work. The optical and native-platform reports support
specific access or measurement facts, not a general optimality theorem.

No new numerical optimum, independent audit of an unavailable experimental
supplement, hardware error budget, Lean formalization or priority claim
is supplied. These results are separate from the
[fresh-frame recovery theorem](theorem.md#nr-r01), the
[known-basis fault checks](architecture-baselines.md#nr-r06) and the
[hard-query noisy-phase comparison](metrology.md#nr-r15).
