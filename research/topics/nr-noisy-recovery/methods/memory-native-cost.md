# Native controls and physical costs of memory qualification

This component of [NR-R20](../memory-qualification.md#nr-r20) examines the
physical premises of
$\mathcal E_1=(1-t)\mathrm{Id}+t\Delta_U$ and
$\mathcal E_0=(1-t)\mathrm{Id}+t\Omega_D$, where $D=2^n\ge2$,
$\Delta_U$ pinches in one fixed rank-one basis and
$\Omega_D(\rho)=I\operatorname{Tr}(\rho)/D$. The diagnostic and capacity
statements belong to the parent result. No screened platform establishes
the complete generic-hidden-basis, independent-fresh-noise, coherent-order
interface. The restrictions below concern particular implementations and
ordinary controls, not a universal exponential implementation cost.

## Pointer-state pilots and a one-helper energy witness

If one pointer state $|u_j\rangle$ can be prepared and its return tested,
$\mathcal E_1$ never fails that test, whereas $\mathcal E_0$ fails
with probability $r=t(1-D^{-1})$. Decide $\mathcal E_0$ upon any
failure. After $N$ independent pilots its false-negative probability is
$(1-r)^N\le e^{-rN}$, and the ideal false-positive probability is zero.
Thus
$$
 N\ge\frac{\log(1/\delta)}{t(1-D^{-1})}
$$
suffices. At fixed confidence this is $O(1/t)$, without a reference
bank. Pointer preparation, its predicate, reset and readout accuracy are
costs. Fixed-basis calibration may be reused when the device permits it;
this does not assert efficient learning of every unknown $U$.

A complicated energy eigenbasis also admits an ordinary test when its
few-body Hamiltonian is known. Write
$$
 H=h_I I+\sum_{j=1}^M h_jP_j,\qquad J=\sum_j|h_j|>0,
$$
combining equal nonidentity Pauli terms. Choose a maximal-magnitude
coefficient $h_P$, so $|h_P|\ge J/M$, and prepare
$\rho_P=(I+P)/D$. This requires only one bit of payload polarization.
Starting from $I/D$, prepare a helper in $|+\rangle$, apply
controlled-$P$, and measure helper $X$. The target operators are
$$
 K_\pm=(I\pm P)/2,\quad
 K_\pm(I/D)K_\pm^\dagger=(I\pm P)/(2D).
$$
Both outcomes have probability one-half. A known Pauli $Q$
anticommuting with $P$ maps the minus conditional state to the plus
state. Consequently the complete preparation channel
$$
 \mathcal R_P(\rho)=K_+\rho K_+^\dagger+
 QK_-\rho K_-^\dagger Q^\dagger
$$
is trace preserving and sends $I/D$ to $\rho_P$. No trials are
discarded. The helper is measured/reset and can be reused; its classical
record, feedforward and entropy removal remain physical resources.

For energy-basis pinching, including degenerate energy-block pinching,
$\Delta_H^\dagger(H)=H$. Therefore
$$
 \operatorname{Tr}[H\mathcal E_1(\rho_P)]=h_I+h_P,
 \qquad
 \operatorname{Tr}[H\mathcal E_0(\rho_P)]=h_I+(1-t)h_P.
$$
To measure energy without diagonalizing $H$, draw term $j$ with
probability $|h_j|/J$, measure $P_j$, and report
$Y=J\operatorname{sgn}(h_j)$ times its sign. Then
$|Y|\le J$ and $\mathbb EY=\operatorname{Tr}[(H-h_I I)\rho]$.
Thresholding the empirical mean midway between the two hypotheses gives,
by the one-sided Hoeffding bound, each error probability at most
$\exp[-Nt^2h_P^2/(8J^2)]$. It suffices that
$$
 N\ge8M^2t^{-2}\log(1/\delta).
$$
Each trial uses one channel call, deterministic parity-sector preparation
and one sampled Pauli measurement. For polynomially many bounded-weight
terms, this is a polynomial ordinary test without protected reference
qubits. Controlled Paulis, local rotations, readout/reset and preparation
errors must be priced. This implementation prepares $\rho_P\ne I/D$.
Requiring $I/D$ on every record-conditioned branch, independent of retained
records, excludes that preparation. Requiring only the unconditional target
marginal $I/D$ does not exclude the correlation test below. The energy test
does not apply to arbitrary hidden $U$ without the stated observable and
control access.

### Unknown coefficients in a known physical operator span

Knowing the Hamiltonian coefficients is unnecessary for a weaker uniform
test. Let $V$ be the known span of $M$ distinct nonidentity physical
Paulis, orthonormal for $\langle A,B\rangle=\operatorname{Tr}(A^\dagger B)/D$.
Suppose the nonzero traceless part $H_0=H-\operatorname{Tr}(H)I/D$ lies
in $V$. Rank-one energy-basis pinching, or spectral-block pinching,
is a Hilbert--Schmidt orthogonal projection fixing $H_0$. Its compression
$$
 C_{PQ}=D^{-1}\operatorname{Tr}[P\Delta_H(Q)],\qquad P,Q\in V,
                                                               \tag{NS1}
$$
is therefore a positive semidefinite contraction. The coefficient vector
of $H_0$ is an eigenvector of $C$ with eigenvalue one, so
$\operatorname{Tr}C\ge1$. Choose a uniform listed $P$, prepare
$\rho_P$ by the complete helper instrument above, query once, and measure
$P$. The resulting sign $Y$ satisfies
$$
 \mathbb E_1Y=1-t+(t/M)\operatorname{Tr}C\ge1-t+t/M,
 \qquad \mathbb E_0Y=1-t.                              \tag{NS2}
$$
Threshold $1-t+t/(2M)$ and Hoeffding again give
$N\ge8M^2t^{-2}\log(1/\delta)$. No Hamiltonian learning,
diagonalization or reference register is used. The span of all weight-at-most
$k$ Paulis has $M=\sum_{j=1}^k3^j\binom nj$, polynomial for fixed $k$.
The nonzero-$H_0$ condition matters for arbitrary rank-one refinements:
a scalar Hamiltonian alone restricts no refined basis. Its actual
spectral-block pinching is instead the identity and is easily tested.

A shallow hidden basis rotation also supplies a known span. Suppose $U$
is a depth-$L$ circuit on a known one-dimensional nearest-neighbor layout,
and $\Delta_U$ pinches in its rotated computational basis. For any site
$i$, $K_i=UZ_iU^\dagger$ is nonzero, traceless and fixed by $\Delta_U$.
Each layer extends support by at most one site on either side, so $K_i$
is supported in a known interval $I_i$ of size
$\ell\leq\min\{n,2L+1\}$. The $M=4^\ell-1$ nonidentity Paulis on
$I_i$ span $K_i$. Thus the same one-helper test (NS2) suffices with
$$
 N\geq8(4^\ell-1)^2t^{-2}\log(1/\delta).
$$
It learns neither $U$ nor its key; controls and readout have Pauli weight
at most $\ell$, with the same preparation/reset costs. For $L=O(\log n)$
the test is polynomial for inverse-polynomial $t$ and error tolerance
$\delta$; polylogarithmic $L$ gives a quasipolynomial bound. This assumes
the **basis rotation itself** is shallow, not merely a shallow Floquet
period whose eigenbasis may require a deep circuit.

There is also a more expensive test beyond positive pinching. Let a
unital CPTP map $\mathcal F$ conserve some traceless unit-Hilbert--Schmidt-norm
$H\in V$, meaning $\mathcal F^\dagger(H)=H$. Its real Pauli compression
$C_{PQ}=D^{-1}\operatorname{Tr}[P\mathcal F(Q)]$ has a left unit
eigenvector $h^{\mathsf T}C=h^{\mathsf T}$, hence
$\|C\|_F\ge\|h^{\mathsf T}C\|_2=1$. For supplied
$r=1-t$, compare $r\operatorname{id}+t\mathcal F$ with
$r\operatorname{id}+t\Omega_D$. Draw uniform listed $P,Q$, prepare
$\rho_Q$, and use two fresh independent repetitions to obtain signs
$Y,Y'$ by measuring $P$. Unitality gives their conditional mean
$r1_{P=Q}+tC_{PQ}$. Thus, with
$U=Y-r1_{P=Q}$ and $U'=Y'-r1_{P=Q}$,
$$
 \mathbb E_1[UU']=t^2\|C\|_F^2/M^2\ge t^2/M^2,
 \qquad \mathbb E_0[UU']=0.                             \tag{NS3}
$$
Since $UU'\in[-4,4]$, threshold $t^2/(2M^2)$ and Hoeffding give
$N\ge128M^4t^{-4}\log(1/\delta)$ paired trials, or $2N$ channel
calls. This needs neither $\mathcal F^\dagger$ access nor knowledge of
the conserved coefficients. Its large polynomial bound does not claim
practical superiority.

Both tests require supplied $t$, or independent calibration precise enough
for their decision margin. A lower bound on unknown $t$ alone does not
fix the replacement mean $1-t$. Each repetition also requires the declared
mixed input: after a polarized probe, restore its marginal by independent
uniform Pauli randomization, or supply a fresh mixed payload. Uniform
randomization uses $n$ single-qubit Paulis and $2n$ random bits; average
all keys rather than postselecting them. Preparation, randomization,
helper reset/feedforward, controlled Paulis, measurement errors and
freshness remain costs. The displayed polarized-probe implementations
require the declared input preparation and known physical span. An
unconditional $I/D$ marginal alone is a weaker restriction than requiring
$I/D$ independently of all retained records, as the next test illustrates.

<a id="nr-r20-controlled-unitary-correlator"></a>

### A two-readout test with an executable controlled unitary

A different side port removes the need for a known small operator span.
Suppose a fixed unitary $F$ satisfies $\Delta_U(F)=F$ and an actual clean
controlled-$F$ operation is supplied. Its matrix, inverse and eigenstates
need not be known. Start each trial with target $I/D$, decoupled from
previous records. Choose $\theta$ uniformly from $\{0,\pi/2\}$. Prepare
a helper in $|+\rangle$, apply controlled-$F$ with the known scalar
phase $e^{-i\theta}$ on its active branch, and read helper $X$, obtaining
$z\in\{\pm1\}$. This implements

$$
 K_z=\frac{I+ze^{-i\theta}F}{2},\qquad
 H_\theta=\frac{e^{-i\theta}F+e^{i\theta}F^\dagger}{2},\qquad
 \rho_z=K_z\frac IDK_z^\dagger=\frac{I+zH_\theta}{2D}.
                                                               \tag{NS4}
$$

Keep $z$ classically, call the production channel once, then reset/reuse
the helper for the same phase-matched controlled-$F$ test, obtaining $z'$.
No trial is discarded. The first signed state is
$\sum_z z\rho_z=H_\theta/D$ and the second signed measurement effect is
$H_\theta$, so $Y=zz'\in\{\pm1\}$ has mean

$$
 \mathbb E[Y\mid\theta]
   =\frac{\operatorname{Tr}[H_\theta\mathcal E(H_\theta)]}{D},
 \qquad
 \mu:=\mathbb EY
   =\frac{\operatorname{Re}\operatorname{Tr}
      [F^\dagger\mathcal E(F)]}{2D}.
                                                               \tag{NS5}
$$

The second identity follows by expanding the two choices of $H_\theta$:
the $F,F$ and $F^\dagger,F^\dagger$ terms cancel. Put
$\tau=\operatorname{Tr}F/D$. Since $F$ is unitary and pinching fixes it,
the two promised means are $\mu_1=1/2$ and
$\mu_0=[1-t+t|\tau|^2]/2$. If supplied bounds
$|\tau|^2\le1-\gamma$ and $t\ge t_0>0$ hold, with $\gamma>0$, their
gap is at least $g=t_0\gamma/2$. Thresholding the average $Y$ at
$1/2-g/2$ gives each hypothesis error at most $e^{-Ng^2/8}$ by
Hoeffding. It suffices that

$$
 N\ge\frac{32}{t_0^2\gamma^2}\log\frac1\delta.
                                                               \tag{NS6}
$$

Unlike (NS2), a lower bound on unknown $t$ suffices here because the
exact-fixed-point mean $\mu_1$ does not depend on $t$. A nearly scalar
$F$ need not have a useful $\gamma$; any trace-margin calibration and
its uncertainty are additional costs.

For approximate preservation, define
$\|A\|_{2,D}^2=\operatorname{Tr}(A^\dagger A)/D$ and
$\epsilon_F^2=\|F-\Delta_U(F)\|_{2,D}^2$. Orthogonal pinching preserves
trace and satisfies
$\langle F,\Delta_U(F)\rangle_{2,D}=\|\Delta_U(F)\|_{2,D}^2$.
Consequently

$$
 \mu_1=\frac{1-t\epsilon_F^2}{2},\qquad
 \mu_1-\mu_0
 =\frac t2(1-|\tau|^2-\epsilon_F^2)
 =\frac t2\|\Delta_U(F)-\tau I\|_{2,D}^2.
                                                               \tag{NS7}
$$

With known $t$, bounds $\epsilon_F^2\le\epsilon^2<\gamma$ give a
known separating midpoint between the bounding means, with gap at
least $t(\gamma-\epsilon^2)/2$. If only $t\ge t_0$ is known across
the two composite promises, use instead

$$
 \mu_1\ge\frac{1-\epsilon^2}{2},\qquad
 \mu_0\le\frac{1-t_0\gamma}{2}.
                                                               \tag{NS8}
$$

These bounds separate when $\epsilon^2<t_0\gamma$, with gap
$(t_0\gamma-\epsilon^2)/2$; their midpoint and the same Hoeffding
argument apply. A positive same-$t$ gap from (NS7) alone does not
provide one uniform threshold when $t$ is unknown and may vary across
the two promises. The squared-distance identity uses orthogonal
pinching and is not asserted for an arbitrary approximately conserving
CPTP map.

Each trial costs one production call, two controlled-$F$ uses, the phase
setting, two helper preparations/readouts and reset, a retained classical
sign, and fresh or restored mixed input. No $F^\dagger$ is called and
no input-bearing quantum reference is kept across the production interval.
Unitality makes the unconditional target marginal exactly $I/D$ before
and after that interval and after the second meter. The conditional state
is correlated with $z$: a port requiring $I/D$ independently of every
retained record excludes the test. For independent trials, restore $I/D$
decoupled from earlier records; an unchanged marginal alone is insufficient.
A complete random-Pauli channel can supply this restoration on known
qubit hardware, averaging/discarding its key with the costs stated above.

A static unknown global phase of controlled-$F$ cancels in the two-phase
average. For these self-adjoint promised channels, a relative phase offset
$\varphi$ between its two uses, common to both choices of $\theta$,
multiplies the ideal fixed-$F$ means by $\cos\varphi$ and can remove the
gap; arbitrary meter drift need not have this scalar form. Meter noise
and phase stability need qualification. Bare unknown
forward-$F$ access does not supply controlled-$F$. A known circuit whose
gates can be controlled, or a demonstrated coherent side port, is additional
access with its own implementation cost. The ordinary Hadamard-test
primitive is established in the
[one-clean-qubit framework](https://arxiv.org/abs/quant-ph/9802037);
[unknown-unitary control requires extra access](https://arxiv.org/abs/1309.7976).
This comparator covers the stated controlled-unitary subcase, without
claiming a new diagnostic mechanism, a generic hidden-basis algorithm or
a native hardware advantage.

## What the measured interfaces supply

[Curtis et al., *Physical Review A* **103**, 023705 (2021)](https://doi.org/10.1103/PhysRevA.103.023705),
[Secs. II–IV and Appendix A](https://arxiv.org/html/2010.04817), resolve
occupations 0–15 using four generalized-parity measurements. Each bit
entangles the cavity and ancilla, followed by readout/reset. Their ideal
commuting binary projectors compose to rank-one Fock projectors. Reset
duration fluctuates and is photon-number dependent; the paper retains
runs rather than imposing a biasing reset cutoff. Its calibrated error
model corrects outcome-distribution bias, not photon loss on a retained
state or diamond distance to ideal pinching. This supplies a concrete
small-dimensional instrument with accessible Fock preparation and bit
records. It also shows why $D$ distinguishable outcomes need not require
$D$ separate ancillas or interrogation steps: sequential binary meters
can carry the record.

For the ideal closed first-$D$ Fock code, the complete instrument is
$\sum_j|j\rangle\langle j|_R\otimes
|j\rangle\langle j|\rho|j\rangle\langle j|$, with $R$ the
accumulated classical bit string. Discarding $R$ gives number pinching;
retaining it provides an ordinary label. A coherent-order proposal must
also retain the readout fields and early/late reset histories when
computing its cross term. Assignment accuracy alone does not certify
that coherent extension. Supplied basis rotations $U^\dagger$ before
the meter and $U$ after it require those actual controls; if they also
prepare $U|j\rangle$, the ordinary pointer pilot applies.

[Kaplan et al., *Physical Review Letters* **125**, 120605 (2020)](https://doi.org/10.1103/PhysRevLett.125.120605),
[main text and supplement](https://arxiv.org/html/2001.02477), measure
persistent temporal fluctuations after a long-range transverse-field
Ising quench in trapped ions. Their many-body dephasing concerns temporal
averages of observables in a closed interacting system. At a programmed
time the full register evolves unitarily. Observable equilibration is
neither an all-input pinching-channel certificate nor an independently
resampled environment. A stochastic clock and coherent-order ports are
additional physical premises.

[Reiserer et al., *Physical Review X* **6**, 021040 (2016)](https://doi.org/10.1103/PhysRevX.6.021040),
[device and reset model](https://arxiv.org/html/1603.01602), demonstrate
nuclear-memory dephasing from stochastic NV-electron reset and protect a
two-nucleus subspace through over 1,000 entanglement attempts. High-field
hyperfine dynamics have structured, nearly longitudinal axes; retaining
transverse terms gives tilted conditional axes, not one generic hidden
pinching basis. Echo, protected subspaces and reset records are ordinary
resources. The resetting electron cannot simultaneously be assumed to be
an independent clean order helper without another qualified control.

[Milul et al., *PRX Quantum* **4**, 030336 (2023)](https://doi.org/10.1103/PRXQuantum.4.030336),
[Fig. 3 and Appendix D](https://arxiv.org/html/2302.06442), report cavity
single-photon $T_1=25.6\pm0.2$ ms and $T_2=34\pm1$ ms. Loss is
the largest coherence contribution, followed by thermal transmon
excitations. Their number-dependent dephasing and cat storage do not
certify a generic hidden basis or independent high-dimensional slots.
[Chapman et al., *PRX Quantum* **4**, 020355 (2023)](https://doi.org/10.1103/PRXQuantum.4.020355)
demonstrate a 1.3-microsecond whole-mode controlled-SWAP on a different
device. Its two storage modes provide a reference-capable mode, while
state preparation and a uniform large-code process error remain costs.
These devices must not be combined into one unmeasured operating point.

## Oscillator encoding and replacement costs

For any rank-$D$ oscillator projector $\Pi$, put
$p_m=\langle m|\Pi|m\rangle$. Then $0\le p_m\le1$ and
$\sum_m p_m=D$. Filling the lowest occupations first minimizes
$\sum_m mp_m$: transferring occupation from any occupied higher level
to an unfilled lower level decreases the objective. Finite truncation
and a monotone limit give
$$
 \operatorname{Tr}(N\Pi/D)\ge D^{-1}\sum_{m=0}^{D-1}m=(D-1)/2.
$$
This includes unknown rotated subspaces. The mixed payload therefore
already costs at least $(2^n-1)/2$ mean photons in this encoding.
A maximally entangled two-mode reference has uniform rank-$D$
marginals and at least $D-1$ total mean photons. Its additional hardware
is one mode, not $n$ fabricated oscillators, but entanglement preparation,
energy, storage and decoding are real. Controlled-SWAP access alone does
not prepare that state. These bounds do not apply to many-spin or
one-photon multimode encodings.

Natural number dephasing has the known Fock pointer basis; vacuum gives
the pilot above. On the first-$D$ uniform Fock state, dephasing preserves
$\langle N\rangle=(D-1)/2$, pure loss of transmissivity $\eta$
changes it to $\eta(D-1)/2$, and thermal replacement gives its bath
mean. Thus actual loss/reset can expose ordinary energy information on
mixed data that the unital $\Omega_D$ promise suppresses.

A passive oscillator Gibbs state has populations $(1-r)r^m$,
$0\le r<1$. Conditioning onto the first $D>1$ levels makes these
proportional to $r^m$, uniform only as $r\to1$; the unconditioned
limit is not normalizable and acceptance $1-r^D$ tends to zero.
Finite-code uniform replacement needs an engineered completion.
[Leviant et al., *Quantum* **6**, 821 (2022), Eqs. (4)–(6)](https://arxiv.org/html/2205.00341)
instead model physically relevant loss and number-phase diffusion, whose
coherences acquire $e^{-\gamma_\phi(m-n)^2/2}$. That finite-strength
law is not the same as uniform partial pinching.

## Single-clock resolution bounds

Set $\hbar=1$. Suppose the sole randomization is waiting time $\tau$
under a fixed nondegenerate $H$, with ordered energies spanning width
$W$. Its channel multiplies $|E_j\rangle\langle E_k|$ by
$\chi(E_j-E_k)=\mathbb E e^{-i(E_j-E_k)\tau}$. Full pinching accuracy
requires $|\chi(E_j-E_k)|\le\epsilon<1$ for every pair. Indeed,
the equal superposition of a pair has output difference from pinching
with trace norm $|\chi|$. Diamond error at most $\epsilon$, with no
extra one-half convention, therefore implies this condition. For the
event mixture with weight $t$ and diamond error $\zeta$, use
$\epsilon=\zeta/t<1$.

Some neighboring gap obeys $d\le W/(D-1)$. If $\tau$ has support
in an interval of width $T$ and $dT<\pi$, center the interval.
All phases lie on an arc with real part at least $\cos(dT/2)$, so
$|\chi(d)|\ge\cos(dT/2)$. Hence $dT\ge2\arccos\epsilon$.
When $dT\ge\pi$ that conclusion is automatic. Therefore
$$
 \boxed{WT\ge2(D-1)\arccos\epsilon.}
$$
For finite variance $\sigma_\tau^2$, center at the mean instead.
The inequality $\cos x\ge1-x^2/2$ gives
$|\chi(d)|\ge1-d^2\sigma_\tau^2/2$. Consequently
$$
 \boxed{W\sigma_\tau\ge(D-1)\sqrt{2(1-\epsilon)}.}
$$
These are necessary, not sufficient: other gaps may have revivals.
For a bounded-strength local Hamiltonian of polynomial spectral width,
rank-one resolution of $D=2^n$ levels by this **single clock** forces
large timing spread or bandwidth. Degeneracy produces block pinching;
independent commuting bath coordinates, parallel binary meters, or an
expanded spectral range change the premises. This is not a universal
time–energy prohibition. Commuting random evolutions already give zero
switch-minus probability without approaching full pinching; that flag
alone cannot certify a capacity.

## Joint-process qualification

One-use tomography cannot certify freshness. Draw one Hermitian tensor
Pauli per trial with
$p_a=(1-t)\delta_{a0}+t/D^2$, then reuse it in both windows. Each
window marginal is $\mathcal E_0$, but both histories apply
$P_aP_a=I$, giving only the plus flag. This correlated process does
not satisfy the parent's independent-slot promise, even when the label
is inaccessible.

A native claim therefore needs the same closed code, a justified fixed
basis and replacement mechanism, independent noise events, and the full
coherent routing extension. Bath-reset time, helper storage, discarded
ports, intermediate meter records, leakage and every failed attempt
belong in that model. Known encoders or pointer predicates also belong
to the ordinary comparator. No screened source supplies this entire
interface; neither the generic hidden-basis ordinary frontier nor a
native architecture advantage is settled by these structured-platform
obstructions.

## Matched terminal noise and noise inside each channel slot

A target-only channel applied after a diagnostic has formed its retained
helper record cannot change that record. For every joint state $\sigma_{CTM}$
and trace-preserving $\mathcal N_T$,
$$
 \operatorname{Tr}_T[(\operatorname{id}_{CM}\otimes\mathcal N_T)
                  (\sigma_{CTM})]=\operatorname{Tr}_T\sigma_{CTM}.
 \tag{NC1}
$$
The identity follows from $\mathcal N_T^\dagger(I)=I$. It applies equally
to ordinary helper compression completed before that layer. If the noise
has a recorded instrument outcome, summing all outcomes proves (NC1);
conditioning on a favorable outcome instead requires the conditional law.
This is a statement about diagnostic records, not protection of the stored
quantum payload. Moving an unavoidable ingress layer past a controller is
not justified by (NC1). The
[public-Clifford calibration method](pauli-clifford-calibration.md)
gives an ordinary mixed-payload helper example and prices its controls.

Now place independent local depolarizing noise **inside each opaque slot**.
Use the Bloch-shrinkage convention
$\mathcal N_\nu(X)=\nu X+(1-\nu)\operatorname{Tr}(X)I/2$,
$0\le\nu\le1$, whose one-qubit Pauli-label law is
$u_\nu=\nu\delta_0+(1-\nu)\operatorname{Unif}(\mathbb F_2^2)$.
For arbitrary spatially correlated Pauli laws $p,q$, switch the composite
channels $\mathcal N_\nu^{\otimes n}\circ\mathcal E_p$ and
$\mathcal N_\nu^{\otimes n}\circ\mathcal E_q$ using their standard
independent-environment extension. This is a specified channel model;
equal reduced channels alone do not certify a physical routed extension.

Write $\chi(a,b)=(-1)^{[a,b]}$. Conditional on the original one-site
labels $a,b$, independent local noise labels give
$$
\begin{aligned}
 m_\nu(a,b)
 &=\mathbb E_{u,v}\chi(a+u,b+v)\\
 &=\nu^2\chi(a,b)+\nu(1-\nu)
       (1_{a=0}+1_{b=0})+(1-\nu)^2/4.
\end{aligned}                                                    \tag{NC2}
$$
To prove the expansion, the two single-uniform terms vanish unless the
opposite fixed label is zero, by character orthogonality. The
double-uniform term is $1/4$. The four possible values are
$$
\begin{array}{c|c}
a=b=0&r_\nu=1-3(1-\nu)^2/4\\
\text{exactly one zero}&s_\nu=(1+\nu)^2/4\\
a=b\ne0&d_\nu=\nu^2+(1-\nu)^2/4\\
a,b\ne0,\ a\ne b&e_\nu=-\nu^2+(1-\nu)^2/4.
\end{array}                                                       \tag{NC3}
$$
Here $r_\nu-s_\nu=\nu(1-\nu)$,
$r_\nu-d_\nu=2\nu(1-\nu)$ and $|e_\nu|\le d_\nu$.
Thus $\max_{a,b}|m_\nu(a,b)|=r_\nu$. Conditioning on the entire
original label pair, the independent noise coordinates factor; averaging
over $p_aq_b$ then gives
$$
 \left|\eta(\mathcal N_\nu^{\otimes n}\circ\mathcal E_p,
             \mathcal N_\nu^{\otimes n}\circ\mathcal E_q)\right|
 =\left|\sum_{a,b}p_aq_b\prod_i m_\nu(a_i,b_i)\right|
 \le r_\nu^n=:R.                                      \tag{NC4}
$$
No independence of sites within $p$ or $q$ was used. Fixed $\nu<1$
therefore suppresses this scalar exponentially. This is not one unknown
visibility multiplying the original statistic: noiseless identity and
noiseless fixed-$X$ channels each have self-statistic one, but their
one-site noisy self-statistics are respectively $r_\nu$ and $d_\nu$.
A single calibration divisor cannot correct both.

The same local noise also limits this particular capacity certificate.
Its largest noise atom is identity, of mass
$a_\nu^n=[(1+3\nu)/4]^n$. For every original law $p$, convolution gives
$p'_0=\sum_a p_a u_\nu^{\otimes n}(a)\le a_\nu^n$.
Combining this with (NC4), the leading coefficient of the
[entropy certificate](pauli-entropy-capacity.md) obeys
$$
 p'_0-\sqrt{1-\eta'}
 \le a_\nu^n-\sqrt{1-r_\nu^n},                         \tag{NC4a}
$$
which is negative for all sufficiently large $n$ at fixed $\nu<1$.
That witness then returns zero. This does not bound actual capacity:
for an identity original channel the noisy memory is
$\mathcal N_\nu^{\otimes n}$, with hashing lower bound
$n[1-H_4(a_\nu,(1-\nu)/4,(1-\nu)/4,(1-\nu)/4)]$,
positive for sufficiently small fixed $1-\nu$. The certificate can
therefore fail even for a useful memory; finite sizes and noise shrinking
with size remain distinct questions.

## A converse for the retained-helper-only port

The following port restriction is essential: after every launch the target
is traced **before any controller interaction with, measurement of, or
compression of its output**. Arbitrary helper–target–memory input
entanglement and arbitrary coherent processing of retained helpers and
memory are allowed. The slots, local-noise convention and switched
program remain fixed; within-slot interventions and other block programs
are outside this claim.

For any Pauli pair the switch Kraus operator, up to an irrelevant scalar
phase, factors as
$$
 W_{ab}=\sqrt{p_aq_b}\,
       \operatorname{diag}(1,\chi(a,b))_C\otimes(P_bP_a)_T.
                                                               \tag{NC5}
$$
Partial trace is invariant under the target unitary even on an entangled
$C,T,M$ input. The retained port is therefore exactly
$$
 (\mathcal D_\eta\otimes\operatorname{id}_M)
       (\operatorname{Tr}_T\rho_{CTM}),\qquad
 \mathcal D_\eta(\rho)=\frac{1+\eta}{2}\rho+
                       \frac{1-\eta}{2}Z\rho Z.          \tag{NC6}
$$
This applies to the composite noisy Pauli laws in (NC4). With fresh
independent launches, granting their classical $Z$-flip labels simulates
every adaptive coherent retained-helper strategy: apply each known flip
and then its prescribed hypothesis-independent controller. Thus its
final output is a channel applied to independent Bernoulli labels with
law $\pi_\eta=((1+\eta)/2,(1-\eta)/2)$.

For two hypotheses $|\eta_0|,|\eta_1|\le R\le1/2$, relative entropy
data processing and the classical chi-square bound imply
$$
\begin{aligned}
 D(\rho_0^{(L)}\Vert\rho_1^{(L)})
 &\le L D(\pi_{\eta_0}\Vert\pi_{\eta_1})\\
 &\le L\frac{(\eta_0-\eta_1)^2}{1-\eta_1^2}
 \le\frac{16}{3}LR^2.
\end{aligned}                                                    \tag{NC7}
$$
Entropies here use natural logarithms. Here $L$ is a hard maximum on
launches; a shorter adaptive strategy can ignore unused labels. An equal-prior decision with error
at most $\delta<1/2$ needs trace distance at least $1-2\delta$.
Quantum Pinsker therefore yields
$$
 L\ge\frac{3(1-2\delta)^2}{8R^2}
   =\Omega(r_\nu^{-2n}).                              \tag{NC8}
$$
The result includes coherent helper inputs, retained quantum memory and
adaptive processing; it is not limited to measuring each helper in $X$.
It does not bound access to the full target output. In particular,
allowing an output target–memory gate before discarding the target changes
the port and can invalidate (NC6).

The exponential conclusion also holds under a finite expected launch
budget with classically recorded stopping. Let $N$ be the almost surely
finite launch count, let $c=\max_h\mathbb E_h N$, and fix
$g=1-2\delta>0$. For $c>0$, truncate before launch $L+1$ with
$L=\lceil4c/g\rceil$. Under either hypothesis Markov's inequality gives
$\Pr_h(N>L)\le c/L\le g/4$. The truncated instrument agrees on every
shorter branch; replacing the cap branch by any fixed terminal decision
increases the equal-prior error by at most $g/4$, even with retained
quantum memory. Its decision gap is consequently at least $g/2$.
Apply (NC8) to this hard-budget strategy and use $L\le4c/g+1$ to obtain
$$
 c\ge\frac{3g^3}{128R^2}-\frac g4
   =\Omega(r_\nu^{-2n}) .                              \tag{NC9}
$$
The asymptotic statement holds for fixed $\delta<1/2$ and $R\le1/2$.
If $c=0$, no launch occurs almost surely under either hypothesis, so
hypothesis-independent initial resources cannot yield error below
$1/2$. This proof includes adaptive classical stopping and coherent
processing between launches; it makes no claim about a coherent
superposition of query counts or a different target-output port.

[Cotler, Gong and Kannan, *Nature Communications* **17**, 6979 (2026)](https://doi.org/10.1038/s41467-026-73693-x),
[arXiv:2512.10929v2, Theorem 2.4/E2 and F13](https://arxiv.org/html/2512.10929),
give related noisy-learning obstructions for state copies corrupted before
learner interaction. Their pair-copy purity theorem permits arbitrary
noiseless pair measurements after that ingress cut; their persistent-memory
Pauli-state bound has a different model. The formal v2 F13 exponent is
$\Omega(2^{(n-k)/3}(1-\lambda)^{-n/3})$; the stronger informal 2.6 wording
must not be substituted for it. These state-access bounds do not themselves
prove (NC4)–(NC9), which concern a specified channel/control port. Conversely,
terminal target noise after a helper record has formed cannot be placed
only before the ordinary receiver's processing in a matched comparison.

The [exact standard-library replay](../checks/architecture/verify_pauli_slot_noise.py)
checks all 16 local label polynomials, their all-parameter envelope
certificates, complete finite control–target–memory matrix units and the
KL constant. Tensor factorization, the arbitrary-memory simulation and
information-theoretic converse are the analytic proofs above; finite
checks do not establish a native hardware implementation or a full-output
lower bound.
