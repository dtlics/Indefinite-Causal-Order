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
errors must be priced. A constraint that the data remain **exactly**
$I/D$ removes this contrast: both promised maps are unital. The test
does not apply to arbitrary hidden $U$ without the stated observable
and control access.

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
