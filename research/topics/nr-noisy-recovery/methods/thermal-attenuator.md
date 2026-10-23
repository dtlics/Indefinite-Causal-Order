# Conditional target outputs under partial thermal attenuation

This proof component of [NR-R04](../obstructions.md#nr-r04) concerns two
independent thermal attenuators on an infinite-dimensional oscillator. It
extends the exact-output obstruction beyond the parent's additive-displacement
case. It does not bound approximate recovery, quantum capacity or a physical
implementation's throughput. The separate vacuum-input calculation gives a
fully specified retained-state preparation comparison, rather than a claim
about arbitrary unknown inputs.

## Full retained output has no exact heralded recovery branch

Let $\mathcal H=\ell^2(\mathbb N_0)$, $N=a^\dagger a$. Slot $i$ is a
thermal attenuator $\mathcal E_i$ with $0<\eta_i<1$ and finite bath occupation
$\bar n_i>0$. Its passive dilation mixes the signal with an independent
thermal mode at a beam splitter; keep a purification of that mode when
specifying the physical experiment. The usual Gaussian-channel definition
and attenuator Kraus representation are given in
[Ivan, Sabapathy and Simon, PRA **84**, 042311 (2011)](https://doi.org/10.1103/PhysRevA.84.042311).
In the convention $D(z)=\exp(za^\dagger-z^*a)$, its characteristic-function
action is

$$
\mathcal E_i^\dagger(D(z))=
 e^{-(1-\eta_i)(\bar n_i+1/2)|z|^2}D(\sqrt{\eta_i}z).
\tag{TA1}
$$

Here is the required decomposition, including its normalization. Define
$v_i=(1-\eta_i)\bar n_i>0$ and
$\mathcal N_v(X)=\int p_v(\alpha)D(\alpha)XD(\alpha)^\dagger d^2\alpha$,
where $p_v(\alpha)=e^{-|\alpha|^2/v}/(\pi v)$. Since
$\mathcal N_v^\dagger(D(z))=e^{-v|z|^2}D(z)$, (TA1) gives
$\mathcal E_i=\mathcal N_{v_i}\circ\mathcal L_{\eta_i}$ on every trace-class
input. The pure-loss operators are

$$
A_l(\eta)=\sqrt{(1-\eta)^l/l!}\,\eta^{N/2}a^l.
\tag{TA2}
$$

Consequently a Kraus family of each slot includes the $l=0$ subfamily
$\sqrt{p_{v_i}(\alpha)}D(\alpha)T_i$, $T_i=\eta_i^{N/2}$. The Gaussian
density is strictly positive everywhere and $T_i$ is bounded and injective.
The following proof uses these properties, not knowledge of either actual
thermal displacement.

Prepare an independent helper in $|+\rangle_C$ and an arbitrary normal
state $\rho_{SR}$. The reference $R$ is inaccessible. The standard switch
has branch operators

$$
K_{ij}=\frac1{\sqrt2}\bigl(|0\rangle_C B_jA_i+
 |1\rangle_C A_iB_j\bigr),\qquad
\Omega_{CSR}=\sum_{ij}(K_{ij}\otimes I_R)\rho_{SR}
 (K_{ij}^\dagger\otimes I_R).
\tag{TA3}
$$

The sum includes the continuous Kraus indices. Both the helper and oscillator
are retained; no helper outcome is discarded. Baths are inaccessible and
traced. A real implementation must establish this coherent extension with
fresh independent slots. Extra direction, timing or accessible bath records
are additional physical ports, not implicit parts of (TA3).

**Claim.** $\Omega$ is faithful on
$\mathbb C^2_C\otimes\mathcal H_S\otimes\operatorname{supp}\rho_R$:
every nonzero vector in this support has strictly positive expectation.

First take a pure input
$|\psi\rangle=\sum_{p\ge0}|p\rangle|\psi_p\rangle_R$ and a putative null
vector $|\xi\rangle=|0\rangle|u\rangle+|1\rangle|w\rangle$.
Positivity of every contribution to (TA3), restricted to the two $l=0$
families, implies

$$
\langle u|(BA\otimes I_R)|\psi\rangle+
\langle w|(AB\otimes I_R)|\psi\rangle=0
\tag{TA4}
$$

for almost every $A=D(\alpha)T_1$, $B=D(\beta)T_2$. Strong continuity
of displacements makes the scalar expression continuous; the positive
densities therefore extend (TA4) to every $\alpha,\beta$.

The passage from those families to arbitrary matrix units needs a bounded
approximation argument. The finite linear span of the Weyl displacements
is a unital $*$-algebra: their products are scalar multiples of other
displacements. Its oscillator representation is irreducible, so its strong
closure is $\mathcal B(\mathcal H)$. Kaplansky density, followed by norm
approximation in the generated $C^*$-algebra, gives uniformly bounded finite
Weyl sums $X_r\to X$ strongly for every bounded $X$. For the desired
matrix unit $|k\rangle\langle p|$, choose the bounded rank-one operator
$X=\eta_i^{-p/2}|k\rangle\langle p|$. Then

$$
X_rT_i\longrightarrow XT_i=|k\rangle\langle p|
\quad\text{strongly, with }\sup_r\|X_rT_i\|<\infty.
\tag{TA5}
$$

The bound may depend on the fixed index $p$; no uniform inverse of $T_i$
is claimed. Equation (TA4) is separately complex linear in $A,B$, hence
holds for their finite sums. Uniformly bounded strong convergence extends
through tensoring with $I_R$, and through products: prove it first on finite
sums of tensor products and approximate a general vector in norm. Taking
the two limits successively therefore proves (TA4) for every pair of
matrix units. No inverse attenuator is physically implemented here.

Put $A=|k\rangle\langle p|$, $B=|q\rangle\langle k|$. For $p\ne q$,
$BA=|q\rangle\langle p|$ and $AB=0$, so
$\langle u|q,\psi_p\rangle=0$. Reversing $A,B$ gives
$\langle w|q,\psi_p\rangle=0$ for the same indices. For $p=q$, (TA4)
instead says

$$
a_p+b_k=0\quad\text{for all }p,k,\qquad
a_p=\langle u|p,\psi_p\rangle,\quad
b_k=\langle w|k,\psi_k\rangle.
\tag{TA6}
$$

Thus all $a_p$ equal one constant and all $b_k$ its negative.
Normalizability gives $\sum_k\|\psi_k\|^2=1$, so $\|\psi_k\|\to0$ and
$|b_k|\le\|w\|\|\psi_k\|\to0$. The constant is zero. All diagonal and
off-diagonal contractions vanish, forcing $u,w$ to be orthogonal to
$\mathcal H\otimes\overline{\operatorname{span}}\{\psi_p\}$.

For a mixed trace-class input, use its countable positive spectral
decomposition. A null expectation annihilates the switched output of each
positive-weight pure component separately. The closed span of all of their
reference vectors $\psi_{r,p}$ is precisely $\operatorname{supp}\rho_R$,
since $\rho_R=\sum_{r,p}\lambda_r|\psi_{r,p}\rangle\langle\psi_{r,p}|$.
This proves the claim.

The infinite oscillator and normalizable input are essential. In a genuinely
$D$-dimensional target with a maximally entangled input $\Phi_D$, the vector
$|-\rangle_C\otimes|\Phi_D\rangle_{SR}$ is a universal kernel vector:
its contraction with every switched branch is proportional to
$\operatorname{Tr}(BA-AB)=0$. In the oscillator proof a finite code still
has unused target directions: choosing $k$ outside its support already sets
the constant in (TA6) to zero. A finite Fock truncation that deletes those
directions must not be mistaken for a proof or counterexample to
infinite-dimensional faithfulness.

Now encode a $d$-dimensional unknown input entirely into the oscillator,
$d\ge2$, with Bell reference $R$, and allow an arbitrary physical normal CP
trace-nonincreasing receiver on $C,S$. Include independent receiver ancillas,
all accepted records, feedforward, decoding and discarded receiver garbage
in that map. If its output were a nonzero pure Bell state, refine the map
into bounded Kraus operators $L_j$. For every vector $x$ orthogonal to that
Bell state, positivity and faithfulness imply
$(I_R\otimes L_j^\dagger)x=0$. Hence the range of $I_R\otimes L_j$ would
lie in a single entangled line. A nonzero $L_j$ has nonzero product vectors
$|r\rangle\otimes L_j|s\rangle$ in that range, a contradiction.
Thus no such exact heralded recovery or delivered pure Bell branch exists.
Similarly, two normalizable signal inputs have faithful outputs on the same
$C,S$ space, excluding nonzero unambiguous discrimination effects.

This conclusion permits arbitrary **post-switch** receivers. An input-bearing
control/bypass memory, inter-slot interventions, measured bath records or
additional channel queries change its premises. Zero thermal occupation,
an identity slot and finite-dimensional channel models are excluded. The
proof gives no strictly positive finite-error fidelity gap, success-rate
bound, energy-constrained optimum or capacity upper bound.

## A complete partial-loss source instrument and ordinary preparation

There is also an explicit target-output test that does not concern unknown
data. Let the two attenuators be identical, $x=\sqrt\eta\in[0,1)$, with
bath occupation $\bar n>0$ and vacuum signal input. Set

$$
b=(1-x^2)\bar n,\quad m=(1+x^2)b,\quad
d=(1+b)^2-2bx,\quad
\tau_m=\sum_{k\ge0}\frac{m^k}{(1+m)^{k+1}}|k\rangle\langle k|.
\tag{TA7}
$$

The ordinary serial output is $\tau_m$. To derive the complete switch
cross-block, write each thermal input as a Gaussian coherent-state mixture
$u,v\sim\mathrm{CN}(0,\bar n)$ and $s=\sqrt{1-x^2}$. For the two orders,
the output signal amplitudes and two bath amplitudes are

$$
\alpha_0=s(xu+v),\ e_0=(xu,-s^2u+xv),\qquad
\alpha_1=s(u+xv),\ e_1=(xu-s^2v,xv).
\tag{TA8}
$$

This is the complete three-mode passive dilation; tracing the two bath
outputs contributes $\langle e_1|e_0\rangle$, not one. If $J_0$ is the
target cross-block, coherent-state overlaps give

$$
\begin{aligned}
\operatorname{Tr}(z^N J_0)
&=\mathbb E\exp[-|u|^2-|v|^2+e_1^\dagger e_0+
 z\alpha_1^*\alpha_0]\\
&=\det\!\left[I+b\begin{pmatrix}1-xz&-z\\2x-zx^2&1-xz\end{pmatrix}\right]^{-1}
=\frac1{(1+b)^2-2bxz}.
\end{aligned}\tag{TA9}
$$

For $0\le z\le1$ the Hermitian part of the Gaussian quadratic form is
positive semidefinite, so the normalized Gaussian integral converges.
Phase covariance makes $J_0$ diagonal; expanding the last expression yields

$$
J_0=\sum_{k\ge0}j_k|k\rangle\langle k|,\quad
j_k=\frac{(2bx)^k}{(1+b)^{2k+2}},\qquad
\Omega=\frac{I_C\otimes\tau_m+X_C\otimes J_0}{2}.
\tag{TA10}
$$

The two unnormalized target outcomes are
$\sigma_\pm=(\tau_m\pm J_0)/2$, with probabilities
$p_\pm=(1\pm d^{-1})/2$. These are exact infinite sums. In the no-noise
limit $b=0$, only plus occurs and the target remains vacuum.

Here is a source-specific ordinary realization retaining the same helper
state as well as both flag outcomes. Write $t_k=m^k/(1+m)^{k+1}$. The
inequalities $0\le j_k\le t_k$ follow from

$$
\begin{aligned}
(1+b)^2-(1+m)&=b(1-x^2+b)\ge0,\\
(1+x^2)(1+b)^2-2x(1+m)
&=(1-x)^2+2b(1+x^2)(1-x)+b^2(1+x^2)\ge0.
\end{aligned}\tag{TA11}
$$

The first bounds the $k=0$ ratio and the second bounds its successive
geometric ratio. After the same two serial contacts, use the same clean
helper to implement number-conditioned flag probabilities
$a_\pm(k)=(1\pm j_k/t_k)/2$. Dephase that helper in its $X$ basis using an
independent fair choice of $I_C$ or $X_C$. This removes coherences between
the two flag states and gives exactly (TA10), not just its measured
populations. The known probabilities require calibrated parameters and
number-conditioned rotations. Restricting those controls to $k\le K$,
with any admitted default above the cutoff, changes the complete retained
state by at most $[m/(1+m)]^{K+1}$ in half trace norm. The bound is the
initial thermal tail, not an operator-norm approximation on arbitrary inputs.

A useful preparation endpoint is a retained single photon. Neither switch
flag has joint single-photon probability greater than
$t_1=m/(1+m)^2$. An ordinary QND number-one predicate attains precisely
that probability and produces exact $|1\rangle$, without knowing $m$.
For a finite-resolution alternative, a number-modulo-$L$ instrument,
$L=2^k$ with integer $k\ge1$, accepts $n\equiv1\pmod L$ and gives

$$
p_{O}=\frac{t_1}{1-r^L},\quad q_{O}=t_1,\quad
F_{O}=1-r^L,\qquad r=\frac m{1+m}.
\tag{TA12}
$$

All modulo outcomes are kept in the instrument. Phase estimation of
$e^{2\pi iN/L}$ uses one helper reused for $k$ number-phase measurements,
with their readouts/resets and feedforward; it supplies no free ancilla bank.
For $L=2$ this is ordinary parity. These comparisons price those extra
controls rather than calling them free thermal contacts. They do not
establish an optimal ordinary finite-error memory receiver.

## Native source and port test

[Xi et al., PRL **133**, 040401 (2024)](https://arxiv.org/html/2406.01951)
implement a four-$^{13}$C-spin NMR experiment with a target, helper and two
finite bath spins. Their calibrated contact is
$U_j=\cos\theta I+i\sin\theta\operatorname{SWAP}_{S,E_j}$, controlled with
universal radio-frequency operations. For identical contacts let
$B=\operatorname{SWAP}_{E_1,E_2}$ and $Q=P_0\otimes I+P_1\otimes B$.
Direct multiplication gives

$$
Q\,U_2U_1\,Q=P_0\otimes U_2U_1+P_1\otimes U_1U_2.
\tag{TA13}
$$

This ordinary chronological circuit reproduces the **whole joint unitary**,
including arbitrary target/reference/bath correlations and every later
record, using the same two contacts and two controlled bath swaps. It
requires bath retention and access. One cannot delete the first $Q$ merely
because two identical mixed bath marginals commute with their swap: the
control off-diagonal also contains that swap. The identity applies equally
to identical beam-splitter contacts on two retained bosonic bath modes;
inaccessible dissipative continua do not grant those controlled swaps.

[Yam et al., npj Quantum Information **11**, 87 (2025)](https://arxiv.org/html/2308.12398)
demonstrate a 6.6-meter inter-fridge microwave link, distribute squeezed-state
entanglement and vary its center temperature up to 1 K. The measured cable
attenuation is about 1.01 dB/km at 5.65 GHz; each temperature setting is
stabilized for approximately one hour. Their model keeps local component
losses as beam splitters coupled to measured thermal baths. They attribute
robust transmission to weak coupling of superconducting cables to the hot
environment. These are actual thermal ports, not a demonstration of two
independent channel slots in coherent order. Cable loss alone is not the
complete apparatus's transmissivity or thermal-mode profile.

[Yam et al., PRL **136**, 180801 (2026)](https://doi.org/10.1103/n8j9-63mz)
subsequently demonstrate coherent-state teleportation across that network,
reporting fidelities $72.3\pm0.5\%$ at 1 K and $59.9\pm2.5\%$ at 4 K.
Their source, analog feedforward and displacements are ordinary explicit
Gaussian resources. The main identified fidelity bottleneck is parasitic
heating of the cold nodes by the channel heater. A proposed switch must
compare against that entanglement-assisted instrument and its source/control
costs, rather than unassisted thermal propagation alone; the coherent-state
fidelities do not certify arbitrary-state teleportation performance.

The needed ordinary number access is concrete:
[Sun et al., Nature **511**, 444–448 (2014)](https://arxiv.org/abs/1311.2534)
demonstrate repeated QND parity, and
[Curtis et al., PRA **103**, 023705 (2021)](https://arxiv.org/abs/2010.04817)
resolve occupations 0–15 with four generalized-parity bits, including
ancilla readout and reset. These demonstrate controls, not the ideal
thermal-source protocol above; measured assignment-error mitigation is not
an exact state-recovery certificate. Their real duration, number dependence,
readout/reset faults, storage loss and rejected runs must be included.
Available active preparation, cooling and reuse are additional comparators.

For the vacuum-input model, if $\delta=1-\eta\to0$ with fixed $\bar n$,
(TA7) gives
$p_-=\delta^2\bar n(\bar n+1)/2+O(\delta^3)$. Moreover
$\tfrac12\|\sigma_+/p_+-\tau_m\|_1\le p_-$, since
$\tau_m=p_+\rho_++p_-\rho_-$. Thus a nearly lossless warm cable does not
automatically give a sizeable order-conditioned source change. This is a
model consequence, not a fit to the measured link's nonuniform baths.

The surviving physical test is an approximate **unknown-state/reference**
task with a specified code, energy and all-attempt acceptance/rate metric.
It needs the full temporal Gaussian ports, independent bath freshness,
loss and timing records, and a helper that survives vacuum. A router
acting on an empty thermal port can receive bath photons, so a vacuum
dummy is not automatically an identity branch. Neither the abstract
faithfulness theorem nor the two reduced channel marginals establishes
that interface. The source-specific ordinary filter and accessible-bath
compiler above close their stated endpoints; a matched approximate
thermal-memory advantage remains open.

The [exact checker](../checks/architecture/verify_thermal_attenuator.py)
replays the Gaussian determinant and ratio polynomials, full finite
source/flag identities, and matrix-unit boundary guards including the
finite-dimensional kernel. Faithfulness, bounded strong density, Gaussian
integration, infinite tails and the physical source premises are analytic
or measured inputs, not conclusions of a Fock-cutoff numerical replay.
