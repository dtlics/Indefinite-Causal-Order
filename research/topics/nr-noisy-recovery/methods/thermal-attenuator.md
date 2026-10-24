# Conditional target outputs under partial thermal attenuation

This proof component of [NR-R04](../obstructions.md#nr-r04) concerns two
independent thermal attenuators on an infinite-dimensional oscillator. It
extends the exact-output obstruction beyond the parent's additive-displacement
case and bounds a weak-loss all-attempt payoff at fixed mean input energy.
It does not optimize approximate recovery, quantum capacity or a physical
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
traced. A real implementation must establish this module-paired coherent
extension with independent module baths. The same module-labelled bath
and its purification are paired between the two histories; fresh clock
windows need a separate extension, derived below. Extra direction, timing
or accessible bath records are additional physical ports, not implicit
parts of (TA3).

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

## Exact unknown-input visibility and the weak-loss payoff budget

<a id="nr-r04-thermal-visibility"></a>

Keep the same standard switch and independent identical thermal slots,
with $x=\sqrt\eta$, finite $n=\bar n\ge0$ and arbitrary normal input
$\rho_{SR}$. The reference stays inaccessible. Define

$$
c=(1-x)^3(1+x),\qquad
d=1+2n(1-x)(1-x^2)+n^2(1-x^2)^2,\qquad
q=1-\frac{(2n+1)c}{d}.
\tag{TA14}
$$

Then $0\le q\le1$, $d\ge1$, and the exact minus probability is

$$
p_-(\rho)=\frac12\left[1-\frac{\operatorname{Tr}(q^N\rho_S)}d\right].
\tag{TA15}
$$

Here $q^0=1$, including at $q=0$. No photon-number cutoff, input
incoherence or second-moment assumption is used. Vacuum recovers (TA7)–(TA10).
The formula also includes a vacuum bath and the endpoints $\eta=0,1$;
these additional boundary cases do not extend the earlier faithfulness claim.

Here is a full-dilation proof. On the signal and two bath one-particle
modes the contacts are

$$
R_1=\begin{pmatrix}x&s&0\\-s&x&0\\0&0&1\end{pmatrix},\qquad
R_2=\begin{pmatrix}x&0&s\\0&1&0\\-s&0&x\end{pmatrix},\quad
s=\sqrt{1-x^2}.
$$

Their passive Fock-space unitaries are the second quantizations of these
matrices. The relative matrix $V=(R_1R_2)^T(R_2R_1)$ is in $SO(3)$.
Its signal entry and bath block are

$$
a=x^4-2x^3+2x=1-c,\quad h=x+x^2-x^3,\quad
D=\begin{pmatrix}h&1-x^2\\
(1-x^2)x(x-2)&h\end{pmatrix},
\quad \det D=a.
$$

Put $r=n/(n+1)$ and
$T=\operatorname{Tr}_{E_1E_2}[(I\otimes\tau_n\otimes\tau_n)\Gamma(V)]$.
Cyclicity gives $\operatorname{Tr}J(\rho)=\operatorname{Tr}(T\rho_S)$
for the switch cross map $J$. Number conservation and the phase-invariant
baths make $T$ diagonal. For $0\le z<1$ its generating trace is

$$
\begin{aligned}
\sum_{k\ge0}z^k\langle k|T|k\rangle
&=\frac{(1-r)^2}{\det[I-V\operatorname{diag}(z,r,r)]}\\
&=\frac{(1-r)^2}{(1-2rh+r^2a)-z(a-2rh+r^2)}
=\frac{d^{-1}}{1-qz}.
\end{aligned}\tag{TA16}
$$

To justify the infinite trace, $\|V\operatorname{diag}(z,r,r)\|<1$.
On total number $m$, second quantization is the symmetric power, of
dimension $(m+1)(m+2)/2$, so the trace series converges absolutely.
The symmetric-power trace identity is the reciprocal determinant:
it follows for diagonal matrices by multiplying three geometric series,
and for arbitrary three-dimensional matrices by the eigenvalue identity
and continuity. Direct determinant expansion, or the $SO(3)$ cofactors,
gives the middle expression in (TA16). Coefficient comparison proves
$T=d^{-1}q^N$, a bounded operator, and then (TA15) for every normal input.
For positivity, the numerator of $q$ is
$(r-h)^2+(a-h^2)$, where
$a-h^2=-(1-x^2)^2x(x-2)\ge0$; the denominator minus numerator is
$(1-a)(1-r^2)\ge0$. This proves the asserted interval for $q$.

For a declared mean input energy $\operatorname{Tr}(N\rho_S)\le E<\infty$,
write $K=\lfloor E\rfloor$ and $t=E-K$. The sharp probability budget is

$$
\sup_{\operatorname{Tr}(N\rho_S)\le E}p_-
=\frac12\left[1-\frac{(1-t)q^K+tq^{K+1}}d\right].
\tag{TA17}
$$

The piecewise-linear interpolation of $q^k$ is decreasing and convex.
Its supporting lines and Jensen's inequality bound every number
distribution, including infinite tails. The adjacent-Fock mixture with
weights $1-t,t$ attains (TA17); handle $q=0$ with $q^0=1$ as above.
The simpler inequality $1-q^k\le k(1-q)$ gives

$$
\frac{d-1}{2d}\le p_-\le
\min\left\{\frac12,\frac{d-1}{2d}
 +\frac{(2n+1)cE}{2d^2}\right\}.
\tag{TA18}
$$

For $\delta=1-\eta\to0$ at fixed $n,E$, this is
$p_-\le n(n+1)\delta^2/2+O_{n,E}(\delta^3)$.
In a vacuum bath it sharpens to $p_-\le cE/2
=E\delta^3/8+O_E(\delta^4)$. These are probability statements;
they do not give a uniform conditional-fidelity remainder.

The bound has an all-attempt operational implication. Identical slots
give the same serial map $S=\mathcal E^2$ on both helper diagonals,
and exchanging their Kraus labels makes $J$ Hermiticity preserving.
Thus, with the reference retained,

$$
\Omega=|+\rangle\langle+|\otimes\sigma_+
       +|-\rangle\langle-|\otimes\sigma_-,\quad
\sigma_++\sigma_-=S(\rho_{SR}),\quad
\frac12\|\Omega-|+\rangle\langle+|\otimes S(\rho_{SR})\|_1=p_-.
\tag{TA19}
$$

The last equality follows because the difference has two orthogonal
helper blocks $-\sigma_-$ and $\sigma_-$, both with trace $p_-$.
An ordinary experiment can supply the same clean helper in $|+\rangle$,
use the same two serial contacts, and then apply the same admitted
receiver, program and records. Every all-launch positive payoff
represented by an effect between zero and identity, including accepted
Bell-good mass, improves by at most $p_-$; optimizing the ordinary
receiver only strengthens this comparison. Large changes in conditional
fidelity on a rare accepted branch do not evade this probability budget.

This closes a weak-loss, fixed-energy all-attempt comparison, rather than
the general approximate-memory problem. Unequal slots, multiple adaptive
switched contacts, additional bath records, input-bearing bypass memory,
different coherent extensions and energies growing with inverse loss
require separate analysis. Routing, helper survival, storage, calibration
and every rejection still count. Ordinary non-Gaussian codes and filters
must also be admitted: for example,
[Mele et al., arXiv:2607.27449v1](https://arxiv.org/html/2607.27449v1)
certify positive ordinary coherent information for a finite-support
non-Gaussian input where every single-mode Gaussian input gives zero.
A Gaussian-input comparison is therefore not an ordinary capacity ceiling.

### A parameter-free ordinary parity comparison on a fixed code

A concrete ordinary approximate receiver is available when the actual
apparatus supplies a known logical swap and QND parity. Encode entirely
in $\mathcal C=\operatorname{span}\{|0\rangle,|2\rangle\}$, with any
unknown code/reference state. Toss a fair classical coin; apply the known
unitary $X_{02}$ before the same two serial contacts when it is one,
accept the even-parity outcome, undo the same swap, and discard the coin.
The full oscillator unitary swaps $|0\rangle,|2\rangle$ and is identity
elsewhere. It commutes with parity. The coin-averaged input mean photon
number is exactly one for every unknown code state; there is no
input-bearing bypass memory or measured bath.

The serial channel is a thermal attenuator with transmissivity
$T=\eta^2$ and the same bath occupation $n$. For the analysis only, set

$$
G=1+(1-T)n,\quad \tau=T/G,\quad u=1-\tau,\quad v=G-1,\quad
t=\eta/G.
\tag{TA20}
$$

Use its exact pure-loss-then-quantum-limited-amplifier decomposition,
with transmissivity $\tau$ and gain $G$. The no-event Kraus operator is
$G^{-1/2}t^N$, hence on the code it is
$G^{-1/2}\operatorname{diag}(1,t^2)$. Averaging the two known swap
frames gives exactly

$$
\frac{D\rho D+XDX\rho XDX}{2G}
=p_T\rho+z_T Z\rho Z,\quad D=\operatorname{diag}(1,t^2),\quad
p_T=\frac{(1+t^2)^2}{4G},\quad z_T=\frac{(1-t^2)^2}{4G}.
\tag{TA21}
$$

Here $X,Z$ are logical Paulis on $\mathcal C$; the reference is untouched.
For every other accepted Kraus history, loss count $L$ plus amplifier gain
count $K$ is even and at least two. Since the input support has $N\le2$,
the binomial loss law and unbounded negative-binomial gain law obey
$\mathbb E[L(L-1)]/2\le u^2$,
$\mathbb E[LK]\le4uv$ and
$\mathbb E[K(K-1)]/2\le6v^2$.
For the middle inequality, condition on the loss result: the gain mean
is $(N-L+1)v$, and $N-L\le1$ when $L\ge1$, while
$\mathbb E L\le2u$. The last inequality uses
$\mathbb E[K(K-1)\mid N-L]/2=(N-L+1)(N-L+2)v^2/2$.
The indicator of $L+K\ge2$ is bounded by the sum of these three
nonnegative factorial products. Their Kraus probability effects are
number diagonal, so these bounds hold uniformly on the entire code,
including its coherences and any passive reference.

Consequently the complete accepted map, with full oscillator output, is

$$
\mathcal O_{\rm acc}=p_T\operatorname{Id}_{\mathcal C}+\mathcal R,
\quad \mathcal R\text{ CP},\quad
\|\mathcal R\|_\diamond\le z_T+\beta,\quad
\beta=u^2+4uv+6v^2.
\tag{TA22}
$$

For a CP map its diamond norm is the operator norm of its probability
effect. Every accepted gain output, including levels above two, remains
inside $\mathcal R$; no free code projection or output Fock cutoff is used.
Thus success is at least $p_T$ and encoded Bell-good mass is at least
$p_T$. Conditional Bell fidelity is at least
$p_T/(p_T+z_T+\beta)$. At fixed $n$ and $\delta=1-\eta\to0$,
$p_T=1-O_n(\delta)$ and $z_T+\beta=O_n(\delta^2)$.
For any code/reference state, the normalized accepted state's half
trace distance from that encoded input is at most
$(z_T+\beta)/(p_T+z_T+\beta)$, by the same positive-mixture decomposition.
The controller never uses $\eta,n$; those parameters only evaluate the
bound. This is a supplied-control comparison, not an ordinary optimum.

The physical cost is the encoding/capture, known $0\leftrightarrow2$
swap pulses, one clean helper for the QND parity measurement and its
readout/reset, the discarded coin, storage and every rejected run.
Known-control calibration, finite pulse errors, parity assignment errors
and actual clock must be included. The parity sources below establish
that control's relevance; they do not implement this whole receiver.
A rare high-quality switch branch must be compared against this
near-unit-acceptance ordinary alternative when these same controls exist.

## Clock-resolved baths and the complete retained-output comparison

<a id="nr-r04-clock-thermal-ports"></a>

This qualification concerns the physical extension of two attenuators,
not their reduced Gaussian-channel marginals alone. It specializes the
[record-sensitive temporal comparison](../communication.md#photon-preserving-markov-records-the-complete-routed-instrument)
to thermal beam-splitter baths and preserves the full retained helper.
The earlier faithfulness and visibility results concern the standard
module-paired SWITCH; the fresh-clock extension below is a different
physical model.

Let $U_j$ mix the signal with one bath mode, with one-particle matrix
$R_j=\bigl(\begin{smallmatrix}c_j&s_j\\-s_j&c_j\end{smallmatrix}\bigr)$,
$c_j=\sqrt{\eta_j}\in[0,1]$, $s_j=\sqrt{1-c_j^2}$. Prepare the bath in
$\tau_j=(1-z_j)\sum_{n\ge0}z_j^n|n\rangle\langle n|$,
$z_j=\bar n_j/(1+\bar n_j)<1$, independently of all input, helper and
passive-reference systems. Fix a thermal purification
$|\Theta_j\rangle=\sum_n\sqrt{(1-z_j)z_j^n}|n\rangle_{E_j}|n\rangle_{F_j}$.
All discarded purifiers remain in the physical record ledger.

The standard module-labelled SWITCH uses the same pair $E_A,F_A$ in
both histories and the same pair $E_B,F_B$ in both histories. Its two
complete words are $U_BU_A$ and $U_AU_B$. Expanding in outgoing bath
number and incoming purifier number gives the usual Kraus-paired sum:
the labels $(m_A,n_A,m_B,n_B)$ agree between the two orders. Merely
putting equal reduced attenuators at two different clock times does not
establish that pairing.

For comparison, declare four independent bath/purifier pairs
$A_1,A_2,B_1,B_2$ and the controlled histories

$$
V_0=U_{B_2}U_{A_1},\qquad V_1=U_{A_2}U_{B_1}.
\tag{TA23}
$$

Every unused opportunity is assumed to act as the identity on its bath
and on every other field. This is an **inactive-window gating premise**.
An always-on warm beam splitter with a vacuum input can emit thermal
photons into that signal port. Such unused signal outputs must instead
be included explicitly; they are not an identity extension of (TA23).
The words also assume matched signal/output modes, control phases and
the common finish, without additional inaccessible route tags.

The one-sided thermal mean of a contact is a bounded operator

$$
M_j=\langle\Theta_j|U_j|\Theta_j\rangle
=\operatorname{Tr}_{E_j}(\tau_jU_j)
=\alpha_j\beta_j^N,\qquad
\alpha_j=\frac{1-z_j}{1-z_jc_j},\quad
\beta_j=\frac{c_j-z_j}{1-z_jc_j}.
\tag{TA24}
$$

Here $0<\alpha_j\le1$ and $|\beta_j|\le1$. In particular $\beta_j$
can be negative; it must not be replaced by an unsigned loss amplitude.
This amplitude supplies neither a no-jump measurement nor access to a
thermal purifier. To prove the identity, phase covariance
makes $M_j$ number diagonal, and for $0\le y<1$ the symmetric-power
trace identity gives

$$
\sum_{m\ge0}y^m\langle m|M_j|m\rangle
=\frac{1-z_j}{\det[I-R_j\operatorname{diag}(y,z_j)]}
=\frac{1-z_j}{1-z_jc_j-y(c_j-z_j)}.
\tag{TA25}
$$

The trace is absolutely convergent because
$\|R_j\operatorname{diag}(y,z_j)\|<1$. The determinant formula follows
by tracing each symmetric power, or by the two-mode eigenvalue identity
and continuity. Expanding its geometric series proves (TA24) on the
infinite oscillator. It also gives the endpoints: $z=0$ yields $c^N$,
$c=1$ yields $I$, and $c=0$ yields $(1-z)(-z)^N$.

Write an arbitrary initial normal state on $C,S,R$ as
$\sum_{h,k}|h\rangle\langle k|\otimes\rho_{hk}$; the blocks need not be
positive individually. Tracing the four bath/purifier pairs in (TA23)
gives the exact accessible map

$$
\rho_{CSR}\longmapsto
\begin{pmatrix}
(\mathcal E_B\mathcal E_A\otimes I_R)(\rho_{00})&
(K\otimes I_R)\rho_{01}(K^\dagger\otimes I_R)\\
(K\otimes I_R)\rho_{10}(K^\dagger\otimes I_R)&
(\mathcal E_A\mathcal E_B\otimes I_R)(\rho_{11})
\end{pmatrix},\qquad K=M_BM_A=M_AM_B.
\tag{TA26}
$$

Indeed each bath acts on only one side of the cross-history expression,
so its contraction is $M_j$ or $M_j^\dagger$. Before using commutativity,
the upper-right block is
$M_BM_A\rho_{01}(M_AM_B)^\dagger$. All $M_j$ are functions of $N$, so
they commute even at unequal bath occupations. This proof includes the
thermal purifiers; independently relabelling them is not an allowed
change of physical history. The result differs from the standard
module-paired Kraus cross sum.

For an independent helper $+$, (TA26) also gives the exact fresh-clock
minus probability on every normal input,

$$
p_-(\rho)=\frac12\left[1-\alpha_A^2\alpha_B^2
\operatorname{Tr}\bigl((\beta_A^2\beta_B^2)^N\rho_S\bigr)\right].
\tag{TA27}
$$

The convention $0^0=1$ includes a zero base on the vacuum. This scalar
visibility loses the sign of $\beta_A\beta_B$, whereas the full cross
map on $|0\rangle\langle1|$ has coefficient
$\alpha_A^2\alpha_B^2\beta_A\beta_B$. The sign is retained in (TA26)
and in its reference-sensitive coherence, not discarded as a visibility
convention.

If both baths have the same occupation $\bar n$, their reduced
attenuators commute, even for unequal transmissivities. The characteristic
action of either composition has signal multiplier
$\sqrt{\eta_A\eta_B}$ and noise exponent
$(1-\eta_A\eta_B)(\bar n+1/2)$. Now consider an ordinary same-order
coherent delayed route with words $A_1B_2$ and $A_2B_3$, using the same
gated fresh-window model. Both diagonal blocks are
$\mathcal E_B\mathcal E_A$, and the cross block is the same
$\operatorname{Ad}_K$. Therefore it equals (TA26) on **every initial
helper/signal/reference state**, before measuring or discarding the
helper. Any common joint receiver, code decoder or all-launch payoff on
$C,S$ consequently has the same output. This statement does not need a
Fock cutoff, a Gaussian input or an oscillator-to-qubit encoding. Equal
physical temperatures imply equal occupations only for matched carrier
frequencies, as in this same-carrier attenuator convention.

For unequal occupations, the two reduced diagonal compositions generally
differ: their noise exponents differ by
$(1-\eta_A)(1-\eta_B)(\bar n_B-\bar n_A)$. Full retained-helper equality
with that one same-order route is then not asserted. For an independently
prepared helper $+$ and signal/reference input $\rho$, the native measured
$X$ instrument is

$$
\mathcal I_\pm(\rho)=
\frac{\mathcal E_B\mathcal E_A(\rho)+
\mathcal E_A\mathcal E_B(\rho)\pm2K\rho K^\dagger}{4}.
\tag{TA28}
$$

A fair recorded choice of the ordinary delayed forward and reverse
experiments gives exactly (TA28), by the existing temporal-filter
construction. This matches both flags, complete signal output and any
reference. It does not match an arbitrary unmeasured helper at unequal
bath occupations or an arbitrary different prescribed measurement history.

The full-output common-occupation comparator uses the same two occupied
contacts in each history but a third global clock window. Its extra
delay, coherent whole-mode route, helper survival and storage noise remain
costs. Equality here concerns accessible $C,S,R$, not the bath-output
isometry or a future persistent environment: the ordinary route has
different clock registers. If a bath or its emissions are retained or
accessible, their actual outputs must be compared too. Swapping only mixed
bath marginals or deleting a classical log does not supply coherent access
to their purifiers. The accessible-bath identity (TA13) provides a distinct
exact ordinary compiler when its actual controlled bath swaps are supplied.

There is an exact elementary falsifier before attempting logical-recovery
optimization. With $c_A=c_B=3/5$, $\bar n_A=\bar n_B=1$, a vacuum signal
and independent helper $+$, (TA24) gives
$M=(5/7)(1/7)^N$. The fresh-clock cross visibility is $(5/7)^4$, whereas
the standard module-paired visibility from (TA15) is $625/1201$. Thus

$$
p_-^{\rm clock}=\frac{888}{2401},\qquad
p_-^{\rm module}=\frac{288}{1201}.
\tag{TA29}
$$

Both instruments have the same ordered thermal signal channels. These
different flag probabilities expose a changed physical extension, not a
memory advantage. Agreement with one vacuum statistic alone would not
verify the entire coherent channel or a future bath process.

### A complete ordinary approximation at unequal bath occupations

The measured-$X$ equality also has a controlled approximation for the full
unmeasured helper. Here the helper is initially independent in $|+\rangle$;
the signal may have any inaccessible reference. Retain the same gated,
stationary fresh-bath premises. Put $\mathcal A=\mathcal E_B\mathcal E_A$,
$\mathcal B=\mathcal E_A\mathcal E_B$, $\mathcal T=\operatorname{Ad}_K$,
and $P_h=|h\rangle\langle h|$. Projection of the two used purified bath
outputs onto their initial joint vector gives the Kraus operator $K$.
Its orthogonal complement proves that
$\mathcal D_A=\mathcal A-\mathcal T$ and
$\mathcal D_B=\mathcal B-\mathcal T$ are CP and trace-nonincreasing.
The complete native accessible-output channel is

$$
\mathcal N=P_+\otimes\mathcal T+
 \frac{P_0\otimes\mathcal D_A+P_1\otimes\mathcal D_B}{2}.
\tag{TA30}
$$

For an integer $m\ge2$, prepare a uniform coherent superposition
$|s_m\rangle$ of ordinary fixed-order histories $A_jB_{j+1}$,
$j=1,\ldots,m$. Distinct histories have disjoint module/time bath
supports: even adjacent arms use different modules in their shared clock
window. Their diagonal time blocks are $\mathcal A/m$, and every
off-diagonal block is $\mathcal T/m$. Thus their full output is

$$
\mathcal W_{AB}=\frac{I_m}{m}\otimes\mathcal D_A+
 |s_m\rangle\langle s_m|\otimes\mathcal T.
\tag{TA31}
$$

Measure the helper projectors $P_s=|s_m\rangle\langle s_m|$ and $I-P_s$.
Prepare the output helper in $P_+$ on the first record and $P_0$ on the
second. Both records are used; this is a complete CPTP receiver. Its output
is $P_+\otimes\mathcal T+[P_+/m+(1-1/m)P_0]\otimes\mathcal D_A$.
For the corresponding $BA$ circuit prepare $P_1$ on the complementary
record. A fair classical choice between these ordinary circuits gives a
CPTP channel $\mathcal F_m$ with exact difference

$$
\mathcal F_m-\mathcal N=
 \frac{(P_+-P_0)\otimes\mathcal D_A+
       (P_+-P_1)\otimes\mathcal D_B}{2m}.
\tag{TA32}
$$

For a bounded normal CP map $\mathcal D$ on trace class,
$\|\mathcal D\|_\diamond=\|\mathcal D^\dagger(I)\|_\infty$.
Both remainders have norm at most one, and
$\|P_+-P_h\|_1=\sqrt2$ for $h=0,1$. The triangle inequality proves

$$
\frac12\|\mathcal F_m-\mathcal N\|_\diamond
 \le\epsilon_m=\frac1{\sqrt2\,m}.
\tag{TA33}
$$

This includes arbitrary signal/reference inputs without a Fock cutoff,
photon-moment hypothesis or input-energy restriction. There is no rejected
attempt in this ordinary approximation. Any common later recovery and
complete accept/reject instrument preserves the bound. Acceptance
probabilities $p,q$ and joint accepted Bell-good masses each differ by at
most $\epsilon_m$. If $\sigma,\tau$ are the accepted subnormalized
states, retaining the complementary reject records gives
$\|\sigma-\tau\|_1+|p-q|\le2\epsilon_m$. Consequently, for
$p>\epsilon_m$,

$$
q\ge p-\epsilon_m>0,\qquad
\frac12\|\sigma/p-\tau/q\|_1\le\frac{\epsilon_m}{p}.
\tag{TA34}
$$

This follows by normalizing the accepted difference with denominator $p$
and applying the preceding complete-flag bound. A rare branch has no
normalized-quality guarantee independent of its probability.

The construction uses two occupied contacts per history, but $2m$ possible
module/time visits over $m+1$ global windows, an $m$-dimensional coherent
whole-payload route and receiver, up to $m-1$ extra windows of relative
storage, phase stabilization, mode matching, readout/reset and the classical
order choice. It is an ordinary timing construction, rather than a hard
two-call comb simulation. Achieving error $\epsilon$ requires
$m=O(1/\epsilon)$. A two-path native router does not automatically supply
this larger route port or its storage quality.

All pairs of distinct arms must obey the specified common coherence. A
uniform calibrated scalar ordinary visibility at least as large as the
native visibility can be deliberately reduced to match it; the proof then
uses the corresponding scaled $\mathcal T$ and CP remainders. Generic
delay-dependent or payload-dependent noise, attenuation, nonstationarity or
bath reuse requires its actual instrument. No uniform multiarm quality
follows from a scalar memory lifetime. This bound establishes neither an
exact unequal-occupation compiler, an optimal ordinary frontier nor a
measured clock or throughput advantage.

### A classical-order coherence budget without extra time bins

There is also a cheaper complete ordinary comparison for the same initial
helper $+$ and arbitrary signal/reference input. Choose $AB$ or $BA$ with
equal classical probability and retain that choice as output helper
$P_0$ or $P_1$. With the notation of (TA30), this channel and its exact
distance from the native fresh-clock output are

$$
\begin{aligned}
\mathcal N_{\rm cl}&=\frac{P_0\otimes\mathcal A+
                              P_1\otimes\mathcal B}{2},\\
\mathcal N-\mathcal N_{\rm cl}&=\frac{X_C}{2}\otimes\mathcal T,\\
\frac12\|\mathcal N-\mathcal N_{\rm cl}\|_\diamond
 &=\frac{\|K\|^2}{2}
  =\frac{(\alpha_A\alpha_B)^2}{2}=:\epsilon_{\rm cl}.
\end{aligned}\tag{TA35}
$$

The trace norm of $X_C/2$ is one and the CP map
$\operatorname{Ad}_K$ has diamond norm $\|K\|^2$. Since
$|\beta_j|\le1$, the vacuum eigenvalue attains
$\|K\|=\alpha_A\alpha_B$; the vacuum input also attains the displayed
channel distance. This proves equality on the infinite oscillator.
Negative $\beta_j$ retains its parity sign without changing that norm;
$\beta_j=0$ uses the vacuum convention $0^0=1$. The cases $c_j=0,1$ and
$z_j=0$ are included, while a nonnormalizable $z_j=1$ bath is excluded.
Equivalently $\alpha_j=[1+\bar n_j(1-\sqrt{\eta_j})]^{-1}$, so this
budget can be small for hot baths at fixed nonunit transmissivities.

Any common complete recovery has acceptance and joint accepted Bell-good
mass differences at most $\epsilon_{\rm cl}$, with the conditional-state
bound (TA34) using that error. Each ordinary route occupies two contacts
over two windows. Classical route selection, transport, loss, readout/reset
and the retained order bit still cost resources; a receiver needing a
computational-basis helper must be supplied one. This baseline needs no
coherent superposition of time paths. It compares accessible outputs,
rather than bath records or actual laboratory rates.

Where both ordinary interfaces are admitted, the ideal output error is
bounded by $\min\{\epsilon_{\rm cl},1/(\sqrt2 m)\}$ with their respective
costs. The separate common-occupation two-path compiler is exact and
remains stronger in its scope. None of these comparisons supplies a
physical standard module-paired SWITCH or validates ungated thermal idle
ports.

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

A coherent finite-code receiver is a separate port from number resolution.
[Ni et al., Nature **616**, 56–60 (2023)](https://arxiv.org/html/2211.09319v2)
use the binomial code $(|0\rangle+|4\rangle)/\sqrt2,|2\rangle$ and a
tailored transmon frequency comb to extract the $\{1,3\}$ loss syndrome,
with readout, reset, feedback and recovery. This preserves the relevant
coherences; it does not establish an exact arbitrary threshold predicate
on an unbounded thermal output or transfer their loss-dominated measured
performance to a thermal gain/loss channel. Measuring every number and
then forgetting it destroys the binomial code's $0/4$ coherence.

An ideal coherent optical threshold has a constructive resource cost:
[Guanzon et al., PRL **128**, 160501 (2022), Eqs. (2)–(3)](https://arxiv.org/html/2110.03172v4)
at gain one and with all corrected bunched-resource heralds realizes
$\sqrt{c_K}P_{\le K}$, where
$c_K=K!/[(K+1)^{K-1}2^K]$. For example $c_4=3/250$.
A prepared and stored alternative resource gives an online factor at least
$1/[(K+1)2^K]$. These are achievable factors of named optical networks,
not upper bounds on a threshold receiver. Resource photons, multiport
interference, number-resolving heralds, phase correction, preparation,
storage and any microwave capture/conversion remain costs. Neither this
ideal optical construction nor number-distribution calibration supplies a
measured microwave cutoff instrument. A combined accepted decoder need
not use a separate threshold meter, but its coherent accepted effect and
all complementary failures still need a physical implementation.

For the vacuum-input model, if $\delta=1-\eta\to0$ with fixed $\bar n$,
(TA7) gives
$p_-=\delta^2\bar n(\bar n+1)/2+O(\delta^3)$. Moreover
$\tfrac12\|\sigma_+/p_+-\tau_m\|_1\le p_-$, since
$\tau_m=p_+\rho_++p_-\rho_-$. Thus a nearly lossless warm cable does not
automatically give a sizeable order-conditioned source change. This is a
model consequence, not a fit to the measured link's nonuniform baths.

The remaining physical test is an approximate **unknown-state/reference**
task with a specified code, energy and all-attempt acceptance/rate metric,
using either an established module-paired extension or an unequal-occupation
fresh-clock route with its actual finite timing and coherence costs. The
gated common-occupation fresh-clock output is already exactly compiled;
for unequal occupations (TA33) gives the larger ordinary temporal baseline.
It needs the full temporal Gaussian ports, declared bath memory/freshness,
loss and timing records, and a helper that survives vacuum. A router
acting on an empty thermal port can receive bath photons, so a vacuum
dummy is not automatically an identity branch. Neither the abstract
faithfulness theorem nor the two reduced channel marginals establishes
that interface. The source-specific ordinary filter, accessible-bath
compiler and clock-resolved comparisons close their stated endpoints; a matched
approximate thermal-memory advantage remains open. If an actual reversible
code/controller transfer is available, ordinary intermediate correction,
energy restoration and logical parking must also be compared at their
real storage, reset, measurement and gate costs. An independent route
helper alone does not imply a code-to-helper transfer or a separate free
syndrome meter while that helper stores the data.

The [exact checker](../checks/architecture/verify_thermal_attenuator.py)
replays the Gaussian determinant and ratio polynomials, full finite
source/flag identities, and matrix-unit boundary guards including the
finite-dimensional kernel. Its [visibility helper](../checks/architecture/thermal_self_visibility.py)
also lifts complete finite total-photon sectors, checks thermal-series
coefficients and retains reference/flag/payoff fixtures, with exact omitted
initial thermal-mixture weight. These are independent finite guards;
the infinite trace, sharp mean-energy budget and all-input payoff bound
remain analytic. Faithfulness, bounded strong density, Gaussian
integration, infinite tails and the physical source premises are analytic
or measured inputs, not conclusions of a Fock-cutoff numerical replay.
The [clock-port checker](../checks/architecture/thermal_clock_ports.py)
adds exact thermal-mean coefficients, a sign-sensitive coherence and the
vacuum pairing falsifier, plus complete finite non-Gaussian bath-sector
fixtures for retained-control and measured-flag maps. These finite bath
mixtures are not thermal-channel truncations. The
[temporal receiver checker](../checks/architecture/thermal_temporal_receiver.py)
checks the complete multiarm receiver and channel difference on matrix
units for two abstract rational CPTP maps sharing a Kraus operator. The
infinite thermal trace, channel-commutation theorem, all-reference norm
and conditional-state bounds, and actual ports remain analytic premises
or proofs, not conclusions of those finite fixtures.
