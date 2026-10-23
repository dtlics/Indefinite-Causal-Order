# A finite-energy bosonic logical-memory comparator

<a id="nr-r06-bosonic-logical-frontier"></a>

This proof component of [NR-R06](../architecture-baselines.md#nr-r06)
compares a specified switched plus-flag memory with an ordinary protocol
using the same two independent quadrature-noise calls. The ordinary
protocol supplies calibrated Fourier rotations and finite squeezing.
For the fixed product decoder below, it attains at least the switch's
conditional logical entanglement fidelity at the same acceptance.
Its transient energy and controller costs are additional resources.
This is neither equal-energy optimality nor a bound on every decoder
or heralded frontier.
After the same fixed gauge trace, the ordinary protocol also dominates
arbitrary deterministic recovery using all retained control outcomes.
Recovering from the full coherent oscillator before that trace is a
different problem.

The [isotropic bosonic compiler](../architecture-baselines.md#nr-r06-bosonic-compilers)
already gives full-instrument equality on a different noise class. The
[ideal GKP comparison](../architecture-baselines.md#nr-r06-anisotropic-gkp)
allows arbitrary joint recovery but bounds unconditional fidelity in an
ideal-syndrome model. Here the plus-flag comparison and its all-control
extension keep a specified gauge trace, and one explicit normalizable
finite-energy encoding is derived in full.
The exact decoder used in that derivation is an abstract CPTP map; a
finite-cost physical implementation is not assumed.

## Physical calls and the retained score

Use $[Q,P]=i$, $N=(Q^2+P^2-1)/2$ and
$D(x,y)=\exp[i(yQ-xP)]$. The two mandatory independent slots apply
$X(x)=e^{-ixP}$ with $x\sim N(0,a)$ and
$Z(y)=e^{iyQ}$ with $y\sim N(0,b)$, where $a,b>0$ are calibrated.
Their draws are fresh and inaccessible. The payload may be entangled
with an inaccessible reference. A separately initialized plus control
selects their two orders coherently; no logical input is stored in that
control before the slots.

The Weyl relation makes the two order amplitudes differ by $e^{ixy}$,
up to its sign convention. Measuring the control in the $X$ basis
therefore gives the exact target/reference instruments

$$
\mathcal F_\pm(\rho)=\frac12\int_{\mathbb R^2}
 p_a(x)p_b(y)[1\pm\cos(xy)]
 D(x,y)\rho D(x,y)^\dagger\,dx\,dy,
\qquad
c=\mathbb E\cos(xy)=\frac1{\sqrt{1+ab}},
\qquad
A_S=\frac{1+c}{2}.
\tag{BL1}
$$

The reference identity factor is implicit. Integrating over $y$ first
gives $\mathbb E_y\cos(xy)=e^{-bx^2/2}$; integrating the remaining
Gaussian gives $c$. Acceptance is independent of the logical input.
A physical realization must separately establish this complete
coherent-order instrument, including independent baths and routing
records. Merely programming independent recorded displacements does
not hide their classical labels from an ordinary receiver.

Let $k_q(x),k_p(y)\in[0,1]$ be coordinate retention functions for a fixed
decoder, and put

$$
h_q=\mathbb E k_q(x),\qquad h_p=\mathbb E k_p(y),\qquad
H=\mathbb E[k_q(x)k_p(y)\cos(xy)].
\tag{BL2}
$$

Suppose the decoded identity-Pauli probability for each displacement is
$k_q(x)k_p(y)$. This premise is proved for the finite-energy code below.
The switch's accepted-correct probability per launched attempt and its
accepted entanglement fidelity are respectively

$$
W_S=\frac{h_qh_p+H}{2},
\qquad
F_S=\frac{W_S}{A_S}=\frac{h_qh_p+H}{1+c}.
\tag{BL3}
$$

For a Pauli channel the identity probability is its entanglement
fidelity on a maximally mixed logical qubit. It is not the return
fidelity of every pure logical state. Pointwise, the weight in (BL1)
is at most one, so $W_S\le h_qh_p$: postselection alone cannot increase
this all-attempt score above the same decoder's unfiltered serial score.
The meaningful postselection comparison keeps acceptance as well as
conditional fidelity.

## Product-retention dominance and an ordinary attaining protocol

**Claim.** For independent centered Gaussian $x,y$ and any measurable
$k_q,k_p\in[0,1]$,

$$
F_S\le\max\{h_q,h_p\}.
\tag{BL4}
$$

No evenness or small-noise approximation is required. Assume without
loss of generality $h_q\ge h_p$. If $h_p\le(1+c)/2$, then
$H\le h_qh_p$, hence $F_S\le2h_qh_p/(1+c)\le h_q$.

Otherwise both $h_i>(1+c)/2$. Write $t_i=1-h_i$, so
$t_q\le t_p$ and $t_q<(1-c)/2$. The unnormalized failure numerator is

$$
B=\mathbb E\bigl[(1-k_q(x)k_p(y))(1+\cos(xy))\bigr].
\tag{BL5}
$$

Expand $1-k_qk_p=(1-k_q)+(1-k_p)-(1-k_q)(1-k_p)$.
The cosine contribution to each of the first two terms is nonnegative:
for example,
$\mathbb E[(1-k_q(x))\cos(xy)]
=\mathbb E_x[(1-k_q(x))e^{-bx^2/2}]\ge0$.
The subtracted term is at most $2t_qt_p$, by $1+\cos(xy)\le2$
and independence. Consequently

$$
B\ge t_q+t_p-2t_qt_p
 \ge2t_q(1-t_q)=2h_qt_q\ge(1+c)t_q.
\tag{BL6}
$$

The middle inequality is $(t_p-t_q)(1-2t_q)\ge0$.
Since $1-F_S=B/(1+c)$, (BL4) follows. Boundary cases follow directly
or by continuity.

Turning this upper bound into an ordinary memory requires zero-shift
correctness in the noise-free coordinate: $k_p(0)=1$ to attain $h_q$,
or $k_q(0)=1$ to attain $h_p$. Both hold for the code below.
Take a known Fourier rotation $F$ with
$F^\dagger Z(y)F=X(y)$, and a known squeeze $S_g$ satisfying
$S_g^\dagger P S_g=gP$, $S_g^\dagger Q S_g=Q/g$.
The chronological circuit and its pathwise action are

$$
S_g\ \longrightarrow\ \mathcal A\ \longrightarrow\ F\
\longrightarrow\ \mathcal B\ \longrightarrow\ F^\dagger\
\longrightarrow\ S_g^\dagger,
\qquad
S_g^\dagger F^\dagger Z(y)F X(x)S_g=X(g(x+y)).
\tag{BL7}
$$

Choose $g^2=a/(a+b)$. The final displacement is purely along $q$,
with the original variance $a$, so its decoded entanglement fidelity is
exactly $h_q$. Conjugating the whole circuit by a known Fourier
rotation gives a purely $p$ displacement; choosing
$g^2=b/(a+b)$ attains $h_p$. This version may add known endpoint
rotations, whose time and faults must also be charged.
Thus the larger of $h_q,h_p$ is achievable with two mandatory unknown
calls, calibrated Gaussian controls, no helper and no postselection.
Neither unknown displacement is learned or inverted.
The squeeze setting, choice of better axis and acceptance coin use
the calibrated variances and the known fixed decoder. Parameter
learning, finite control precision and their resulting error bounds
must be included if those quantities are not supplied exactly.

Independently retaining each ordinary attempt with probability $A_S$
matches the switch acceptance, preserves the ordinary fidelity and
gives accepted-correct probability at least $W_S$. Without that
thinning its all-attempt identity probability is larger still.
For $a=b$, the squeeze is the fixed finite value $g=1/\sqrt2$, or
$3$ dB. Infinite squeezing is not used. If one noise variance vanishes,
the switch plus flag is deterministic and the serial channel already
matches the corresponding product-decoder score without a singular
squeeze.

## An explicit normalizable encoding and exact decoder

Let $L=\sqrt\pi$, $C=[-L/2,L/2)$ and
$\mathcal H_s=L^2(C\times C)$. Define a map
$V:\mathbb C^2\otimes\mathcal H_s\to L^2(\mathbb R)$ by

$$
(Vf)(z)=L^{-1/2}\int_C f_\ell(u,v)e^{ikLv}\,dv,
\qquad
z=u+kL,\quad k=2m+\ell,\quad \ell\in\{0,1\}.
\tag{BL8}
$$

The representation of $z$ is unique except at irrelevant interval
boundaries. For each $u,\ell$, the functions
$L^{-1/2}e^{-i(2m+\ell)Lv}$ form a complete orthonormal Fourier basis
on $C$: their frequency differences are $2(m-m')L$ and $L^2=\pi$.
Multiplication by $e^{-i\ell Lv}$ relates the two parity bases.
Partitioning the real line into $kL+C$ and applying Parseval gives
$\|Vf\|^2=\sum_\ell\int_Cdu\int_Cdv\,|f_\ell(u,v)|^2$.
Inverse Fourier series in each parity sector gives surjectivity.
Thus $V$ is an exact unitary, without nonnormalizable ideal combs.

For a normalized $h\in\mathcal H_s$, define

$$
\mathcal E_h(\rho_L)=V(\rho_L\otimes|h\rangle\langle h|)V^\dagger,
\qquad
\mathcal D(\rho)=\operatorname{Tr}_s(V^\dagger\rho V).
\tag{BL9}
$$

These are well-defined CPTP encoding and decoding maps on normalizable
states. The embedded-error-wavefunction construction of
[Gottesman, Kitaev and Preskill, PRA **64**, 012310 (2001),
Eqs. (40)--(43)](https://arxiv.org/pdf/quant-ph/0008040)
is the primary precedent. The following calculations specify one
compact-support specialization, its ordered gauge and its energy;
they do not claim a new code mechanism or a demonstrated implementation
of the exact decoder.

Take real even compact functions

$$
h_\delta(u)=
\begin{cases}
\delta^{-1/2}\cos\!\left(\dfrac{\pi u}{2\delta}\right),
 & |u|\le\delta,\\
0,& |u|>\delta,
\end{cases}
\qquad
0<\delta<L/2,
\qquad
h(u,v)=h_{\delta_q}(u)h_{\delta_p}(v).
\tag{BL10}
$$

The encoded basis wavefunctions are

$$
\psi_\ell(z)=\sum_{m\in\mathbb Z}c_m^{(\ell)}
 h_{\delta_q}(z-(2m+\ell)L),
\qquad
c_m^{(\ell)}=L^{-1/2}\int_C
 h_{\delta_p}(v)e^{i(2m+\ell)Lv}\,dv.
\tag{BL11}
$$

Unitarity of $V$ proves their normalization and orthogonality.
The two logical parity sectors have disjoint position supports.
Their weak first derivatives also have disjoint supports; each cosine
bump vanishes at its support boundary, so its weak derivative has no
delta contribution. The code is in the quadratic-form domains of
$Q^2$ and $P^2$.

Here are the complete energy identities. For compact $H^1$ functions
$h_q,h_p$ vanishing at their support boundaries, derivative Parseval
gives, for either parity sector,

$$
\sum_m|c_m^{(\ell)}|^2=1,\qquad
\sum_m((2m+\ell)L)^2|c_m^{(\ell)}|^2=\|h_p'\|^2,\qquad
M_p:=\sum_m(2m+\ell)L|c_m^{(\ell)}|^2
 =\int_C h_p(v)^*\,i h_p'(v)\,dv.
\tag{BL12}
$$

Disjoint bumps then give
$\langle P^2\rangle=\|h_q'\|^2$ and
$\langle Q^2\rangle=\|h_p'\|^2+\mathbb E_{|h_q|^2}u^2+
2M_p\mathbb E_{|h_q|^2}u$.
The last cross term must be kept for a general complex asymmetric
choice. It vanishes for (BL10). Direct integration yields
$\|h_\delta'\|^2=\pi^2/(4\delta^2)$,
$\mathbb E u=0$ and
$\mathbb E u^2=\delta^2(1/3-2/\pi^2)$, hence

$$
\langle P^2\rangle=\frac{\pi^2}{4\delta_q^2},\qquad
\langle Q^2\rangle=\frac{\pi^2}{4\delta_p^2}
 +\delta_q^2\left(\frac13-\frac2{\pi^2}\right),
\qquad
E=\langle N\rangle=
\frac12\left[
\frac{\pi^2}{4\delta_q^2}+\frac{\pi^2}{4\delta_p^2}
+\delta_q^2\left(\frac13-\frac2{\pi^2}\right)-1\right].
\tag{BL13}
$$

The off-diagonal logical matrix elements of both quadratic forms
vanish by the disjoint supports. Their compressed operators are the
displayed constants times logical identity. Thus (BL13) holds for every
logical state, including one entangled with a reference; it is not
merely a basis-state average. It asserts finite mean energy, not finite
Fock support or finite higher moments.

## Displacements induce an exact decoded Pauli channel

For a fixed physical displacement,
$(D(x,y)\psi)(z)=e^{iy(z-x/2)}\psi(z-x)$.
For each initial syndrome $(u,v)\in C^2$, choose the unique integers
$r,s$ and reduced coordinates

$$
u'=u+x-rL\in C,\qquad v'=v+y-sL\in C.
\tag{BL14}
$$

Write the output coordinate as $z=u'+k'L$,
$k'=2m'+\ell'$. The input index is $k=k'-r$, so
$\ell'=\ell+r\pmod2$. Its wavefunction integrand transforms as

$$
e^{iy(u'+k'L-x/2)}e^{i(k'-r)Lv}
 =
e^{iy(u'-x/2)-irLv}\,
e^{ik'Lv'}\,(-1)^{\ell's}.
\tag{BL15}
$$

The phase before $e^{ik'Lv'}$ depends on syndrome and displacement
but not on the logical input. The logical action is exactly $Z_L^sX_L^r$.
Translation modulo $C$ is a measure-preserving bijection for each
fixed $(x,y)$, so each final syndrome has one preimage. Taking the
syndrome trace in (BL9) therefore gives

$$
\mathcal D\circ\operatorname{Ad}_{D(x,y)}\circ\mathcal E_h(\rho_L)
 =
\int_{C^2}|h(u,v)|^2
 Z_L^sX_L^r\rho_L X_L^rZ_L^s\,du\,dv.
\tag{BL16}
$$

There are no amplitude cross terms between distinct final syndromes.
Classically averaging over random displacements preserves this Pauli
mixture. This is an exact channel statement for arbitrary logical
inputs and references, rather than a classical-smearing ansatz.

Define the stabilizer-equivalent correct cells by
$g(t)=1$ if $\lfloor(t+L/2)/L\rfloor$ is even, and $g(t)=0$
otherwise; boundaries have zero probability here. From (BL16),

$$
p_I=\mathbb E_{x,y,u,v}[g(x+u)g(y+v)],\qquad
k_q(x)=\mathbb E_u g(x+u),\qquad
k_p(y)=\mathbb E_v g(y+v).
\tag{BL17}
$$

The initial syndrome density is
$|h_{\delta_q}(u)|^2|h_{\delta_p}(v)|^2$, independently of the
logical input. Thus the identity probability at each physical
displacement factorizes, $k_q(0)=k_p(0)=1$, and (BL2)--(BL7) apply
to this normalizable code with exactly the decoder (BL9).
For the switched plus map, its scalar displacement weight in (BL1)
does not alter the per-displacement derivation; it simply reweights
the Pauli probabilities.

The ordered gauge in (BL8) corresponds to
$e^{-iuP}e^{ivQ}=e^{-iuv/2}D(u,v)$.
In symmetric-Weyl embedded-error notation the amplitude is therefore
$h_q(u)h_p(v)e^{-iuv/2}$. Omitting this phase while computing the
physical wavefunction or its energy would change the construction.

## Energy, implementation costs and verification scope

For every positive possibly unnormalized state $\sigma$, as a
quadratic-form inequality,

$$
\operatorname{Tr}(N S_g\sigma S_g^\dagger)
\le\kappa\,\operatorname{Tr}(N\sigma)
 +\frac{\kappa-1}{2}\operatorname{Tr}\sigma,
\qquad
\kappa=\max\{g^2,g^{-2}\}.
\tag{BL18}
$$

Indeed $S_g^\dagger(Q^2+P^2)S_g=Q^2/g^2+g^2P^2
\le\kappa(Q^2+P^2)$.
For an encoded input with uniform mean energy $E$, its pre-noise
squeezed energy is at most $\kappa(E+1/2)-1/2$.
The corresponding unnormalized substitution
$\operatorname{Tr}(N\sigma)\le E\operatorname{Tr}\sigma$ requires
$\sigma$ to lie in that encoded-input cone. An arbitrary noisy or
postselected branch needs its own energy and probability in (BL18).

The two independent zero-mean kicks add $(a+b)/2$ to the intermediate
ensemble mean energy; Fourier rotations preserve $N$. For (BL7),
where $g\le1$, a safe peak ensemble-mean bound is therefore

$$
E_{\rm peak}\le\kappa(E+1/2)-1/2+(a+b)/2.
\tag{BL19}
$$

The final restored state has the input energy plus
$g^2(a+b)/2$, also below this bound. The $p$ version's endpoint
rotations preserve energy. These bounds apply to the unknown logical
input uniformly, but are ensemble means: Gaussian kicks have
unbounded tails. At $3$ dB the vacuum squeezing energy is $1/8$
photon; an encoded input has its actual larger state-dependent cost.
Known displacement echoes likewise incur transient drive energy,
helper coherence, readout and reset, even when their inverse pulses
restore the net target displacement.

No actual squeezing gate is supplied without its calibration, duration,
bandwidth, pump work, faults and storage loss. No exact implementation
of (BL9) is supplied by the existence of $V$ either. Preparation,
finite-resolution syndrome recovery, recovery ancillas and reset must
be included for both processors at the same device operating point.
The port model must remain valid at the transient energies.

Finite mean energy gives only a conservative truncation ledger:
$\Pr(N>K)\le E_{\rm out}/(K+1)$.
A cutoff followed by a replacement on overflow has disturbance
$O(\sqrt{E_{\rm out}/(K+1)})$ in trace distance by the gentle-measurement
bound. This does not identify efficient finite gates or a physical
decoder. An approximate decoder comparison must bound its actual
channel error on both output families; conditional accepted-score
errors are divided by the actual acceptance.

## All retained control outcomes after the fixed gauge trace

The comparison extends beyond the plus flag if the specified first
operation on the oscillator is still the gauge trace in (BL9).
Retain the entire switch control and allow arbitrary deterministic
joint recovery of that control and the decoded logical qubit.
This is a stronger recovery in that reduced interface, but it is
not arbitrary recovery of the physical oscillator before the trace.

Write $k_{q,0}=k_q$, $k_{q,1}=1-k_q$, and likewise for $p$.
For $e=(r,s)\in\{0,1\}^2$, define

$$
p_{rs}=\mathbb E[k_{q,r}(x)k_{p,s}(y)],\qquad
H_{rs}=\mathbb E[k_{q,r}(x)k_{p,s}(y)\cos(xy)].
\tag{BL20}
$$

The code's real even product syndrome density makes each retention
function even. The sine term therefore vanishes separately for each
error label. Choosing Hermitian representatives
$P_{00}=I$, $P_{10}=X_L$, $P_{01}=Z_L$, $P_{11}=Y_L$,
whose phases do not affect these diagonal Pauli terms, the exact
reduced channel is

$$
\rho_L\longmapsto\sum_{r,s}\Gamma_{rs}^C\otimes
 P_{rs}\rho_LP_{rs},\qquad
\Gamma_{rs}=\frac{p_{rs}I+H_{rs}X_C}{2}.
\tag{BL21}
$$

Here $\operatorname{Tr}\Gamma_{rs}=p_{rs}$ and
$|H_{rs}|\le p_{rs}$. All control operators are $X$-diagonal.
Consequently measuring $X_C$ loses no information in this reduced
channel. The exact optimum, retaining both outcomes and correcting
the most likely Pauli separately for each, is

$$
F_{\rm trace,opt}=
\sum_{f=\pm1}\max_{r,s}\frac{p_{rs}+fH_{rs}}2.
\tag{BL22}
$$

Here is the complete recovery argument, also valid for arbitrary
qubit tags $\Gamma_e=p_e\tau_e$ that need not commute. Expand each
recovery Kraus operator from $C\otimes L$ to $L$ as
$K_j=\sum_e\langle v_{je}|_C\otimes P_e$.
Pauli trace orthogonality in the Bell-fidelity formula leaves
$\sum_e\operatorname{Tr}(M_e\Gamma_e)$, where
$M_e=\sum_j|v_{je}\rangle\langle v_{je}|\ge0$.
The identity-Pauli coefficient of trace preservation gives
$\sum_eM_e=I_C$. Conversely any such POVM followed by the guessed
Pauli correction realizes that objective, so optimal logical recovery
equals optimal tag discrimination.
Since $\tau_e\le I_C$ and $M_e\le I_C$,

$$
\operatorname{Tr}(M_e\Gamma_e)
\le p_e\min\{1,\operatorname{Tr}M_e\},\qquad
\sum_e\operatorname{Tr}M_e=2.
\tag{BL23}
$$

Allocating total weight at most two, with weight at most one per
label, bounds the objective by the two largest priors.
Independence makes the four priors
$h_qh_p$, $(1-h_q)h_p$, $h_q(1-h_p)$,
$(1-h_q)(1-h_p)$. Relabel each marginal's more likely value as zero.
Writing $m=\max(h_q,1-h_q)$, $n=\max(h_p,1-h_p)$, their two largest
sum to $mn+\max\{m(1-n),(1-m)n\}=\max(m,n)$.

For the present code $h_q,h_p\ge1/2$. To prove this rather than
assume it, let $G$ be the even-cell indicator in (BL17) and put
$f_a(u)=\mathbb E_{x\sim N(0,a)}G(u+x)-1/2$.
It solves $\partial_a f_a=\tfrac12\partial_u^2f_a$.
The even and antiperiodic extension of $G-1/2$ gives zero boundary
values at $\pm L/2$, while its initial value is $1/2$ in the
central cell. The Dirichlet heat maximum principle gives
$f_a(u)\ge0$ for $u\in C$.
Equivalently, it is one half the probability that a standard Brownian
motion started at $u$ has not exited $C$ by time $a$.
Averaging over the code's initial compact syndrome density proves
the claim for $h_q$, and the same reasoning applies to $h_p$.
It follows that

$$
F_{\rm trace,opt}\le\max\{h_q,h_p\}.
\tag{BL24}
$$

The calibrated ordinary protocol (BL7) attains this upper bound.
Thus all retained flags, arbitrary control readout and arbitrary
deterministic control/logical recovery are closed **after the fixed
gauge trace**. This unconditional result does not order every
accepted-fidelity frontier.

## A measured final syndrome and the coherent gauge are different ports

Suppose instead that the receiver first measures the final Zak
syndrome $(U,W)\in C^2$ and keeps its classical outcome.
Let $f_q=|h_{\delta_q}|^2$, $f_p=|h_{\delta_p}|^2$ and define the
unnormalized even/odd weights

$$
A_e(U)=\sum_{j\equiv e\ ({\rm mod}\ 2)}
 \int_C f_q(u)p_a(U-u+jL)\,du,\qquad
B_f(W)=\sum_{k\equiv f\ ({\rm mod}\ 2)}
 \int_C f_p(v)p_b(W-v+kL)\,dv.
\tag{BL25}
$$

Put $Z_q=A_0+A_1$, $Z_p=B_0+B_1$.
The outcome density is $Z_q(U)Z_p(W)$ and the posterior Pauli priors
are exactly $A_e(U)B_f(W)/(Z_q(U)Z_p(W))$.
Inserting the physical control state for
$x=U-u+jL$, $y=W-v+kL$ in the same integrals gives its corresponding
unnormalized tag; its trace is $A_eB_f$.
This follows from (BL15)--(BL16) after the specified final syndrome
measurement, without revealing an initial gauge label.

The even compact densities imply $A_0\ge A_1$ and $B_0\ge B_1$
on $C$. For example, extend $f_q$ evenly and antiperiodically by
$L$; its heat evolution is $A_0-A_1$. Evenness and antiperiodicity
force zero boundary values on $C$, and its initial interior density
is nonnegative. Dirichlet positivity proves the assertion.
Applying (BL23) pointwise therefore bounds the measured-interface
fidelity by

$$
F_{\rm measured,opt}\le
\int_{C^2}\max\{A_0(U)Z_p(W),Z_q(U)B_0(W)\}\,dU\,dW.
\tag{BL26}
$$

This ceiling can exceed $\max(h_q,h_p)$ because integration and
taking a maximum do not commute. It is not asserted to be tight
for the actual switch.

The ideal-code ordinary parity echo does not transfer unchanged.
Physical controlled $D(L,L)$ gives relative phase $e^{iL(y-x)}$.
Subtracting the known final-syndrome phase $L(W-U)$ leaves
$(-1)^{r+s}e^{iL(u-v)}$, with the unknown initial coordinates
$u,v$. Positive finite widths give a nonconstant phase on each
posterior's interval of support, so this is not an exact parity
readout. A controlled encoded Pauli
$V(Y_L\otimes I_s)V^\dagger$ would read parity exactly, but
$V^\dagger D(L,L)V=Y_L\otimes e^{iL(U_s-V_s)}$.
The additional coherent modular-gauge phase, its domain and physical
cost are not supplied by Gaussian controls or by merely naming the
traced CPTP decoder.

Before either gauge measurement or trace, a full recovery sees more.
For a draw $\xi=(x,y)$ let
$|c_\xi\rangle=(e^{ixy/2}|0\rangle+e^{-ixy/2}|1\rangle)/\sqrt2$.
For a final syndrome $z=(u',v')$, take its unique preimage
$u_z=[u'-x]_C$, $v_z=[v'-y]_C$ and integers $r_z,s_z$ as in
(BL14). Set $P_\xi(z)=Z_L^{s_z}X_L^{r_z}$ and
$\phi_\xi(z)=y(u'-x/2)-r_zLv_z$.
The full operator kernel between final syndromes $z,t$ is

$$
\begin{aligned}
\mathcal N_S(\rho_L)[z,t]
={}&\int_{\mathbb R^2}p_a(x)p_b(y)\,
 e^{i(\phi_\xi(z)-\phi_\xi(t))}
 h(u_z,v_z)\overline{h(u_t,v_t)}\\
&\quad{}\times|c_\xi\rangle\langle c_\xi|
 \otimes P_\xi(z)\rho_LP_\xi(t)^\dagger\,dx\,dy .
\end{aligned}
\tag{BL27}
$$

The diagonal $z=t$ gives (BL25). Off-diagonal blocks can have
different logical Paulis on their two sides.
Keeping both measured $X$ flags replaces the control state by its
classical flag weights but does not remove those gauge coherences.
Consequently neither (BL24) nor (BL26) bounds arbitrary recovery of
the physical output before that degradation. Replacing the initial
pure $|h\rangle\langle h|$ by a mixture of exact syndrome labels is
also a different input, not free classical information available to
the ordinary receiver.

## A complete finite-energy coherence counterexample

A different, non-Gaussian noise law demonstrates the distinction
exactly. Let the first slot apply $I$ or $X(L)$ with equal
probabilities and let the second be identity. The switch then equals
ordinary order. For the same compact code,

$$
V^\dagger X(L)V=X_L\otimes e^{-iLV_s},\qquad
\rho_L\longmapsto\frac12|h_0\rangle\langle h_0|\otimes\rho_L
 +\frac12|h_1\rangle\langle h_1|\otimes X_L\rho_LX_L,
\quad
h_0=h,\quad h_1=e^{-iLv}h.
\tag{BL28}
$$

The two tags have identical coordinate probability densities.
Measuring their final syndrome or tracing them leaves optimal
logical entanglement fidelity $1/2$.
Their coherent overlap is real and

$$
\zeta=\langle h_0|h_1\rangle
=\frac{\pi^2\sin(L\delta_p)}
 {L\delta_p[\pi^2-(L\delta_p)^2]},
\qquad 0<\zeta<1.
\tag{BL29}
$$

Integrating the cosine density in (BL10) gives this expression;
$0<L\delta_p<\pi/2$ gives positivity, and its nonconstant phase
gives the strict upper inequality. The difference of the two tag
projectors has nonzero eigenvalues $\pm\sqrt{1-\zeta^2}$.
Its spectral measurement followed by the indicated $I/X_L$
correction has success $(1+\sqrt{1-\zeta^2})/2>1/2$.
The recovery-to-discrimination argument above proves that this is
the exact optimal entanglement fidelity for (BL28).

An explicit heralded recovery is stronger still on its conclusive
outcomes. Let $\Pi$ project onto the two-tag span and take

$$
E_0=\frac{\Pi-|h_1\rangle\langle h_1|}{1+\zeta},\qquad
E_1=\frac{\Pi-|h_0\rangle\langle h_0|}{1+\zeta},\qquad
E_?=I_s-E_0-E_1.
\tag{BL30}
$$

The conclusive effects vanish outside the span. Inside it their sum
has eigenvalues $1$ and $(1-\zeta)/(1+\zeta)$, so $E_?\ge0$.
Outcome zero never occurs on $h_1$ and outcome one never occurs
on $h_0$; each correct conclusive probability is $1-\zeta$.
Apply $I$ or $X_L$ on the respective outcome. For every logical
input, including reference-entangled inputs, the accepted and failed
maps are exactly

$$
\Lambda_{\rm accept}=(1-\zeta)\operatorname{Id}_L,\qquad
\Lambda_{\rm fail}=\frac{\zeta}{2}
 (\operatorname{Id}_L+\operatorname{Ad}_{X_L}).
\tag{BL31}
$$

Thus acceptance $1-\zeta$ has perfect conditional fidelity and all
failure attempts remain counted. The code has finite energy
(BL13). Its compressed $Q$ is zero by the same real-even and
disjoint-support calculation, so the $X(L)$ branch adds mean energy
$L^2/2$ and the equal mixture adds $L^2/4$.
The coherent finite-rank gauge measurement is an abstract instrument,
not a demonstrated finite-time native operation.
Both protocols receive exactly the same benefit and costs in this
example. It proves that the syndrome measurement need not be
lossless, although (BL26)'s two-largest-prior ceiling is one here.

A four-label specialization also separates that dimension ceiling
from coherent recovery. Set both widths to $\delta=2L/5$ and take
independent fair shifts $x,y\in\{0,5L\}$, again a non-Gaussian law.
For labels $i,j\in\{0,1\}$ the gauge tags are, up to global phase,
$h(u,v)e^{i5jLu-i5iLv}$, and the logical errors are the four Paulis.
The same cosine integral as (BL29), with wavevector $k$, is
$\chi_\delta(k)=\pi^2\sin(k\delta)/
[k\delta(\pi^2-k^2\delta^2)]$.
Here $5L\delta=2\pi$, so $\chi_\delta(5L)=0$.
Product structure makes the four tags mutually orthogonal.
Their coherent projective measurement and Pauli correction therefore
give the identity channel on every logical input.
Ordinary order has the same tags and the same perfect recovery.

The final-coordinate measurement instead sees the same density
$|h(u,v)|^2$ for all four labels. Its priors are uniform, so the
two-largest-prior argument gives ceiling $1/2$.
The actual switch attains that measured-interface value: its control
is plus for three labels and minus for the joint displacement,
whose order phase is $25\pi$. Thus the measured optimum is $1/2$
while full coherent recovery has fidelity one.
The code energy remains finite by (BL13); these finite displacements
also add finite mean energy, and implementing the coherent tag
measurement remains an additional cost.
This disproves promoting the measured-interface dimension ceiling
by code algebra alone. It is not a counterexample within the
Gaussian-noise promise and supplies no advantage over ordinary order.

## A finite recovery optimization method, not a solved frontier

For a fixed supplied code and pre-noise controller, the full Gaussian
recovery problem has a precise finite-cutoff target.
Apply an oscillator number cutoff $\Pi_K$ to the complete switched
Choi output for a maximally entangled logical input, replacing
overflow by an orthogonal erasure symbol while retaining the control.
Let $\rho_{RB}^{(K)}$ be this normalized finite-dimensional Choi state.
The output $B$ contains the control and truncated oscillator, or
both specified classical flags and that oscillator.
For a recovery $\mathcal R:B\to L$, set
$X=2(\operatorname{Id}_R\otimes\mathcal R^\dagger)(\Phi_{RL})$.
Complete positivity and trace preservation give
$X\ge0$, $\operatorname{Tr}_R X=I_B$, and the recovered
entanglement fidelity is
$\operatorname{Tr}(\rho_{RB}^{(K)}X)/2$.
The exact finite primal and dual are

$$
F_{\rm opt}^{(K)}
=\frac12\max_{\substack{X\ge0\\\operatorname{Tr}_RX=I_B}}
 \operatorname{Tr}(\rho_{RB}^{(K)}X)
=\frac12\min_{\substack{\sigma_B\ge0\\
 I_R\otimes\sigma_B\ge\rho_{RB}^{(K)}}}
 \operatorname{Tr}\sigma_B.
\tag{BL32}
$$

The primal point $X=I_R\otimes I_B/2$ and a sufficiently large
scalar $\sigma_B$ are strictly feasible, so finite SDP strong
duality applies. No infinite-dimensional duality assertion is used.
For a trace-nonincreasing accepted recovery, use
$S=\operatorname{Tr}_R X\le I_B$. At specified average acceptance
$A>0$, the finite accepted frontier is

$$
X\ge0,\quad S\le I_B,\quad
\operatorname{Tr}(\rho_B^{(K)}S)=A,\qquad
W=\frac12\operatorname{Tr}(\rho_{RB}^{(K)}X),\quad
F_{\rm conditional}=W/A.
\tag{BL33}
$$

This $A$ is acceptance on the maximally mixed logical input.
Uniform acceptance on every logical state adds the stronger linear
condition
$\operatorname{Tr}_B[(I_R\otimes S)\rho_{RB}^{(K)}]=(A/2)I_R$.
The explicit map (BL31) already has that uniform property.

For the full Gaussian switch the target ensemble energy is
$E_{\rm out}=E+(a+b)/2$, because tracing the control leaves the
serial displacement mixture. The overflow probability obeys
$p\le\min\{1,E_{\rm out}/(K+1)\}$.
Embedding the finite erasure output and original state in one
common space, the gentle projection bound and overflow replacement
give

$$
\operatorname{TD}(\rho_{RB},\rho_{RB}^{(K)})
\le\sqrt p+p/2.
\tag{BL34}
$$

Indeed the removed success/off-diagonal part has trace norm at
most $2\sqrt p$ and the replacement block has trace $p$.
The adjoint pullback of a recovered Bell projector is an effect
between zero and identity, so optimal deterministic fidelities
differ by at most this bound. For a fixed accepted recovery,
$W$ and $A$ each differ by at most the same amount; conditional
errors must be divided by the actual positive acceptance.
A fixed-acceptance numerical frontier must report uncertainty in
both coordinates.

No such full Gaussian optimization is claimed solved here.
It requires controlled matrix elements of (BL27), finite primal
and dual certificates and a useful cutoff error. The SDP optimizes
post-noise recovery for its fixed input channel; it does not optimize
or supply arbitrary pre-noise encoders and controllers.
The aligned ordinary
channel has output energy $E+g^2(a+b)/2$ but the higher transient
cost (BL19). A physical comparison must use one actual peak-energy
and time budget, permit ordinary reoptimization of code widths,
alignment, squeezing and recovery, and count all actual modular,
ancilla-transfer or bypass controls the device supplies.
No all-ordinary optimum, native gain or capacity formula follows
from these reduced bounds or the optimization prescription.

The [exact finite replay](../checks/architecture/verify_bosonic_logical_frontier.py)
checks rational dominance and product-prior bounds,
controller/Weyl identities, wrap/parity phases, energy coefficients,
coherent phase-tag recovery maps and finite SDP normalizations.
The all-function inequalities, heat positivity, continuous Gaussian
integration, Fourier-basis completeness, weak-derivative energy
calculation, recovery duality and full channel/implementation
statements are the analytic arguments above. Finite guards do not
solve the full Gaussian recovery problem, certify an experimental
decoder or replace those proofs.
