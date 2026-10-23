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

The [isotropic bosonic compiler](../architecture-baselines.md#nr-r06-bosonic-compilers)
already gives full-instrument equality on a different noise class. The
[ideal GKP comparison](../architecture-baselines.md#nr-r06-anisotropic-gkp)
allows arbitrary joint recovery but bounds unconditional fidelity in an
ideal-syndrome model. Here the score is a fixed-decoder plus-flag score,
and one explicit normalizable finite-energy encoding is derived in full.
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

The conclusion concerns the fixed product decoder and plus-$X$ flag.
Arbitrary flag-dependent recovery, both retained flags with separate
decoders, other control readout phases, rotated nonproduct correct
regions and other quantum-controller records are not covered by
(BL4). Reoptimizing the ordinary code under the same actual energy
and time budget is also a separate problem. No native advantage,
all-ordinary optimum or capacity formula follows here.

The [exact finite replay](../checks/architecture/verify_bosonic_logical_frontier.py)
checks rational dominance bounds, controller/Weyl identities,
wrap/parity phases, energy coefficients and acceptance bookkeeping.
The all-function inequality, continuous Gaussian integration,
Fourier-basis completeness, weak-derivative energy calculation and
full channel/implementation statements are the analytic arguments
above. Finite guards do not certify an experimental decoder or replace
those proofs.
