# Certified photon tails for a heat-regularized GKP code

<a id="nr-r06-heat-gkp-certification"></a>

This proof component of [NR-R06](../architecture-baselines.md#nr-r06)
provides an alternative finite-energy code and a uniform photon-cutoff
certificate for full-output recovery calculations. It preserves the
logical reference and retained switch control. It supplies neither an
optimal recovery nor a physical coherent-order implementation, and it
does not replace the compact-syndrome code in the
[bosonic logical-frontier comparison](bosonic-logical-frontier.md).

The heat envelope and Mehler/theta normalizations are established in
[Matsuura, Yamasaki and Koashi, PRA **102**, 032408 (2020),
Approximation 3 and Sec. V](https://arxiv.org/html/1910.08301v4).
The exact symmetric Gram embedding is explicit in
[Koudia and Chatzinotas, arXiv:2608.08051v1,
Sec. II.G--H](https://arxiv.org/html/2608.08051v1).
The arguments below specialize those ingredients to uniform
exponential-moment and cutoff bounds. No new-code or priority claim
is made.

## Raw convention, normalization and a finite lattice remainder

Use $[Q,P]=i$, $N=(Q^2+P^2-1)/2$, $L=\sqrt\pi$ and the equally
weighted raw distributions

$$
C_\ell(q)=\sum_{m\in\mathbb Z}\delta(q-(2m+\ell)L),
\quad
A_\delta=(e^{-\delta N}C_0,\ e^{-\delta N}C_1),
\quad
G_\delta=A_\delta^\dagger A_\delta,
\quad
V_\delta=A_\delta G_\delta^{-1/2}.
\tag{HG1}
$$

The columns of $A_\delta$ are not individually renormalized before
forming $G_\delta$. Their common raw convention is independent of
$\delta$. A convention using $N+1/2$ instead of $N$ has an additional
scalar factor that must be retained when comparing different
envelope parameters. Ideal combs are distributions, not normalized
physical input states.

For $\tau>0$, the oscillator kernel is

$$
K_\tau(x,y)=\langle x|e^{-\tau N}|y\rangle
=\frac{e^{\tau/2}}{\sqrt{2\pi\sinh\tau}}
\exp\!\left[-\frac{(x^2+y^2)\cosh\tau-2xy}{2\sinh\tau}\right].
\tag{HG2}
$$

Consequently, putting $c_\delta=e^\delta/\sqrt{2\pi\sinh(2\delta)}$,

$$
(G_\delta)_{\ell j}
=c_\delta\!
\sum_{\substack{k\equiv\ell\ ({\rm mod}\ 2)\\
                 l\equiv j\ ({\rm mod}\ 2)}}
\exp\!\left[-\frac\pi4
 \{\tanh\delta\,(k+l)^2+\coth\delta\,(k-l)^2\}\right].
\tag{HG3}
$$

These positive sums converge absolutely. They also give a Hilbert-space
definition of the heat-smoothed columns: finite spatial comb sums are
Cauchy because the omitted/omitted Gram sums tend to zero.
All formulas involving $G_\delta^{-1/2}$ assume a certified positive
lower eigenvalue. That is verified quantitatively below rather than
inferred from separately normalizing two columns.

Here is the explicit remainder used by the replay. Define

$$
a_\delta=\frac\pi2\tanh\delta,\qquad
S(a)=1+\sqrt{\pi/a},\qquad
T(J,a)=\frac{2e^{-a(J+1)^2}}{1-e^{-a(2J+3)}}.
\tag{HG4}
$$

The exponent in (HG3) is at least
$a_\delta(k^2+l^2)$.
The full one-dimensional sum obeys
$\sum_{k\in\mathbb Z}e^{-ak^2}\le S(a)$ by the Gaussian integral.
For the omitted positive integers, successive terms have ratio at
most $e^{-a(2J+3)}$; including negative integers gives
$\sum_{|k|>J}e^{-ak^2}\le T(J,a)$.
A union bound on which of $|k|,|l|$ exceeds $J$ proves that each
entry's omitted positive contribution is at most

$$
0\le (G_\delta-G_{\delta,J})_{\ell j}
\le 2c_\delta S(a_\delta)T(J,a_\delta).
\tag{HG5}
$$

The matrix remainder need not be bounded entrywise as a positive
matrix; the stated positive entry bounds are sufficient for the
interval principal-minor test used below.

## Uniform exponential moments and source-prefix normalization

Let $0<t<2\delta$ and $\eta=\delta-t/2>0$.
The already-smoothed Hilbert-space columns satisfy
$A_\delta=e^{-(t/2)N}A_\eta$.
Thus $A_\delta$ lies in the domain of $e^{tN/2}$ and

$$
V_\delta^\dagger e^{tN}V_\delta
=G_\delta^{-1/2}G_\eta G_\delta^{-1/2}.
\tag{HG6}
$$

This is an operator identity on the logical qubit, not a basis-state
norm ratio. If a rational $b_t$ is certified to satisfy
$b_tG_\delta-G_\eta\ge0$, then for every normalized logical input,
including one entangled with a reference,

$$
\operatorname{Tr}(e^{tN}V_\delta\rho_LV_\delta^\dagger)\le b_t,
\qquad
\Pr(N>K)\le b_te^{-t(K+1)}.
\tag{HG7}
$$

For a real symmetric $2\times2$ matrix, nonnegative diagonals and
determinant certify positivity. The replay uses interval lower
diagonal bounds and the largest possible absolute off-diagonal
entry, so the condition is sufficient for every matrix in the
enclosure. It does not substitute a floating eigenvalue for this test.

There is also a uniform mean-energy bound from the same calculation.
For the integer spectrum $n\ge0$,
$e^{tn}\ge1+n(e^t-1)$, hence

$$
V_\delta^\dagger NV_\delta\le
\frac{b_t-1}{e^t-1}I_L.
\tag{HG8}
$$

The small positive $t$ used for (HG8) need not be the larger exponent
used for a useful tail. This avoids confusing equal basis energies
with an energy bound on arbitrary logical superpositions.

Let $\Pi_M=\sum_{n=0}^M|n\rangle\langle n|$ and suppose (HG7) gives
the uniform source bound $p_M<1$. Set

$$
H_M=V_\delta^\dagger\Pi_MV_\delta\ge(1-p_M)I_L,\qquad
V_{\delta,M}=\Pi_MV_\delta H_M^{-1/2}.
\tag{HG9}
$$

This is the exact polar-normalized Fock prefix, an isometry.
For every logical/reference purification,
$V_\delta^\dagger V_{\delta,M}=H_M^{1/2}\ge\sqrt{1-p_M}I_L$,
so the encoded states differ in trace distance by at most $\sqrt{p_M}$.
Since $\Pi_M$ commutes with $N$ and $e^{tN}$,
its mean energy and exponential moment are at most
$E/(1-p_M)$ and $b_t/(1-p_M)$, respectively, if $E$ bounds the
original code energy. Every prefix-output tail below includes this
moment inflation.

(HG9) concerns an exact prefix and exact Gram correction. Numerically
approximating its Fock coefficients or inverse square root requires
additional operator-error enclosures. Those errors are not removed by
the photon-tail bound and are not included in the numerical tail
budget reported here.

## Positive-kernel propagation through Gaussian displacement noise

For $z>1$ put $u=1-z^{-1}\in(0,1)$. A positive coherent-state identity,
understood as a quadratic-form identity on its moment domain, is

$$
z^N=\frac1z\int_{\mathbb C}\frac{d^2\alpha}{\pi}
 e^{u|\alpha|^2}|\alpha\rangle\langle\alpha|.
\tag{HG10}
$$

To verify it, take Fock matrix elements. The angular integral removes
off-diagonal terms; the $n$th diagonal integral is
$z^{-1}(1-u)^{-n-1}=z^n$.
Positivity permits monotone truncation of the integral.

Let $\mathcal N_\Sigma$ add a centered real Gaussian displacement
$\xi=(x,y)$ of covariance $\Sigma\ge0$, with
$D(\xi)=e^{i(yQ-xP)}$. For
$r=(\sqrt2\operatorname{Re}\alpha,\sqrt2\operatorname{Im}\alpha)$,
averaging the translated coherent-state weight in (HG10) gives

$$
\mathbb E_\xi e^{u\|r+\xi\|^2/2}
=\frac{\exp[\tfrac u2r^T(I-u\Sigma)^{-1}r]}
 {\sqrt{\det(I-u\Sigma)}},
\qquad I-u\Sigma>0.
\tag{HG11}
$$

If $\Sigma\le vI$ and $d=1-v(z-1)>0$, then
$(I-u\Sigma)^{-1}\le(1-uv)^{-1}I$ and
$\det(I-u\Sigma)^{-1/2}\le(1-uv)^{-1}$.
This bounds the positive integral pointwise by the isotropic one.
Evaluating that radial integral with (HG10) proves

$$
\mathcal N_\Sigma^\dagger(z^N)\le
d^{-1}R^N,\qquad
R=1+\frac{z-1}{d},\qquad d=1-v(z-1)>0.
\tag{HG12}
$$

There is equality for $\Sigma=vI$.
For example, the prefactor follows by writing
$u'=u/(1-uv)$ and $R=(1-u')^{-1}$; it is
$R/[z(1-uv)]=d^{-1}$.
This proof uses a positive kernel, not exponentiation of
noncommuting quadratic-form inequalities.
If $R\le e^t$ and the input moment is bounded by $b_t$,
then the output moment at $z$ is at most $d^{-1}b_t$ and its
number tail above $K$ is at most $d^{-1}b_tz^{-(K+1)}$.

For the standard two-slot switch of independent
$x\sim N(0,a)$ and $y\sim N(0,b)$, tracing the control gives the
serial displacement mixture with covariance $\operatorname{diag}(a,b)$.
The target photon moment therefore obeys (HG12) with
$v=\max(a,b)$ even when the control is retained coherently.
It bounds the overflow probability of the complete joint
reference/control/target state. No control or gauge measurement is
inserted into the recovery interface.

## A valid squeezing bound

Let $S_g^\dagger QS_g=Q/g$,
$S_g^\dagger PS_g=gP$, and
$\kappa=\max(g^2,g^{-2})$.
For an input exponent $t>0$ define
$\nu_t=\tfrac12\coth(t/2)$.
For an output $z>1$, set

$$
C_{t,g}=\operatorname{diag}(\nu_t/g^2+1/2,\nu_tg^2+1/2),
\qquad
K(t,z,g)=
\frac1{(1-e^{-t})z\sqrt{\det[I-(1-z^{-1})C_{t,g}]}}.
\tag{HG13}
$$

It is finite when
$(1-z^{-1})(\kappa\nu_t+1/2)<1$, equivalently
$\kappa(z-1)/(z+1)<\tanh(t/2)$.
Then, for every positive input with a finite moment at $t$,

$$
\operatorname{Tr}(z^NS_g\rho S_g^\dagger)
\le K(t,z,g)\operatorname{Tr}(e^{tN}\rho).
\tag{HG14}
$$

Here is the operator justification. Initially on finite Fock spans
put $A=z^{N/2}S_ge^{-tN/2}$.
Its squared Hilbert--Schmidt norm, computed by positive summation, is
$\operatorname{Tr}(z^NS_ge^{-tN}S_g^\dagger)$.
The normalized thermal state
$(1-e^{-t})e^{-tN}$ has quadrature covariance $\nu_tI$.
After squeezing its Husimi covariance is exactly $C_{t,g}$.
The positive integral (HG10) and an ordinary Gaussian integral
therefore give $\|A\|_{\rm HS}^2=K(t,z,g)$.
Finiteness supplies a bounded Hilbert--Schmidt extension of $A$.
Apply it to the positive trace-class weighted state
$e^{tN/2}\rho e^{tN/2}$ to obtain (HG14), first by finite cutoffs
and then by positivity. Fourier rotations commute with $N$ and
preserve every such moment.
For $g=1$, (HG13) reduces to $1/(1-e^{\log z-t})$ when $\log z<t$,
which is a useful normalization check.

Mean energy is a separate ledger. The valid quadratic-form inequality is

$$
\operatorname{Tr}(NS_g\rho S_g^\dagger)
\le\kappa\operatorname{Tr}(N\rho)+(\kappa-1)/2
\tag{HG15}
$$

for normalized $\rho$. It is not used to assert an exponential
operator inequality. For an unnormalized state, the last term is
multiplied by its trace.

## A closed rational interval certificate

The [standalone replay](../checks/architecture/verify_heat_gkp_tails.py)
certifies the following one operating point without floating
quadrature or a sampled photon histogram:
$\delta=1/4$, moment exponent $t=1/4$, and source prefix $M=128$.
It evaluates the raw Gram matrices using the box $|k|,|l|\le20$
and (HG5). Its Gershgorin lower bound is greater than $3/5$.
It finds a rational $b_{1/4}<2$ satisfying the full matrix
inequality in (HG6)--(HG7). A separate exponent $1/1024$ in
(HG8) certifies $E<117/50$; the exact polar prefix obeys the
same displayed energy and moment ceilings after its small inflation.

All interval endpoints are dyadic rationals with 192 fractional bits.
The replay encloses $\pi$ using
$16\arctan(1/5)-4\arctan(1/239)$ and alternating rational series.
Negative exponentials are range-reduced to an argument in $[-1/32,0]$,
bounded between the even Taylor partial sum of degree 24 and that
sum minus its next term, then repeatedly squared.
Positive exponentials use reciprocals. Integer square roots enclose
square roots. Every elementary operation rounds outwards to the
dyadic grid. Principal-minor checks and final comparisons use
fractions; decimal display is not an input to certification.

The reported strict bounds below hold for every logical input,
including reference-entangled inputs. Output bounds cover both the
original heat code and its exact polar Fock prefix.

| Quantity and declared operation | Certified strict upper bound |
| --- | --- |
| Original and polar-prefix moment at $t=1/4$ | $2$ |
| Original and polar-prefix mean photon number | $117/50$ |
| Original input overflow above $M=128$ | $2\times10^{-14}$ |
| Switch target overflow above $K=128$, $a=b=1/2$ | $1.36\times10^{-10}$ |
| $g=1/2$ pre-noise squeezed overflow above $K=512$ | $2.63\times10^{-10}$ |
| Aligned ordinary overflow above $K=1024$ before undoing the squeeze | $2.04\times10^{-10}$ |
| Restored aligned ordinary overflow above $K=128$ | $1.29\times10^{-10}$ |
| Combined input-prefix and switched-output cutoff trace distance | $1.2\times10^{-5}$ |

For clarity, the exact composition choices are:

* For the switched marginal, use $v=1/2$, $z=6/5$,
  $d=9/10$, $R=11/9<e^{1/4}$ in (HG12).
* Before the ordinary noise calls, use $g=1/2$, $z=21/20$
  in (HG13). Its condition holds and the replay certifies
  $K(1/4,21/20,1/2)<1218/125$.
* The two Fourier-aligned calls have total one-axis variance
  $a+b=1$ before the squeeze is undone. With $z=41/40$,
  (HG12) has $d=39/40$ and $R=40/39<21/20$.
  Substituting $v=1/2$ for this intermediate would be incorrect.
* After undoing the known squeeze, the net one-axis variance is
  $g^2(a+b)=1/4$. With $z=6/5$, use $d=19/20$ and
  $R=23/19<e^{1/4}$.

The aligned circuit is the calibrated two-call protocol in
[the logical-frontier component](bosonic-logical-frontier.md).
All moment-linear output bounds use
$b_{1/4}/(1-p_M)$ for the polar prefix.
The mean-energy bounds include the same prefix correction.

These two fixed mathematical circuits fit a conservative common
peak **oscillator ensemble-mean** cap of $5679/500=11.358$ photons:
the ordinary bound is
$\kappa(E_{\rm prefix}+1/2)-1/2+(a+b)/2
=4(E_{\rm prefix}+1/2)$.
The replay checks the cap using unrounded rationals, before
reporting the energy ceiling in the table.
The switch itself has the simpler cap $E_{\rm prefix}+1/2<71/25$.
Thus the common admissibility cap is not equality of realized peaks
or an optimized encoder comparison. In any optimized comparison
the switched protocol may also spend its unused budget on known
input controls or a different permitted code.

## From cutoff control to a recovery calculation

For the complete joint output, project only oscillator number
onto $0,\ldots,K$ and replace overflow by an orthogonal erasure
symbol while retaining the full control.
If its overflow probability is $p$, gentle projection and the
replacement block give trace-distance error at most
$\sqrt p+p/2$.
Compare the original code output to the polar-prefix output using
(HG9), then apply this output cutoff to the prefix. Consequently

$$
\epsilon_{\rm source+output}
\le\sqrt{p_M}+\sqrt{p_{\rm prefix,out}}+
p_{\rm prefix,out}/2<1.2\times10^{-5}
\tag{HG16}
$$

at the declared switched operating point.
Every adjoint-recovered Bell projector is an effect between zero
and identity, so this controls the change in any fixed recovery's
Bell objective and the optimal deterministic recovery value.
For accepted recovery, both accepted Bell probability and
acceptance have such an additive error; conditional-fidelity
uncertainty must be divided by the actual positive acceptance.
It is not enough to propagate a variance alone.

The finite recovery SDP and its acceptance constraints are owned by
[the logical-frontier component, (BL32)--(BL34)](bosonic-logical-frontier.md).
Here $K=128$ gives 129 retained oscillator states plus erasure.
Keeping a qubit control produces a normalized logical Choi matrix
of dimension $2\cdot2\cdot130=520$.
The tail certificate makes a full-coherent finite-output comparison
well defined; no gauge or control readout is imposed to reduce that
dimension.

No recovery fidelity, numerical SDP optimum, interval Choi matrix
or advantage is asserted by this replay. A completed screen still
needs certified Fock-prefix coefficients and Gram arithmetic,
channel-matrix assembly, numerical residual/rounding bounds and
primal/dual feasible recovery witnesses. Those errors must be
added to (HG16). Gaussian quadrature convergence by itself is not
such a certificate.

The controller assumptions are public calibrated Gaussian calls
and the explicitly supplied known rotations/squeeze.
Their finite duration, gate faults, pump work, storage/capture,
code preparation, decoder and helper/reset costs remain to be
established for a device. The common number cap is not a bound on
total apparatus energy or time. The heat state and its abstract
isometry are not an available native encoder merely because their
tails are certified. All actual ancillary transfer or bypass
controls supplied to either processor remain admissible for the
ordinary comparison. No global ordinary-dominance, capacity or
native coherent-order claim follows from this fixed-code
certification component.
