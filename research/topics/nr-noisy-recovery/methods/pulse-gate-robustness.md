# Unknown-axis pulse gates: finite-penalty existence and mean-query utility

This is a proof component of [NR-R21](../unknown-pulse-gates.md#nr-r21),
using its existing exact support and common causal dual. It establishes
an unquantified robustness statement in that oracle model, with no
certified numerical error tolerance or physical noise budget.

## Service, score and continuous angle family

Keep the original continuously unknown orthonormal qubit frame
$A=\boldsymbol a\cdot\boldsymbol\sigma$,
$B=\boldsymbol b\cdot\boldsymbol\sigma$. Each indivisible uncontrolled
query is $e^{-iaA}$ or $e^{-ibB}$, with its real angle and name chosen
classically before the call. Arbitrary known instruments, ancillary
memory, routing and classical adaptation are allowed. Coherent name or
angle selection, controlled queries, simultaneous $A+B$ access and
uncharged oracle-related advice are outside this interface. Charge
training and probes, including calls before payload arrival. A batch
sharing a learned frame or program needs its own amortized analysis.

The target is $U=I/\sqrt2-i(A+B)/2$. For every final accepted fine
operator $K$, including known final recovery and all records, define
on a normalized Bell input with passive reference

$$
p(K)=\frac{\operatorname{Tr}K^\dagger K}{2},\qquad
q(K)=\frac{|\operatorname{Tr}(U^\dagger K)|^2}{4},\qquad
b(K)=p(K)-q(K),\qquad u(K)=q(K)-\lambda b(K).
$$

These are launched accepted, good and bad masses, not conditional
fidelities. This Bell score is not a worst-input or diamond-norm claim.
For a fixed ordered cross-axis two-query record $\theta=(a,b)$, the
linked operator is linear in its 64-dimensional physical comb vector
$w$. Haar-average the quadratic forms over the common $SO(3)$ frame,
writing their Hermitian matrices as $P_\theta,G_\theta$ and
$L_\theta=P_\theta-G_\theta\ge0$. Haar averaging is a mathematical
witness against a uniformly valid unknown-frame service; it does not
supply a fresh-frame laboratory prior. An averaged bound need not hold
separately at every frame.

Angles lie on a compact torus modulo $\pi$, since that shift contributes
only a global phase to an uncontrolled call. The three matrices are
continuous in both angles, including zero-sine and zero-cosine endpoints.

## A finite common penalty exists

Let $B_0=I_F\otimes Y>0$ be the existing exact $13/20$ certificate,
whose upstream price is $W_0=(13/40)I$. Fix any

$$
\frac{13}{20}<t<\frac34,\qquad
B_t=\frac{20t}{13}B_0,\qquad W_t=\frac t2 I.
$$

Scale the same intermediate positive causal duals by $20t/13$.
At nondegenerate angles, $\ker L_\theta$ is precisely the old
five-dimensional universal exact-success support. Indeed the Bell
defect is continuous and nonnegative in the frame, so zero Haar-average
defect implies zero defect at every frame. Each linked fine map is then
collinear with $U$ everywhere; the necessary-support proof (AP20)--(AP21)
identifies this kernel. The exact certificate therefore gives, for
$w\in\ker L_\theta$,

$$
\langle w,(B_t-G_\theta)w\rangle
\ge\left(\frac{20t}{13}-1\right)
       \lambda_{\min}(B_0)\|w\|^2>0
\quad (w\ne0).
\tag{RU1}
$$

At a zero-sine endpoint the corresponding axis is absent. At a
zero-cosine endpoint reversing that axis changes its query only by a
global sign. Hold the other axis fixed and respectively vary or
sign-flip the missing axis. An exact fine map would have to be
proportional to different nonparallel target matrices, so it is zero.
Thus $G_\theta$ annihilates $\ker L_\theta$ at these endpoints and
$B_t$ is strictly positive there. This also covers simultaneous
endpoints without dividing by a sine or cosine.

On the compact set of angle pairs and unit complex comb vectors, set
$F(\theta,w)=\langle w,(B_t-G_\theta)w\rangle$. It is strictly positive
on the closed zero-defect subset. If no finite common $\lambda$ made
$B_t-G_\theta+\lambda L_\theta$ positive semidefinite at every angle,
choose violating unit $(\theta_n,w_n)$ for $\lambda_n\to\infty$.
Boundedness of $F$ forces
$\langle w_n,L_{\theta_n}w_n\rangle\to0$. A convergent subsequence
limits to the zero-defect subset, where $F>0$, whereas each violation
requires $F<0$. This is a contradiction. Consequently some finite
$\lambda_t$, increased to at least three if necessary, satisfies

$$
G_\theta-\lambda_t L_\theta\preceq B_t
\qquad\text{for every real angle pair.}
\tag{RU2}
$$

This proves existence, not a useful value for $\lambda_t$. It assumes
no uniform positive eigenvalue of $L_\theta$ outside its kernel.
Such a physical-coordinate gap actually fails near endpoints: the unit
Pauli tensor $|I\rangle\rangle|\sigma_1^*\rangle\rangle
|\sigma_2^*\rangle\rangle/\sqrt8$ is orthogonal to the exact support,
but its defect at $a=b=\epsilon$ is $(2/15)\sin^4\epsilon$.
Its delivered mass also vanishes, so it does not invalidate (RU2).

## Adaptive instruments and the scalar upstream price

Unlike the exact support inequality, (RU2) holds on the full
64-dimensional comb space. Sum or integrate it through the existing
positive causal chain at the actual temporal stages. The same scaled
$Y,Z$ work for every first or second angle, including choices depending
on earlier classical records. Reverse first-query type renames the
ports and has the same scalar upstream price. Both first-query types
share the initial normalization; there is no extra factor two.
Countable or continuous records use the finite-dimensional positive
instrument measure from the exact proof, without an exactness-induced
record-support restriction.

Let $R$ be the effect of ever invoking a first query and
$r=\operatorname{Tr}R/2$. It precedes all oracle access and is frame
independent, although it may depend on the input. Keeping this initial
normalization instead of replacing it by identity yields

$$
g_2\le\operatorname{Tr}(W_tR^T)=tr,
\tag{RU3}
$$

where $g_2$ is Haar-average launched utility from accepted two-query
cross-axis records. Input-dependent prefilters are included without
pretending their conditional inputs have a new universal promise.

Missing-axis branches cause no exception. Even grant the queried axis
for free. Averaging the target's normalized Choi vector over the
perpendicular unqueried axis gives eigenvalues $3/4,1/8,1/8,0$.
Any accepted branch using one or two calls to only that axis therefore
has $q\le3p/4$ on this conditional average. Its utility is nonpositive
for $\lambda\ge3$. Zero-query branches obey the stronger $q\le p/2$.
Endpoint sign-pair averaging likewise gives $q\le3p/4$.
Dropping these nonpositive contributions leaves positive causal
deficits, so (RU3) also bounds useful two-query mass. It rules out a
uniformly better universal-frame guarantee, not performance on a
particular known or restricted frame.

## All-attempt mean-query utility

Allow aborts, stopping and more calls. Average both total utility
$\overline{\mathcal U}$ and query count $\overline N$ over the same
frame measure on the Bell input, retaining failed, training and probe
calls. Let $p_2$ be accepted mass at query two after dropping zero- and
one-query branches of nonpositive utility, $g_2$ its launched utility,
and $p_3$ accepted mass at query three or later. Then

$$
g_2\le tr,\qquad g_2\le p_2,\qquad p_2+p_3\le r,\qquad
\overline{\mathcal U}\le g_2+p_3,\qquad
\overline N\ge r+p_2+2p_3.
$$

For $0<t<1$, these imply

$$
\begin{aligned}
\overline N-(3-t)\overline{\mathcal U}
&\ge r+p_2+(t-1)p_3-(3-t)g_2\\
&\ge tr+(2-t)p_2-(3-t)g_2\\
&\ge tr-g_2\ge0.
\end{aligned}
\tag{RU4}
$$

Infinite means satisfy the bound trivially; countable tails use monotone
convergence. Positive ratio of averaged utility to averaged query cost
is at most $1/(3-t)$. Hence no ordinary protocol can beat that rate
uniformly on all frames. This is neither an average of framewise
ratios nor a per-pure-input query-cost bound. Losing an unknown payload
is terminal without a separate restoration or factory interface.

The native one-shot instrument has $p=q=8/9$ and $N=2$, giving ideal
utility per query $4/9>1/(3-t)$ since $t<3/4$. If its accepted Bell
fidelity is at least $1-\varepsilon$ uniformly, with acceptance still
exactly $8/9$ and count still two, separation remains whenever

$$
\varepsilon<
\frac{1-9/[4(3-t)]}{1+\lambda_t}.
\tag{RU5}
$$

This is a mathematically nonzero neighborhood under those specific
conditions. A numerical tolerance requires a quantitatively proved
$\lambda_t$, and changes in acceptance or cost require a fresh ledger.

An ordinary deterministic two-query product remains an essential
baseline: $e^{-isB}e^{-isA}$ with $\tan(2s)=\sqrt2$ has
frame-independent Bell fidelity $(2+\sqrt3)/4\simeq0.933013$.
Its utility forbids reusing $13/20$ at
$\lambda<(9+7\sqrt3)/5$, or $3/4$ at $\lambda<1+\sqrt3$.
It is not claimed to be optimal. The old exact-success certificate
cannot simply be relabelled as an approximate-output bound.

The compactness and mean-utility arguments above are analytic; the
existing exact support/dual replays verify their stated ingredients.
No numerical penalty, source clock/noise model, approximate ordinary
optimum, new exact guard, Lean audit or hardware advantage is certified.
The [physical selector component](pulse-selector-ports.md) records the
stronger optical ports and measured-service requirements that must be
settled before seeking a quantitative matrix-polynomial certificate.
