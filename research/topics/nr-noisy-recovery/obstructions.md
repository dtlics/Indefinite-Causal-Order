# Recovery boundaries and scoped obstructions

[Topic](README.md) · [Local-noise recovery](theorem.md) · [Global replacement noise](global-noise.md)

The results below retain useful limits on the recovery task. They do not
negate its fresh-frame average theorem, and they do not rule out every
other higher-order protocol.

<a id="nr-r03"></a>

## NR-R03 — Local output noise does not give a uniform frame guarantee

Let $D=2^n$, choose the allowed frame $U=I$, and set $A=X_1$,
$B=Y_1$, with identity on the remaining $n-1$ qubits. The target is
$BA$. For physical Pauli errors $P,Q$, the minus-switch Kraus
operator, without its probability amplitude, is

$$
K_{PQ}=\frac{QBPA-PAQB}{2}.
$$

Each branch is either zero or the unitary $QBPA$, depending on whether
$PA$ and $QB$ commute or anticommute. Its target Bell overlap is one
only for $P=Q$. Among equal errors, the first-qubit factor must be
$I$ or $Z$ to be accepted. This gives exact counterexamples.

### Independent phase flips

For $\Phi_\eta=(1-\eta)\mathrm{id}+\eta\operatorname{Ad}_Z$ at every
output site, put $c_\eta=(1-\eta)^2+\eta^2$. On the first qubit the
minus flag requires matching error bits, while all spectator phase
errors appear in both orders. Thus the accepted operation is exactly

$$
M_-=
c_\eta\operatorname{Ad}_{YX}\otimes
(\Phi_\eta\circ\Phi_\eta)^{\otimes(n-1)}.
$$

Success is input independent, and the full-system fidelities are

$$
p_-=c_\eta,\qquad
F_{-,\mathrm{cond}}=c_\eta^{\,n-1},\qquad
F_{\mathrm{bare}}=c_\eta^n.
$$

At $\eta=c/n$, both fidelities tend to $e^{-2c}$, and their difference
is $O(1/n)$. This concerns the entire physical register, not a chosen
logical subsystem.

### Independent depolarization

For $\operatorname{Dep}_\eta=(1-\eta)\mathrm{id}+\eta\Omega_2$, define

$$
a_0=1-\frac{3\eta}{4},\quad a=\frac{\eta}{4},\quad
c_0=a_0^2+3a^2,\quad
s=1-\frac{3\eta^2}{4},\quad
\ell=1-2\eta+\frac{3\eta^2}{4}.
$$

The spectator expectation of the Pauli commutation sign is $s$;
the corresponding first-qubit sign with $X,Y$ is $\ell$.
Consequently exact summation of the zero-or-unitary branches gives

$$
p_-=\frac{1+\ell s^{\,n-1}}2,\qquad
q_-=(a_0^2+a^2)c_0^{\,n-1},\qquad
F_{-,\mathrm{cond}}=\frac{q_-}{p_-},\qquad
F_{\mathrm{bare}}=c_0^n.
$$

The good-weight expression requires equal spectator errors, contributing
$c_0$ per spectator, and an $I$ or $Z$ equal error on the first
qubit, contributing $a_0^2+a^2$. At $\eta=c/n$, success tends to one
and both fidelities tend to $e^{-3c/2}$.

For every frame, bare composition has fidelity at least the no-error
weight: $(1-\eta)^{2n}$ for phase flips and
$(1-3\eta/4)^{2n}$ for depolarization. Comparing that ordinary
worst-frame lower bound with the switch value at $U=I$ proves

$$
\limsup_n\left[
\inf_U F_{\mathrm{switch},U}
-
\sup_{\mathrm{ordinary}}\inf_U F_{\mathrm{ordinary},U}
\right]\le0
$$

under either $1/n$ scaling above. Bare composition always succeeds, so
it satisfies any acceptance floor imposed by this switch.

At a fixed positive depolarizing rate, both fidelities in this example
decay exponentially and their ratio has a finite limit. The standard
unencoded module therefore supplies neither a uniform-frame constant
advantage nor a fixed local fault-rate threshold. The theorem in
[NR-R01](theorem.md#nr-r01) instead uses a specified fresh-frame average.
This obstruction does not rule out another protocol, extra queries,
protected encodings, or a different promise.

<a id="nr-r04"></a>

## NR-R04 — Full-support noisy queries cannot give exact unknown-unitary recovery

### Finite-dimensional global replacement queries

This statement uses **global replacement noise**, not the local model of
NR-R01. For $0<\gamma\le1$, every supplied box
$G_U=(1-\gamma)\operatorname{Ad}_{V_U}+\gamma\Omega_D$ obeys the
completely positive order bounds

$$
\gamma\Omega_D\le_{\mathrm{CP}}G_U
\le_{\mathrm{CP}}c\Omega_D,\qquad
c=(1-\gamma)D^2+\gamma.
$$

The upper bound follows because the Choi operator of a unitary channel
has its sole nonzero eigenvalue $D$, whereas
$J_{\Omega_D}=I/D$, so
$\operatorname{Ad}_{V_U}\le_{\mathrm{CP}}D^2\Omega_D$.

Let $M_U$ be the successful subchannel of a fixed $Q$-query protocol.
It may use arbitrary memory, encodings, data bypass, finite offline
programs, classical adaptive choices, or any admissible positive
multilinear $Q$-slot process. Its initial resources are frame independent,
and all unknown-box calls used for offline programs count in $Q$.
Let $M_*$ use $\Omega_D$ in every slot.
Positivity and multilinearity give

$$
\gamma^Q M_*\le_{\mathrm{CP}}M_U\le_{\mathrm{CP}}c^Q M_*.
$$

The reference $M_*$ is independent of $U$. If
$M_U=p_U\operatorname{Ad}_{W_U}$ were exact for every frame, its Choi
operator would have rank at most one on the target line. The lower
inequality places the support of $J_{M_*}$ inside every such line.
Two inequivalent target channels have distinct lines and zero
intersection. Hence $M_*=0$, and the upper inequality forces $M_U=0$
for all $U$.

No finite-query protocol therefore exactly realizes a nonconstant
unknown target-unitary family with positive heralded yield from these
full-support noisy boxes. The conclusion includes the related target
$W_U=B_UA_U$, not just the full unitary group.

For a protocol with a classical or recorded stopping instrument, suppose
each successful run uses finitely many calls. Its total successful Choi
operator is a positive sum of its $Q$-call stopping contributions.
If that sum has rank one on the target line, every summand has support
on the same line. Apply the finite-$Q$ argument to each contribution:
all are zero. Thus almost-sure finite stopping does not restore exact
positive-yield implementation; finite expected cost is unnecessary
for this exact no-go statement.
This stopping argument uses a positive CP sum of call-count outcomes; it
does not assert a theorem about coherent interference across different
query counts.

A simple quantitative consequence is available for a fixed $Q$.
Choose two frames with orthogonal target Bell vectors. Normalized
successful Choi states each contain the same normalized
$\tau=J_{M_*}/\operatorname{Tr}J_{M_*}$ with weight at least
$(\gamma/c)^Q$. One target has overlap at most $1/2$ with $\tau$.
For that frame the conditional Bell infidelity is at least
$(\gamma/c)^Q/2$. This is a weak support bound, not an optimal
purification-complexity theorem.

Known fixed targets, exposed noise records, frame-dependent free advice,
and coherent dilation access need not obey these premises. The result
does not prohibit approximate success with an exactly preserved failure
branch.

<a id="nr-r04-gaussian-displacement"></a>

### Gaussian displacement noise: no exact heralded code recovery

There is an infinite-dimensional physical extension for a **specified
two-slot switch**, with a different access scope from the finite-query
statement above. Let $S$ be one bosonic mode, with
$D(\alpha)=\exp(\alpha a^\dagger-\alpha^*a)$, and let the two independent
channels be

$$
\mathcal A(\rho)=\int_{\mathbb C}p_A(\alpha)
 D(\alpha)\rho D(\alpha)^\dagger\,d^2\alpha,
\qquad
\mathcal B(\rho)=\int_{\mathbb C}p_B(\beta)
 D(\beta)\rho D(\beta)^\dagger\,d^2\beta.
$$

Both displacement laws are Gaussian with strictly positive real
$2\times2$ covariance matrices. Their means may be nonzero. Thus both
densities are positive on the full complex plane; singular
one-quadrature noise and a noiseless slot are outside this statement.
Use each channel once in the standard channel switch, with an independent
control fixed to $|+\rangle$. Displacement records are inaccessible.
The receiver may keep and jointly process the output control and signal,
use independent ancillas, non-Gaussian operations, measurement and
feedforward, and herald a successful branch.

For every normalizable signal state, the joint output has full support
on $\mathbb C^2_C\otimes\mathcal H_S$. More generally, for any state
$\rho_{RS}$ with a finite-dimensional passive reference $R$, the output
is faithful on
$\mathbb C^2_C\otimes\operatorname{supp}(\rho_R)\otimes\mathcal H_S$:
it has no nonzero vector of zero expectation on that space.

To prove this, put $\delta=\alpha+\beta$ and
$\chi=\operatorname{Im}(\beta\alpha^*)
=\operatorname{Im}(\delta\alpha^*)$. The Weyl products are

$$
D(\beta)D(\alpha)=e^{i\chi}D(\delta),\qquad
D(\alpha)D(\beta)=e^{-i\chi}D(\delta).
$$

Consequently each displacement pair leaves the control in

$$
|c_\chi\rangle=
\frac{e^{i\chi}|0\rangle+e^{-i\chi}|1\rangle}{\sqrt2}
$$

and acts on the signal by $D(\delta)$. Let $w(\delta)$ be the density
of the total displacement and define

$$
M_\delta=\frac{w(\delta)}2
\begin{pmatrix}1&m_\delta\\m_\delta^*&1\end{pmatrix},
\qquad
m_\delta=\mathbb E[e^{2i\chi}\mid\delta].
$$

In real coordinates $(\operatorname{Re}\alpha,\operatorname{Im}\alpha)$,
the conditional covariance of $\alpha$ is
$C=(\Sigma_A^{-1}+\Sigma_B^{-1})^{-1}\succ0$. With
$\ell_\delta=(\operatorname{Im}\delta,-\operatorname{Re}\delta)$,
the conditional phase is $\chi=\ell_\delta\cdot\alpha$, so

$$
|m_\delta|=e^{-2\ell_\delta^T C\ell_\delta}<1
\qquad(\delta\ne0).
$$

Since $w(\delta)>0$, both eigenvalues
$w(\delta)(1\pm|m_\delta|)/2$ are positive for every
$\delta\ne0$. The complete reference-preserving output is

$$
\Omega_{CRS}=\int_{\mathbb C}M_\delta\otimes
 (I_R\otimes D(\delta))\rho_{RS}
 (I_R\otimes D(\delta)^\dagger)\,d^2\delta.
$$

Suppose $|\Psi\rangle=|0\rangle|u\rangle+|1\rangle|v\rangle$
has zero expectation in $\Omega$. Positivity bounds each integrand below
by $\lambda_{\min}(M_\delta)$ times the sum of the corresponding
$u$ and $v$ expectations in the displaced $\rho_{RS}$. These
nonnegative expectations must therefore vanish almost everywhere.
No uniform lower bound on $\lambda_{\min}(M_\delta)$ is needed;
the exceptional point $\delta=0$ has measure zero.

The Weyl orthogonality identity, as a weak operator integral, is

$$
\int_{\mathbb C}(I_R\otimes D(\delta))\rho_{RS}
 (I_R\otimes D(\delta)^\dagger)\,d^2\delta
 =\pi\rho_R\otimes I_S.
$$

Its scalar normalization follows from
$\big(D((q+ip)/\sqrt2)\psi\big)(x)=e^{ip(x-q/2)}\psi(x-q)$:
Fourier Plancherel and integration over $q$ give
$\int d^2\delta\,|\langle u|D(\delta)|\psi\rangle|^2
=\pi\|u\|^2\|\psi\|^2$.
Spectral decomposition and Tonelli extend this to positive trace-class
states; polarization gives the displayed identity blockwise for finite
$R$. On $\operatorname{supp}(\rho_R)$ the right-hand quadratic form
is strictly positive for any nonzero vector. Hence $u=v=0$, proving
faithfulness without a Fock cutoff.

This excludes exact unambiguous readout of any two signal states by a
downstream receiver: a bounded positive effect with zero probability on
one faithful output must be zero, and cannot identify the other input.
There is also a reference-complete quantum consequence. Encode a
$k$-dimensional logical input, $k\ge2$, entirely into $S$ by a
trace-preserving encoder, and prepare a Bell pair between that input
and an inaccessible $k$-dimensional reference. Then $\rho_R=I_k/k$.
No nonzero physical normal CP trace-nonincreasing receiver branch on
$C,S$ can produce a pure Bell state on $R$ and a decoded logical output.

Indeed, refine that branch into bounded Kraus operators $L_j$. If its
output were $p|\Phi_k\rangle\langle\Phi_k|$, every vector orthogonal
to $\Phi_k$ would have zero expectation in each positive Kraus
contribution. Faithfulness forces
$(I_R\otimes L_j^\dagger)|x\rangle=0$ for all such $x$.
Thus the range of $I_R\otimes L_j$ would lie in the single entangled
line spanned by $\Phi_k$. For nonzero $L_j$, that range contains
nonzero product vectors $|r\rangle\otimes L_j|s\rangle$, which
cannot lie on a Bell line. All $L_j$ are therefore zero and $p=0$.
Tracing any receiver garbage or resolving additional success records is
already included in this CP branch. The same argument permits any
declared Bell frame, and in particular rules out exact heralded
unitary recovery of an unknown logical state.

The restriction that the input is carried entirely by the noisy signal
is essential. An input-bearing bypass memory, encoding into a protected
control, access to the random displacement record, or additional
pre/inter-query controls changes the model. Independent receiver ancillas
and arbitrary processing after this switch are already allowed. The
argument concerns every strictly positive pair of Gaussian covariances,
but supplies **no positive finite-error margin**, Gaussian-code optimum,
entanglement-breaking claim or quantum-capacity conclusion. Approximate
error correction, high-energy limits and finite-error readout utility
remain open; ideal nonnormalizable grid states are not density operators
covered by the proof. General thermal attenuators, amplifiers,
correlated noise and other physical order dilations need their own
support argument rather than an import of this displacement result.

<a id="nr-r05"></a>

## NR-R05 — Rejection, stochastic rewinding and finite-program limits

### The rejected global-noise switch branch destroys target-reference entanglement

Use the anticommuting $A,B$ and global replacement model of
[NR-R02](global-noise.md#nr-r02). The switch is prepared in control plus;
minus is accepted and plus is rejected. For one ideal slot and one
replacement slot, the plus submap is

$$
M_{A,\Omega,+}(X)=
\frac{\operatorname{Tr}(X)I+\operatorname{Tr}(AX)A}{2D}.
$$

Let $P_{A,\pm}=(I\pm A)/2$, each of rank $m=D/2$. The
measure-and-prepare channel

$$
C_A(X)=\sum_{s=\pm}\operatorname{Tr}(P_{A,s}X)P_{A,s}/m
$$

has $M_{A,\Omega,+}=C_A/2$. The same holds for $B$. For two
replacement slots,

$$
M_{\Omega,\Omega,+}
=\frac{\Omega_D+\mathrm{id}/D^2}{2}
=\frac12\left[
\frac{D+1}{D^2}T_D+\frac{D-1}{D}\Omega_D\right],
$$

where

$$
T_D(X)=D\int\langle\psi|X|\psi\rangle
|\psi\rangle\langle\psi|\,d\psi
=\frac{X+\operatorname{Tr}(X)I}{D+1}
$$

is also measure and prepare. The ideal anticommutator vanishes, so the
complete rejected map is

$$
M_+=\frac{\gamma(1-\gamma)}2(C_A+C_B)
+\gamma^2M_{\Omega,\Omega,+}.
$$

Every summand is entanglement breaking. Its input-independent probability
is $f=\gamma-(1-D^{-2})\gamma^2/2>0$; normalizing does not change
entanglement breaking.

If the unknown logical input is stored only in this target, subsequent
local processing, fresh ancillas, extra noisy-box queries, and heralded
postprocessing cannot recreate its entanglement with an inaccessible
reference. The recovered Bell fidelity for a $k$-dimensional logical
input is at most $1/k$, even on a nonzero-probability postselected
branch. Thus a rejected trial of this module is not a nondestructive
retry on the same irreplaceable input.

This target-only conclusion does not cover a code retaining a
noiseless side register. Such a register may already contain the input.
Nor does it apply automatically to the rejected branch under local
Pauli noise, which can preserve information.

### Exactly preserved failure with a finite noisy program is an offline filter

Suppose the input arrives **after** a finite-query noisy storage step
has prepared a program $\sigma_U$, and retrieval uses no additional
unknown-box calls. The CP-order argument of NR-R04 shows that all nonzero
program states have the same support $S$ and are strictly positive
there. Compress to $S$.

If a fixed retrieval instrument, after known outcome correction, has
failure map $F(\rho\otimes\sigma_U)=r_U\rho$, diagonalize any one
positive-definite $\sigma_U$. In program blocks, each failure Kraus
operator contributes a positive rank-one Choi projector with strictly
positive coefficient. The resulting data map has rank-one identity
Choi support. Every block must therefore be a scalar identity, giving

$$
F_\alpha=I_{\mathrm{data}}\otimes\langle v_\alpha|,
\qquad
F(\rho\otimes\sigma)=\rho\,\operatorname{Tr}(E\sigma),
\quad 0\le E\le I_S.
$$

If a failure program is retained, resolve an output-program basis first;
the same reasoning gives $F_\alpha=I\otimes B_\alpha$. Failure still
acts only on the program.

For success Kraus operators $S_\beta$, completeness gives
$\sum_\beta S_\beta^\dagger S_\beta=I\otimes(I-E)$.
Set $L=\sqrt{I-E}$. On its support,
$T_\beta=S_\beta(I\otimes L^+)$ defines a trace-preserving retrieval
after a program-only filter; extend it arbitrarily outside that support.
Thus the success/failure filter can be run before the data interacts.
This is a CP-processing equivalence, not a guarantee about a restricted
gate set, depth, or memory cost.

Approximate success and exactly preserved failure are compatible.
Offline programs are a legitimate option, but all program-preparation
attempts count. Independent $Q$-call trials with success $s_U$ cost
$Q/s_U$ calls on average. An accepted switch Choi state is a program,
not an already applied gate: basic Bell-projection retrieval succeeds
with probability $1/D^2$, and its other outcomes are not generally
correctable after an unknown gate. More sophisticated retrieval needs
its own resource accounting. This finite-program result does not
classify every online encoding retaining quantum memory during queries.

### A particular unitary rewinding recursion has infinite mean overhead

This statement concerns the explicit unitary random-walk recursion in
Appendix A of [Trillo, Dive and Navascués](https://arxiv.org/html/2205.01131v1),
not every quantum rewinding or inversion algorithm. Its target is a
closed qubit, with fixed repeatable unitaries $W,V$. A complete
interferometric module $Q$ has Kraus operators
$[V,W]/2$ and $\{V,W\}/2$. Write

$$
pI=\frac14[V,W]^\dagger[V,W],\qquad 0<p<1.
$$

The scalar probability follows directly by writing, up to global phases,
$W=\cos a\,I-i\sin a\,\mathbf n\cdot\boldsymbol\sigma$ and
$V=\cos b\,I-i\sin b\,\mathbf m\cdot\boldsymbol\sigma$:

$$
p=\sin^2a\,\sin^2b\,[1-(\mathbf n\cdot\mathbf m)^2].
$$

Consequently the port probabilities remain $p,1-p$ after every previous
outcome, including for a target entangled with an inaccessible reference.
Let $H$ count $Q$ modules until the walk first completes one corrected
commutator, and put $f(z)=\mathbb E z^H$. More explicitly, write the
walk's vertices as $\underline{k},\overline{k}$ for $k\in\mathbb Z$.
From $\underline{k}$ it moves to $\overline{k}$ with probability $p$
or $\underline{k+1}$ with probability $1-p$; from $\overline{k}$ it
moves to $\underline{k}$ with probability $p$ or $\overline{k-1}$
with probability $1-p$. Here $H$ is the first passage from
$\underline0$ to $\overline0$, and $g(z)$ is the generating function
for the first passage from $\underline0$ to $\underline1$.
First-step conditioning, translation/reflection symmetry and the strong
Markov property give

$$
f=pz+(1-p)zfg,\qquad g=(1-p)z+pzfg.
$$

Thus $g=(1-p)z/(1-pzf)$ and

$$
pzf^2-[1+(2p-1)z^2]f+pz=0.
$$

The solution with $f(0)=0$ is

$$
f(z)=\frac{1+(2p-1)z^2-
\sqrt{(1-z^2)[1-(2p-1)^2z^2]}}{2pz}.
\tag{1}
$$

The full recursion completes two such passages. The first-passage times
are independent copies by the strong Markov property and the fixed scalar
port probabilities, even though the target state changes. Hence, for its
total module count $N=H_1+H_2$,

$$
F(z):=\mathbb E z^N=f(z)^2.
\tag{2}
$$

$N$ excludes the deliberate long forward-evolution interval. Each $Q$
module itself contains one $W$ and one $V$ call; a module is not a single
elementary traversal. With $c=\sqrt{2(1-p)/p}$, expansion at $z=1$ yields

$$
f(z)=1-c\sqrt{1-z}+O(1-z),\qquad
F(z)=1-2c\sqrt{1-z}+O(1-z).
\tag{3}
$$

Therefore $F(1^-)=1$ but $F'(1^-)=\infty$: the recursion terminates
almost surely and has **infinite expected module count** for every
$0<p<1$. Positivity of the probability coefficients justifies identifying
the derivative limit with the first moment. At $p=1$, $N=2$;
at $p=0$, the commutator event never occurs.

The parity can be handled without treating the singularity at $z=-1$
as an independent tail. Since $N$ is even, let
$G(w)=F(\sqrt w)=\mathbb E w^{N/2}$. Equation (3) gives

$$
\sum_{j\ge0}\Pr(N/2>j)w^j
=\frac{1-G(w)}{1-w}
=2\sqrt{\frac{1-p}{p}}(1-w)^{-1/2}+O(1).
$$

In (1), the other square-root singularity in $w$ lies at
$1/(2p-1)^2>1$, or is absent when $p=1/2$. Expanding the analytic factor
at $w=1$ and using the coefficient asymptotic
$\operatorname{coeff}_{w^j}(1-w)^{-1/2}\sim1/\sqrt{\pi j}$ proves

$$
\Pr(N>m)\sim\frac{2c}{\sqrt\pi}\,m^{-1/2},\qquad
\mathbb E\min(N,m)\sim\frac{4c}{\sqrt\pi}\sqrt m.
\tag{4}
$$

In particular the smallest high-confidence cap obeys
$m_\delta\sim8(1-p)/(\pi p\delta^2)$ as the allowed terminal failure
$\delta\downarrow0$, for fixed $p$. These are asymptotic formulas, not
finite-cap confidence certificates. They are consistent with the
published fixed-confidence duration $T+O(1)$: that statement fixes the
confidence and noncommutation scale before varying the rewound time $T$.
It does not assert finite mean overhead or uniform cost as $p\downarrow0$.

### Independent module loss gives an exact delivered-success law

Assume every complete $Q$ module has an independent, state- and
port-independent survival probability $\ell$. A lost target is unusable.
The lossless outcome history of length $N$ survives with probability
$\ell^N$, so the eventual delivered-rewind probability is exactly

$$
P_{\mathrm{delivered}}=F(\ell)=f(\ell)^2,
\qquad
1-F(\ell)=2c\sqrt{1-\ell}+O(1-\ell).
\tag{5}
$$

This delivery law does not require immediate loss detection. If loss is
immediately heralded and $L$ is the index of the first failed module,
the number of attempted modules, including the failed one, satisfies

$$
\begin{aligned}
\mathbb E\min(N,L)
&=\sum_{k\ge1}\Pr(N\ge k)\ell^{k-1}\\
&=\frac{1-F(\ell)}{1-\ell}.
\end{aligned}
\tag{6}
$$

With a deterministic cap $m$, delivery is
$\sum_{n\le m}\Pr(N=n)\ell^n$, and the corresponding expected attempted
count is $\sum_{k=1}^m\Pr(N\ge k)\ell^{k-1}$. If loss is not immediately
heralded, actual scheduled hardware use needs its own stopping rule.
For example, $p=1/2$, $\ell=0.99$ gives delivered probability
$0.752744904$ and mean $24.7255096$ attempted modules under immediate
loss stopping. Source, detector and deliberate-wait losses are additional.

This is a uniform independent-erasure model, not a fit to an optical
apparatus. Port-dependent attenuation, polarization leakage, drift,
imperfect readout and environmental records require their full
instruments. A lost arbitrary input cannot be restarted; trials on fresh
prepared inputs serve a different task. Equations (1)–(6) make no
infinite-mean claim about other resetting or rewinding algorithms.

### Restored optical output and the strongest admitted ordinary controls

[Schiansky et al.](https://doi.org/10.1364/OPTICA.469109) demonstrate
$[U,V]U^n[U,V]$ for $n=1,2,3$, using polarization waveplates, a Sagnac
path control and electro-optic routing. Their successful conditional
outputs have mean state fidelity above $0.95$. Anticommutator outputs are
discarded; the adaptive correction is proposed rather than implemented.
The [archived experiment, Section IV and Appendix A](https://arxiv.org/html/2205.01122v1)
specifies the tested family

$$
U_j=e^{-i\arcsin(j/10)Z},\quad j=1,\ldots,10,
\qquad
V_k=\cos(k\pi/11)Z+\sin(k\pi/11)Y.
$$

For every member of this family, every $n$ and every input/reference,

$$
XU_j^nX=U_j^{-n}.
\tag{7}
$$

Two fixed known polarization flips therefore give an exact ordinary
echo without identifying $j$ or postselecting. This is a consequence of
the tested ensemble, not a refutation of universal unknown-axis
rewinding. The experiment's restricted sequential comparator permits
positive free waits and the designated $V$, excluding arbitrary known
waveplate controls.

The same source reports approximately $400$ ns routing rise time,
$106$, $109$ and $155$ m delays, $1.5$ dB per electro-optic pass,
$12$ dB across eight such passes at $n=3$, and another $3.5$ dB from
mirrors. Runs last $2.5$–$4.5\,\mu$s. The quoted $15.5$ dB contributions
alone correspond to $10^{-1.55}\simeq0.0282$ transmission before port
selection and other losses; this conversion is not a reported delivered
rate. Conditional tomography and separately normalized counts do not
establish an all-attempt service yield.

Other ordinary interfaces must be distinguished explicitly:

- When $V$ is known and its controlled implementation is available, the
  [known-intervention sandwich in NR-R14](backaction.md#nr-r14), with one
  intervention set to the identity, reproduces the entire commutator/
  anticommutator instrument with one unknown $U$ call. It never controls
  the unknown $U$. The actual conditional gates, delays and losses count.
- For two unknown transferable unitary slots, the
  [three-call ordinary construction in NR-R12](dispatch.md#nr-r12)
  implements their complete switch, including arbitrary reference
  coherence. It uses the sequence $U,V,U$, one clean memory of the data
  dimension and four known controlled swaps. Replacing each short $Q$
  this way preserves a capped rewinder's $T+O(m)$ timing form, with
  different physical overhead. That memory/swap interface is not supplied
  by an immobile uncontrolled target merely because coherent flight-path
  access exists.
- A genuine reciprocal reverse port can be stronger still.
  [Strömberg et al.](https://doi.org/10.1103/PhysRevResearch.6.023071)
  realize waveplate gadgets with
  $U_{\rm bw}=P U_{\rm fw}^T P^\dagger$ for a known frame $P$.
  The $2\times2$ identity $YU^TY=\det(U)U^{-1}$ shows that fixed
  endpoint controls turn one such backward traversal into the inverse
  channel. Coherently superposing directions is unnecessary for that
  task. Reverse access, its frame correction and its loss are additional
  physical resources; they do not follow from a one-way oracle premise.

General ordinary inversion also supplies finite-cost comparators under
its stronger circuit interface. [Quintino et al.](https://arxiv.org/html/1810.06944v3)
use one qubit $U$ query, an entangled pair and a Bell measurement to
implement $U^{-1}$ with probability $1/4$. A failed attempt gives
$U^{-1}X^iZ^j|\psi\rangle$; an additional $U$ call and the known inverse
Pauli recover the original arbitrary input, including its reference
coherence. If $A$ is geometric with success $1/4$, the total query count
is $2A-1$, has mean $7$, and has success
$1-(3/4)^{\lfloor(k+1)/2\rfloor}$ by query cap $k$.
Bell detection, coherent auxiliary storage and feedforward are charged.

There is also a deterministic exact four-query qubit inverter:
[Yoshida, Soeda and Murao](https://doi.org/10.1103/PhysRevLett.131.120602)
give the original construction, while
[Mo et al.](https://doi.org/10.1038/s41534-025-00979-1) give a simpler
analytic circuit using three ancillas initialized to zero. The latter's
four-call construction leaves two ancillas in $U$-dependent garbage that
is traced out; zero initialization is not a claim of free clean reuse.
Its device-noise comparison is simulated. In general dimension,
[Chen et al., Theorem 1](https://arxiv.org/html/2403.04704v3)
give exact deterministic inversion with at most
$d\lceil\pi/[2\arcsin(1/d)]\rceil-1=O(d^2)$ forward calls, using
known interleaved control and auxiliary registers. Parallel query
layers are not a single station's elapsed time. None of these ordinary
circuits presumes a controlled unknown $U$, but none supplies its
ancillas, routing or gate-oracle access to a restricted native target
for free.

Applying a four-call inverter directly to a long evolution of duration
$T$ generally consumes four long slots. This alone does not remove the
abstract fixed-confidence $T+O(1)$ distinction. The controlled-$V$ or
three-short-call compilations can preserve that schedule when their
interfaces are available. For $d=2^n$, universal ordinary inversion can
be expensive, but the qubit commutator identities do not themselves give
a generic many-body switch rewinder. An open target's reduced noisy
channel likewise is not a repeatable closed-qubit unitary. Thus the
optical output is a valid useful-state demonstration, while a native
finite-cost advantage over all controls admitted by the same device
remains unestablished.

## Interface changes that remove the comparison

The ordinary lower bounds allow arbitrary clean ancillas and probes.
What is withheld is a clean **unscrambled copy of the challenge
payload** and frame-correlated advice. Revealing $U$, allowing free
current-frame training, or permitting source assistance changes the
task. In the Bell version, $C^T$ on the retained reference alone would
undo the source scramble, so that reference remains passive until the
fixed Bell test.

The selected frame is fresh per task. Persistent same-frame jobs enable
amortized calibration, which the one-output expected-cost theorem does
not bound. Known-frame corrections, a virtual output frame accepted by
the verifier, and an additional coherent indexed oracle are likewise
different interfaces. These are boundaries of the proved resource
problem, not impossibility results for those richer tasks.

## Positioning

The CP-support and rank-one arguments above are direct deductions for
this model, not priority claims. General purification no-go results
include [Fang and Liu](https://arxiv.org/abs/2010.11822).
Clean-unitary storage and retrieval are studied by
[Sedlák, Bisio and Ziman](https://arxiv.org/abs/1809.04552);
their full-unitary-group retrieval formula is not asserted for the
smaller noisy target family here. See the consolidated
[literature context](references.md).
