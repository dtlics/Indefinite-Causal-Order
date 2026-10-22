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

This result uses **global replacement noise**, not the local model of
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

<a id="nr-r05"></a>

## NR-R05 — Rejection and offline-program limits

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
