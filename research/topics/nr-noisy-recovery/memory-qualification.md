# Qualifying a memory-rate promise through hidden dephasing geometry

[Application assessment](architecture.md) · [Ordinary memory tests](methods/memory-ordinary-tests.md) · [Native cost screen](methods/memory-native-cost.md) · [Topic](README.md)

<a id="nr-r20"></a>

## NR-R20 — Memory-rate qualification, ordinary-query reductions and switched blocks

The manuscript's hidden-basis decision theorem has a concrete capacity
corollary. Under an exact two-family promise, a switched diagnostic can
distinguish a production memory with positive unassisted quantum capacity
from one with zero capacity. For arbitrary hidden bases, the ordinary-query
lower bound covers arbitrary quantum memory, adaptive controls and collective
measurements. It follows by a reduction to the manuscript, rather than a new
lower-bound proof. A structured Pauli specialization has strong ordinary
learners; the generic Haar lower bound does not transfer to that restriction.

The conclusion is a model-dependent qualification of an asymptotic rate.
The test neither learns a usable encoder nor improves the production channel.
A substantial advantage for a physically justified architecture remains open.

Capacity qualification without full process tomography is established
prior work. [Pfister et al., *Nature Communications* **9**, 27 (2018)](https://doi.org/10.1038/s41467-017-00961-2)
estimate one-shot capacity using preparation and measurement in two
bases, and verify capacity while data are stored or communicated,
including correlated multiqubit errors. Switch measurement of channel
noncommutativity is the mechanism of
[Gao et al., PRL **130**, 170201 (2023)](https://arxiv.org/abs/2208.06210);
[Loizeau and Grinbaum, PRA **101**, 012340 (2020)](https://arxiv.org/abs/1906.08505)
already study a representation-independent self-channel commutator
scalar and its relation to switched communication capacity. The generic
result here is a capacity corollary of the manuscript's ordinary-query
theorem, rather than a new switch diagnostic mechanism or a claim to
the first capacity test. The
[entropy component](methods/pauli-entropy-capacity.md) positions the
distinct Pauli entropy witness and its capacity-detection predecessors.

### Production memory and qualification endpoint

Let $D=2^n$. For a fixed orthonormal basis given by the columns of $U$, put

$$
\Delta_U(X)=\sum_{j=1}^{D}|u_j\rangle\langle u_j|X|u_j\rangle\langle u_j|,
\qquad \Omega(X)=\operatorname{Tr}(X)I/D.
$$

Two opaque rank-one dephasers $A,B$ obey one of the manuscript's promises:
they dephase in the same basis, or in mutually unbiased bases. Their
superoperators commute in either case. With $C=B\circ A$, define a
production memory, for a supplied $0<t\leq1$, by

$$
\begin{array}{c|c|c}
 & C & \mathcal E_t=(1-t)\operatorname{id}+tC\\ \hline
H_1\text{ (same basis)} & \Delta_U & (1-t)\operatorname{id}+t\Delta_U\\
H_0\text{ (unbiased bases)} & \Omega & (1-t)\operatorname{id}+t\Omega.
\end{array}                                                     \tag{M1}
$$

Indeed, if $P_j,Q_k$ are the two rank-one projector families, unbiasedness
gives $Q_kP_jQ_k=Q_k/D$; summing the composed measurement proves
$B\circ A=A\circ B=\Omega$. In the same-basis case both compositions are
the same idempotent pinching. The basis is fixed throughout calibration and
qualification. Each use has a fresh environment; the Bernoulli production
choice is redrawn independently. A fresh environment does not mean a fresh
unknown basis.

Here $Q(\mathcal E)$ is the unassisted asymptotic quantum capacity in qubits
per $n$-qubit production-channel invocation: independent uses of the same
channel, with encoding before transmission and decoding afterward. All
payload traverses that channel. A noiseless quantum bypass, intermediate
active control during the storage interval, two-way assistance and
temporally correlated noise define other endpoints. The diagnostic's
training registers and their ordinary processing may be arbitrary; the
payload restrictions are part of the capacity being qualified.

### Capacity implication and its proof

Let $Z^z=\bigotimes_{j=1}^n Z_j^{z_j}$ for $z\in\mathbb F_2^n$. The
$D$ unitaries $W_z=UZ^zU^\dagger$ are mutually orthogonal in the
Hilbert--Schmidt inner product and commute, and

$$
\Delta_U=D^{-1}\sum_z\operatorname{Ad}_{W_z}.
$$

Consequently the random-unitary weights of $\mathcal E_{1,t}$ are
$p_0=1-t+t/D$ and $p_z=t/D$ for $z\ne0$. At input $I/D$ the output
entropy is $n$, while orthogonality makes the exchange entropy $H(p)$.
Writing $a=t(1-D^{-1})$ therefore gives

$$
I_c(I/D,\mathcal E_{1,t})
 =n-H(p),\qquad
H(p)=h_2(a)+a\log_2(D-1)\leq h_2(t)+tn.                \tag{M2}
$$

For the inequality, expose the Bernoulli production choice before choosing
a uniform phase label. Its joint entropy is $h_2(t)+t\log_2D$, and the
resulting error label is a deterministic function of that record. The
quantum coding direct theorem implies

$$
Q(\mathcal E_{1,t})\geq\max\{0,n-H(p)\}
 \geq\max\{0,(1-t)n-h_2(t)\}.                         \tag{M3}
$$

The dependency is [Devetak, *The private classical capacity and quantum
capacity of a quantum channel*, IEEE TIT **51**, 44–55 (2005), Theorem 5
and its direct proof](https://arxiv.org/pdf/quant-ph/0304127). The
[Pauli entropy method](methods/pauli-entropy-capacity.md) treats general
Pauli laws; the conjugated commuting family above needs no calibrated
knowledge of $U$ for this existence bound.

The low-capacity channel is receiver postprocessing of the $D$-dimensional
erasure channel with erasure probability $t$: replace its orthogonal
erasure symbol by $I/D$ and discard the flag. Capacity cannot increase
under this postprocessing, so

$$
Q(\mathcal E_{0,t})\leq\max\{0,1-2t\}\,n.             \tag{M4}
$$

The erasure formula is due to [Bennett, DiVincenzo and Smolin, PRL **78**,
3217 (1997)](https://doi.org/10.1103/PhysRevLett.78.3217);
[Barnum, Smolin and Terhal, PRA **58**, 3496 (1998), Eq. 61](https://arxiv.org/pdf/quant-ph/9711032)
supplies the converse without the earlier continuity assumption. For a
qudit, the receiver and environment receive the input with probabilities
$1-t$ and $t$. At $t\leq1/2$ degradability gives capacity
$(1-2t)\log_2D$; at $t\geq1/2$ antidegradability gives zero.

In particular, at $t=1/2$ and $n\geq3$,

$$
H_1:\ Q\geq n/2-1>0,
\qquad H_0:\ Q=0.                                    \tag{M5}
$$

More generally, for $0<t\leq1/2$ and $tn>h_2(t)$, any rate strictly
between $(1-2t)n$ and $(1-t)n-h_2(t)$ is impossible under $H_0$ and
achievable in principle under $H_1$. This implication uses the exact
promise (M1); a control visibility by itself is not a general capacity
witness. The coding theorem may choose codes that depend on the fixed
channel. It does not provide an efficient encoder, decoder, finite-block
error guarantee or inexpensive training procedure for an unknown basis.

### Ordinary access: maximum and expected query costs

An ordinary receiver may prepare arbitrary entangled probes, retain any
finite quantum memory, apply arbitrary known quantum instruments, select
the next unknown box from its classical history, and make collective
measurements. The environment, measurement outcomes and basis unitary of
the opaque dephasers remain inaccessible. Success is unconditional;
rejection and long learning branches are included. These are the ordinary
QC-CC rules in [the manuscript](../../../paper/main.tex), Theorem
`thm:c6` and its access-model paragraph. Its hard prior chooses one
Haar $U$ and uses $(A,B)=(\Delta_U,\Delta_U)$ under $H_1$ and
$(\Delta_U,\Delta_{UH})$ under $H_0$, with known
$H=H_2^{\otimes n}$. Theorem `thm:c6` states that success at least $2/3$
on every promised pair requires more than

$$
L_D=D^{1/16}/100                                     \tag{M6}
$$

primitive $A/B$ calls. Its shared-basis indistinguishability lemma
`lem:c6-comparison` further bounds the hard-prior output half trace
distance by $215/10000$ whenever the hard primitive cap is at most $L_D$.
This already includes quantum memory and coherent known processing;
there is no Pauli or stabilizer restriction on the ordinary competitor.

An atomic production-memory call can be simulated exactly by a fresh
private Bernoulli$(t)$ coin: on zero do nothing, and on one call $A$ then
$B$ on the designated subsystem. Discard the coin. This implements
$(1-t)\operatorname{id}+t(B\circ A)$ even on inputs entangled with retained
memory. Applying the simulation to every adaptive call preserves the
whole transcript and output distribution. The simulation is ordinary
because its unknown-box selection is classical and its nonidentity
branch has definite order.

Thus a hard cap $q_E$ for atomic $\mathcal E_t$ access gives a primitive
cap $2q_E$, and (M6) implies $q_E>L_D/2$. If the receiver can also query
$A,B$ directly, the correct hard ledger is

$$
\max_{\text{branches}}(N_A+N_B+2N_E)>L_D.              \tag{M7}
$$

There is a stronger rare-production scaling from the actual trace-distance
lemma. Set $q_*=\lfloor L_D\rfloor\geq1$. Let an ordinary primitive
strategy succeed with probability at least $2/3$ under the balanced hard
prior and have mean primitive cost $c$. Truncate immediately before a
$(q_*+1)$st call, outputting any fixed bit on truncated branches. The
balanced success decreases by at most $\Pr[N>q_*]\leq c/q_*$.
If $c\leq q_*/12$, the truncated success is at least $7/12$, whereas the
lemma permits success at most

$$
\frac12+\frac{215}{20000}=0.51075.
$$

This contradiction proves $c>q_*/12$. In the atomic simulation, the
decision to make the $j$th production call precedes its fresh coin $Z_j$.
Tonelli's theorem and that independence give, without assuming a
deterministic stopping time,

$$
\mathbb E[N_{A/B}]
 =2\sum_{j\geq1}\Pr[N_E\geq j,Z_j=1]
 =2t\sum_{j\geq1}\Pr[N_E\geq j]
 =2t\mathbb E[N_E].                                  \tag{M8}
$$

Therefore any atomic-memory receiver with the success promise satisfies

$$
\mathbb E[N_E]>\frac{q_*}{24t}
 =\Omega(D^{1/16}/t).                                \tag{M9}
$$

The expectation can be the balanced-prior mean; a uniform maximum mean
is at least that mean. A hard production-call cap also bounds the mean,
so (M9) applies to it. Floors can make the explicit bound vacuous at
small $D$; the exponential statement is asymptotic. For mixed direct and
production access the mean primitive ledger is

$$
\mathbb E[N_A]+\mathbb E[N_B]+2t\mathbb E[N_E]
 >q_*/12.                                           \tag{M10}
$$

It does not impose an extra $1/t$ penalty on direct $A/B$ calls. Finite
strategies are within the manuscript's model. An extension to almost-sure
finite stopping with finite mean first truncates the overall execution
to a finite circuit with arbitrarily small extra error, then applies the
same argument. More explicitly, after the primitive-call truncation,
truncate the known-step count with extra balanced-prior error less than
$1/24$. The resulting finite-circuit success is at least $13/24$, still
above $0.51075$. Finite mean query count alone does not assert overall
halting; this extension assumes almost-sure termination. An
unnormalized postselected success probability is not the stated endpoint.

An exposed production Bernoulli flag can also be reproduced by the
simulator; its presence alone does not defeat the ordinary reduction.
Equations (M2)–(M5) concern the unflagged payload map. Giving that flag to
the payload decoder defines a different channel and must be specified,
even though the erasure postprocessing bound still applies. Exposing
dephaser meter outcomes, a pointer state or $U$ supplies other resources
that the hidden-basis theorem has not granted.

### Two switch interfaces and their different ledgers

If native $\mathcal S(A,B)$ is available, use the manuscript's existing
test on a maximally mixed target and one $|+\rangle$ control. The control
visibility is $1$ under $H_1$ and $1/D$ under $H_0$. Four independent
launches, declaring $H_0$ upon any minus outcome, have one-sided error

$$
\left(\frac{1+1/D}{2}\right)^4\leq(3/4)^4=81/256<1/3.
                                                               \tag{M11}
$$

They cost eight primitive $A/B$ calls, independently of the production
mixture weight $t$. This diagnostic classifies (M1) and hence the rate
promise; it does not perform a protected payload-storage operation.

A distinct interface supplies two independently reset, coherently
reorderable ports for the atomic production channel. The following
amplification requires a standard switch of whole repeated blocks,
$\mathcal S(\mathcal E_t^\ell,\mathcal E_t^\ell)$. A single-pass router
or the reduced map $\mathcal E_t$ does not automatically supply this
multi-visit interface. Each port contains $\ell$ fresh primitive calls;
one launch consumes $2\ell$ production calls. The control must remain
coherent across the whole launch.

For either $\mathcal P=\Delta_U$ or $\mathcal P=\Omega$, idempotence and
independent slots imply

$$
[(1-t)\operatorname{id}+t\mathcal P]^\ell
 =r\operatorname{id}+s\mathcal P,
\qquad r=(1-t)^\ell,\quad s=1-r.                      \tag{M12}
$$

Prepare an independent $|+\rangle$ control and measure it in the $X$
basis at the end. The complete unnormalized target instruments are

$$
\begin{aligned}
\mathcal F_{1,+}&=r^2\operatorname{id}+(1-r^2)\Delta_U,
&\mathcal F_{1,-}&=0,\\
\mathcal F_{0,+}&=r^2\operatorname{id}+2rs\Omega
       +\frac{s^2}{2}(\Omega+\operatorname{id}/D^2),
&\mathcal F_{0,-}&=\frac{s^2}{2}(\Omega-\operatorname{id}/D^2).
\end{aligned}                                                   \tag{M13}
$$

These maps hold on arbitrary target/reference inputs, with identity on
the reference understood. Idempotence alone only proves (M12); the
$H_1$ zero-minus assertion also needs a commuting Kraus representation,
which rank-one pinching has. To prove (M13), use the commuting unitary
representation $W_z$ for $\Delta_U$, and the uniform Pauli representation
for $\Omega$. Commuting effective errors leave the control in plus.
For $\Omega/\Omega$, its off-diagonal switch map is
$\operatorname{id}/D^2$: on any Pauli $P_x$, the coefficient is

$$
D^{-4}\sum_{a,b\in\mathbb F_2^{2n}}
 (-1)^{[a,b]+[a+b,x]}=D^{-2},
$$

because the sum over $a$ leaves only $b=x$. An identity/depolarizing
cross block is $\Omega$. Combining these cross maps with the ordinary
composition proves (M13). This argument evaluates the standard switch,
whose result is independent of the chosen Kraus representation.

The control visibilities and minus probabilities consequently are

$$
\eta_1=1,\quad p_{1,-}=0,
\qquad \eta_0=1-s^2(1-D^{-2}),\quad
p_{0,-}=\frac{s^2}{2}(1-D^{-2}).                      \tag{M14}
$$

At $\ell=1$ the gap is quadratic in $t$. This visibility is not the
entanglement fidelity of the ordinary composed channel.

Given $0<t_{\min}\leq t$ and $0<\delta\leq1/4$, choose

$$
\ell=\left\lceil\frac{\ln2}{t_{\min}}\right\rceil,
\qquad
J=\left\lceil
 \frac{\ln(1/\delta)}{-\ln(1-3/32)}
\right\rceil.                                            \tag{M15}
$$

Then $r\leq e^{-t\ell}\leq1/2$, so $s\geq1/2$ and
$p_{0,-}\geq3/32$. Declare $H_0$ upon any minus and $H_1$ after $J$
all-plus launches. The $H_1$ error is zero and the $H_0$ error at most
$(1-3/32)^J\leq\delta$. Its hard production-call cap is

$$
2\ell J=O(t_{\min}^{-1}\ln(1/\delta)).                \tag{M16}
$$

If this production device is itself constructed from $A,B$ using fresh
classical mixture choices, each production visit costs at most two
primitive calls, giving a maximum $4\ell J$ primitive $A/B$ ledger
(and $4t\ell J$ mean for all $J$ launches). The physical coherent router,
mixture implementation and their records still need the two-block
interface. The ordinary simulation of one production map does not
construct its quantum switch.

Thus with $t_{\min}=t$ and fixed confidence, granted native whole-block
switch access uses $O(1/t)$ production calls, compared with the ordinary
$\Omega(D^{1/16}/t)$ consequence (M9) for the generic hidden-basis family.
Granted native $\mathcal S(A,B)$ has instead the direct eight-call
primitive comparison (M11). These are two different access models.

### Rare-event cost and the control's physical lifetime

For atomic-production access, the $t^{-1}$ scale at fixed confidence is
unavoidable even for a general normalized higher-order tester. With $T$
primitive production slots, expand each slot as in (M1). If the tester
is positive, multilinear and normalized on product CPTP slots, its
all-identity branch is a common normalized output with weight $(1-t)^T$.
All remaining positive outputs have total weight $1-(1-t)^T$, including
every classical record. Thus

$$
\tfrac12\|\rho_1-\rho_0\|_1\leq1-(1-t)^T.             \tag{M17}
$$

Errors at most $\delta<1/2$ on both hypotheses require half trace
distance at least $1-2\delta$, hence, for $0<t<1$,

$$
T\geq\frac{\ln(1/(2\delta))}{-\ln(1-t)}.              \tag{M18}
$$

For $t\leq1/2$ this is $\Omega(t^{-1}\ln(1/\delta))$ in the stated
confidence range. At $t=1$ the common-branch bound is trivial. Bounded
early stopping can be padded with discarded calls to the cap. This
argument does not give the same confidence formula for an arbitrary
mean-cost constraint, postselected outputs or mixed direct $A/B$ access.

The helper must stay coherent over all $2\ell$ visits and any travel,
waiting and reset delays. To make that cost explicit, suppose an
independently calibrated helper dephasing leaves visibility
$0<\nu_\ell\leq1$ over the complete launch and does not change the slot
laws. With

$$
b_\ell=(1-\nu_\ell)/2,\qquad
\Delta_\ell=\frac{\nu_\ell s^2}{2}(1-D^{-2}),
$$

the two observed minus probabilities are $b_\ell$ and
$b_\ell+\Delta_\ell$. A midpoint decision and Bernstein's inequality
give the sufficient launch budget

$$
J\geq\frac{8b_\ell+(28/3)\Delta_\ell}{\Delta_\ell^2}
 \ln\frac2\delta.                                    \tag{M19}
$$

Indeed, each midpoint deviation is $\Delta_\ell/2$ and each Bernoulli
variance is at most $b_\ell+\Delta_\ell$, yielding that denominator in
the exponent. Constant visibility bounded away from zero preserves
(M16) up to constants. It cannot be assumed constant as $\ell$ grows:
for Markov dephasing rate $\gamma$ over duration $T_\ell$,
$\nu_\ell=e^{-\gamma T_\ell}$. If $T_\ell$ is proportional to $\ell$,
the chosen rare-event block can suffer an exponential-in-$1/t$ coherence
penalty. Survival probability $\zeta_\ell$ further reduces throughput;
heralded rejected launches still cost time and visits. State-independent
known loss and biased discarded events require different analyses.

An unmodeled error of at most $\xi$ in each hypothesis's minus
probability needs $\xi<\Delta_\ell/2$ for the ideal midpoint to remain
separating. Under a genuine independent-slot implementation, half-diamond
error at most $\epsilon$ in each primitive channel gives the conservative
whole-launch bound $2\ell\epsilon$ by telescoping. Keeping the amplified
constant gap requires $\ell\epsilon$ small, hence
$\epsilon=O(t_{\min})$ at (M15). This does not control extra time records,
cross-slot bath correlations or faults in the router merely from a
one-use fitted channel.

The [native cost method](methods/memory-native-cost.md) owns the broader
time, control, reset, loss, purity and ordinary-hardware comparison.
Noiseless helper routing alongside noisy ordinary preparation/readout
would be an unequal comparison.

### Structured Pauli specialization and ordinary counterchecks

For public physical Pauli axes, let $G=\mathbb F_2^{2n}$ with its
symplectic form and choose an unknown Lagrangian $L=L^\perp$. Replacing
$\Delta_U$ by

$$
\mathcal P_L=D^{-1}\sum_{a\in L}\operatorname{Ad}_{P_a}
$$

gives a rank-one stabilizer dephaser, so the capacity proof and switched
block instrument above apply. Its Pauli eigenvalues are

$$
\lambda_1(b)=1-t+t\mathbf1_{\{b\in L\}},\qquad
\lambda_0(b)=1-t+t\mathbf1_{\{b=0\}}.                 \tag{M20}
$$

If $L$ has no nonzero vector of Pauli weight at most $w$, all fitted
nonidentity eigenvalues of those weights agree. For arbitrary initial
target/reference states, the reduced output on any at most $w$ target
qubits and the untouched reference agrees as well: expand observables
on that subset in Paulis and use the adjoint of (M20). This equality
does not identify joint high-weight measurement records, changes of
layout or multi-time intervention experiments. Such $L$ exist whenever

$$
\frac{\sum_{j=1}^w3^j\binom nj}{D+1}<1,               \tag{M21}
$$

because a uniform random Lagrangian contains each fixed nonzero vector
with probability $1/(D+1)$, and the numerator counts the excluded vectors.
This is an existence argument, not a physical mechanism for noise.

The [ordinary memory-test method](methods/memory-ordinary-tests.md)
owns the following competitors and their full proofs: a
zero-reference random-stabilizer syndrome-rank test using
$O((n+\ln(K/\delta))\ln(1/\delta)/t)$ calls, with
$K=O(\ln(1/\delta))$, and a partial-Bell relation test with $k\geq1$
clean references using $O((n-k+2)\ln(1/\delta)/t)$ calls. The latter
requires only local target preparation/readout beyond the Bell bank.
With all $n$ references, ordinary Bell error-label measurements already
give the $O(t^{-1}\ln(1/\delta))$ qualification scale. The distinct
[general subspace calibration method](methods/pauli-subspace-calibration.md)
also gives polynomial calibration of low-rank error supports and
subsequent ordinary label sampling under fixed reuse.
Global Clifford cost, clean references and
classical processing must all be charged at their actual native cost.

The Haar lower-bound prior in (M6) ranges over arbitrary bases, rather
than public-axis stabilizer bases. Conjugating a Pauli description by an
unknown arbitrary $U$ does not supply the calibrated probes and
error-label readout used by these learners. Conversely, the lower bound
for that larger family says nothing by itself about the restricted
public-Pauli instance. No lower bound growing as $n-k$ against every
adaptive, concatenating ordinary receiver is established here. Restricted
fixed-probe results in the memory-test method retain their stated scope. Agreement
of low-weight fits is not a substitute for such a lower bound.

Even modest calibration can remove the difficulty. If a preparable
pointer state $|u_j\rangle$ and its return projector are known, an
ordinary prepare--query--return test has return probability $1$ under
$H_1$ and $1-t+t/D$ under $H_0$. It qualifies with
$O(t^{-1}\ln(1/\delta))$ calls. For the Pauli family it suffices to know
one nonzero $b\in L$: prepare a product $+1$ eigenstate of $P_b$ and
read its parity. The minus probabilities are $0$ and $t/2$. Neither
shortcut requires learning a full encoder or every basis vector.

### An entropy certificate beyond the two-family promise

The [general-channel entropy component](methods/unital-entropy-capacity.md)
proves a sufficient certificate for every unital CPTP channel. Put
$f=F_e(I/D,\mathcal E)$, let $\eta$ be its self-switch control mean with
target $I/D$, and write $C_D=(2-D^{-1})/\ln2<3$. Then
$$
Q(\mathcal E)\geq
\max\{0,[f-\sqrt{1-\eta}]\log_2D-h_2(f)-(1-f)C_D\}.
$$
The proof bounds Choi entropy using mixed-adjoint commutators and
pinching along the maximally entangled vector. It does not assume
unitary Kraus operators, an identity branch, or that $f$ is a Choi
eigenvalue. For nonunital CPTP channels it supplies an explicit
correction in $u=\|\mathcal E(I)-I\|_F^2/D$; a bound on $u$ is a
separate resource. A supplied diamond-distance bound to a unital model
gives a continuity-based alternative, with its model promise charged.
At $n=32$, jointly valid lower confidence bounds
$f\geq0.38$ and $\eta\geq0.96$ certify $Q\geq2.9$ qubits per use
under known unitality. No finite-block encoder or native query
advantage follows from this sufficient certificate.

The [unitary-error component](methods/pauli-entropy-capacity.md)
separately bounds the Shannon entropy of an orthogonal unitary
realization, including arbitrary spatially correlated Pauli laws.
Its full-support example realizes the confidence region above. There,
even exact identity probability and scalar purity together cannot give
a positive worst-case entropy-based hashing certificate, while the
commutation information can. This compares sufficient certificates;
it supplies no ordinary-estimation lower bound for $\eta$. Its input
independence is a Pauli specialization.

The [overlap-robust extension](methods/unitary-error-overlap.md) treats
at most $D^2$ unitary branches with supplied normalized pairwise overlap
bound $\mu$ and $D\mu^2<1$. It distinguishes identity branch mass from
measured entanglement fidelity, proves the corrected entropy and
confidence bounds, and gives a nonorthogonal positive-rate example.
The branch model and overlap promise are assumptions about the device;
two measured moments do not establish that realization or its label
entropy. The general Choi-entropy theorem uses the different argument
above and does not require this branch promise.

Strong ordinary comparisons remain essential. [Local product probes](methods/pauli-local-certification.md)
can give a dimension-independent sufficient certificate without a helper
for spatially diluted overlap. [Noisy-structure calibration](methods/pauli-noisy-structure.md)
closes further promise families in device calls, explicitly charging its
classical processing, and gives polynomial total cost when short exposures
or specified known controls are supplied. [Public-tableau checks](methods/pauli-clifford-calibration.md)
also work on a mixed target with one reusable helper. These are scoped
ordinary upper bounds, rather than an unrestricted scalar-estimation lower bound.

### A working code supplies an ordinary qualification test

The [code-verification method](methods/memory-code-verification.md)
makes the deployment caveat quantitative. At $t=1/2$, every deterministic
unassisted $L$-use code for the low channel, transmitting a
$K$-dimensional logical system, has entanglement fidelity at most
$(K+1)/(2K)$. Its proof constructs a symmetric two-output extension;
zero asymptotic capacity alone would not imply this finite-block bound.
Thus a supplied logical-qubit code with high-channel fidelity at least
$7/8$ can be checked by $319$ ordinary Bell trials, each costing $L$
production calls, with each validation error at most $1/12$.

If ordinary training outputs a classical code description with that
fidelity on at least two-thirds of the Haar high prior, freeze the code,
discard quantum training memory and validate on fresh calls. The
resulting balanced-prior decision succeeds with probability at least
$55/72$. Equation (M9) at $t=1/2$ then charges

$$
\mathbb E[N_{\rm train}]+319\,\mathbb E[L]>q_*/12.
$$

The method gives the full proof, stopping assumptions and a return-test
alternative without a retained logical reference. A code supplied as
$U$-correlated advice is extra access; a code learned through the
stipulated ordinary interface incurs the training and block cost above.
Shared encoder/decoder quantum assistance or an input-bearing bypass
changes the unassisted-code model. Receiver-only program memory has the
more specific extension below.

### Decoder bootstrap with retained quantum programs

The [bootstrap component](methods/memory-code-bootstrap.md) proves that
every unframed self-switch of production powers has exactly the serial
full output on the high dephasing promise. Its high-case emulator preserves
arbitrary receiver-side quantum programs. With a syntactic unassisted
deployment interface enforced for every oracle and truncation, one Bell
validation gives, for high-prior almost-surely terminating protocols, the mean bound
$c_h\ge q_*(F_h-3/4-215/10000)$; at $F_h\ge7/8$, this is
$207q_*/2000$. Training, deployment and validation calls all enter the
cost. The proof does not assume that the emulated low protocol halts.

The same component separates available self-adjoint noise from the
code-dependent inverse filter in Petz recovery. A particular raw-filter
routine has success at most $tK/D$ on a full-rank output for a proper
rank-$K$ code; this is not a lower bound on every decoder. Ordinary
Clifford code projection already gives high conditional fidelity under
both capacity promises, so conditional output quality alone does not
qualify a working memory. Framed switches, online higher-order storage,
shared entangled programs and coherent environment access require their
own comparisons. The component also closes a particular framed-qubit
heralded-recovery candidate using a stronger ordinary helper echo, while
retaining its protected-helper and unknown-input failure costs.

### What remains to make this an architecture advantage

The rigorous generic result is a reduction-based exponential ordinary
query separation for a promise about memory rate, with unrestricted
ordinary memory and explicit maximum/mean ledgers. The structured
Pauli branch supplies a locally indistinguishable qualification model,
an amplified switch protocol and competitive ordinary algorithms.
The available upper bounds alone do not prove a Pauli architecture gap.

A physical proposal must justify why even one usable pointer is opaque,
why both ports share the stipulated fixed geometry, why each visit resets
its environment, and why the full coherent block switch has no
order-revealing interaction-time, routing or controller record. A joint
error law concentrated on identical labels in both ports can have the
same one-slot Pauli marginals as independent draws while making every
commutation sign plus. A shared burst indicator also changes the
two-burst probability. One-time channel characterization therefore does
not certify (M12)–(M14) as a process model.

Arbitrary Haar orientation does not itself provide an efficient,
fault-tolerant device or a native switch. Supplying a usable calibrated
pointer can make diagnosis easy, while withholding all basis knowledge
can also obstruct deployment of a high-capacity code. A useful workload
must account for this qualification/deployment distinction and the
amortization of calibration on a persistent device. Until that interface,
encoder access and matched time/memory/noise frontier are justified,
the mathematical corollary remains an oracle application rather than a
demonstrated substantial physical advantage.
