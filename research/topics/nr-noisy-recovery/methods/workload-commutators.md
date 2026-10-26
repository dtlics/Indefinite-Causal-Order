# Workload commutators: useful certificates and ordinary baselines

Proof component of [NR-R06](../architecture-baselines.md#nr-r06). The results below identify quantities needed by named workloads and delimit the proposed SWITCH benefit. They establish no practitioner-relevant SWITCH separation. All statements are analytic; finite certificate replay does not prove them.

## Observable-aware mitigation has a real commutator demand

[Eddins, Tran and Rall, Lightcone shading, arXiv:2409.04401v1](https://arxiv.org/html/2409.04401v1), Sections III–VI, use commutator bounds to allocate probabilistic error cancellation (PEC). Their forward shade uses a spectral norm, while their backward shade uses a trace norm with the initial state. Tight propagation through non-Clifford circuits can be classically costly. This is an existing mitigation-allocation task; it does not make every commutator estimator an improved PEC algorithm.

For Hermitian-unitary fault $E$, state $\rho$ and observable $A$, the source's single-fault identity is

\[
\delta_E(A;\rho)=\operatorname{Tr}A(E\rho E-\rho)
=\tfrac12\operatorname{Tr}([E,\rho][E,A]).
\]

The required spectral/trace norms differ from the normalized Hilbert–Schmidt quantity supplied by the usual maximally mixed SWITCH experiment.

<a id="nr-r06-state-sensitive-shade"></a>

## A state-sensitive observable-bias certificate

Let $A=A^\dagger$, $A^2=I$, and let $\mathcal N$ be any CPTP map with Kraus operators $N_i$. On target state $\rho$, the standard SWITCH of $\mathcal N$ and $\operatorname{Ad}_A$ gives

\[
p_-(\rho;\mathcal N,A)
=\tfrac14\sum_i\operatorname{Tr}\rho[A,N_i]^\dagger[A,N_i].
\]

Then

\[
\left|\operatorname{Tr}A\bigl(\mathcal N(\rho)-\rho\bigr)\right|
\le2\sqrt{p_-(\rho;\mathcal N,A)}. \tag{WC1}
\]

No unitality or Pauli-noise hypothesis is needed. To prove it, put $u_i=N_i\rho^{1/2}$ and $v_i=[A,N_i]\rho^{1/2}$. Trace preservation gives

\[
\sum_i\operatorname{Tr}(u_i^\dagger v_i)
=\operatorname{Tr}A\bigl(\mathcal N(\rho)-\rho\bigr),\qquad
\sum_i\|u_i\|_F^2=1,\quad
\sum_i\|v_i\|_F^2=4p_-.
\]

Cauchy–Schwarz proves (WC1). A reference can be retained by tensoring all operators with its identity. For $A=\sum_\ell a_\ell P_\ell$, applying the result to each Hermitian Pauli term gives $2\sum_\ell|a_\ell|\sqrt{p_-(\rho;\mathcal N,P_\ell)}$; its term count and coefficient norm are additional resources.

This is a useful error bound only for the relevant state and observable. A noisy implementation of an ideal propagated observable is a different channel. Measuring that noisy echo does not certify the ideal shade without a transfer theorem. Granting clean ideal prefix/suffix circuits can also grant ordinary direct estimation of the target observable, so those circuits cannot be a free unique advantage for the proposed QEM method.

## A small global scalar does not bound the required worst-case shade

Let $d=2r$, $A=Z\otimes I_r$, $P_0=|0\rangle\langle0|$ on the second factor, and $\sin^2\theta=1/r$. Define

\[
E_1=X\otimes P_0+Z\otimes(I_r-P_0),\qquad
E_2=(\cos\theta Z+\sin\theta X)\otimes I_r.
\]

Both are Hermitian unitaries with balanced eigenspaces, and are conjugates of the same single-qubit Pauli fault: use a conditional Hadamard for $E_1$ and a single-qubit rotation for $E_2$. Yet

\[
p_-(I/d;E_1,A)=p_-(I/d;E_2,A)=1/r,
\qquad
\|[A,E_1]\|_\infty=2,\quad
\|[A,E_2]\|_\infty=2/\sqrt r. \tag{WC2}
\]

Indeed $[Z,X]=2iY$, so both squared Frobenius norms equal $8$, while their nonzero spectral norms have the displayed values. Since $\|EAE-A\|_\infty=\|[A,E]\|_\infty$, these are also the maximum possible absolute expectation biases. One error is maximally harmful on a small sector; the other is uniformly weak. The factor $\sqrt r$ loss is unavoidable for this scalar alone, even within efficiently specified propagated-Pauli examples.

## A known arm has an exact ordinary implementation

If the actual unitary $A$ has a known efficient controlled implementation, apply controlled $A$ before one unknown $\mathcal N$ call on one control value, and after that call on the complementary value. The Kraus operators are exactly

\[
|0\rangle\langle0|\otimes A N_i
+|1\rangle\langle1|\otimes N_i A,
\]

up to the convention for naming the control values. This reproduces the full SWITCH on every target/control/reference input, including the same private $\mathcal N$ environment. One unknown-channel call and two known controlled operations suffice. A public Pauli uses ordinary Clifford control. No inverse or controlled version of the unknown channel is required.

The [existing fixed-arm superchannel argument](../../c6-hidden-dephasing/applications.md#c6-r08-robust) also covers a known channel with an available efficient Stinespring unitary: coherently apply that unitary before/after the unknown slot using the same fresh environment. Merely knowing the desired ideal gate does not provide the dilation of its unknown physical noise.

Consequently the state-sensitive shade is not a unique SWITCH advantage when its observable arm is public and controllable. A classically difficult propagated circuit may still be ordinary quantum processing. A future claim must distinguish classical simulation cost, ordinary quantum implementation cost and the extra native coherent-order resource.

## Ordinary noisy-prefix measurements supply another comparator

For any state $\rho$ and Hermitian unitary $P$,

\[
\|[P,\rho]\|_1\le2\sqrt{1-\mu^2},\qquad
\mu=\operatorname{Tr}(P\rho). \tag{WC3}
\]

For a pure state, the two nonzero commutator singular values give equality. For a mixed state, purify it and compare the purification with $(P\otimes I)|\Psi\rangle$; their overlap is $\mu$, and tracing the reference contracts the trace norm. Multiplication by $P$ identifies the commutator norm with $\|P\rho P-\rho\|_1$.

For known Markovian Pauli faults $\Lambda_j=(1-p_j)\mathrm{id}+p_j\operatorname{Ad}_{P_j}$ interspersed with ideal unitary layers, let $\rho_j$ be the actual noisy prefix just before fault $j$. Chronologically insert faults in a telescope. The remaining ideal suffix contracts trace distance, so for $\|A\|_\infty\le1$,

\[
|\mathrm{Bias}_{\rm raw}(A)|
\le\sum_j p_j\|[P_j,\rho_j]\|_1
\le\sum_j2p_j\sqrt{1-\mu_j^2},\qquad
\mu_j=\operatorname{Tr}(P_j\rho_j). \tag{WC4}
\]

Each $\mu_j$ is obtained by ordinary prefix execution and Pauli measurement, with repeated samples and a confidence interval. No clean future circuit is required. If only layer-end readout is available, the fault's own Pauli factor leaves $P_j$ unchanged; later same-layer Pauli factors multiply it by scalars of magnitude at most one. The measured magnitude therefore only decreases, giving a conservative bound. This is not monotonicity under arbitrary later gates.

The certificate concerns a **fixed policy**. Removing earlier faults in a selective-PEC policy can change later prefix states. That new policy needs its own effective prefix means, and quasiprobability estimation must pay the corresponding variance. Raw-prefix means do not give a free optimized PEC allocation. Valid use of (WC3)–(WC4) substitutes a lower confidence bound for $|\mu_j|$.

<a id="nr-r06-workload-reorder"></a>

## A finite-workload serial-reordering certificate

Let $\mathcal A,\mathcal B$ be two memoryless CPTP ports with the standard paired-history SWITCH extension. For target marginal $\rho$ put

\[
p=p_-(\rho;\mathcal A,\mathcal B)
=\tfrac14\sum_{i,j}\operatorname{Tr}([B_j,A_i]\rho[B_j,A_i]^\dagger).
\]

For any joint state $\psi_{SR}$ with that target marginal,

\[
\operatorname{TD}\!\left((\mathcal B\circ\mathcal A\otimes\mathrm{id})(\psi),
 (\mathcal A\circ\mathcal B\otimes\mathrm{id})(\psi)\right)
\le2\sqrt{p(1-p)}. \tag{WC5}
\]

To prove it, use the matched-environment isometries $V=\sum_{ij}|ij\rangle\otimes B_jA_i$ and $W=\sum_{ij}|ij\rangle\otimes A_iB_j$ on a purification of $\psi$. Both output vectors are normalized. Their overlap $c$ obeys $\operatorname{Re}c=1-2p$. Their pure-state trace distance is $\sqrt{1-|c|^2}\le\sqrt{1-(\operatorname{Re}c)^2}=2\sqrt{p(1-p)}$. Trace out the environments and any additional purifying reference. This also proves the mixed-extension case.

The bound is tight: on a Bell target/reference input, $A=Z$ and $B=e^{-i\theta X}$ give $p=\sin^2\theta$ and output distance $|\sin2\theta|$. Both $p$ near zero and $p$ near one certify a small reorder disturbance. At $p=1$ the matched purifications differ only by a global minus sign.

This is a sufficient certificate on the specified workload state, not a diamond-norm guarantee from the maximally mixed scalar. Repeated prefix/state preparations, all two-port trials, control work and readout must count. A unique unknown live payload cannot be copied into calibration data. A native joint temporal-memory process or simultaneous crosstalk needs its own extension; serial channels do not identify it.

For a proposed compiler pass, the still-missing evidence is a named workload in which accepted reorders save a computational resource, plus a matched ordinary/classical comparison for the required error decision. C6 SAME and MUB hard centers commute as channel maps in **both** cases; their reorder error is zero in both, so their hardness does not transfer to an actual reorder-error promise. A certificate's sufficient upper bound is not a lower bound on the disturbance.

## Two algorithmic routes with stronger ordinary comparators

### RCS collision statistics are not a hardness or fidelity certificate

For the public computational dephaser $\Delta_Z$ and an opaque rank-one dephaser $\Delta_U$, the visibility is

\[
v(\Delta_Z,\Delta_U)=\frac1d\sum_{i,j}|U_{ij}|^4. \tag{WC6}
\]

An ordinary protocol chooses $i$ uniformly, prepares $|i\rangle$, invokes $\Delta_U$ once and tests whether the computational output is $i$. Its return probability is exactly (WC6), because $\langle i|\Delta_U(|i\rangle\langle i|)|i\rangle=\sum_j|U_{ij}|^4$. No device meter record is needed. This task has a public reference basis and does not inherit C6's two-hidden-basis lower bound.

Moreover $U=H_2^{\otimes n}$ has the minimal visibility $1/d$ despite an elementary classical simulator. The scalar is ideal self-collision, whereas [linear XEB](https://arxiv.org/html/1910.11333v1) compares experimental samples with ideal probabilities. It contains no experimental-versus-ideal fidelity input by itself.

If a bounded score rescales $v=\Theta(1/d)$ by $d$, fixed additive score accuracy requires $O(1/d)$ additive visibility accuracy. Independent native control-sign trials are nearly balanced Bernoulli variables, requiring $\Omega(d^2)$ shots for constant-confidence discrimination of two such separated scores. The ordinary rare-return variable has probability $v$; its rescaled estimator $dY$ has variance $d^2v(1-v)=O(d)$, giving $O(d\epsilon^{-2}\log(1/\delta))$ ordinary queries at score accuracy $\epsilon\le1$. This is a comparison with that independent-sign estimator, not a lower bound on every coherent SWITCH protocol or an assertion about all classical samplers.

### Basic Trotter postselection must beat random order

For unitary slots $A,B$, let $K_\pm=(BA\pm AB)/2$ and $\mathcal M_\pm(\rho)=K_\pm\rho K_\pm^\dagger$. The ordinary two-call random-order channel is exactly

\[
\mathcal R=\mathcal M_++\mathcal M_-
=\tfrac12\operatorname{Ad}_{BA}+\tfrac12\operatorname{Ad}_{AB}.
\]

On any specified input/reference with $p_+>0$, write the normalized branches as $\sigma_\pm$, choosing $\sigma_-$ arbitrarily if $p_-=0$. Then $\mathcal R(\rho)=p_+\sigma_++p_-\sigma_-$ and $\operatorname{TD}(\sigma_+,\mathcal R(\rho))\le p_-$. For $A=e^{-ihH_1}$, $B=e^{-ihH_2}$,

\[
p_-\le\tfrac14\|[A,B]\|_\infty^2
\le\frac{h^4}{4}\|[H_1,H_2]\|_\infty^2. \tag{WC7}
\]

The second inequality follows by applying the integral commutator formula twice to unitary exponentials. Thus this postselection changes the averaged ordinary channel only at fourth local order. The ordinary randomized product formula already has second-order averaged-channel accuracy; see [Childs, Ostrander and Su, arXiv:1805.08385v2](https://arxiv.org/html/1805.08385v2), Section 2. A deterministic $AB$ comparator misses this alternative.

An explicit cubic-error witness is $H_1=X$, $H_2=Z$. Put $c=\cos h$, $s=\sin h$. Then

\[
K_+=c^2I-ics(X+Z),\qquad p_+=1-s^4,
\quad
\frac{K_+}{\sqrt{p_+}}
=e^{-i\theta(h)(X+Z)/\sqrt2},\quad
\theta(h)=\arctan(\sqrt2\tan h)
\]

for sufficiently small $h$. Since $\theta(h)=\sqrt2h-(\sqrt2/3)h^3+O(h^5)$, the half-diamond error relative to $e^{-ih(X+Z)}$ is $|\sin(\theta(h)-\sqrt2h)|=(\sqrt2/3)|h|^3+O(|h|^5)$. The random-order channel differs by at most $s^4=O(h^4)$, so the nonzero leading cubic error remains for both in this witness. This excludes the basic two-order plus-filter argument, not every retained-control simulation algorithm or error model.

## Current disposition

Lightcone shading supplies real demand and (WC1) supplies an exact operational link. Equations (WC2)–(WC4) and the fixed-arm compiler prevent calling this a SWITCH separation. Equation (WC5) is a candidate bridge to serial compilation, not an established workload advantage. The broader practitioner objective remains open.
