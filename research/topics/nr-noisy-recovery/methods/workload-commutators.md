# Workload commutators: useful certificates and ordinary baselines

Proof component of [NR-R06](../architecture-baselines.md#nr-r06). The results below identify quantities needed by named workloads and delimit the proposed SWITCH benefit. They establish useful common-workload certificates and bounded comparisons, without an optimal separation from every ordinary or classical method. All statements are analytic; finite certificate replay does not prove them.

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

<a id="nr-r06-average-case-trotter"></a>

## A measured step-count certificate for average-case Hamiltonian simulation

The literal maximally mixed SWITCH scalar gives a finite-shot certificate for a common simulation workload. It can reduce the number of certified first-order product-formula steps relative to a stated conservative policy, and saves one forward call per calibration trial against the explicit three-query ordinary reproduction of the same meter. The production-step reduction is shared with that ordinary method; explicit Pauli algebra and local Hamiltonian learning remain admitted competitors. No optimal advantage over every ordinary or classical method is claimed.

### Established simulation demand

[Zhao, Zhou, Shaw, Li and Childs, Hamiltonian simulation with random inputs, PRL 129, 270502 (2022)](https://arxiv.org/pdf/2111.04773), Theorem 1 Eq. (4) and Theorem 3 Eq. (10), establish average-case product-formula error in the normalized Frobenius metric. A uniform computational-basis ensemble already suffices; Haar states are unnecessary. Their applications include spin dynamics and infinite-temperature OTOC simulation. For two Hamiltonian fragments their first-order triangle bound is

\[
R\le\frac{t^2}{2r\sqrt d}\|[H_1,H_2]\|_F.
\]

A concrete two-fragment workload is [Arrazola et al., Digital-Analog Quantum Simulation of Spin Models in Trapped Ions, Scientific Reports 6, 30534 (2016)](https://arxiv.org/pdf/1602.06248), Eqs. (1)–(4): Heisenberg simulation with \(H=H_{XY}+H_{ZZ}\), implementing each Trotter step using two analog evolution blocks and single-qubit basis rotations. The source identifies fragment noncommutation as a truncation-error source. Its published numerical demonstration uses fixed initial states; applying the certificate here concerns the established random-input simulation variant, not a guarantee for those fixed states.

Opaque implemented evolution is also an established characterization setting: [Pastori, Olsacher, Kokail and Zoller, PRX Quantum 3, 030324 (2022)](https://arxiv.org/pdf/2203.15846), Secs. II B and IV B, treat experimental Trotter blocks as black boxes, including unknown deviations of analog resource Hamiltonians. The same paper supplies an important ordinary competitor: Hamiltonian/Floquet learning with polynomial measurement scaling for a polynomial local ansatz. These sources supply workload demand; neither supplies a free native SWITCH interface or proves the extra spectral bounds assumed below.

### Exact scalar-to-error theorem

Let fixed Hermitian generators \(H_1,H_2\) have available forward evolutions \(A_s=e^{-isH_1}\), \(B_s=e^{-isH_2}\). Let \(s>0\) be a calibration time independent of the eventual Trotter time slice. Assume supplied centers \(a_1,a_2\) and bounds

\[
\|s(H_1-a_1I)\|_\infty\le\alpha<\pi,
\qquad
\|s(H_2-a_2I)\|_\infty\le\beta<\pi.
\]

Put \(c(x)=x/\sin x\), continuously setting \(c(0)=1\), and measure

\[
p_s=\frac{\|[A_s,B_s]\|_F^2}{4d}.
\]

Then, with \(C_F=\|[H_1,H_2]\|_F/\sqrt d\),

\[
\frac{2\sqrt{p_s}}{s^2}\le C_F
\le\frac{2c(\alpha)c(\beta)\sqrt{p_s}}{s^2}. \tag{WC8}
\]

**Proof of the useful upper bound.** For Hermitian \(X\) with eigenvalues in \([-\alpha,\alpha]\),

\[
|x_j-x_k|\le c(\alpha)|e^{-ix_j}-e^{-ix_k}|.
\]

Multiply squared inequalities by \(|Z_{jk}|^2\) and sum: \(\|[X,Z]\|_F\le c(\alpha)\|[e^{-iX},Z]\|_F\) for every matrix \(Z\). Apply this with \(X=s(H_1-a_1I),Z=s(H_2-a_2I)\), and again in the second generator's eigenbasis. Scalar shifts only change irrelevant phases. The lower bound follows from the double Duhamel integral for the exponential commutator.

For \(P_r(t)=(e^{-itH_1/r}e^{-itH_2/r})^r\), variation of constants and a unitary telescope give

\[
\frac{\|P_r(t)-e^{-it(H_1+H_2)}\|_F}{\sqrt d}
\le\frac{t^2C_F}{2r}
\le\frac{t^2c(\alpha)c(\beta)\sqrt{p_s}}{rs^2}. \tag{WC9}
\]

For a pure-input ensemble \(\mathcal E\) whose mean is \(I/d\), the left side is exactly the RMS vector error, because \(\mathbb E_{\psi\sim\mathcal E}\|D\psi\|_2^2=\operatorname{Tr}(D^\dagger D)/d\). It also bounds mean vector error and mean output trace distance. Mean absolute error for an observable of operator norm at most one is at most twice (WC9). This concerns labeled random pure inputs or a reference-sensitive task: evolving an unlabelled \(I/d\) state alone is trivial for every unitary.

Without the spectral bound, (WC8) is false: \(H_1=\pi X/s,H_2=\pi Z/s\) give \(A_s=B_s=-I\) and \(p_s=0\), although \(e^{-is(H_1+H_2)}\) differs from the product. Small finite-time commutation alone cannot validate a Trotter step.

### Complete finite-shot decision and resource action

Fix \(s\), confidence failure probability \(\eta\), calibration shot count \(N\), simulation time \(t\), and allowed mean trace error \(\epsilon\). Prepare \(I/d\) by uniformly sampling computational-basis inputs. Run independent standard SWITCH trials and count minus outcomes \(K\). Any valid one-sided Bernoulli upper bound \(p_U(K,N,\eta)\) suffices. A fully explicit choice valid for every count is

\[
p_U=\min\!\left\{1,\frac KN+\sqrt{\frac{\log(1/\eta)}{2N}}\right\}.
\]

An exact binomial upper bound is sharper, especially for rare minus events: at \(K=0\), use \(p_U=1-\eta^{1/N}\). The confidence statement is \(\Pr[p_s\le p_U]\ge1-\eta\), over the calibration outcomes. Suppose a supplied conservative bound satisfies \(C_0\ge C_F\), with baseline \(r_0=\max\{1,\lceil t^2C_0/(2\epsilon)\rceil\}\). Define the capped certificate

\[
C_{\rm cert}=\min\left\{C_0,\frac{2c(\alpha)c(\beta)\sqrt{p_U}}{s^2}\right\}.
\]

The minimum certified step count used below is

\[
r=\max\!\left\{1,\left\lceil
\frac{t^2C_{\rm cert}}{2\epsilon}
\right\rceil\right\}. \tag{WC10}
\]

On the coverage event \(p_s\le p_U\), this \(r\le r_0\) has mean trace error at most \(\epsilon\). Thus the probability that this data-dependent certificate is invalid is at most \(\eta\). If several probe times or stopping points are examined, allocate confidence failure probabilities across all tests or use a valid confidence sequence; a fixed-time interval does not justify arbitrary adaptive stopping.

Calibration can reduce the certified Trotter count from \(r_0\) to \(r\), saving \(2(r_0-r)\) analog evolution blocks per production execution. The minimum-count variant uses \(2N+2Mr\) native forward calls on its realized calibration history, versus \(2Mr_0\) for the conservative policy. The following fixed-target policy makes both acceptance and rejection costs explicit.

Here is a directly reviewable acceptance condition. Preselect an integer \(1\le r_*<r_0\). If the observed upper bound satisfies

\[
p_U\le q_*:=\left(\frac{\epsilon s^2r_*}{t^2c(\alpha)c(\beta)}\right)^2,
\qquad N<M(r_0-r_*), \tag{WC11}
\]

then \(r\le r_*\). Define acceptance by the displayed \(p_U\) threshold. Upon acceptance run the preselected \(r_*\) steps; upon rejection use \(r_0\). The second inequality in (WC11) proves strict total forward-call savings on an accepted history. It is not an expected-policy guarantee. More precisely,

\[
\Pr[\mathrm{accept}\ \text{and the }r_*\text{-step mean-error certificate is invalid}]
\le\Pr[p_s>p_U]\le\eta. \tag{WC12}
\]

This is a frequentist false-acceptance statement, not posterior confidence \(1-\eta\) conditional on acceptance. Writing \(a=\Pr[\mathrm{accept}]\), the latter conditional failure probability is bounded only by \(\min\{1,\eta/a\}\) when \(a>0\).

The complete forward-call ledger for this fixed-target native policy is

\[
Q_{\rm accept}=2N+2Mr_*,\qquad
Q_{\rm reject}=2N+2Mr_0,
\]

\[
\mathbb E Q=2N+2M\bigl[r_0-a(r_0-r_*)\bigr]. \tag{WC13}
\]

Consequently \(N<Ma(r_0-r_*)\) is sufficient for expected net savings over \(2Mr_0\). If an accepted run instead uses the smaller capped count \(r\), (WC13) becomes an upper bound and the same condition remains sufficient. The acceptance rate \(a\) is an additional quantity; one accepted calibration does not establish it. The weaker observed condition (WC11) establishes only savings on that accepted history.

Use the best applicable prior \(C_0\), such as a locality-aware spectral commutator bound; taking a needlessly loose \(2\|H_1\|\|H_2\|\) bound would inflate the advertised saving. The shared step reduction is a comparison within first-order product-formula simulation, not against every higher-order, randomized, or signal-processing simulator.

Every calibration trial also consumes one target preparation, control preparation and control readout, plus its native coherent-order resource. The ordinary simulator adds a dummy-register preparation and controlled routing operations. Every production execution consumes its input preparation, final measurement, and digital basis rotations; the cited DAQS decomposition has two global basis rotations per step. These are extra charged resources, not free queries. The explicit saving in (WC11) concerns forward evolution-block calls; it is not a claim about total gates, elapsed time, or integrated Hamiltonian evolution time. Production measurements used to estimate observables have their own statistical precision requirement, separate from calibration confidence \(\eta\).

Small \(p_s\) is not free to estimate. With a sharp binomial or multiplicative interval, constant-relative estimation needs \(O(p_s^{-1}\log(1/\eta))\) independent shots. For extensive local fragments, safe \(s=\Theta(1/n)\) with \(C_F=\Theta(\sqrt n)\) can give \(p_s=\Theta(n^{-3})\), hence cubic shot cost with those sharper intervals. The displayed additive Hoeffding interval alone would instead need sixth-order shot scaling for that precision. Calibration amortization and the actual probe costs must count.

### Strong ordinary comparators and exact claim boundary

* **Opaque unitary modules:** the definite-order unitary SWITCH simulator uses two calls to one arm and one to the other, one extra \(d\)-dimensional dummy register, and controlled swaps. It reproduces every control outcome exactly using only forward calls; no inverse or controlled unknown arm is needed. The minimum-count variant costs \(3N+2Mr\); the fixed-target policy costs \(3N+2Mr_*\) on acceptance and \(3N+2Mr_0\) on rejection. Its acceptance distribution and error guarantee are identical to the native protocol, and it can duplicate the cheaper arm if costs differ. See [Bavaresco et al., Nature Communications 16, 10216 (2025)](https://pmc.ncbi.nlm.nih.gov/articles/PMC12635086/), Eqs. (4)–(5), with Theorem 1 giving a stronger extension. The native protocol saves exactly \(N\) forward calls against this specific tester on every history, a factor of \(3/2\) for calibration calls. This proves no lower bound on the useful threshold decision (WC10).
* **Known controlled arm/circuits:** the ordinary before/after controlled-arm construction reproduces the meter; count its known-gate implementation costs. Ideal circuit knowledge does not grant the actual noisy dilation. Conversely, hiding a gate description that the workload already provides would fabricate an advantage.
* **Explicit Pauli fragments:** collect equal strings in \([H_1,H_2]=\sum_R\gamma_RR\); then \(C_F^2=\sum_R|\gamma_R|^2\). Pair enumeration is polynomial in the supplied term-list lengths and often sparse. This computes the actual quantity needed by (WC9), bypassing both finite-time exponentials and rare-event meter shots. It is the decisive classical shortcut for standard specified spin models.
* **Opaque local Hamiltonians:** the ordinary Hamiltonian-learning workflow cited above estimates actual coefficients and target mismatch. No superiority over that learner is proved. A four-call controlled group-commutator trace test with inverses is therefore an unnecessarily weak sole baseline.

The certificate bounds splitting error relative to the sum of the actual generators. It does not establish agreement with the intended generator. If a separate bound \(\|H_1+H_2-H_{\rm target}\|_F/\sqrt d\le\Delta\) is supplied, Duhamel adds \(t\Delta\) to (WC9). Without such information, commuting but wrong generators can have \(p_s=0\) and large target error. Nonunitary modules, drift, shared environments and uncontrolled temporal memory require further theorems.

Thermal inputs do not automatically inherit (WC9). For any input ensemble with mean \(\rho\le\kappa I/d\), its RMS error is at most \(\sqrt\kappa\) times the normalized-Frobenius error; this can be weak for Gibbs states. A single thermal-weighted \(p_s(\rho)\) does not supply the unitary invariance used in the global telescope. The clean result here is random-input/infinite-temperature metric certification.

There is a useful sector version: if a supplied projector \(\Pi\) commutes with both actual generators, restrict the entire proof to \(\Pi\mathcal H\), replace \(d\) by \(d_\Pi\), and probe \(\Pi/d_\Pi\). Random computational-basis states with a fixed excitation number then suffice when the blocks conserve that number. In the ideal Heisenberg decomposition above, \(H_{XY}\) and \(H_{ZZ}\) both conserve total magnetization, so this includes infinite-temperature dynamics within a fixed magnetization sector. Conservation by the intended generators alone does not justify the restriction if actual opaque blocks break it. [Chen and Brandão, Average-Case Speedup for Product Formulas, CMP 405, 32 (2024)](https://link.springer.com/article/10.1007/s00220-023-04912-5) independently establishes the relevance of fixed-particle-number input subspaces in average-case product-formula analysis; the finite-step sector certificate follows here simply by restriction.

<a id="nr-r06-trotter-query-advantage"></a>

## A query advantage for the actual one-step accuracy decision

The preceding theorem gives a common simulation application and an explicit ordinary comparator. The following restricted certification benchmark also transfers a known query obstruction to the **useful accuracy decision**, rather than merely to exact estimation of its sufficient scalar. It is a promised opaque-generator subproblem of adaptive Trotter certification, not an advantage theorem for every Heisenberg implementation or explicit Hamiltonian description.

### Task, input metric and access

Fix $s>0$, $h=\pi/(2s)$, and an accuracy threshold $0<\epsilon<2/3$. The actual stationary generators are

$$
H_1=\sigma hP,\qquad H_2=\tau hQ,
\qquad P=P^\dagger,\ Q=Q^\dagger,\ P^2=Q^2=I,
\tag{WC14}
$$

where the unknown fixed signs $\sigma,\tau$ may independently be $\pm1$. Promise either $[P,Q]=0$ or $\{P,Q\}=0$. The hard qubit subfamily includes identity; excluding identity and allowing only two traceless qubit reflections changes the problem. Anticommuting invertible involutions exist only in even dimension. The lower bound below already holds for $d=2$ and extends to qubit registers by tensoring with spectators.

The scientific task is to decide **accept one Trotter step** or **refine** at simulation time $t=s$, with respect to mean output trace distance on a supplied global projective two-design of pure inputs. Global Clifford-state ensembles give efficient such preparation on qubit registers; arbitrary one-designs do not suffice for this lower-bound statement. A one-step acceptance service must accept every promised zero-error instance and reject every promised instance whose actual one-step mean error exceeds $\epsilon$. A policy that always refines is sound but does not solve this complete decision task.

The Hamiltonians are separate opaque forward-evolution interfaces. Calibration may use arbitrary states, references, known processing and adaptive times. A single known clock-controlled call $\exp[-iT\otimes H_j/h]$, for known Hermitian angle register $T$, is also admitted. Each invocation queries one specified Hamiltonian. There is no additional coherently indexed $\operatorname{SELECT}(H_1,H_2)$ interface, no hidden sequence of repeated contacts inside one counted call, and no supplied matrix, gate description or canonical controlled-reflection gate. Clock control includes the actual unknown sign in (WC14). This is a contact-count model, not a total-evolution-time or hardware-clock comparison.

### The labels force different actual simulation decisions

At $t=s$, the implemented one-step product is

$$
V=e^{-isH_1}e^{-isH_2}=-\sigma\tau PQ.
$$

If $P,Q$ commute, this equals $U=e^{-is(H_1+H_2)}$ exactly. If they anticommute, put $c=\cos(\pi/\sqrt2)$ and $z=\sin(\pi/\sqrt2)$. Then

$$
U=cI-\frac{iz}{\sqrt2}(\sigma P+\tau Q),\qquad
V^\dagger U=\sigma\tau cPQ-\frac{iz}{\sqrt2}(\sigma P-\tau Q).
$$

Conjugation by the other involution shows $\operatorname{Tr}P=\operatorname{Tr}Q=0$, and cyclicity shows $\operatorname{Tr}PQ=0$. Thus $W=V^\dagger U$ is a traceless unitary. The global two-design second-moment identity gives

$$
\mathbb E_\psi |\langle\psi|W|\psi\rangle|^2
=\frac{\operatorname{Tr}WW^\dagger+|\operatorname{Tr}W|^2}{d(d+1)}
=\frac1{d+1}.
$$

Since pure-state trace distance satisfies $D_\psi^2=1-|\langle\psi|W|\psi\rangle|^2$ and $0\le D_\psi\le1$,

$$
\mathbb E_\psi D_\psi\ \ge\ \mathbb E_\psi D_\psi^2
=\frac d{d+1}\ge\frac23.
\tag{WC15}
$$

Consequently the commuting and anticommuting labels require opposite answers to the stated **actual-error** decision. This would fail for an arbitrary one-design: an eigenbasis of $W$ has zero output-state trace distance despite being a one-design. The two-design assumption is therefore material, while the earlier upper certificate (WC9) still needs only a one-design.

At the calibration time $s$, the two supplied channels are $\operatorname{Ad}_P,\operatorname{Ad}_Q$. A single native SWITCH gives $p_-=0$ in the commuting case and $p_-=1$ in the anticommuting case, on every calibration input. One control measurement decides the promised accuracy question perfectly using one call to each Hamiltonian. The common bounds $\alpha=\beta=\pi/2<\pi$, with centers zero, satisfy (WC8). For a safe fallback one may use

$$
r_{\rm safe}=\left\lceil\frac{\pi^2}{4\epsilon}\right\rceil,
$$

because $C_F\le2h^2$ gives (WC9) at most $\pi^2/(4r)$. This fallback and one-step acceptance concern the sum of the actual generators; intended-target mismatch remains a separate budget.

### Analytic ordinary obstruction and variable-time access

[Chiribella, PRA 86, 040301(R) (2012)](https://arxiv.org/html/1109.5154v2), Eqs. (7)–(8) and Appendices A–B, proves that two averaged no-signalling qubit channels cannot be perfectly discriminated by any one-call-per-side sequential tester, in either order. The zero-overlap condition contradicts tester normalization. For the present reduction, write $R_U=UZU^\dagger$ and

$$
\mathcal M_U=\tfrac12(\mathrm{id}+\operatorname{Ad}_{R_U}),\quad
\mathcal C_0=\int dU\,\mathcal M_U\otimes\mathcal M_U,\quad
\mathcal C_1=\int dU\,\operatorname{Ad}_{UXU^\dagger}\otimes\operatorname{Ad}_{UYU^\dagger}.
$$

The first is an average of commuting pairs $(I,I),(I,R_U),(R_U,I),(R_U,R_U)$; the second averages anticommuting pairs. A universal exact classifier for these involutions with one bare call per port would distinguish these channels, contradicting the analytic theorem. This imports the published discrimination obstruction; it is not a new proof of causal nonseparability or an asymptotic separation.

Bare-reflection access alone would not justify a Hamiltonian lower bound, because fractional evolution can be stronger. The independent signs in (WC14) supply an exact reduction. For any known clock $T$, averaging one call over its unknown sign gives

$$
\frac12\sum_{\sigma=\pm1}\operatorname{Ad}_{e^{-i\sigma T\otimes P}}
=\mathcal K_0+\mathcal K_1,\qquad
K_0=\cos T\otimes I,\quad K_1=-i\sin T\otimes P.
\tag{WC16}
$$

Implement the known signed Kraus instrument $\{\cos T,-i\sin T\}$ on the clock, then query bare $P$ on the target only for outcome 1; a discarded dummy query may pad outcome 0. This reproduces the whole sign-averaged call, including references, with at most one bare-$P$ contact. Using only positive square-root effects without the known signs/phases would not give the same instrument. Independent sign averages compose for one invocation of each Hamiltonian, including classical adaptive durations and the displayed coherent clocks. The signs are fixed unknown instance parameters, not fresh physical noise per production run.

Thus any universal one-call-per-Hamiltonian perfect accuracy classifier would produce the forbidden ordinary tester. The reduction also yields a bounded-error statement without assigning a numerical constant: normalized finite-dimensional two-slot testers, both orders and their convex mixtures form a compact set; their success on the fixed $\mathcal C_0/\mathcal C_1$ prior is continuous. The analytic absence of a perfect tester implies an attained maximum $1-\delta_0<1$. Therefore some fixed $\delta_0>0$ lower-bounds prior error, and hence worst-case error, for every ordinary **one-per-Hamiltonian** classifier in this model. Native error is zero. No value of $\delta_0$ or generic repeated-port bounded-error lower bound is asserted.

### Exact two-versus-three contacts and computational payoff

For exact decisions, two total ordinary calls with classical port allocation also cannot evade the obstruction by querying the same port twice. After a first query to a nontrivial qubit $P$, a branch spending its last query on $P$ has no $Q$ information; that same $P$ admits both $Q=I$ and an anticommuting $Q$. Exact correctness forces such a branch to have zero probability. A positive-probability repeated-port branch can therefore occur only on the scalar-identity subfamily, whose answer is already accept. Replace that branch by accept and pad the unused other port on a discarded dummy. This converts any perfect two-total-call policy into a one-per-port tester. The same argument applies when the other Hamiltonian is queried first. It is an exact classical-port-allocation argument, not an extension of $\delta_0$ to arbitrary two-total-call bounded-error policies.

Three ordinary fixed-duration unitary contacts suffice using the exact two-$P$, one-$Q$ controlled-routing construction; it returns the same control statistic. Hence the worst-case exact calibration cost for this complete promised decision is **two native contacts versus three ordinary contacts** under the stated interfaces. An efficient circuit description, canonical controlled-reflection access, coherent SELECT across the two ports, or a weaker safety-only task changes that comparison.

For $M$ subsequent simulations, the native exact policy spends $2+2M$ evolution-block calls on a commuting instance, or $2+2Mr_{\rm safe}$ on an anticommuting one. The ordinary three-contact implementation spends one extra calibration contact with the same production policy. Relative to always using $r_{\rm safe}$, native acceptance saves $2M(r_{\rm safe}-1)-2$ contacts when positive. All preparations, global two-design production sampling, native routing and controller cycles, ordinary dummy/routing operations, digital basis rotations, storage and readout remain additional resource-vector components. This is neither a claim about expected stopping-query optima nor a total gate/runtime advantage.

The common workload is simulation-depth certification; the lower-bound instance is a restricted ideal reflection promise. It demonstrates a theoretical query advantage for a useful certification decision, with no claim of a growing system-size separation, noisy-processor threshold, generic DAQS superiority, first priority, or new quantum-versus-classical algorithm theorem.

## Current disposition

Lightcone shading supplies real demand and (WC1) supplies an exact operational link. Equations (WC2)–(WC4) and the fixed-arm compiler prevent calling that a SWITCH separation. Equation (WC5) is a candidate bridge to serial compilation. Equations (WC8)–(WC13) establish a direct measured-scalar application: certified average-case Trotter depth, including accepted/rejected calibration and bounded ordinary-query comparisons. Equations (WC14)–(WC16) additionally give an exact two-versus-three contact advantage for the complete one-step accuracy decision on the stated signed-reflection promise, with an existential bounded-error gap for the one-per-port class. Neither result proves an optimal general simulator or an advantage on explicit Pauli lists, structured local learning or additional SELECT interfaces. Generic noisy-device and larger workload separations remain open.
