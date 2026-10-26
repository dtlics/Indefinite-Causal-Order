<a id="nr-r22"></a>

# NR-R22 — Hidden noise memory and universal capacity qualification

This is a theoretical characterization task with a classical decision output. It reuses the existing C5 fixed-hidden-basis indistinguishability theorem; it introduces no new lower-bound method. A coherent order interface is an explicit resource of the model, not an inferred hardware capability.

## Oracle and decision

Let $d=2^n\ge2$, $\Omega(X)=\operatorname{Tr}(X)I/d$, and
$\Delta_U(X)=\sum_iP_i^UXP_i^U$, where $P_i^U=U|i\rangle\langle i|U^\dagger$.
There are two hypotheses for ONE characterization session:

* **Quasistatic disorder:** a physical private classical register draws one Haar $U$ at session initialization and keeps it throughout every call, calibration experiment and measurement round. Each call applies $\Delta_U$ with a fresh private measurement meter.
* **Rapid fluctuations:** each new invocation has an independently Haar-drawn basis and a fresh private meter.

The learner receives input-output access. It may prepare arbitrary mixed or entangled probes, keep arbitrary finite quantum memory, use arbitrary known quantum instruments, reset its payload, adapt its classical query choices, stop early, and make a collective final measurement. All oracle calls count toward a worst-case total budget $q$. Basis registers, measurement outcomes and environment records are inaccessible. Initial advice or probes do not depend on $U$. There is no free session restart that redraws the quasistatic basis; that is a separate access model. A payload reset does not reset this hidden register.

The output chooses a persistent-latent-frame error model or a product-of-one-use-marginals error model. Success is the unconditional probability of correctly identifying the hypothesis, averaged over the specified physical disorder and balanced hypotheses. No conditioning on a successful diagnostic outcome is allowed.

## Identical snapshots, different processes

The Haar second moment gives, on all matrices and hence with arbitrary references,

$$
\mathbb E_U\Delta_U=\Lambda=
\frac{\operatorname{id}+d\Omega}{d+1}.
$$

Thus every single-use characterization experiment has exactly the same averaged output under the two hypotheses. This is an identifiability statement about snapshots, not an impossibility statement about ordinary multi-use characterization.

Conditioned on a particular fixed $U$, $\Delta_U$ itself is a memoryless channel. The quasistatic **averaged session process** has classical memory because the private basis is physically shared across uses. For example, prepare $|\psi\rangle$, measure whether its output returns to $|\psi\rangle$, reset the payload to that same state, and repeat. Writing $a(U)=\sum_i|\langle\psi|U|i\rangle|^4$, the two-record covariance is $\operatorname{Var}_U a(U)>0$ for quasistatic disorder and zero for rapid fluctuations. The reset breaks payload memory but not the hidden basis. This is not a claim of quantum memory, information backflow, or generic non-Markovianity of an unknown fixed calibration parameter.

## Coherent two-invocation extension and test

The native interface coherently reorders two labelled invocations. Their private bases are sampled independently of routing and arrival time: both are the same session $U$ in the quasistatic case, while they are independent in the rapid case. A labelled invocation and its meter are paired across the two control histories as in the standard channel SWITCH. These joint rules are part of the oracle definition. One must not replace the quasistatic extension by a SWITCH of its averaged marginals.

Prepare a maximally mixed target and a $|+\rangle$ control. For a channel pair with Kraus operators $A_i,B_j$, write

$$
v=\operatorname{Re}\sum_{i,j}\operatorname{Tr}
 [A_i^\dagger B_j^\dagger A_iB_j]/d,
\qquad p_-=(1-v)/2.
$$

For two uses of $\Delta_U$, all projector Kraus operators commute, so $v_{\rm qs}=1$. Rapid invocations instead supply the standard independent-use SWITCH of $\Lambda$ with itself. Set $a=1/(d+1)$ and $b=d/(d+1)$. Identity/identity and identity/depolarizing cross terms have visibility one, while depolarizing/depolarizing visibility is $1/d^2$. Therefore

$$
v_{\rm rapid}=a^2+2ab+b^2/d^2=\frac{2}{d+1},\qquad
p_{-,\rm rapid}=\frac{d-1}{2(d+1)}\ge\frac16.
$$

Declare rapid fluctuations if any minus is observed. Seven rounds, using fourteen primitive noise invocations within the SAME session, have zero quasistatic error and rapid error at most $(5/6)^7<1/3$. More generally the invocation count is $O(\log(1/\delta))$ for error $\delta$. Quasistatic bases need not be redrawn between these rounds; rapid invocations are independent by definition.

## Ordinary-query lower bound from the actual C5 endpoint

For the complete output of any allowed $q$-query ordinary strategy, let $\rho_{\rm qs}$ average over the fixed Haar basis, and let $\rho_\Omega$ be the output with every query replaced by $\Omega$. The repository's actual physical endpoint
`ICO.OrdinaryHaarStates.adaptive_haar_distance` gives, for $q\ge1$ and $2q<d$,

$$
\tfrac12\|\rho_{\rm qs}-\rho_\Omega\|_1\le B(q,d):=
\frac{18(2q)(2q+1)}{d^{1/8}}
+\frac{4q}{\sqrt{d-2q}}+\frac{q^2}{d}.
$$

This already includes adaptive known processing, mixed inputs, entangled quantum memory and all early-stopping branches. Its normalized trace distance is exactly half the trace norm. The scalar endpoint `TestingBounds.distanceBound_le` establishes $B(q,d)\le509/10000$ when $1\le q\le d^{1/16}/100$; that regime also ensures the required dimensional conditions.

For rapid fluctuations the ordinary process is the memoryless channel $\Lambda$ at every call. Since

$$
\tfrac12\|\Lambda-\Omega\|_\diamond
=\frac{\tfrac12\|\operatorname{id}-\Omega\|_\diamond}{d+1}
\le\frac1{d+1},
$$

an adaptive, trace-preserving hybrid over all $q$ slots gives
$\tfrac12\|\rho_{\rm rapid}-\rho_\Omega\|_1\le q/(d+1)$.
Consequently, throughout the same small-query regime,

$$
\tfrac12\|\rho_{\rm qs}-\rho_{\rm rapid}\|_1
\le B(q,d)+q/(d+1)
\le\frac{609}{10000}<\frac13.
$$

The last inequality uses $d^{1/16}\le d$. Even the optimal final measurement then has balanced success at most $10609/20000<2/3$. Zero queries also fail. Thus success at least $2/3$ requires

$$
q>d^{1/16}/100=2^{n/16}/100.
$$

This is a scalar process-model decision lower bound, not a lower bound inferred from process-tomography size or from simulating the full SWITCH channel. It is the direct C5 reduction; a C6 composition reduction is possible but loses a factor two in this threshold. The exponent is not claimed optimal. Independently restarted sessions, exposed basis/outcome records, restricted efficiently learnable noise families, and a different coherent extension need their own analyses.

## Weak-noise extension

The same application need not apply a projective fault on every invocation. For supplied $0<t\le1$, replace each conditional slot by

$$
\mathcal E_{t,U}=(1-t)\operatorname{id}+t\Delta_U,
\qquad
\overline{\mathcal E}_t=(1-t)\operatorname{id}+t\Lambda.
$$

Active/skip coins are fresh, independent and private at every labelled invocation; the quasistatic $U$ is still held throughout the session. Their pre-sampled slot records are paired across control histories in the stated extension. The one-use averages are equal. Quasistatic Kraus operators $\sqrt{1-t}I$ and $\sqrt tP_i^U$ all commute, giving $p_{-,\rm qs}=0$. Writing the rapid map as
$[1-td/(d+1)]\operatorname{id}+[td/(d+1)]\Omega$ gives

$$
p_{-,\rm rapid}=\frac{t^2(d-1)}{2(d+1)}\ge\frac{t^2}{6}.
$$

The same any-minus test uses $O(t^{-2}\log(1/\delta))$ primitive invocations. This is polynomial for known $t\ge1/\operatorname{poly}(n)$.

For the ordinary lower bound, simulate each weak query by a private Bernoulli-$t$ coin, applying the strong oracle on active branches and identity otherwise. The total strong-oracle budget is at most $q$, and all skipped branches remain in the unconditional output. C5 therefore bounds the quasistatic weak process against $\mathcal R_t=(1-t)\operatorname{id}+t\Omega$ by the same $B(q,d)$. The rapid weak process differs from $\mathcal R_t$ by at most $t/(d+1)$ in half diamond distance per invocation. The adaptive triangle is consequently

$$
\tfrac12\|\rho_{\rm qs,t}-\rho_{\rm rapid,t}\|_1
\le B(q,d)+\frac{qt}{d+1}\le\frac{609}{10000}
$$

at the same query threshold. Thus $q>d^{1/16}/100$ is still necessary; no optimal dependence of the ordinary lower bound on $t$ is claimed. This reduction uses ordinary random mixing, not a free controlled call to the hidden channel or access to its active coin.

<a id="nr-r22-universal-capacity"></a>

## Universal coding consequence of one-session noise-model selection

This corollary qualifies an asymptotic unassisted quantum-storage or communication property using the same noise-model diagnostic. The encoder and decoder do not know the hidden basis. No efficient finite-block QEC implementation is claimed.

### Session and coding endpoint

Fix a known dimension $d=2^n$ and known $t=3/4$. Write $\tau=I/d$, $\Omega(X)=\operatorname{Tr}(X)\tau$, and $\Delta_U(X)=\sum_iP_i^UXP_i^U$, where $P_i^U=U|i\rangle\langle i|U^\dagger$. Define

$$
\mathcal E_{t,U}=(1-t)\operatorname{id}+t\Delta_U,
\qquad \mathfrak I_t=\{\mathcal E_{t,U}:U\in U(d)\}.
$$

In the **static** model, a private physical classical register draws one Haar $U$ at the start of the entire communication session. It remains fixed through any characterization, training and transmitted block. Conditional on $U$, different calls have fresh independent active/skip coins and dephasing meters. The $m$-contact production map, with the register inaccessible, is

$$
\mathfrak S_m=\int\mathcal E_{t,U}^{\otimes m}\,dU.
$$

In the **rapid** model, each invocation independently redraws the Haar basis as well. Its production map is $\overline{\mathcal E}_t^{\otimes m}$, where

$$
\overline{\mathcal E}_t=(1-t)\operatorname{id}+t\Lambda,
\qquad \Lambda=\frac{\operatorname{id}+d\Omega}{d+1}.
$$

These models have identical one-contact averaged channels. Their block maps differ: an integral of tensor powers is not a tensor power of the integral. No session restart or redraw of the static register is offered within a diagnostic or code. Independent sessions can have independent registers, but none are needed for the theorem below.

An unassisted $m$-contact code consists of one CPTP encoder $\mathcal A_m$ and decoder $\mathcal B_m$, fixed using $n,t$ and the family, not the actual $U$. Every input-bearing encoded system crosses the production channel; the decoder has no protected payload bypass, preshared entanglement or feedback assistance. The unknown message and its inaccessible purifying reference are independent of the physical noise register. Decoder failures are included in a TP output. Capacity means entanglement-transmission rate, with entanglement fidelity on the maximally mixed logical code approaching one as $m\to\infty$ at **fixed** $n$.

### The common-code theorem supplies the missing universal decoder

[Bjelaković, Boche and Nötzel, CMP 292, 55–97 (2009), arXiv:0811.4588v3](https://arxiv.org/html/0811.4588v3), §2.3 and Theorem 1, establish the uninformed-encoder, uninformed-decoder compound capacity for an arbitrary family on fixed finite-dimensional spaces:

$$
Q(\mathfrak I)=\lim_{\ell\to\infty}\frac1\ell
 \max_\rho\inf_{\mathcal N\in\mathfrak I}
 I_c(\rho,\mathcal N^{\otimes\ell}).
$$

Its operational requirement is one channel-independent pair of CPTP maps with $\inf_{\mathcal N\in\mathfrak I}F_e\to1$. Section 6.1, Theorem 18, supplies the general-family direct coding result. Thus an uncountable conjugated family is allowed; an informed decoder or supplied estimate of $U$ is unnecessary. The theorem is an asymptotic existence statement, without a polynomial circuit or blocklength guarantee. The older arXiv:0808.1007 finite-family uninformed result alone would not suffice.

Here $U\mapsto\mathcal E_{t,U}$ is continuous on compact $U(d)$, so the family is compact, although the cited theorem permits arbitrary sets. For $z\in\mathbb F_2^n$, put $W_z=UZ^zU^\dagger$. The commuting Hilbert–Schmidt-orthogonal unitaries give

$$
\Delta_U=\frac1d\sum_z\operatorname{Ad}_{W_z},\qquad
p_0=1-t+t/d,\quad p_z=t/d\quad(z\ne0).
$$

At input $\tau$, the output is $\tau$ and the orthogonal Choi error vectors have probabilities $p$. Consequently, for every $U$,

$$
I_c(\tau,\mathcal E_{t,U})=n-H(p)
\ge (1-t)n-h_2(t).
$$

For the inequality, retain a private Bernoulli active flag and, when active, a uniform $d$-valued phase label. Their entropy is $h_2(t)+t\log_2d$. Forgetting the active flag merges the two identity labels, producing $p$ and not increasing entropy. For the **common** product input $\tau^{\otimes\ell}$, coherent information adds for every fixed $U$. Inserting that same input before taking the infimum proves

$$
Q(\mathfrak I_t)\ge n-H(p)\ge \frac n4-h_2(3/4)>0
\qquad(n\ge4).
$$

This does not interchange a maximum and an infimum or select different inputs for different $U$.

For an exact rational rate witness, $3^{12}>2^{19}$ implies
$h_2(3/4)=2-(3/4)\log_2 3<13/16$. Thus the displayed rate is strictly greater than $n/4-13/16$, which is at least $3/16$ for $n\ge4$.

For every rate below this lower bound, the compound theorem supplies one sequence $(\mathcal A_m,\mathcal B_m)$ with fidelity tending uniformly to one over all $U$. Linearity of entanglement fidelity in the channel then gives

$$
\begin{aligned}
F_e(\pi_m,\mathcal B_m\mathfrak S_m\mathcal A_m)
&=\int F_e(\pi_m,\mathcal B_m\mathcal E_{t,U}^{\otimes m}\mathcal A_m)\,dU\\
&\ge\inf_U F_e(\pi_m,\mathcal B_m\mathcal E_{t,U}^{\otimes m}\mathcal A_m)
\longrightarrow1.
\end{aligned}
$$

Thus the physically averaged **static memory process itself** admits positive-rate entanglement transmission with a common encoder and decoder. This is stronger than merely observing that each conditional channel has its own positive-capacity code. Uniformity also permits any posterior distribution of $U$ after characterization: the same code can ignore the characterization record. The existence proof needs no basis calibration; any actual training calls are included in contact costs.

### The rapid production channel has zero unassisted capacity

Write

$$
\overline{\mathcal E}_t=(1-\beta)\operatorname{id}+\beta\Omega,
\qquad \beta=\frac{td}{d+1}\ge\frac12
\quad(t=3/4,\ d\ge2).
$$

This is receiver postprocessing of the $\beta$-erasure channel: replace the erasure flag by $\tau$. The erasure channel is antidegradable for $\beta\ge1/2$, as its environment receives the input with probability $\beta$ and can retain that state with probability $(1-\beta)/\beta$ to simulate the receiver. Output postprocessing preserves antidegradability, hence the rapid channel has zero unassisted quantum capacity.

For a direct finite-block guard, the same rapid channel has the symmetric two-output extension

$$
\mathcal J_\beta(\rho)
=(1-\beta)(\rho\otimes\tau+\tau\otimes\rho)
 +(2\beta-1)\operatorname{Tr}(\rho)\tau\otimes\tau.
$$

Its nonnegative weights sum to one, and either marginal is $\overline{\mathcal E}_t$. Apply $\mathcal J_\beta^{\otimes m}$ after a single encoder, then the same decoder to each output bank. For a $K$-dimensional logical system this gives a symmetric extension of the logical Choi state. The [existing NR20 code-verification argument](methods/memory-code-verification.md) gives

$$
2F_e\le\|\Phi_{RB_1}\otimes I_{B_2}
           +\Phi_{RB_2}\otimes I_{B_1}\|_\infty
=1+1/K.
$$

The norm follows by writing the projectors as $V_jV_j^\dagger$ with $V_1^\dagger V_2=I/K$. In particular every unassisted TP logical-qubit code has rapid-channel Bell fidelity at most $3/4$, irrespective of $m$. This finite-block ceiling does not follow from zero asymptotic capacity alone.

### Qualification advantage and a necessary finite-block cost

Under the coherent two-labelled-slot extension already specified in NR22, static invocations share their session $U$, while rapid invocations have independent pre-sampled bases; each labelled meter is paired across control histories independently of arrival time. The existing weak-noise calculation gives

$$
p_{-,\rm static}=0,\qquad
p_{-,\rm rapid}=\frac{t^2(d-1)}{2(d+1)}\ge\frac{t^2}{6}.
$$

The any-minus test therefore qualifies the positive-capacity static promise versus the zero-capacity rapid promise with $O(t^{-2}\log(1/\delta))$ invocations, constant in $n$ at $t=3/4$ and fixed error. This is SWITCH access for **diagnosis**. The property certified is ordinary unassisted production capacity. Giving SWITCH access, a noiseless helper or a protected input-bearing side channel to the production code would define a different capacity problem.

The same NR22 C5 reduction bounds the complete output distance of every strong ordinary $q$-query strategy, including entangled probes, quantum memory, calibration and collective readout:

$$
\tfrac12\|\rho_{\rm static}-\rho_{\rm rapid}\|_1
\le B(q,d)+\frac{qt}{d+1}\le\frac{609}{10000},
\qquad 1\le q\le d^{1/16}/100.
$$

Thus ordinary constant-error qualification still requires $q>2^{n/16}/100$. There is also a direct finite-block consequence that grants the known code and all its processing for free. Suppose a fixed, $U$-independent, $m$-contact unassisted TP code transmits a $K\ge2$ dimensional logical system with **Haar-average unconditional** static entanglement fidelity at least $7/8$. Prepare a logical Bell pair, encode one half, use the $m$ contacts, decode, and perform its Bell test. The static event probability is at least $7/8$, while the rapid event probability is at most $(K+1)/(2K)\le3/4$.

The single event therefore has gap at least $1/8>609/10000$. It contradicts the existing complete-output C5 bound whenever $1\le m\le d^{1/16}/100$. Consequently

$$
m>d^{1/16}/100.
$$

Only the Haar-average fidelity hypothesis is needed; uniform fidelity is stronger. The diagnostic Bell reference is inaccessible to the decoder and supplies no payload bypass. Free channel-dependent advice or a retained $U$-correlated quantum program is outside this corollary; if learned, all preparation and calibration contacts enter the same total ledger. A postselected-only fidelity with uncounted failures is also a different endpoint.

Accordingly, the universal existence theorem and the exponential finite-block obstruction are compatible: its limit is $m\to\infty$ at fixed $n$. This is a separation in **capacity and noise-model qualification**, not an efficient universal QEC construction or an end-to-end QEC runtime advantage. It does not promise a finite-code worst-input or diamond-norm error, a useful finite block, or an efficient encoder/decoder. The static basis must persist over the whole block; an arbitrarily varying basis or a redraw between coding subblocks is a different model. Training, restarts or an actual code-execution benchmark must use their stated access and count all channel calls.

Dependencies are the one-session theorem and weak-noise hybrid above, the cited uninformed-user compound theorem, and the existing NR20 symmetric-extension code-verification proof. The rate witness, static-mixture transfer and finite-block C5 corollary are derived here, not attributed as claims of the compound-channel paper.

## Error-characterization consequence and limits

The decision determines whether a model used to predict repeated noise contacts may multiply the one-use averaged channel, or must keep a persistent hidden-frame variable. For bare consecutive contacts and $a=1/(d+1)$, quasistatic idempotence gives the weak-noise ensemble attenuation

$$
\lambda_{\rm qs}(L)=a+(1-a)(1-t)^L,
\qquad
\lambda_{\rm rapid}(L)=[1-t+ta]^L
$$

on a fixed traceless observable and input independent of the hidden frame. The strong case $t=1$ reduces to $a$ versus $a^L$. A noise-scaling or QEM calibration pipeline choosing between a product-marginal law and a persistent-disorder law is making an operationally different modeling decision despite identical one-use data. Convexity gives $0\le\lambda_{\rm qs}(L)-\lambda_{\rm rapid}(L)\le a$ for $L\ge1$, so no large mean-observable benefit is hidden in this statement.

The diagnostic does not learn the hidden basis or prove a QEM sampling improvement. Its capacity corollary establishes common-code existence, while the finite-block lower bound prevents interpreting that existence as an efficient universal QEC implementation. The ensemble-prediction statement does not grant the learner independent session restarts. Interleaved noncommuting gates or inputs chosen using basis-correlated training data require a conditional calculation; the bare-contact scalar law does not transfer automatically. The absolute mean-observable difference in this example is small, so a large characterization-query advantage is not itself a large computation-quality advantage.

Primary context: [Gao et al., PRL 130, 170201 (2023)](https://arxiv.org/html/2208.06210v3), Eqs. (7)--(10) and Appendix C, supply the representation-independent SWITCH noncommutativity measurement and dimension-independent sampling mechanism. [Pollock et al., PRL 120, 040405 (2018)](https://arxiv.org/abs/1801.09811) give the operational process-memory distinction using interventions and causal breaks. The particular two-hypothesis task and the C5 hybrid above are this analytic application corollary, not claims attributed to those papers.

The closest conceptual precedent is [Kristjánsson, Mao and Chiribella, PRResearch 3, 043147 (2021)](https://arxiv.org/abs/2004.06090): coherent temporal/path access already reveals latent noise correlations and can change communication capacity. The present application is a one-session qualification theorem against strong adaptive ordinary channel access, using the existing C5 bound and a standard compound-coding theorem. It claims neither the first temporal-correlation interferometer nor a new memory-capacity phenomenon. Coherent vacuum/time extensions supply different oracles and require their own comparison.

Dependencies: [C5 owner](../c5-interference-testing/README.md); [formal correspondence](../../../proofs/lean/THEOREMS.txt), C5 adaptive fixed-basis indistinguishability; [fixed-basis endpoint](../../../proofs/lean/ICO/OrdinaryHaarStates.lean); [scalar constants](../../../proofs/lean/ICO/TestingBounds.lean). Selected finite identities are exercised by the [exact application checker](checks/architecture/verify_theory_applications.py). The all-dimension Haar, adaptive-query and interface arguments remain analytic; no new Lean endpoint or kernel audit is claimed.
