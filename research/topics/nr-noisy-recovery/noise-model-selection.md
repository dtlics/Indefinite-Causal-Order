<a id="nr-r22"></a>

# NR-R22 — One-session noise-model selection from order interference

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

## Error-characterization consequence and limits

The decision determines whether a model used to predict repeated noise contacts may multiply the one-use averaged channel, or must keep a persistent hidden-frame variable. For bare consecutive contacts and $a=1/(d+1)$, quasistatic idempotence gives the weak-noise ensemble attenuation

$$
\lambda_{\rm qs}(L)=a+(1-a)(1-t)^L,
\qquad
\lambda_{\rm rapid}(L)=[1-t+ta]^L
$$

on a fixed traceless observable and input independent of the hidden frame. The strong case $t=1$ reduces to $a$ versus $a^L$. A noise-scaling or QEM calibration pipeline choosing between a product-marginal law and a persistent-disorder law is making an operationally different modeling decision despite identical one-use data. Convexity gives $0\le\lambda_{\rm qs}(L)-\lambda_{\rm rapid}(L)\le a$ for $L\ge1$, so no large mean-observable benefit is hidden in this statement.

This does not learn the hidden basis, implement an error correction, or prove a QEM sampling improvement. The ensemble-prediction statement does not grant the learner independent session restarts. Interleaved noncommuting gates or inputs chosen using basis-correlated training data require a conditional calculation; the bare-contact scalar law does not transfer automatically. The absolute mean-observable difference in this example is small, so a large characterization-query advantage is not itself a large computation-quality advantage.

Primary context: [Gao et al., PRL 130, 170201 (2023)](https://arxiv.org/html/2208.06210v3), Eqs. (7)--(10) and Appendix C, supply the representation-independent SWITCH noncommutativity measurement and dimension-independent sampling mechanism. [Pollock et al., PRL 120, 040405 (2018)](https://arxiv.org/abs/1801.09811) give the operational process-memory distinction using interventions and causal breaks. The particular two-hypothesis task and the C5 hybrid above are this analytic application corollary, not claims attributed to those papers.

Dependencies: [C5 owner](../c5-interference-testing/README.md); [formal correspondence](../../../proofs/lean/THEOREMS.txt), C5 adaptive fixed-basis indistinguishability; [fixed-basis endpoint](../../../proofs/lean/ICO/OrdinaryHaarStates.lean); [scalar constants](../../../proofs/lean/ICO/TestingBounds.lean). Selected finite identities are exercised by the [exact application checker](checks/architecture/verify_theory_applications.py). The all-dimension Haar, adaptive-query and interface arguments remain analytic; no new Lean endpoint or kernel audit is claimed.
