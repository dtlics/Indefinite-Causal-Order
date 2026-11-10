<a id="nr-r26"></a>

# Eigenbasis susceptibility and ordinary OTOC baselines

[Investigation handoff](README.md) · [Application assessment](../architecture.md)

**Status and scope.** Measurement interpretation and scoped no-go screens only; a practical or asymptotic advantage for a natural Hamiltonian family has not been established. These are supplied analytic derivations and scoped computational checks, not a new Lean audit or a publication-priority claim. See [verification scope](checks/README.md).

## 9. OTOCs: exact ordinary reproduction remains the first screen

### Proposition 6: known-arm compilation

For a known controllable unitary M and arbitrary channel B, the fixed chronological circuit

\[
C_0(M)\longrightarrow B\longrightarrow C_1(M)
\]

has Kraus operators |0><0| tensor B_j M + |1><1| tensor M B_j. It exactly reproduces the switch with one unknown B call, including arbitrary references. Noise in B does not invalidate the identity.

For Hermitian involutions M and B, let R_k=B(MB)^{k-1}. It is a palindrome and an involution, with M R_k=(MB)^k. The switch of M and R_k measures Re Tr[rho(MB)^{2k}], but the same known-arm construction reproduces it. If B=U^†O_2U, both methods use k forward and k inverse evolutions.

This blocks the naive transfer of the ordinary quantum-over-classical OTOC benchmark [L11] into a switch-over-ordinary advantage. It does not say that the OTOC is classically easy.

### Replayable random-unitary implementation

If A and B are implemented by experimenter-selected random unitaries, and a selected realization can be repeated, sample one realization of each and use the ordinary unitary ABA simulator. Averaging yields S[A,B] by bilinearity. Hidden unrepeatable realization access and controllable sampled-trajectory access are not interchangeable.

## 10. Eigenbasis susceptibility: a full measurement result, not yet an advantage theorem

Let H(lambda)=H_0+lambda V have a nondegenerate spectrum in a neighborhood of zero. Write P_i(lambda) for its rank-one eigenprojectors, smoothly labeled. Suppose the corresponding unread dephasers are actually available. Then

\[
v(lambda)=\frac1d\sum_{ij}|\langle i(0)|j(lambda)\rangle|^4.
\]

Define

\[
\bar\chi_F=\frac1d\sum_i\sum_{j\ne i}
\frac{|V_{ji}|^2}{(E_i-E_j)^2}.
\]

### Proposition 7: switch susceptibility identity

\[
1-v(lambda)=2lambda^2\bar\chi_F+O(lambda^3),
\qquad p_-(lambda)=lambda^2\bar\chi_F+O(lambda^3). \tag{18}
\]

**Proof.** Nondegenerate perturbation theory gives the diagonal transition probabilities 1-lambda^2 chi_i+O(lambda^3) and off-diagonal probabilities lambda^2 |V_ji|^2/(E_i-E_j)^2+O(lambda^3). Squaring these probabilities, summing over both indices, and dividing by d gives (18). The leading contributions of off-diagonal fourth powers start at order lambda^4. QED.

This equals the normalized Frobenius norm squared of the off-diagonal, unregularized adiabatic gauge potential. The scientific interpretation comes from [L10]. It is not automatically the same as a frequency-cutoff or regularized AGP used in a particular many-body study.

### Bias and sample cost

If |v''''(x)|<=B_4 for |x|<=lambda, then the symmetric estimator

\[
\hat\chi=\frac{\hat p_-(lambda)+\hat p_-(-lambda)}{2lambda^2}
\]

has deterministic finite-difference bias at most B_4 lambda^2/48. This follows from fourth-order Taylor remainder and cancellation of odd terms. A spectral gap/smoothness argument must justify B_4; it is not a universal constant independent of the Hamiltonian.

With N independent samples at each sign,

\[
\mathrm{Var}(\hat\chi)
\le\frac{p_-(lambda)+p_-(-lambda)}{4Nlambda^4}
=\frac{\bar\chi_F}{2Nlambda^2}+O(N^{-1}).
\]

In the controlled perturbative regime, constant relative precision r needs order log(1/delta)/(r^2 lambda^2 bar_chi_F) trials. Making lambda smaller reduces finite-difference bias but suppresses the signal. All channel-generation time, coherent routing, and p_- apparatus errors must be included.

### Proposition 8: exact spectral dephasing has an expensive random-evolution realization

Suppose a proposed dephaser is only the time average

\[
D_{H,mu}(rho)=\mathbb E_{t\sim mu}[e^{-iHt}rho e^{iHt}],
\]

with mean absolute evolution time E|t|<=T. Let g_min>0 be the smallest nonzero eigenvalue gap. On its two corresponding eigenstates, the coherence multiplier is phi(g)=E[e^{-igt}]. The inequality

\[
|phi(g)|\ge1-|g|T
\]

follows from |e^{-igt}-1|<=|g t|. A superposition of those two eigenstates gives

\[
D(D_{H,mu},Delta_H)\ge |phi(g)|/2.
\]

Therefore approximating full spectral dephasing within half-diamond error eta<1/2 requires

\[
T\ge\frac{1-2eta}{g_{\min}}. \tag{19}
\]

If d distinct energies occupy bandwidth W, then g_min<=W/(d-1), hence

\[
T\ge(1-2eta)(d-1)/W. \tag{20}
\]

For polynomial bandwidth and d=2^n, this time cost is exponential. This theorem applies to the random-evolution realization just specified, not arbitrary controlled measurement hardware. A native irreversible eigenbasis meter might be a different resource, but must be justified rather than treated as free.

Together with replayable-trajectory compilation, this means the susceptibility identity is scientifically useful but presently does not establish a scalable switch advantage for ordinary Hamiltonian-simulation hardware.


## Source pointers

The supplied susceptibility interpretation cites Pandey et al., arXiv:2004.05043; the known-circuit benchmark is arXiv:2610.32595. The general known-arm compiler is also owned by [workload commutators](../methods/workload-commutators.md), and its fixed-dilation contractivity use by [robust C6 applications](../../c6-hidden-dephasing/applications.md#c6-r08-robust). No new ordinary-versus-switch advantage is proved for known local Hamiltonian circuits.
