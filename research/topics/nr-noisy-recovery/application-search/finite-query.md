<a id="nr-r24"></a>

# Exact two-call discrimination certificate

[Investigation handoff](README.md) · [Application assessment](../architecture.md)

**Status and scope.** Supporting finite-size result, not the intended substantial application. Independent of C5/C6, but no statement about eight-call or unbounded-budget optimality. Supplied analytical derivations and scoped checks; not a new Lean audit or a publication-priority claim.

## Theorem

Let d=4 and suppose an unknown, fixed memoryless channel is drawn from a balanced prior:

* H: draw a Haar-random U once and give repeated access to its rank-one dephaser Delta_U. Use fresh private meters on every call; U remains fixed.
* L: give repeated access to Lambda=(id+4 Omega)/5, with fresh independent channel environments.

No U-correlated advice, device measurement records, inverse basis unitary, or controllable dilation is supplied. All training uses count. An ordinary strategy may use arbitrary ancillas, entanglement, intermediate instruments, adaptation, and a collective final measurement, with a hard maximum of two channel calls.

Then

\[
\boxed{P_{\rm ordinary}\le29/50=0.58,\qquad
P_{\rm switch}=13/20=0.65.}
\]

The switch tester uses the standard paired-history self-switch of two labelled invocations, target I/4, control |+>, and an X measurement. It guesses L on minus and H on plus. The success probabilities are balanced-prior averages; the H result is averaged over the stipulated Haar draw. No outcome-dependent postselection is used.

The rational upper bound is not claimed optimal. A numerical primal optimization found approximately 0.5777924 for the best ordinary success, but that number is only a numerical diagnostic. The exact inequality above is independently certified by the included rational verifier.

## Why this is an error-characterization task

For every U, both hypotheses have the same one-use entanglement fidelity f1=1/4 and the same one-use average gate fidelity 2/5. Also their complete single-use ensemble averages are equal. No one-call protocol has nontrivial Bayes discrimination advantage.

But a two-contact memory workload has different identity entanglement fidelity:

\[
F_e(\Delta_U^2)=1/4,\qquad F_e(\Lambda^2)=1/10.
\]

Thus the task decides whether the fitted depolarizing model underestimates the two-cycle memory fidelity. At long times the distinction becomes hidden information preservation versus complete forgetting. The switch is a diagnostic, not a device that itself supplies the missing encoder or corrects the production memory.

An ordinary serial Bell-return test gives success 0.575 at d=4. The certified 0.58 ceiling includes all stronger two-call adaptive/entangled strategies, not merely this baseline.

## Switch protocol

The dephaser's projectors commute, so v_H=1 and p_minus,H=0. For Lambda,

\[
v_L=2/(d+1)=2/5,\qquad p_{-,L}=3/10.
\]

The announced decision rule has success

\[
\tfrac12\cdot1+\tfrac12\cdot\tfrac3{10}=13/20.
\]

The same U is reused, but independent meters are paired between the two coherent histories according to the standard SWITCH resource. An arbitrary physical time-correlated bath does not automatically realize this extension.

## Causal-tester formulation

Use unnormalized channel Choi matrices in factor order (A_in,A_out,B_in,B_out). Define

\[
W_H=\int J(\Delta_U)^{\otimes2}\,dU,\qquad
W_L=J(\Lambda)^{\otimes2},\qquad \Delta=W_H-W_L.
\]

Every ordinary binary two-query tester can be represented by positive T0,T1 satisfying

\[
T_0+T_1=\Xi\otimes I_{B_{out}},\qquad
\operatorname{Tr}_{B_{in}}\Xi=\rho_{A_{in}}\otimes I_{A_{out}},\qquad
\operatorname{Tr}\rho=1.
\]

The input transpose convention can be absorbed in the tester. Here all hypothesis moment matrices are real and symmetric, but the upper-bound proof below allows arbitrary complex Hermitian testers. Quantum memory and intermediate outcomes are already contained in the tester characterization. Fewer than two calls can be padded by a discarded dummy call.

The average discrimination success is

\[
P=\frac12+\frac12\operatorname{Tr}(\Delta T_0).
\]

A sufficient dual certificate consists of Z,Y and a real lambda such that

\[
Z\succeq0,\qquad Z-\Delta\succeq0,
\]

\[
\operatorname{Tr}_{B_{out}}Z=Y\otimes I_{B_{in}},\qquad
\operatorname{Tr}_{A_{out}}Y=\lambda I_{A_{in}}.
\]

Indeed,

\[
\begin{aligned}
\operatorname{Tr}(\Delta T_0)
&\le\operatorname{Tr}(ZT_0)\\
&\le\operatorname{Tr}[Z(T_0+T_1)]\\
&=\operatorname{Tr}[(Y\otimes I)\Xi]\\
&=\operatorname{Tr}[Y(\rho\otimes I)]\\
&=\lambda.
\end{aligned}
\]

The supplied certificate has **lambda=4/25 exactly**, proving P <= (1+4/25)/2=29/50. This proof does not require an optimality claim or the correctness of the numerical optimizer that suggested Z.

The comb/tester framework is standard: Chiribella, D'Ariano, and Perinotti, PRL 101, 180501 (2008), arXiv:0803.3237; and PRA 80, 022339 (2009), arXiv:0904.4483.

## Exact reconstruction of the Haar hypotheses

Set

\[
O=d^{-2}\sum_{i,j}|i,i,j,j\rangle\langle i,i,j,j|.
\]

Its U^{tensor 4} Haar twirl lies in the span of the 24 permutation matrices P_sigma. At d=4 these permutation matrices are linearly independent. Write its twirl as sum_sigma c_sigma P_sigma. The coefficients satisfy

\[
\sum_\tau G_{\sigma\tau}c_\tau=b_\sigma,
\quad
G_{\sigma\tau}=d^{\#\operatorname{cycles}(\sigma^{-1}\tau)},
\quad
b_\sigma=\operatorname{Tr}(P_\sigma^\dagger O).
\]

Here b_sigma=1 if sigma preserves the two pairs {0,1} and {2,3} separately, and b_sigma=1/d otherwise. The verifier solves this 24-by-24 system with exact Fraction Gaussian elimination. Twirling is an orthogonal projection, so these moment-matching equations determine the exact twirl.

Then

\[
W_H=d^2\left(\sum_\sigma c_\sigma P_\sigma\right)^{T_{A_{in}}T_{B_{in}}},
\qquad
J(\Lambda)=\frac{|I\rangle\!\rangle\langle\!\langle I|+I}{d+1}.
\]

The partial transposes turn P_i^{tensor 2} into the channel Choi factor P_i^T tensor P_i. No approximate unitary design or Monte Carlo estimate is used. Standard Haar-integration background: Collins and Sniady, CMP 264, 773-795 (2006), arXiv:math-ph/0402073.

## Certificate and independent verification

`two_call_exact_certificate.json` stores 1,486 nonzero upper-triangular entries of the symmetric 256-by-256 Z, all over the common denominator 640,000,000. Y is reconstructed from Z rather than separately trusted.

Run

```bash
python certify_two_call.py
```

The verifier uses only Python's standard library and exact rational arithmetic. It:

1. reconstructs W_H, W_L and Delta from the mathematical definitions;
2. checks the output partial trace of Delta is zero;
3. checks the independent switch-contraction identity v_H-v_L=3/5;
4. checks both dual partial-trace equalities exactly;
5. verifies positive definiteness of Z and Z-Delta using rational LDL decompositions.

Diagonal-unitary covariance splits the matrices into 55 blocks labelled by the charge -e_a+e_b-e_c+e_d of the computational basis vector |a,b,c,d>. The verifier checks that all off-block entries vanish exactly before using the decomposition. The largest block is 28-by-28. Every LDL diagonal pivot is strictly positive, giving exact PSD certificates, rather than a floating eigenvalue tolerance.

The completed output is recorded in `two_call_exact_verification.json`.

`two_call_diagnostic.py` contains the separate numerical optimizer used to discover a candidate. The verifier does not call it. `--generate` reconstructs the rounded/projected/padded certificate from the saved numerical candidate; this optional path needs numpy, but default verification does not.

## Weak-noise version

Replace the hypotheses by

\[
E_{p,U}=(1-p)id+p\Delta_U,\qquad
M_p=(1-p)id+p\Lambda,\qquad 0\le p\le1.
\]

In the two-query moment difference, all zero-active and one-active terms cancel because integral J(Delta_U)=J(Lambda). Hence Delta_p=p^2 Delta. Scaling Z,Y,lambda by p^2 gives an exact dual for the weak problem. Therefore

\[
\boxed{
P_{\rm ordinary}\le\frac12+\frac{2p^2}{25},\qquad
P_{\rm switch}=\frac12+\frac{3p^2}{20}.
}
\]

The certified success gap is at least **7p^2/100**. In this low-query endpoint it vanishes quadratically with weak noise. This is consistent with block amplification at larger query budgets; it is not evidence that the two-call gap remains large on high-fidelity hardware.

The two-cycle memory-fidelity discrepancy likewise scales as

\[
F_e(E_{p,U}^2)-F_e(M_p^2)=3p^2/20.
\]

At d=2 this particular switch classifier has no advantage over the ordinary serial Bell-return test: both achieve 7/12 at p=1. The certificate above concerns d=4; it does not assert that this is the minimum dimension for every possible switch advantage.

## Perturbation budget

Suppose each actual oracle, under its corresponding hypothesis and hidden draw, is within half-diamond distance zeta of the ideal channel. A two-query hybrid changes any ordinary success by at most 2 zeta; slotwise switch continuity changes its ideal success by at most 2 zeta. If the native switch adds another success-probability error at most b, then

\[
P_{\rm switch}^{\rm actual}-P_{\rm ordinary}^{\rm actual}
\ge\frac{7p^2}{100}-4\zeta-b.
\]

This is a conservative sufficient margin. Native loss, timing-dependent environments, preparation/readout bias and calibration must justify their contributions to zeta and b. Postselecting on detection without counting failures does not satisfy the unconditional score.

## Boundaries and research significance

This result supplies a finite-dimensional, finite-query separation against all causal testers for a noise-model decision, without invoking C5/C6 or a large-n threshold. It does not prove a hardware speedup, optimal performance at eight calls, a practical surface-code decoder benefit, or an unqualified many-round sample separation. Repeated trials, learned U-correlated quantum programs, and additional ports require their own charged comparisons.

The hidden-global-basis family is engineered rather than yet established as a ubiquitous hardware noise law. A positive application result consists of the exact task and bound above; a claim of common-platform advantage still requires a source-specific access and cost model.
