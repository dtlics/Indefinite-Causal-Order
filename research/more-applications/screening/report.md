# Quantum-switch screening for QEC and error-channel characterization

**Investigation date:** 17 November 2026.

**Status:** direct derivations, exhaustive finite Pauli-history sums, symbolic checks, seeded numerical experiments, and a bounded primary-literature comparison. The research was originally delivered separately; it is now preserved on the `more-applications` branch. No publication-priority claim is made.

## Executive result

This investigation starts from the access conditions in the supplied note *Measurement outcomes and quantum-switch simulation*. Its target is an advantage for a useful quantum-computing task, not just a nonzero interference signal. It keeps three endpoints separate:

1. Estimate a device statistic, particularly the maximally mixed-input visibility.
2. Use a control outcome on the **same run** to improve a logical output.
3. Generate a fault-tolerant resource whose ordinary production has a restricted gate/resource budget.

The scripts evaluated 64 base channel/parameter models and 632 equal-dimension pairings (including AA). They also enumerated 43 stabilizer-code/noise cases, 4,332 channel/input/flag combinations in a stabilizer-resource scan, 14 ideal GKP-decoding parameter cases, and independent random/symbolic checks. Parameter variants are not counted as independent application mechanisms. The pair scan is not an exhaustive search over all channels or all quantum strategies.

The most useful additional sufficient condition is constructive: **if one actual box is a mixture of known Hilbert--Schmidt-orthogonal unitaries, an ordinary circuit reproduces the full switch with one query to each box.** Unknown mixture probabilities do not obstruct this. It includes Pauli noise and a noisy known gate under an exact known-frame Pauli-noise promise.

A second general baseline estimates any pair's scalar from two ordinary Choi probes. For qubits its success probability is exactly half the switch minus probability. For a known span of single-site Pauli errors, coherent superpositions included, the same factor-two scalar baseline is independent of the number of qubits. These are input-specific scalar results, not universal full-switch simulators.

The QEC calculations identify the flag as a fault-history parity. It can improve a specified decoder, but many such improvements are exactly reproducible by the preceding Pauli compiler; intermediate syndrome extraction also beats some ostensibly favorable cases. A real output advantage must survive those interfaces.

A concrete positive resource-conversion candidate is a magic-state source using two noisy reset channels. The accepted state is outside the stabilizer polytope, with explicit noise and distillation formulas below. This is a strict separation from stabilizer processing plus those resets, **not** from arbitrary ordinary quantum processing. Prior work already establishes magic generation from stabilizer-preserving channels through a switch [S5]. The calculation here is a specific reset implementation and cost screen.

No large unrestricted ordinary-query advantage for realistic local QEC noise is established by this sweep. The successful and unsuccessful examples identify what the next candidate must exploit: irreducible multi-qubit non-Pauli backaction, genuinely inaccessible per-run information, or a justified fault-tolerant control-resource constraint.

<a id="section-1"></a>

## 1. Interfaces, targets, and what was actually computed

All channel-slot calculations assume square, fixed memoryless CPTP maps. The two labeled slots have independent private environments, paired between coherent histories according to the standard channel switch. Outcome records are not silently supplied, but if a natural device exposes them, its ordinary comparator must receive them too. Shared baths and arrival-time-dependent instruments are **not** characterized by two reduced channels alone and were not modeled in this scan.

For Kraus families A_i,B_j, control |+>, and target rho,

$$
K_{ij}^{\pm}=\frac{B_jA_i\pm A_iB_j}{2},\qquad
\mathcal M_\pm(\rho)=\sum_{ij}K_{ij}^{\pm}\rho K_{ij}^{\pm\dagger}.
$$

The default scalar is

$$
p_- =\frac1{4d}\sum_{ij}\|[B_j,A_i]\|_F^2,\qquad v=1-2p_-,
$$

with rho=I/d. The general probability is Tr(E_- rho), where E_-=sum K^-dagger K^-. Its minimum and maximum eigenvalues test input dependence. Conditional Bell fidelity is not a reusable normalized channel fidelity if acceptance depends on the input.

The main scan records p+/p-, their acceptance-effect eigenvalue ranges, subnormalized identity entanglement fidelity, conditional Bell fidelity, and both ordinary compositions. It checks trace preservation and branch normalization. Among the initial 575 pairs, 224 have nonconstant acceptance effects. A higher conditional score in those cases must not be sold as an input-independent error-corrected channel.

Sufficient conditions used in the screen (the published ingredients and direct extensions are distinguished in [the source guide](../SOURCES.md)):

* A unitary member permits the published ordinary repeated-unitary construction (two calls to it, one to the other channel) [S2].
* A known efficiently controllable dilation of one member permits an ordinary full-switch realization, retaining its auxiliary record coherently. This is the explicit controlled-arm construction used here; [S2] supports the distinction between channel and dilation access.
* One outcome-readable **Luders projective** member permits the ordinary ABA scalar estimator at I/d; the other channel may be arbitrary. Appendix D of [S1] gives the recorded projective/projective experiment. The one-projective/arbitrary-channel extension is a direct Kraus calculation checked in this investigation.
* Readable classical labels are not coherent environment access. A general POVM does not fix its instrument.

A useful robustness consequence is also immediate. If A is within half-diamond distance delta of an (even unknown) unitary U, run the ordinary ABA router on A itself. Its two A slots differ from the exact U router by at most 2 delta, while S[A,B] differs from S[U,B] by at most delta. The total simulation error is at most **3 delta**. This is a coarse-accuracy guarantee; it need not meet the much finer error budget of a logical operation.

The absence of these sufficient conditions is not a hardness proof.

<a id="section-2"></a>

## 2. Additional full-simulation shortcut: one orthogonal-unitary-mixture arm

### Proposition 1

Assume

$$
\mathcal A=\sum_a p_a\operatorname{Ad}_{U_a},\qquad
\operatorname{Tr}(U_a^\dagger U_b)=d\delta_{ab},
$$

where the unitary circuits U_a and their identifying measurement are known, but the probabilities p_a are not. Let B be an arbitrary unknown channel. One ordinary call to A and one to B suffice to reproduce the complete switch.

**Construction.** Apply A to one half of a normalized Bell pair. Its Choi state is the mixture of orthonormal vectors |U_a>>/sqrt(d). Measuring in this known basis returns a with probability p_a. This probes A on an expendable input; it does not reveal an environment from the original device.

Conditional on a, apply the known controlled operations

$$
C_0(U_a)\ \longrightarrow\ \mathcal B\ \longrightarrow\ C_1(U_a)
$$

to the retained control/payload. Its Kraus operators are

$$
|0\rangle\langle0|\otimes B_jU_a+
|1\rangle\langle1|\otimes U_aB_j.
$$

Averaging over a gives exactly the Kraus expansion of S[A,B]. This holds for arbitrary input control, target, and reference. There is no postselection. The sampled error belongs to the expendable probe; the simulator reproduces the output law, not an inaccessible environment history of a different physical run. QED.

**Consequences.** A Pauli channel with completely unknown, arbitrarily correlated Pauli probabilities satisfies the premise. So does an exact Pauli-noise channel surrounding a known ideal gate, with the appropriately rotated Bell basis. The gate-synthesis cost of known controls must be charged; for Pauli U_a the controls are Clifford operations. One such arm is enough; B need not be Pauli.

This is not an impossibility theorem for switch communication: a local compiler may retain the input in its laboratory, which does not transmit it across a noisy network cut. Nor does it describe unavoidable physical storage noise that the experimenter cannot redirect onto a probe. Those are different interfaces and must be explicitly justified.

**Approximate version.** With an arbitrary A, the same Bell sampling in a Pauli basis reproduces S[T(A),B], where T(A) is the Pauli-twirled channel. If delta=||A-T(A)||_diamond/2, the full-switch error is at most delta by slotwise contractivity. Thus small non-Pauli departures cannot justify a large coarse-accuracy query separation without resolving that departure.

[ordinary_compilation.py](experiments/ordinary_compilation.py) independently checked sampling weights and the full control-target Choi matrix for 30 cases in dimensions 2,4,8, with arbitrary other channels. Maximum matrix discrepancies were of order 1e-16. This is a direct construction, not a literature-priority claim.

<a id="section-3"></a>

## 3. A two-copy ordinary estimator for arbitrary channel commutators

### Proposition 2: dimension-dependent universal comparison

Use unnormalized vectorization |A>>. Define the known linear map C by

$$
C(|A\rangle\!\rangle\otimes|B\rangle\!\rangle)
=|BA-AB\rangle\!\rangle.
$$

Writing C=M-N for the two multiplication maps gives

$$
MM^\dagger=NN^\dagger=dI,\qquad
MN^\dagger=NM^\dagger=|I\rangle\!\rangle\langle\!\langle I|.
$$

Thus

$$
CC^\dagger=2dI-2|I\rangle\!\rangle\langle\!\langle I|,
\qquad \Pi_{\rm com}=C^\dagger C/(2d)
$$

is a projector of rank d^2-1. Prepare one normalized Choi state of each channel using two ordinary calls, and measure this known projector. Then

$$
\boxed{\Pr(\Pi_{\rm com})=\frac{2}{d^2}p_-.}
$$

**Proof.** The product Choi state has rank-one components |A_i>> tensor |B_j>> with weight 1/d^2. Contracting C gives sum ||[B_j,A_i]||_F^2/d^2=4p_-/d; the projector normalization supplies 1/(2d). QED.

For d=2 the probability is p_-/2. Additive estimation of p_- therefore has only constant sampling overhead over the direct switch. The method requires two Choi probes, four target-sized registers at peak, and the known joint measurement. It is not a full-channel simulator; it is for I/d input. Large d retains a d^2 penalty and does not contradict the hidden high-dimensional learning obstruction.

Exact SymPy checks verify the operator identity at d=2,3; the all-d proof is above. Ninety random channel pairs in d=2,3,4 independently check the probability formula.

### Qubit error-geometry interpretation

Write A_i=a_i I+u_i dot sigma and B_j=b_j I+v_j dot sigma. Define

$$
C_A=\sum_i u_i u_i^\dagger,\qquad C_B=\sum_j v_jv_j^\dagger.
$$

Then

$$
\boxed{p_-=\operatorname{Tr}C_A\operatorname{Tr}C_B-\operatorname{Tr}(C_A C_B).}
$$

For AA this measures the impurity/diversity of the nonidentity error sector, not total error probability or logical error rate. In particular a single-axis Pauli channel has p_-=0 at every strength, while isotropic Pauli errors at the same total rate have a positive value.

Let Q=I-Phi_2 and e_A=1-F_e(A). Conditional on Q after the Choi experiment, the retained state sigma_A=Q J_A Q/e_A is the normalized error-sector state. The formula becomes

$$
p_-=e_A e_B[1-\operatorname{Tr}(\sigma_A\sigma_B)].
$$

This also allows rare errors to be collected before comparing two specimens, rather than requiring two faults in the same trial.

### An explicit weak-noise ordinary win

Compare H=(1-r)id+r Ad_X with L=(1-r)id+r(Ad_X+Ad_Z)/2, at r=.01. A primitive self-switch yields minus with probability 0 under H and r^2/2 under L. Reaching 1% one-sided error by any-minus testing uses 184,204 calls. An ordinary Bell probe sees a Z label with probability r/2 under L and never under H; 919 calls suffice. This compares these explicit tests, not optimal algorithms with arbitrary block amplification.

Even without a known error axis, compare (1-r)id+r Ad_N for a fixed unknown traceless unitary N with an isotropic nonidentity Pauli mixture. Choi error filtering leaves a pure state versus I_3/3. Twelve antisymmetric two-copy tests have miss probability (2/3)^12. At r=.01, 24 accepted error specimens cost 2,400 queries on average; a cap of 4,045 calls gives total error below .009708, including collection failures. No axis calibration or device outcome record is needed.

<a id="section-4"></a>

## 4. Known error spans can remove the dimension penalty

Let the unknown Kraus operators lie in **known** unitary-orthonormal operator spans {F_a} and {G_b}, with Tr(F_a^dagger F_c)/d=delta_ac. Their Choi states retain coefficient matrices chi_A,chi_B; no measurement is made that destroys their off-diagonal coherence.

Define

$$
T|a,b\rangle=\frac{|G_bF_a-F_aG_b\rangle\!\rangle}{2\sqrt d}.
$$

Then p_-=Tr[T^dagger T(chi_A tensor chi_B)]. Measuring T^dagger T/L, with L=max(1,||T||^2), estimates p_-/L in two ordinary calls. The loose bound L<=r_A r_B follows from the column norms; known operator span is essential. Small unknown Kraus rank alone does not supply the required known basis.

For the span {I,X_j,Y_j,Z_j: j=1,...,n}, exact Pauli multiplication gives ||T||^2=2: only two different axes on the same site contribute, and each output Pauli has two ordered preimages. Thus **even coherent, non-Pauli combinations of exactly single-site Kraus errors have a dimension-independent scalar estimator.** Numeric checks for n=1,...,4 agree.

A finite-time local Lindblad channel can contain multiple-jump Kraus products outside this span. Truncating them needs an error bound; locality of a generator does not automatically grant the exact single-fault-span promise. Known Pauli-diagonal channels satisfy the stronger full-simulation proposition regardless of weight or correlations.

<a id="section-5"></a>

## 5. What a switch flag contributes to a decoder

For Pauli errors P,Q, the flag is the symplectic commutation parity c=[P,Q]. The product error QP is the same in both orders up to phase. Therefore the switched process supplies a **classical bit correlated with this run's fault history**, not merely information about the distribution.

Let pi(s,l,c) be the joint distribution of final stabilizer syndrome s, logical Pauli coset l, and commutation flag. The optimal Pauli correction for each supplied record has Bell fidelities

$$
F_{\rm final}=\sum_s\max_l\sum_c\pi(s,l,c),\qquad
F_{\rm flag}=\sum_{s,c}\max_l\pi(s,l,c).
$$

This is a precise useful-output target. It does not upper-bound every ordinary protocol: one can change the code, record intermediate syndromes, or use the full Pauli compiler above.

[qec.py](experiments/qec.py) enumerates all Pauli histories for the three-qubit repetition code and the five-qubit perfect code, and axis-noise histories for the Steane seven-qubit code. It checks generator commutation, independence, and logical anticommutation. There are 43 noise/strength/code cases. All listed probabilities are ideal-noise-model calculations, not circuit-level thresholds.

At p=.01 per site per layer:

| Code; two layers | Final syndrome only | Plus switch flag | Ordinary intermediate syndrome |
|---|---:|---:|---:|
| Five-qubit; depolarizing/depolarizing | .00377535325 | .00377532572 | .00195463497 |
| Five-qubit; X-only/Z-only | .00332452319 | .00284441540 | .00001970110 |
| Five-qubit; X-only/X-only | .00007533675 | .00007533675 | .00001970101 |
| Steane; X-only/Z-only | .00400413362 | .00394934797 | .00400413362 |

Entries are logical error probabilities. The intermediate comparator has a perfect ordinary recovery between layers and retains both syndrome histories. It consumes the same two noise contacts, but extra syndrome/correction operations, which a practical timing/error ledger must price.

The X/Z five-qubit improvement over final-only decoding is real but is dominated by intermediate recovery. The Steane flag supplies information absent from that particular intermediate record; it still does not beat all ordinary operations, and the full Pauli compiler reproduces its flagged channel in the unrestricted oracle model.

### Exact low-noise polynomials

[qec_polynomials.py](experiments/qec_polynomials.py) counts the histories with integers and constructs rational success polynomials for the small-p maximum-likelihood decoder. For five-qubit depolarizing layers,

$$
1-F_{\rm final}=40p^2-\frac{2080}{9}p^3+\frac{5920}{9}p^4+O(p^5),
$$
$$
F_{\rm flag}-F_{\rm final}=\frac{80}{27}p^4+O(p^5),
\qquad
1-F_{\rm intermediate}=20p^2+O(p^3).
$$

For X/Z layers the corresponding errors begin 35p^2,30p^2,20p^3. A noisy flag/controller can readily erase the tiny isotropic gain.

The reason the flag is weak for ordinary independent depolarization is structural: noncommutation requires faults from both layers on the same site. Two such faults multiply to a one-site error, which the code already corrects. Dominant uncorrectable faults on different sites commute. This intuition does not automatically extend to correlated hooks or biased models whose decoder sacrifices some single-Pauli patterns.

### Recovery modules and gauge checks

Let R_s=C_s P_s be an ideal recovery, with P_0=P_code and C_0=I. For Pauli noise N on a code input,

$$
p_-(R,N)=\tfrac12\Pr(\text{nonzero syndrome}).
$$

A zero-syndrome logical Pauli error is invisible. Its rate is not measured by this signal.

More strongly, take two ideal recovery policies R_s=C_sP_s and S_t=D_tP_t for the same code, both fixing it and returning all syndrome sectors into it. For arbitrary rho,

$$
\boxed{p_-(R,S;\rho)=\tfrac12[1-\operatorname{Tr}(P_{code}\rho)],}
$$

independent of how the two policies correct nonzero syndromes. To prove it, products of two nonzero-syndrome Kraus operators vanish; the remaining commutators are R_s or -S_t with exactly one zero label. Sum their squared norms. This was independently checked for 30 random inputs and distinct three-qubit recovery policies. A large signal does not diagnose a bad decoder.

Likewise, switching I_logical tensor Delta_Z,gauge and I_logical tensor Delta_X,gauge gives p_-=1/4 while the logical channel is exactly identity. Gauge disturbance is not logical damage.

<a id="section-6"></a>

## 6. Leakage and bosonic cases

### Leakage followed by repumping is not a free leakage syndrome

Take qutrit A that leaks |1> to |2> with probability g, and B that repumps |2> to |1> with probability h. On the computational input span {|0>,|1>}, every minus Kraus operator annihilates |0>. Thus the minus branch is measure-|1> and prepare: it is entanglement-breaking on the logical input, not a nondestructive error flag.

$$
p_-(\rho)=\frac g4\left[(1-\sqrt{1-h})^2+h\right]\rho_{11}.
$$

At g=.05,h=.8, p_-(|1>)=.01381966 while p_-(|0>)=0. The flag is partly reading the logical state. Ordinary leakage benchmarking and leakage detection [S8] remain the baseline. This also illustrates why optimizing only a postselected Choi fidelity is dangerous.

### Collective decay, photon loss, and parity

The additional finite models include collective and differential dephasing, collective lowering with relative phases, independent decay, collective heating, finite-Fock pure loss, number dephasing, parity-unitary/measurement channels, and a binomial-code input. Pure loss is represented exactly on inputs supported on the retained Fock levels; number dephasing and the tested diagonal operations do not populate the truncation boundary. This does not claim a full untruncated bosonic treatment for arbitrary operations.

Collective Z dephasing and differential Z dephasing can both have p_-=0 despite spatial correlations. Collective lowering and independent lowering produce different small self-signals, but no unrestricted learning advantage is proved. A known parity unitary plus loss is ordinary Pauli/symmetry-check compilation, not a switch-only error-detection primitive.

### Gaussian displacement channels and a direct GKP decoder test

For independent Gaussian q- and p-kicks x,y with variances sigma_q^2,sigma_p^2 and [q,p]=i, the Weyl commutation phase gives

$$
\Pr(c=\pm\mid x,y)=\frac{1\pm\cos(xy)}2,\qquad
v=(1+\sigma_q^2\sigma_p^2)^{-1/2}.
$$

More generally the centered Gaussian phase-space formula is det(I+Sigma_A Omega Sigma_B Omega^T)^(-1/2). Covariance estimation already supplies ordinary characterization baselines; a geometric phase is not by itself a learning advantage.

For an **ideal square GKP qubit**, let L=sqrt(pi), x=u+mL, y=v+nL, with u,v in [-L/2,L/2). The analog syndrome is (u,v), and the residual logical Pauli is (m mod 2,n mod 2). The extra control likelihood is exactly the conditional cosine above. Therefore a maximum-likelihood decoder can use

$$
w_{l,c}(u,v)=\sum_{(m\bmod2,n\bmod2)=l}
 f_q(u+mL)f_p(v+nL)\frac{1+c\cos[(u+mL)(v+nL)]}{2}.
$$

Ordinary syndrome-only and flagged logical fidelities are respectively integral max_l sum_c w and integral sum_c max_l w. [gkp_flag.py](experiments/gkp_flag.py) evaluates these at two integration resolutions, checks normalization and the analytic marginal p_-, and truncates only Gaussian tails beyond roughly nine standard deviations. This is numerical evidence, not an interval-certified optimal bound. Analog-syndrome decoding is a standard GKP baseline [S9,S10].

| sigma_q=sigma_p | Ordinary logical error | With ideal switch flag |
|---|---:|---:|
| .3 | about .006262 | no resolved improvement |
| .5 | about .146814 | about .146712 |
| .7 | about .368537 | about .356571 |

The common-grid calculation at .5 gives a relative improvement of only .0693%. Independent 1% flag flips eliminate that gain in the tested decision rule. Stronger gains occur at high raw error. There is no finite-energy GKP, noisy-syndrome, outer-code, or all-ordinary-control advantage theorem here. Replayable programmed displacements also permit ordinary unitary-order simulation and invalidate the intended hidden-realization premise.

<a id="section-7"></a>

## 7. Short-time noise-algebra diagnostics

Let E_t=e^{t L} be a finite-dimensional Markov semigroup with Hamiltonian H and Lindblad jumps L_a. Its infinitesimal Kraus operators are K_0=I+tG+O(t^2) and K_a=sqrt(t)L_a+O(t^(3/2)). Hence

$$
\boxed{
p_-(E_t,E_t)=\frac{t^2}{4d}\sum_{ab}\|[L_a,L_b]\|_F^2+O(t^3).
}
$$

Jump/jump commutators contribute at t^2; no-jump/jump contributions begin at t^3. Unitarly mixing the jump list or shifting jumps by scalar identities leaves the leading coefficient unchanged. The identity does not say that every nonzero signal is non-Markovian, nor that one jump is harmless.

For amplitude damping with total probability gamma,

$$
p_-^{AA}=\frac{\gamma(1-\sqrt{1-\gamma})^2}{4}=\frac{\gamma^3}{16}+O(\gamma^4).
$$

For jumps sqrt(.7)X and sqrt(.3)Z the t^2 coefficient is .42. For thermal jumps sqrt(.7)sigma_- and sqrt(.3)sigma_+ it is .105. Self-dephasing and a single-jump leading coefficient vanish. The scripts check convergence at four short times.

This is a compact model-falsification fingerprint: it detects incompatible dissipative directions and can separate a proposed jump-algebra model from alternatives. It is not a complete noise reconstruction, a universal logical-error estimator, or a proven query advantage. For qubits/known sparse error spans the ordinary estimators above already apply; Lindblad tomography and local-noise learning are additional primary baselines [S7].

<a id="section-8"></a>

## 8. Positive local computational resource: noisy resets to magic

This candidate changes the resource question, not the target to communication. The free processor is an ideal stabilizer processor (Clifford gates, stabilizer states, Pauli measurements, classical adaptation), and the supplied reset devices are themselves stabilizer instruments. No input magic state is granted. A native switch is an additional priced resource, not a free ordinary Clifford operation. The free reset interface is outcome-discarded, or every accessible instrument branch is itself stabilizer preserving; a stabilizer-preserving summed channel alone would not justify the same resource claim if extra nonfree branch information were supplied.

Published work already proves that switches can generate magic from completely stabilizer-preserving channels [S5]. The following is a directly calculated reset specialization with a finite distillation ledger. It is not an unrestricted quantum-query advantage or a priority claim.

### Ideal source

Let A reset to |0> and B reset to |+>, and initialize target and control in |+>. The plus branch has

$$
p_+=3/4,\qquad
\rho_+=\frac12\left[I+\frac23X+\frac23Z\right].
$$

Since |r_x|+|r_y|+|r_z|=4/3>1, it is outside the single-qubit stabilizer octahedron. Its H-axis error is (1-2sqrt(2)/3)/2, approximately .0285955. It is Clifford-equivalent to a noisy T-injection state and can enter standard distillation [S6].

Every ordinary adaptive composition of the same stabilizer reset instruments and free stabilizer processing remains a stabilizer instrument, including every nonzero postselected branch. Therefore no number of these free ordinary operations can produce this magic output. A known-dilation switch compiler exists with unrestricted quantum gates, but its non-Clifford control is not free in this comparison.

### Reset imperfections and controller dephasing

Let A reset to tau=(I+aZ)/2 and B reset to sigma=(I+bX)/2, and let kappa be the switch control's coherence visibility. All these individual reset states are stabilizer mixtures for a,b in [0,1]. On the known |+> target,

$$
\mathcal M_+(|+\rangle\langle+|)=
\frac{[4+\kappa(1+b)]I+[2b+\kappa(1+b)]X+a[2+\kappa(1+b)]Z}{16}.
$$

Put D=4+kappa(1+b). Then

$$
p_+=D/8,\quad r_x=\frac{2b+\kappa(1+b)}D,\quad
r_z=\frac{a[2+\kappa(1+b)]}D.
$$

The state is magic exactly when

$$
\boxed{\kappa a(1+b)>4-2(a+b).}
$$

At a=b=.9 and kappa=.98, p_+=.73275, (r_x,r_z)=(.624701467,.592937564). A random I/H twirl makes both components m=.6088195155, for error e_0=.0694995920. This means 95%-fidelity individual reset outputs and 98% control visibility in this declared model, not a demonstrated fault-tolerance threshold.

### Finite resource ledger

Under independent attempts and ideal stabilizer distillation, the standard 15-to-1 H/T-injection-state recursion [S6] is, for r=1-2e,

$$
a(e)=\frac{1+15r^8}{16},\qquad
f(e)=\frac{1-15r^7+15r^8-r^{15}}{2(1+15r^8)}.
$$

The mean reset-call cost obeys C_0=2/p_+ and C_{j+1}=15C_j/a(e_j), counting every rejected source and distillation batch.

| Source/level | Error | Mean reset calls per accepted state |
|---|---:|---:|
| Noisy raw source | .0694995920 | 2.72944 |
| First round | .0147106338 | 118.4521 |
| Second round | .0001165957 | 2,218.8300 |
| Third round | 5.54968e-11 | 33,340.7136 |

Ideal resets/control need about 938.78 mean reset calls for error 2.52154e-8 after two rounds. There is one native switch invocation per two reset calls; local Clifford circuits, storage, routing, and fault-tolerant implementation have additional costs. The magic-polytope condition alone is not the exact convergence threshold of every chosen distillation routine; the displayed points were checked with the actual recursion.

This is a real resource-conversion separation but **not** evidence that a switch factory beats an available high-quality ordinary T-state source. A digital router may already consume more T resources than it produces. The useful architecture question is whether a native coherent-reset device supplies this resource more cheaply than its ordinary non-Clifford alternative. The unknown reset parameters need only be bounded, but black-box ignorance is not the fundamental lower-bound mechanism.

The scan used 19 stabilizer-preserving channel models, six stabilizer input states, all ordered channel pairs and both flags: 4,332 outputs. It found 288 outputs outside the octahedron. These are finite examples, not distinct advantages, and Mo et al. already establish the general phenomenon [S5].

<a id="section-9"></a>

## 9. Bell-fidelity accounting: why a pretty conditional number is insufficient

For every pair of square channels, Tr K^-_ij=0, while Tr K^+_ij=Tr(B_j A_i). Therefore

$$
F_e(\mathcal M_-)=0,\qquad
F_e(\mathcal M_+)=F_e(A\circ B)=F_e(B\circ A),
$$

where the branch entanglement fidelities are **subnormalized**, relative to identity. A larger conditional plus-branch Bell fidelity can result entirely from rejecting weight; it does not increase uncorrected Bell-good weight. Minus branches can still be useful after a known correction, as the Pauli fault-history example shows. This is not a no-go against corrected output protocols or gates with a different ideal target.

This identity was checked separately and across the generic pair scan. It explains why the output objective, acceptance probability, recovery, and repeatability must be kept together.

<a id="section-10"></a>

## 10. What remains a justified application target

The surviving directions are narrower than “two unknown noisy channels.” The scan suggests investigating:

* Multi-qubit nonunital syndrome/feedback or engineered-dissipation modules whose hidden backaction is not covered by a known small error span. The output should be a concrete instrument-comparison or code/decoder decision, not NCOM alone.
* Per-run logical recovery where an order flag resolves an ambiguity not already contained in accessible syndrome histories, and where known-mixture compilation or a stronger ordinary flag gadget is not an equally available substitute.
* Fault-tolerant resource conversion with a priced native controller; the reset-to-magic model gives one explicit finite instance, but an unrestricted-query claim would be false.

The sweep does not establish a large separation for the first two directions. The third has a proved resource-restricted separation, not a proof of practical factory superiority. These distinctions are the research output, not qualifications to be dropped in a later headline.

Full-simulation impossibility does not imply that a desired diagnostic is hard. A state-dependent postselection map is not automatically a logical channel. A large commutator can be confined to a harmless gauge subsystem. A weak-noise signal often records double faults and is statistically less favorable than collecting individual ordinary fault specimens. None of these facts removes the high-dimensional hidden-basis theorem; they delimit which natural workloads actually instantiate it.

<a id="section-11"></a>

## 11. Evidence map and reproduction

From the repository root, run `python research/more-applications/reproduce.py --study screening`. The driver stages the original source scripts in a clean ignored build directory, checks numerical tolerances and exact-regression agreements, and writes a replay record. The tracked current record is [../validation.json](../validation.json). It does not perform an external proof review or certify a physical implementation. NumPy, SciPy, SymPy, and mpmath are required.

* [explore.py](experiments/explore.py), [physics_extensions.py](experiments/physics_extensions.py): 64 base models, 632 pairings; max-mixed and selected code-state calculations.
* [ordinary_compilation.py](experiments/ordinary_compilation.py): full-channel 1+1 ordinary compiler on 30 random test pairs.
* [derived_checks.py](experiments/derived_checks.py): symbolic commutator identity, known-span norm, readable ABA, PCS, leakage, Lindblad and Gaussian checks.
* [rare_fault_baseline.py](experiments/rare_fault_baseline.py): two explicit rare-fault ordinary protocols and the general qubit error-sector identity.
* [qec.py](experiments/qec.py): all finite Pauli histories for 43 code/noise configurations; matched intermediate-syndrome baseline.
* [qec_polynomials.py](experiments/qec_polynomials.py): exact integer history counts and rational five-qubit error polynomials.
* [recovery_policy.py](experiments/recovery_policy.py): decoder-blind recovery/recovery signal.
* [magic_scan.py](experiments/magic_scan.py), [reset_factory.py](experiments/reset_factory.py): 4,332 stabilizer-resource cases, exact symbolic reset formula, 100 independent random-parameter checks, distillation bookkeeping.
* [gkp_flag.py](experiments/gkp_flag.py): ideal-GKP maximum-likelihood integration and grid/marginal checks; no finite-energy claim.

The supplied sufficient-conditions note was reread directly. This report develops extra constructions rather than silently replacing its unresolved projective full-simulation case. No result here claims to settle that case.

## Primary references

[S1] Gao et al., *Measuring incompatibility and clustering quantum observables with a quantum switch*, PRL 130, 170201 (2023), [arXiv:2208.06210v4](https://arxiv.org/html/2208.06210v4). NCOM/MED, Kraus commutators, outcome-readable ABA.

[S2] Bavaresco et al., *Simulating the quantum switch with quantum circuits is computationally hard*, Nature Communications 16, 10216 (2025), [arXiv:2409.18202v2](https://arxiv.org/html/2409.18202v2). Unitary-repeat construction, full-output task, dilation-access distinction.

[S3] Gonzales et al., *Quantum Error Mitigation by Pauli Check Sandwiching*, Scientific Reports 13, 2122 (2023), [arXiv:2206.00215](https://arxiv.org/abs/2206.00215). Ordinary parity filtering and its check-noise assumptions.

[S4] Hockings, Doherty, Harper, *Scalable noise characterization of syndrome-extraction circuits with averaged circuit eigenvalue sampling*, PRX Quantum 6, 010334 (2025), [arXiv:2404.06545v3](https://arxiv.org/html/2404.06545v3). Established syndrome-circuit noise-learning comparator; not evidence for a switch advantage.

[S5] Mo et al., *Enhancement of non-Stabilizerness within Indefinite Causal Order*, PRA 109, 062428 (2024), [arXiv:2311.15494v2](https://arxiv.org/html/2311.15494v2). Prior magic generation from completely stabilizer-preserving inputs.

[S6] Bravyi and Kitaev, *Universal quantum computation with ideal Clifford gates and noisy ancillas*, PRA 71, 022316 (2005), [arXiv:quant-ph/0403025v2](https://arxiv.org/html/quant-ph/0403025v2), especially H-type distillation. Distillation is prior work; the reset source/ledger is derived here.

[S7] Samach et al., *Lindblad Tomography of a Superconducting Quantum Processor*, Physical Review Applied 18, 064056 (2022), [DOI](https://doi.org/10.1103/PhysRevApplied.18.064056). Ordinary dynamical and SPAM-aware noise characterization.

[S8] Wallman et al., *Robust characterization of leakage errors*, New Journal of Physics 18, 043021 (2016), [DOI](https://doi.org/10.1088/1367-2630/18/4/043021). Ordinary leakage-characterization baseline.

[S9] Fukui et al., *Analog quantum error correction with encoding a qubit into an oscillator*, [arXiv:1706.03011](https://arxiv.org/abs/1706.03011). Analog GKP information and maximum-likelihood decoding.

[S10] Noh, Chamberland, Brandao, *Low-overhead fault-tolerant quantum error correction with the surface-GKP code*, PRX Quantum 3, 010315 (2022), [arXiv:2103.06994](https://arxiv.org/abs/2103.06994). Standard use of analog syndrome histories; our ideal one-mode tests do not establish a surface-GKP improvement.

[S11] Seif et al., *Entanglement-enhanced learning of quantum processes at scale*, [arXiv:2408.03376](https://arxiv.org/abs/2408.03376); Nature Communications 17, 9000 (2026), [DOI](https://doi.org/10.1038/s41467-026-75553-0). Entanglement-assisted ordinary Pauli learning and resource-noise overheads.

[S12] Chen and Ma, *Commutator Geometry and Information Preservation in the Quantum Switch*, [arXiv:2609.21310v1](https://arxiv.org/html/2609.21310v1) (2026 preprint). Related code-dependent commutator effects; optimized noise-probe QFI can coincide despite input-specific gains. Not a general all-strategy bound. This source check verified the primary arXiv abstract only; no theorem here depends on it.

[S13] Lee et al., *Error Suppression for Arbitrary-Size Black Box Quantum Operations*, PRL 131, 190601 (2023), [arXiv:2210.10733](https://arxiv.org/abs/2210.10733). Ordinary error filtration with routing/memory, relevant whenever those controls are admitted.
