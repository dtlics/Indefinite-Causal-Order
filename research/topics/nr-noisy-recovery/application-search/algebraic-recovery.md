<a id="nr-r28"></a>

# Qubit central-polynomial recovery and its ordinary-baseline boundaries

[Investigation handoff](README.md) · [Application assessment](../architecture.md)

**Status and scope.** Secondary constructive detour, not a completed natural-black-box quantum-computing/QEC application. The nested-switch distillation mechanism is published prior work. The derivations, scoped classifications and executable checks below were supplied by the conversation; they are not Lean-formalized, independently peer reviewed, or publication-priority claims. See [verification scope](checks/README.md).

## 1. Sources and ordinary competitors

1. Kechrimparis, Moran, Kwon, *Probabilistic channel distillation via indefinite causal order*, PRR 7, 043257 (2025), arXiv:2501.13696. The --+ superswitch branch and Pauli distillation, general-channel twirling, preprocessing and multiqubit limitations are prior work.
2. Navascues, *Resetting uncontrolled quantum systems*, arXiv:1710.02470. Ordinary coherent-probe protocols already use central matrix polynomials under a different access model. Central-polynomial recovery is not intrinsically unique to indefinite order.
3. Lee, Hann, Puri, Girvin, Jiang, *Error Suppression for Arbitrary-Size Black Box Quantum Operations*, PRL 131, 190601 (2023), arXiv:2210.10733. Ordinary gate-based filtration with coherent routing and memory is a required baseline.
4. Horodecki, Shor, Ruskai, *Entanglement Breaking Channels*, arXiv:quant-ph/0302031. Ordinary EB links and LOCC cannot create entanglement across a cut.
5. Khatri, Sharma, Wilde, *Information-theoretic aspects of the generalized amplitude-damping channel*, PRA 102, 012401 (2020). Thermal-relaxation model and EB boundary.
6. Chiribella et al., *Indefinite causal order enables perfect quantum communication with zero capacity channels*, arXiv:1810.10457. Existing activation and resource conventions.

## 2. Access and accounting

Each labeled slot is a square single-qubit CPTP map. No Kraus label, environment, description or coherent dilation is supplied. Distinct slots may be unrelated or nonunital. A standard paired-history switch is explicitly supplied: the same labeled operation and corresponding private environment appear across its coherent placements. Arrival-time-dependent substitutions and uncontrolled quantum shared-bath memory are outside this model. A classical mixture of valid tuples is permitted by linearity.

The general protocol has four elementary calls, two inner switches and an outer switch of those subcircuits: three order controls and eight order histories, not 24 separately executed words. A primitive two-slot switch does not automatically supply coherent ordering of whole subcircuits.

All acceptance probabilities are unnormalized. Failed trials count. The input must be inside the protocol before the noisy calls; it does not restore an unknown state already erased by an ordinary measurement. Repeating trials is valid for expendable probes or fresh Bell-pair halves, not for an irreplaceable live input. A clean local memory already implements identity without the device, so a useful output requires a justified mandatory-transport or no-bypass task.

## 3. Four arbitrary qubit channels: exact identity on the --+ branch

Let A={A_i}, B={B_j}, C={C_k}, D={D_l}. Selecting minus in both inner switches and plus in the outer switch produces

\[
L_{ijkl}=\frac18\{[B_j,A_i],[D_l,C_k]\}.
\]

For arbitrary traceless complex 2-by-2 matrices X,Y,

\[
\{X,Y\}=\operatorname{Tr}(XY)I.
\]

This follows from direct matrix multiplication or the Pauli anticommutator and does not assume Hermiticity. Every commutator is traceless. Hence

\[
L_{ijkl}=\frac{\operatorname{Tr}([B_j,A_i][D_l,C_k])}{8}I,
\qquad
\mathcal H(\rho)=p\rho,
\]
\[
p=\frac1{64}\sum_{ijkl}|\operatorname{Tr}([B_j,A_i][D_l,C_k])|^2.
\]

Acceptance is input-independent, including reference-entangled inputs; no unknown correction is needed. Kraus-isometry changes preserve the probability. None of the maps must be known, equal, unital, Pauli or invertible. However, p can vanish or become arbitrarily small. Slot noise within the qubit model preserves the conditional identity; routing, leakage and flag errors do not follow that guarantee. The full eight-flag instrument, not only this branch, is trace preserving.

### Norm versus algebraic alignment

For self-use put C_a=[K_i,K_j]=c_a dot sigma and G=sum_a c_a c_a^dagger. Then

\[
p_-(I/2)=\operatorname{Tr}G/4,
\qquad p_{--+}=\operatorname{Tr}(GG^{\mathsf T})/16.
\]

For unital qubit channels a random-unitary Kraus representation makes G real symmetric, so

\[
p_-^2/3\le p_{--+}\le p_-^2.
\]

Nonunital commutators can instead lie in a nilpotent direction, yielding nonzero p_- but zero p_{--+}. Total noncommutativity is not a sufficient yield criterion.

## 4. Exact zero-yield criterion for the bare self-protocol

**Theorem.** Four uses of a qubit CPTP map have p_{--+}=0 if and only if that map has a pure fixed state. This classifies the unwrapped protocol, not every possible switch protocol.

**Proof.** Let L be the complex span of [K_i,K_j]. The probability vanishes iff Tr(XY)=0 for all X,Y in L. The trace bilinear form on sl_2(C) is nondegenerate of dimension three. A totally isotropic subspace lies inside its orthogonal complement, so 2 dim L<=3 and dim L<=1.

If L=0 the Kraus operators commute and have a common eigenvector over C. If one is nonscalar, use an invariant eigenspace; if all are scalar, any vector works.

Otherwise L=span{N}, with Tr N=Tr N^2=0. Cayley-Hamilton makes N nilpotent. In a unitary basis it is proportional to |0><1|. Write the traceless part of K_i as [[a_i,b_i],[c_i,-a_i]]. Vanishing diagonal and lower-left commutator entries imply

\[
b_i c_j-b_j c_i=0,\qquad c_i a_j-a_i c_j=0.
\]

If c_k is nonzero, these force all (a_i,b_i,c_i) to be proportional, contradicting a nonzero commutator. Thus every c_i=0 and the Kraus operators share |0>. If K_i|phi>=lambda_i|phi>, trace preservation gives sum_i |lambda_i|^2=1, so |phi> is a pure fixed state.

Conversely a rank-one fixed output forces each K_i|phi> to be proportional to |phi>. All Kraus matrices are upper triangular in a common basis. Their commutators are strictly upper triangular and products of two vanish. Therefore p=0. QED.

Unitary channels, dephasing and zero-temperature amplitude damping fail this bare protocol. Mixed thermal relaxation and mixed replacement need not. Known output rotations can remove a pure-fixed-state obstruction, so this is a protocol-design boundary, not an absolute recovery impossibility.

## 5. Two sequential switches for a fixed Kraus-rank-two channel

Let E={K0,K1}, C=[K0,K1]. A self-switch minus branch is

\[
\mathcal M_-(\rho)=\tfrac12 C\rho C^\dagger.
\]

Two sequential self-switches, conditioned on both minus flags, use C^2=-det(C)I and give

\[
\mathcal M_-\circ\mathcal M_-(\rho)=\frac{|\det C|^2}{4}\rho.
\]

This needs four channel calls but only two controls and no outer switch. The same rank-two map must persist across calls. Arbitrary unrelated maps require the general nested construction instead.

### Unknown unread projective measurement: uniform 1/12 yield

For any fixed unknown qubit basis, E=Delta_U has projectors P0,P1. In each attempt choose W uniformly from the 24 single-qubit Clifford operations. After each of the four calls apply the same W; the effective Kraus matrices are WP0,WP1. Run the two sequential switches and accept both minus flags. Each accepted branch is scalar identity, and

\[
\mathbb E_W p(W)=1/12
\]

for every U, without Haar randomness or calibration of the device. Mean elementary contacts are 48; 53 attempts use 212 calls and deliver at least one ideal Bell pair with probability

\[
1-(11/12)^{53}=0.99006412148\ldots.
\]

Failed candidate pairs are discarded. The known gates W are also granted to ordinary competitors and charged. Their noise may increase Kraus rank; that requires a perturbation budget or the general nested construction rather than silently preserving the rank-two shortcut.

### General rank-two measure-and-prepare map

Take K0=|a><u0|, K1=|b><u1| with normalized a,b and orthonormal input states. Put f=|<a|b>|^2. The same random output rotation gives

\[
\mathbb E_W p(W)=\frac{(1-f)(2-f)}{24}.
\]

In the input basis write a'=Wa=(a,b)^T, b'=Wb=(c,d)^T. Direct multiplication gives det[K0,K1]=bc(ad-bc), with squared modulus (1-f)|<u1|Wa>|^2|<u0|Wb>|^2. The unitary two-design average of the last product is (2-f)/6; the sequential probability supplies the factor 1/4. Projective measurements have f=0; identical prepared outputs f=1 fail.

## 6. Explicit channel models

### Generalized amplitude damping

For relaxation strength gamma, stationary excited population e, and s=sqrt(1-gamma), use

\[
K_0=\sqrt{1-e}\begin{pmatrix}1&0\\0&s\end{pmatrix},\quad
K_1=\sqrt{(1-e)\gamma}|0\rangle\langle1|,
\]
\[
K_2=\sqrt e\begin{pmatrix}s&0\\0&1\end{pmatrix},\quad
K_3=\sqrt{e\gamma}|1\rangle\langle0|.
\]

Direct commutator calculation gives

\[
p_{--+}=\frac{e(1-e)\gamma^2(1-\sqrt{1-\gamma})^4}{8}
+\frac{e^2(1-e)^2\gamma^4}{4}.
\]

One inner minus branch has lowering, raising and Z Kraus directions with weights a/2,b/2,c/2, where a=(1-e)gamma(1-s)^2, b=e gamma(1-s)^2, c=e(1-e)gamma^2. Since {L,R}=I, {Z,Z}=2I and the other relevant anticommutators vanish, the probability is ab/8+c^2/4.

At gamma=.95,e=.25, p=.0148444810987196. Mean contacts are 269.4604; 308 attempts (1,232 contacts) provide at least 99% ideal delivery. A common unknown rotation of the thermal axis does not change p.

The channel is EB precisely when 1-gamma<=e(1-e)gamma^2: its two-qubit Choi partial transpose is then positive. The example satisfies .05<=.16921875. Ordinary EB-link/LOCC communication cannot herald entanglement, but this is not an all-apparatus no-go once additional coherent routing is granted.

For fixed interior e and small gamma the probability is Theta(gamma^4). At e=.25,gamma=.01 it is about 8.79e-11, giving about 4.55e10 mean contacts. This is not a weak-noise local-QEC shortcut.

### Uniform lower bound for heterogeneous slots

If normalized Choi states obey J_j>=m_j I_4, then t_j=4m_j<=1 and E_j=t_j Omega+(1-t_j)R_j with R_j CPTP. Multilinearity and positivity imply

\[
p\ge\frac3{64}\prod_{j=1}^4t_j.
\]

For GAD slots with gamma in [.9,1], e in [.2,.8], t_j>=(55-sqrt(1729))/50, giving p>=.0002431700353. Do not transfer the attractive identical-slot operating point to arbitrary heterogeneous slots without this loss.

### Replacement and distinct pure reset maps

For E(rho)=Tr(rho)tau, tau=(I+rZ)/2, four identical calls give

\[
p=\frac{(1-r^2)(3-r^2)}{64}.
\]

Mixed replacement can be activated; a pure reset gives zero. For A(rho)=|a><a|Tr(rho), B(rho)=|b><b|Tr(rho), use the pair A,B in both inner switches. With f=|<a|b>|^2,

\[
p=\frac{(1-f)(3-f)}{32}.
\]

Orthogonal resets give 3/32 and 47 attempts (188 contacts) suffice for 99% ideal delivery. This is an algebra/access stress test, not a reason to deliberately erase a state when an ordinary clean route exists.

## 7. Output randomization and the resource warning

Uniform output Paulis satisfy, for any TP qubit map,

\[
\tfrac14\sum_{P\in\{I,X,Y,Z\}}\operatorname{Ad}_P\circ E=\Omega.
\]

Choose independent output Paulis for the four labeled slots, keeping each slot's choice fixed across coherent placements. Each individual accepted branch is already scalar identity. By multilinearity its average is (3/64)id, independently of E.

Randomized implementations sample one frame tuple per attempt; they do not need to enumerate every twirling combination. An apparent savings over exhaustive twirling is not a legitimate resource advantage. General-channel twirling is prior work [1]. Activation even of replacement maps highlights that the extra resource is coherent placement, not hidden recoverable information in the one-use marginal.

## 8. Flag errors and normalized acceptance

Suppose the three recorded signs are independently flipped with probability eta<=1/2, and the ideal accepting probability is p. The correctly reported branch has mass (1-eta)^3p. Each other record can be misreported as --+ with probability at most eta(1-eta)^2; together those records have mass 1-p. Hence the conditional output trace distance, including a reference, is at most

\[
\epsilon_{\rm cond}\le
\frac{\eta(1-p)}{(1-\eta)p+\eta(1-p)}.
\]

This is a bound on conditional states, not the diamond norm of a potentially nonlinear normalized transformation. The same expression holds for the two-sign postselection shortcut. At the GAD .95/.25 point and eta=1e-4, the bound is .0065934. Direct Bell-input calculation is sharper (.9989404 fidelity at .01486198 acceptance), but does not establish an all-input theorem. Routing, leakage, loss and decoder faults need separate ledgers. False flags scale roughly as eta/p; an arbitrarily rare perfect branch is not automatically useful.

## 9. Matched ordinary comparisons

A candidate task is calibration-free heralded transport through a mandatory noisy interface: send one half of a fresh Bell pair, discard failed attempts, store success, then teleport the live payload. No estimate of the unknown measurement/thermal basis is required.

For a declared standard network, EB links plus LOCC preserve separability; coherent placement is a distinct resource. This does not prove superiority over every definite-order circuit built from the full apparatus. Any available clean path, retained probe/environment, known dilation, or bypass must be granted to the ordinary side. Locally, retaining the state in a clean memory already gives identity.

Known-arm compilation, ordinary gate-based error filtration [3], and coherent-probe resetting [2] are the main strong comparators. A concrete failed candidate is X after amplitude damping: the rank-two protocol has p=gamma^2(1-gamma)/4, maximized at gamma=2/3, for 108 mean contacts. Ordinary dual-rail encoding corrects the no-jump branch with probability 1-gamma using two contacts, for mean 2/(1-gamma)=6 at that point. The switch's exact accepted map is real but inferior there.

No native platform, general local-QEC acceleration, or all-apparatus ordinary lower bound is established by this investigation. The physical origin of the required coherent slot interface remains separate from the algebraic identity.

## 10. Reproduction and exact polynomial screen

Sources are in `checks/algebra/`; the common runner executes them in `_build/application-search/algebra/`.

`explore.py` uses seed 487902: 300 random qubit CPTP maps at each Kraus rank 2,3,4; 100 unrelated four-channel tuples; 36 amplitude-damping points; six replacement states; five Pauli examples; and 20 qutrit negative controls. The initial source reported scalar residual below 5e-17, identity entanglement fidelity within about 7e-16, and median self-yield .02655 in that selected random ensemble. Those are debugging evidence, not hardware statistics. Qutrit tests had fidelities about .165-.491, exposing failure of naive generalization.

`polynomial_search.py` constructs exact symbolic constraints for homogeneous multilinear linear combinations of all permutations of m independent d-by-d matrices, requiring every off-diagonal entry to vanish and all diagonals to agree for every matrix assignment. It distinguishes scalar polynomials from identically zero matrix identities.

| d | degree | words | scalar kernel dimension | nonzero central directions |
|---|---|---|---|---|
| 2 | 1 | 1 | 0 | 0 |
| 2 | 2 | 2 | 0 | 0 |
| 2 | 3 | 6 | 0 | 0 |
| 2 | 4 | 24 | 3 | 2 |
| 3 | 4 | 24 | 0 | 0 |

At qubit degree four, one kernel direction is the alternating zero matrix identity and two are genuinely central. This is not a lower bound on arbitrary protocols, repeated-variable identities, codes, or extra coherent access.

`verify_extensions.py` checks 80 measure/prepare pairs averaged over 24 Cliffords, 50 unknown projective bases, 100 rank-two maps, 50 maps with pure fixed states, all flag branches for 15 unrelated tuples, GAD/PPT, Kraus invariance, all 256 independent output-Pauli tuples on one nonunital example, exact SymPy identities, and flag readout effects. The pure-reset formula is also retained analytically above.

## 11. What would be a relevant next theorem

The useful principle is to make accepted Kraus operators lie in an executable correctable algebra, not simply maximize their noncommutativity. For an accessible code projector Pi, seek

\[
\Pi L_\alpha^\dagger L_\beta\Pi=c_{\alpha\beta}\Pi
\]

with a recovery implementable without forbidden hidden data, while supplying the same ordinary encoding/recovery resources to the comparator. Scalar identity is only the simplest case.

A restricted extension is immediate if all slots act on the same unknown encoded qubit factor: K_i=V(k_i tensor I_r)V^dagger. The scalar proof holds on the full carrier without learning V. This is not generic multiqubit noise, and known support/Pauli structure or ordinary encoding may remove the advantage. It does not by itself resolve the original natural-black-box practitioner task.
