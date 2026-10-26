# Braided magic, coherent trajectory resources and ordinary factories

[Architecture assessment](architecture.md) · [Recorded-measurement baselines](architecture-baselines.md#nr-r08) · [References](references.md) · [Exact checker](checks/architecture/verify_braided_magic.py)

<a id="nr-r17"></a>

## NR-R17 — An ideal non-Clifford branch does not supply its native router

Coherent order of two Ising exchanges can herald a non-Clifford gate on an unknown logical input. The complete router required for that construction is outside protected Ising braiding and fusion operations. A native hybrid trajectory interface may provide such an additional resource, but it can also provide ordinary magic factories. The physical-trajectory results below identify those comparisons without asserting a native device advantage, a measured hardware fidelity, or a reduction in fault-tolerant factory cost. A separate [charged atomic-source model](#nr-r17-noisy-factory) proves a useful distillation-entry advantage against a specified noisy-T supply, with an exact matched ordinary noisy-CS boundary. They are analytic identities and scoped obstructions, complemented by a finite exact replay; they have not been formalized in Lean.

Magic generation by switching stabilizer-preserving operations is already
established by [Mo et al., PRA **109**, 062428 (2024), Theorem 1](https://arxiv.org/html/2311.15494v2).
The distinct [unknown timed-pulse gate result NR-R21](unknown-pulse-gates.md#nr-r21)
uses the same two-order algebra with classically adjustable pulse angles.
It owns the continuous unknown-frame exact-call bound, ordinary Euler and
approximation comparisons, and their physical timing limitations. That
oracle promise is separate from the known protected-Ising controls below.
The separate [photonic program-resource comparison](backaction.md#nr-r19-private-programs)
keeps its CCZ construction and ordinary controlled-H factory in their
own physical access model. Neither comparison is a priority claim for
magic from coherent order.

<a id="nr-r17-noisy-factory"></a>

### A charged noisy H/S source for standard magic distillation

#### Result and exact scope

There is a nonempty, explicit noise interval in which a native H/S SWITCH supplies **distillable magic for the ordinary T-injection workflow**, while an ordinary memoryless noisy-T supply cannot generate magic using any adaptive stabilizer factory. The comparison uses the **same independent Z-dephasing visibility on each supplied native data slot, on its router control, and on each ordinary T primitive**. Ideal stabilizer processing is the common fault-tolerant processor resource.

This is a common quantum-computing workload: [Haah and Hastings, Quantum 2, 71 (2018), introduction](https://arxiv.org/html/1709.02832), identify magic-resource preparation as a major cost of implementing universal algorithms and study T, CS and CCZ factory endpoints. The supplied state below can enter established H-state distillation and then standard T-gate injection.

The successful native protocol uses a joint Pauli readout. Restricting the readout to the controller alone misses the advantage. With visibility nu, its entry condition is

\[
\nu+\nu^2>1,
\]

while the ordinary noisy T channel is an exact convex mixture of Clifford channels for \(\nu\le1/\sqrt2\). Thus the proved advantage window is

\[
\boxed{\frac{\sqrt5-1}{2}<\nu\le\frac1{\sqrt2}}.
\]

This is a **raw resource distillation-entry advantage under a declared compositional noise model**. It is not a threshold for noisy stabilizer processing, a physical runtime or qubit saving, a theorem that the native router is cheap, or a new general universality principle. The charged native routing resource is what supplies magic. No quantum-over-classical algorithm theorem is required for this workload comparison.

This is a resource-generation use case using the retained quantum output, rather than a workload requesting the scalar commutator meter alone. The physical Ising and trajectory comparisons elsewhere in NR-R17 keep their separate interface assumptions.

An ordinary supplied noisy controlled-$S$ resource can reproduce the complete source state, as shown below; the separation is against the declared noisy-$T$ supply, not every coherent-control interface.

#### Common resource and noise model

Free operations in both architectures are clean Clifford gates, stabilizer-state preparation, Pauli measurement, classical randomness and feedforward. These represent the common ideal stabilizer processor used in standard magic-state distillation analyses. Clean CS, controlled-H/S, Fredkin, magic catalysts and routing are not granted as free operations.

Define

\[
\mathcal Z_v(\rho)=\frac{1+v}{2}\rho+\frac{1-v}{2}Z\rho Z.
\]

The supplied native call has two slots

\[
A_\alpha=\mathcal Z_\alpha\circ\operatorname{Ad}_H,\qquad
B_\beta=\mathcal Z_\beta\circ\operatorname{Ad}_S,
\]

uses their standard quantum SWITCH with control first, and additionally applies \(\mathcal Z_\gamma\) to the router control. Every slot is used once. The physical errors are unflagged; the environments are not supplied as usable records. The comparison specializes to **alpha=beta=gamma=nu**.

Each invocation costs one native routing resource R, one noisy H-slot call and one noisy S-slot call. All discarded attempts remain charged. Clean stabilizer processing outside this atomic native invocation does not include replacing or repairing its internal error events. It also does not grant a generic clean coherently controlled slot interface.

The ordinary architecture has clean stabilizer processing, any number of the same noisy Clifford channels, and an ordinary T or T-dagger supply with the same parameter:

\[
\mathcal E_\nu=\mathcal Z_\nu\circ\operatorname{Ad}_T,
\quad T=\operatorname{diag}(1,e^{i\pi/4}).
\]

It has no native R or other uncharged nonstabilizer primitive. Independent fresh calls and environments are assumed in both architectures. An error record revealing the random Z would be a different and stronger resource.

#### Native factory: preparation, parity readout and decoding

Prepare \(|+\rangle_c|+\rangle_t\), apply the native call, and measure

\[
M=X_cY_t.
\]

Accept outcome -1. On that two-dimensional eigenspace use logical Pauli operators

\[
X_L=X_cI_t,\qquad Z_L=Z_cZ_t,\qquad Y_L=Y_cZ_t.
\]

They commute with M and obey the usual Pauli relations. The parity measurement and decoder require only stabilizer operations. An explicit decoder is

\[
D=H_c\operatorname{CNOT}_{c\to t}S_t^\dagger.
\]

It conjugates M to \(Z_c\), \(X_L\) to \(Z_cX_t\), \(Z_L\) to \(Z_t\), and \(Y_L\) to \(Z_cY_t\). Apply D, measure the control in Z, accept -1, then apply \(Z_t\). The surviving target has the positive logical X,Y,Z moments stated below. Per attempt this decoder uses one clean S-dagger, one clean CNOT, one clean H, one Z measurement and at most one Pauli correction. These are charged to the common stabilizer-processing ledger, rather than silently counting as native routing.

#### Exact conditional output

Let e,f be the independent Z-error bits after the H and S slots. Their parity means are alpha and beta. With control first the switched pure-history output on the prepared input is

\[
|\psi_{ef}\rangle=\frac{|0\rangle_c|0\rangle_t+|1\rangle_c|d_{ef}\rangle_t}{\sqrt2},
\]

where

\[
|d_{ef}\rangle=\frac{(1+i(-1)^f)|0\rangle+(-1)^e(1-i(-1)^f)|1\rangle}{2}.
\]

Average over e,f and multiply the controller off-diagonal block by gamma. The needed joint Pauli expectations are

\[
\begin{array}{c|c}
\text{Pauli}&\text{expectation}\\\hline
XY&-\gamma\alpha\beta/2\\
XI&\gamma/2\\
IY&-\alpha\beta/2\\
ZZ&1/2\\
YX&-\gamma\alpha\beta/2\\
YZ&\gamma\beta/2\\
ZX&0
\end{array}
\]

For \(\Pi_-=(I-M)/2\), the success probability and unnormalized logical moments are consequently

\[
\boxed{
P_- =\frac{2+\gamma\alpha\beta}{4},\quad
(N_X,N_Y,N_Z)=\frac{(\gamma+\alpha\beta,\gamma\beta,1+\gamma\alpha\beta)}4.
}
\]

For example, \(N_X=\operatorname{Tr}(X_L\Pi_-\rho)=[\langle XI\rangle-\langle IY\rangle]/2\). The other entries follow from \(Z_LM=YX\) and \(Y_LM=-ZX\). The normalized target Bloch vector is N/P.

The [exact source ingredient](checks/architecture/uniform_noise_magic.py), included in the existing NR-R17 replay, reconstructs all 128 joint Pauli moments and 32 physical decoded-branch moments at the eight visibility-cube vertices. Both the Kraus construction and the formulas are separately affine in each visibility, so vertex agreement proves these polynomial identities throughout the cube. The analytic derivation above establishes the meaning of those moments. No optimality over input states, readouts or native protocols is claimed.

#### Distillation, yield and usable algorithm resource

Randomly apply identity or logical Hadamard to erase Y and average X,Z. The target becomes

\[
\rho_H(x)=\tfrac12[I+x(X+Z)],\qquad
x=\frac{(1+\gamma)(1+\alpha\beta)}{2(2+\gamma\alpha\beta)}.
\]

[Reichardt, QIP 4, 251–264 (2005), Theorem 1 and §II](https://arxiv.org/html/quant-ph/0411036#S2), proves distillability with ideal stabilizer operations whenever x>1/2. His Steane-code recurrence is

\[
f(x)=\frac{x^3(7+8x^4)}{1+14x^4},\qquad
A(x)=\frac{1+14x^4}{64}.
\]

After this specified twirl, the H-axis state is distillable if and only if

\[
\boxed{\gamma+\alpha\beta>1.}
\]

The clean Clifford $H S^\dagger H$ sends Bloch coordinates $(x,0,x)$ to $(x,x,0)$; after distillation this is the standard $T$-injection state. This directly feeds the common workflow of preparing reliable T resources for algorithms. No supplied T state or nonstabilizer seed is consumed by the native preparation or the distillation circuit.

With fresh independent attempts, one accepted raw state costs mean \(1/P_-=4/(2+\gamma\alpha\beta)\) R calls and twice as many noisy slot calls. Failures are discarded only after their whole cost is charged. Accepted states from independent attempts are identically and independently distributed, as required by this recurrence.

The threshold excess is

\[
d=x-\tfrac12=\frac{\gamma+\alpha\beta-1}{2(2+\gamma\alpha\beta)}.
\]

For x between 1/2 and 3/5 the exact bound

\[
f(x)-x\ge\frac{224}{1759}(x-1/2),\qquad A(x)\ge15/512
\]

implies at most \(k=\max\{0,\lceil\log[(1/10)/d]/\log(1983/1759)\rceil\}\) successful bootstrap levels to reach x>=3/5. Expected R consumption is at most

\[
\frac{4}{2+\gamma\alpha\beta}\left(\frac{3584}{15}\right)^k.
\]

This deliberately loose, rigorous bound is polynomial in the inverse threshold gap. Fixed parameters strictly inside the entry region give finite fixed bootstrap cost. For subsequent fifteen-to-one rounds, put $e=(1-\sqrt2 x)/2$ and $r=1-2e$. The standard acceptance and error recurrence are

$$
p_{15}(e)=\frac{1+15r^8}{16},\qquad
F_{15}(e)=\frac{1-15r^7+15r^8-r^{15}}{2(1+15r^8)}.
$$

At $x\ge3/5$, $e<13/100$, inside this routine's convergence region. One exact check of the latter statement sets $u=r^2$ and $w=u+u^{-1}$: the sign of $F_{15}(e)-e$ is the sign of $w^3+w^2-2w-16$. For $0<e\le13/100$, this polynomial increases on the relevant interval $2\le w\le1369/2500+2500/1369$, and its value at the upper endpoint is negative. Thus the error decreases to zero, with the usual cubic suppression near zero. For either $n$-to-one routine, independent fresh batches and restart on rejection give the exact renewal ledger $C_{\mathrm{next}}=nC_{\mathrm{current}}/p_{\mathrm{accept}}$. It includes every rejected batch; the fixed stabilizer circuit, syndrome measurements, memory and classical processing are additional common processor resources. For an algorithm with $m$ injections, preparing each state to error $\delta$ bounds the final operational trace-distance error, and the half-diamond channel distance, by $m\delta$ through the usual hybrid argument. This supplies a finite-accuracy computational endpoint. No positive perfect-state asymptotic yield or optimized factory overhead is asserted from this bound.

#### Ordinary baseline: an exact no-activation interval

For \(0\le\nu\le1/\sqrt2\), direct action on the Pauli basis proves

\[
\boxed{
\mathcal E_\nu
=\tfrac12\operatorname{Ad}_I
+\frac\nu{\sqrt2}\operatorname{Ad}_S
+\left(\tfrac12-\frac\nu{\sqrt2}\right)\operatorname{Ad}_Z.
}
\]

The coefficients are nonnegative and sum to one. The T-dagger version has S-dagger in place of S. Thus each supplied noisy T primitive is literally a random Clifford channel, even on inputs entangled with arbitrary ancillas. Its output on |+> is the usual noisy T state with Bloch coordinates \((\nu/\sqrt2,\nu/\sqrt2,0)\), inside the stabilizer octahedron in the same interval.

Every ordinary adaptive composition, including arbitrary stabilizer ancillas, feedforward and postselection, therefore remains a stabilizer instrument. Conditioning can change mixture weights but cannot create a nonstabilizer state in any nonzero visible branch. Unlimited unflagged copies, collective distillation, ordinary three-T CS synthesis, and T-state cultivation built only from the stated supply and free processor cannot circumvent this exact convex decomposition. This is stronger than testing a particular conventional factory.

Combining that obstruction with the native entry condition gives the stated nonempty uniform-noise window. Equivalently, with unflagged phase-flip probability \(p=(1-\nu)/2\) on each supplied primitive, the interval is

\[
\frac{1-1/\sqrt2}{2}\le p<\frac{3-\sqrt5}{4}.
\]

These are **raw resource-entry values** under an ideal stabilizer processor. Calling them a hardware fault-tolerance threshold would be incorrect.

A concrete interior witness is \(\nu=2/3\), or phase-flip probability 1/6 at each supplied primitive. The native acceptance probability is 31/54 and the corrected Bloch vector is \((15/31,6/31,35/62)\). Its H-twirled coordinate is \(x=65/124>1/2\), so it is distillable. The ordinary noisy T state instead has coordinates \((\sqrt2/3,\sqrt2/3,0)\), whose l1 norm is below one, and its entire channel has the exact Clifford decomposition above. Native raw preparation costs mean 54/31 R calls per accepted state at this algebraic point; this is a checkable example, not an optimized hardware setting.

This interior example can already enter the familiar 15-to-1 H/T-injection-state routine directly. Its H-eigenstate error is $e=(1-65\sqrt2/124)/2<13/100$, in the exact convergence interval above; numerically it is about 0.129, below the familiar approximately 0.141 entry threshold. [Bravyi and Kitaev, PRA 71, 022316 (2005), §VI, Eqs. (35)–(38)](https://arxiv.org/html/quant-ph/0403025#S6), give the acceptance probability, exact error recurrence and cubic high-fidelity suppression. The sharp Reichardt threshold is needed to establish the full open interval, rather than to make this concrete example operational.

#### What is being improved, and the matched-resource boundary

The demonstrated benefit is the existence of a distillable T resource in a common primitive-noise regime where ordinary noisy-T injection cannot supply one at any copy count. The native method spends R and three noise locations per attempt rather than declaring the router free. No scalar price for R versus a T injection was needed to prove that source-quality benefit.

The result does not imply a universally cheaper native factory. A clean ordinary CS source, or an ordinary source implementing the same full noisy two-qubit map as the native router, can reproduce the output and shares its distillation entry condition. Such a source is itself a nonstabilizer resource and is not available from the stipulated CSP noisy-T supply in the separation interval. Granting it would change the resource comparison. Likewise, different error axes, inter-call correlations, errors in the clean processor, loss, leakage, or a router error that reveals which order occurred require new analysis.

For the strongest supplied-state comparison, write $e,f,g$ for the H-slot, S-slot and controller Z-error bits. Put $|CS\rangle=CS|++\rangle$ and $U_{efg}=Z_c^g\operatorname{CNOT}_{c\to t}^{e}\operatorname{CZ}_{ct}^{f}$. Directly using $HZ^eH=X^e$ gives

$$
(Z_c^g\otimes H_t)|\psi_{ef}\rangle
=\frac{|0\rangle|+\rangle+(-1)^g|1\rangle X^e Z^f S|+\rangle}{\sqrt2}
=U_{efg}|CS\rangle.
$$

Consequently, with $q_v(b)=[1+(-1)^b v]/2$,

$$
(I\otimes H)\rho_{\rm native}(I\otimes H)
=\sum_{e,f,g}q_\alpha(e)q_\beta(f)q_\gamma(g)
 U_{efg}|CS\rangle\langle CS|U_{efg}^{\dagger}.
$$

Every $U_{efg}$ is Clifford. A supplied ordinary CS state followed by this random Clifford channel therefore reproduces the full pre-readout source and every later branch, not just an accepted-state fidelity. This is a fixed-input source identity, not equality of arbitrary-input channels. The exact ingredient checks all eight history identities. An ordinary interface supplying that noisy CS resource shares the claimed benefit. In particular, [Simonov et al., Section II](https://arxiv.org/html/2311.13654v4#S2) discuss controlled/vacuum-extended operations in implementations of coherent order; such apparatus access cannot be excluded by calling it routing. No equal-device or total-cost separation follows from restricting the comparator to noisy T.

#### Prior work and novelty boundary

[Mo et al., PRA 109, 062428 (2024), §III–IV](https://arxiv.org/html/2311.15494v2) already establish SWITCH magic creation from completely stabilizer-preserving channels and noise-assisted retention in depolarizing examples. [Simonov et al., PRResearch 8, 013239 (2026), §III–IV](https://arxiv.org/html/2311.13654v4) already establish universality constructions from superposed single-qubit orders. These broad phenomena are not new claims here.

The presently derived addition is the explicit **joint-parity magic-factory protocol**, its full three-visibility conditional state, the common-noise sufficient threshold \(\gamma+\alpha\beta>1\), and its uniform-noise comparison with an exact random-Clifford ordinary T supply. It upgrades a magic witness to an established distillation endpoint with a counted resource ledger. A bounded check of those closest papers found depolarizing/noise-capacity and universality results rather than this specific dephasing/joint-readout threshold. The algebra, distillation endpoint and baseline have independent bounded reviews. Search absence does not establish priority; no first-priority claim is made.

### Ideal logical gate and complete branch accounting

Four Ising $\sigma$ anyons with total charge $1$ encode a qubit in the $1/\psi$ fusion channel of a pair. In a fixed exchange orientation, adjacent exchanges have the qubit actions

$$
U=\frac{I-iX}{\sqrt2},\qquad V=\frac{I-iZ}{\sqrt2},
\tag{1}
$$

up to their physical Abelian phases. The two histories below contain the same two exchanges, so a common product phase cancels from their relative interference. This does **not** permit dropping a braid phase in an interferometer comparing a braid with no braid.

Assume an independent helper $C$ starts in $|+\rangle$ and a native interface implements the full controlled operation

$$
W=|0\rangle\langle0|_C\otimes VU+
  |1\rangle\langle1|_C\otimes UV.
\tag{2}
$$

Its final helper $X$ measurement must preserve the computational fusion qubit and every inaccessible reference. Multiplication gives

$$
\begin{aligned}
VU&=(I-iX-iZ-iY)/2,& UV&=(I-iX-iZ+iY)/2,\\
M_+&=(VU+UV)/2=\frac{I-iX-iZ}{2}=\frac{\sqrt3}{2}G,
&M_-&=(VU-UV)/2=-\frac{iY}{2},\\
G&=\frac{I-iX-iZ}{\sqrt3},
&M_+^\dagger M_+&=\frac34I,\quad M_-^\dagger M_-=\frac14I.
\end{aligned}
\tag{3}
$$

Since $(X+Z)^2=2I$, $G^\dagger G=I$. Thus the plus branch applies the unitary $G$ to an **arbitrary unknown input**, including a reference, with input-independent probability $3/4$. The minus branch is a known Pauli with probability $1/4$.

With actual Pauli recovery, independent ideal retries have mean $4/3$ attempts: $8/3$ slot exchanges, $4/3$ helper preparations/readouts and $1/3$ Pauli recovery operations, in addition to routing and storage. An adapted frame can replace actual recovery only if specified. For example, after an odd $Y$ frame reverse both known braid orientations, since $YUY=U^\dagger$ and $YVY=V^\dagger$; the desired success then has a known final Pauli frame. A fresh-state factory may instead discard failed inputs and charge their reinitialization. These are expected-cost constructions with no hard attempt cap. An unspecified noisy minus map does not support this retry argument.

For a fresh stabilizer input $|0\rangle$, the successful state is

$$
|g\rangle=G|0\rangle=
\frac{(1-i)|0\rangle-i|1\rangle}{\sqrt3},
\qquad \boldsymbol r_g=(2/3,-2/3,1/3).
\tag{4}
$$

It is outside the stabilizer octahedron. More quantitatively, every single-qubit stabilizer mixture $\rho_{\rm stab}$ obeys

$$
\langle g|\rho_{\rm stab}|g\rangle\le
\frac{1+\max_j|r_{g,j}|}{2}=\frac56.
\tag{5}
$$

The extremal stabilizers have Bloch vectors $\pm\hat x,\pm\hat y,\pm\hat z$; their overlaps are $(1\pm r_{g,j})/2$, and linearity proves the bound for mixtures. Hence an encoded output with target fidelity above $5/6$ certifies magic. $G$ is not the canonical $T$ gate, and one $|g\rangle$ has not been priced as one distilled $|T\rangle$ or as a full injected logical gate.

### Protected Ising operations cannot supply this helper interface

The Clifford restriction on Ising braiding is an established input: [Ahlbrecht, Georgiev and Werner](https://doi.org/10.1103/PhysRevA.79.032311) prove that the braid image lies within the Clifford group. [Bonderson, Clarke, Nayak and Shtengel](https://arxiv.org/html/0911.2691) distinguish these protected operations from interfering-anyon phase gates supplemented by distillation.

Suppose data, helper and ancillas are all standard encoded Ising fusion qubits, initialized by protected vacuum pair creation, and manipulated only by protected braids, ideal topological-charge measurements and classical feedforward. Their initial states are stabilizer states. Braids are Clifford; the $1/\psi$ charge measurements are encoded even-Majorana-parity Pauli measurements. Each nonzero measurement branch of a stabilizer state remains stabilizer. Induction over the complete adaptive record therefore proves closure under ancillas, postselection and finite branching. Properly terminated random-stopping mixtures and limits remain in the closed stabilizer polytope.

If those resources implemented (2), the stabilizer input $|+\rangle_C|0\rangle$ and a Pauli $X$ readout would yield (4) in a nonzero branch, contradicting (5). This also excludes arbitrarily accurate preparation of (4) above the stabilizer fidelity ceiling. A classical choice of braid order does not evade this argument. Quantum control of a known Clifford is an additional operation, not automatically another Clifford.

A narrower loop test helps identify a proposed physical route. If its two full-loop fusion actions are Paulis $P,Q$, then $QP=\epsilon PQ$, $\epsilon=\pm1$, and

$$
|0\rangle\langle0|\otimes QP+
|1\rangle\langle1|\otimes PQ
=\begin{cases}I_C\otimes QP,&\epsilon=1,\\Z_C\otimes QP,&\epsilon=-1.
\end{cases}
\tag{6}
$$

Thus such order control supplies a Pauli and a controller sign, not magic. Loops around disjoint fixed charges commute; overlapping noncommuting Pauli loops still satisfy (6). This assumes equal branch phases and the specified Pauli actions. Additional interferometric phases or other anyon types require their full instrument.

This obstruction is specific to standard protected Ising resources. Fibonacci braiding is already universal. Fusion and charge measurement can also make other non-Abelian models universal: [Lo et al.](https://arxiv.org/html/2601.20956) give a circuit realization of $S_3$ topological order, gates and magic preparation on a trapped-ion processor. That is an ordinary comparator for its own model, not a demonstration of an inexpensive movable-Ising order router.

### A native trajectory proposal already permits an ordinary factory

[Debortoli and Grusdt](https://arxiv.org/html/2610.06203) propose spin-dependent motion of impurities bound to anyons, Ramsey exchange readout and a conventional-to-topological encoder. This is a theoretical interface proposal, not an experiment or an implemented $AB/BA$ gate. Its single-impurity encoder uses a closed loop returning the impurity to its original position. Its stated pure-Ising convention is

$$
B_{23}=e^{i\pi/8}e^{-i\pi X/4},\qquad
B_{23}^2=e^{-i\pi/4}X.
\tag{7}
$$

The following ordinary consequence uses that ideal common-position, common-environment interface. In the spin basis $|\downarrow\rangle,|\uparrow\rangle$, its controlled full loop is

$$
C_{\rm loop}=|\downarrow\rangle\langle\downarrow|\otimes I+
 |\uparrow\rangle\langle\uparrow|\otimes e^{-i\pi/4}X
=(T_C^\dagger\otimes I)\operatorname{CNOT}_{C\to\rm top}.
\tag{8}
$$

Prepare spin $|+\rangle$ and topological $|0\rangle$. One loop gives

$$
\frac{|\downarrow\rangle|0\rangle+
 e^{-i\pi/4}|\uparrow\rangle|1\rangle}{\sqrt2}.
\tag{9}
$$

Spin $X$ outcomes each have probability $1/2$ and leave $(|0\rangle\pm e^{-i\pi/4}|1\rangle)/\sqrt2$. Recorded $Z$ feedforward makes both a topological $T^\dagger|+\rangle$. This raw-state factory uses **one full loop**, one spin preparation/readout and its correction; it does not require order reversal, a second encoder loop or an initial conventional magic state. The spin-phase compensation used to transfer an arbitrary spin state is simply omitted here. This is a state factory on a known input, not a $T$ gate on an unknown existing payload.

There is no contradiction with protected Ising closure: (8) already is non-Clifford on the hybrid spin/fusion Hilbert space. Its externally coherent position/spin control was not among the protected operations in that closure theorem.

The full physical phase is essential. More generally,

$$
B_{23}=e^{i\alpha}e^{-i\pi X/4},\qquad
B_{23}^2=e^{i\chi_{\rm stat}}X,\quad
\chi_{\rm stat}=2\alpha-\pi/2,
\qquad\chi=\chi_{\rm stat}+\phi_{\rm apparatus}\pmod{2\pi},
\tag{10}
$$

where $\phi_{\rm apparatus}$ includes the actual binding, dynamical and background-flux phases relative to the unmoved arm. In the common-environment model the full controlled loop uses $e^{i\chi}X$ and the same protocol prepares

$$
|\chi\rangle=(|0\rangle+e^{i\chi}|1\rangle)/\sqrt2.
\tag{11}
$$

It is magic precisely when $\chi\notin(\pi/2)\mathbb Z$. A physical Ising-type charge sector can change this phase relative to the neutral Ising matrix. [Bonderson, Fidkowski, Freedman and Walker, §6.1](https://arxiv.org/html/1306.2379) explicitly distinguish pure Ising from Moore–Read and other Ising-type theories. A neutral-sector matrix specified only up to global phase therefore does not justify a $\pi/8$ resource claim for a charged Hall anyon or superconducting vortex. If the full $\chi$ is a Clifford angle, a tunable conventional phase may still make (11) magic, but that phase is then an additional supplied non-Clifford resource. The same phase controls and encoder must be available to the ordinary comparator.

For an explicit limited noise model, let the two normalized trajectory records be $|e_0\rangle,|e_1\rangle$, $\eta=\langle e_0|e_1\rangle$, with no loss or leakage and equal branch amplitudes. After either spin outcome and its correction, tracing those records gives

$$
\rho_{\chi,\eta}=\frac12
\begin{pmatrix}1&\bar\eta e^{-i\chi}\\
\eta e^{i\chi}&1\end{pmatrix}.
\tag{12}
$$

This follows by tracing the cross term in (9); the outcome probabilities remain $1/2$ because the logical basis states are orthogonal. Its magic condition is $|\operatorname{Re}(\eta e^{i\chi})|+|\operatorname{Im}(\eta e^{i\chi})|>1$. At $\chi=-\pi/4$ and real visibility $v$, it requires $v>1/\sqrt2$. Loss, unequal path amplitudes or fusion records need their own complete maps; (12) is not a fitted native noise model or an optimized ordinary converse.

### The proposed half-exchange has postselected position histories

The two-impurity exchange proposal does not supply a clean controlled-$B$ oracle. Under its ideal trajectory assumptions, the initial two-spin superposition has four motion histories. Only no motion and both moving end in the designated separated-position sector; the one-moving histories are distinguishable and must be kept or rejected explicitly. Before the final spin Hadamards, the retained sector has amplitude

$$
\frac{|00\rangle\otimes|\psi\rangle+
 e^{-i\phi}|11\rangle\otimes B|\psi\rangle}{2}.
$$

Reading final spins $a,b$ gives

$$
K_{ab}=\frac{I+(-1)^{a+b}e^{-i\phi}B}{4}.
\tag{13}
$$

This follows from $\langle ab|H^{\otimes2}|00\rangle=1/2$ and $\langle ab|H^{\otimes2}|11\rangle=(-1)^{a+b}/2$. There are two copies of each sign, so $\sum_{ab}K_{ab}^\dagger K_{ab}=I/2$. One particular plus outcome has probability $[1+\operatorname{Re}\langle e^{-i\phi}B\rangle]/8$. Its amplitude is half that of an abstract balanced controlled-$B$ $X$ outcome, and its probability is one quarter. All invalid-position histories remain charged; their action on an unknown input has not been replaced by a harmless failure.

This is already an ordinary interferometric magic primitive. If the calibrated phase gives $e^{-i\phi}B=e^{-i\pi Z/4}$, then

$$
\begin{aligned}
\frac{I+e^{-i\pi Z/4}}2&=\cos(\pi/8)e^{-i\pi Z/8},\\
\frac{I-e^{-i\pi Z/4}}2&=i\sin(\pi/8)Z e^{-i\pi Z/8}.
\end{aligned}
\tag{14}
$$

Expanding the exponential proves both identities. All four valid spin outcomes give the same $T$ rotation up to a Pauli and scalar, with total ideal output yield $1/2$. The phase setting is a physical resource. [Ordinary partial interferometry, §7](https://arxiv.org/html/1306.2379), already generates Ising magic through phase tuning; twisted interferometry adds different probe/topology resources with their own implementation conditions. Neither is free merely because it uses braiding terminology.

A physical $AB/BA$ realization instead needs coherent geometry for exchanges sharing a middle anyon, common final positions, and erasure of every unwanted spin, fusion and bath history. The proposal's individual conditional displacements and a Ramsey fringe do not establish that isometry or its cost. Sequentially using (13) is not automatically a two-slot switch of logical braids.

### An ordinary controlled exchange matches the raw-state ensemble

If a **clean** do/don't-$S$ interface, $S=\operatorname{diag}(1,i)$, is available, a simpler raw-state comparator is exact. Prepare $|+\rangle_C|+\rangle$, apply controlled-$S$, measure $X_C$, and apply fixed $S^\dagger$ to the data. Its vectors are

$$
S^\dagger(I\pm S)|+\rangle/2.
\tag{15}
$$

For plus, this is $e^{i\pi/4}M_+|0\rangle$ from (3); for minus it is phase times $M_-|0\rangle$. Thus **both subnormalized flagged outputs** agree: $|g\rangle$ with probability $3/4$ and $|1\rangle$ with probability $1/4$. This uses one controlled exchange **plus** the fixed $S^\dagger$ data Clifford. If physically executed, that correction is another inverse exchange. It is not a one-total-braid claim or a full unknown-input implementation of $G$.

Controlled-$S$ itself is non-Clifford. Moreover, replacing a physical $B=e^{i\alpha}e^{-i\pi Z/4}$ by $S$ under quantum control can require a priced arm phase; its global phase cannot be discarded. Neither an abstract switch resource nor (13) automatically grants clean controlled-$S$. Equation (15) is an apparatus comparison only when that coherent geometry and matched records/phases really are available.

There is also a comparison using (13) itself when the **full physical** braid is $B=S$ and the ordinary dynamical arm phase is calibrated to zero. On input $|+\rangle$, each of the two plus-sign outcomes has probability $3/16$; after fixed $S^\dagger$, both give $|g\rangle$. The yield is $3/8$ per one exchange, or mean $8/3$ exchange attempts per retained state. This matches the ideal two-exchange order factory's $2/(3/4)=8/3$ slot exchanges before different helper, reset and final-Clifford costs. For general $\alpha$, reaching $S$ needs the extra phase $\alpha-\pi/4$; it is not a free change of convention. This equality of one exposure count is not equal wall time or a hardware optimum.

The clean-interface state identity also survives matched independent helper dephasing. Let $0\le\nu\le1$ multiply the two-history coherence, with otherwise ideal operations. For both constructions, the subnormalized $\pm$ states are exactly

$$
\sigma_\pm(\nu)=\frac18
\begin{pmatrix}
2(1\pm\nu)&(1\pm\nu)(1+i)\\
(1\pm\nu)(1-i)&2
\end{pmatrix}.
\tag{16}
$$

For (2), insert the two branch vectors $VU|0\rangle,UV|0\rangle$ in $[aa^\dagger+bb^\dagger\pm\nu(ab^\dagger+ba^\dagger)]/4$. For (15), use $S^\dagger|+\rangle,S^\dagger S|+\rangle$ in the same expression. Multiplication gives (16), proving equality of the full flagged ensemble rather than selected fidelities. Consequently

$$
\begin{gathered}
p_+=(2+\nu)/4,\qquad
\boldsymbol r_+=\left(\frac{1+\nu}{2+\nu},
-\frac{1+\nu}{2+\nu},\frac\nu{2+\nu}\right),\\
\|\boldsymbol r_+\|_1=1+\frac{2\nu}{2+\nu},\qquad
\langle g|\sigma_+/p_+|g\rangle=
\frac{5+4\nu}{6+3\nu}.
\end{gathered}
\tag{17}
$$

The plus state is magic for every $\nu>0$ in this restricted model, but that robustness is not order-specific under the matched clean interface. It is not a distillation-rate theorem or a complete hardware noise model. At $\nu<1$, the minus map on an arbitrary input is no longer the known Pauli in (3), so its ideal retry ledger cannot be retained unchanged.

### Native direct alternatives and the cost ledger

Continuous tunnel controls already supply ordinary non-Clifford alternatives. In a coherent single-charge-transfer model, let

$$
O_\theta=\cos\theta\,\gamma_1+\sin\theta\,\gamma_2.
$$

Using $\gamma_j^2=I$ and $\gamma_1\gamma_2=-\gamma_2\gamma_1$ gives

$$
O_\theta^2=I,\qquad
O_\varphi O_\theta=
\cos(\varphi-\theta)I-\sin(\varphi-\theta)\gamma_1\gamma_2
=e^{-(\varphi-\theta)\gamma_1\gamma_2}.
\tag{18}
$$

Two transfers restore the dot charge and permit a calibrated $\pi/8$ rotation. An individual transfer changes island parity while preserving total dot-plus-island parity. [Flensberg](https://arxiv.org/html/1011.5467) proposes this continuous-angle charge-control mechanism; its tunnel amplitudes and required relative phase are physical calibrations, not discrete protected braids or a free violation of fermion superselection.

[Aasen et al., Appendix D](https://arxiv.org/html/2502.12252v3#A4) explicitly include ordinary timed $H_T=\epsilon_Ti\gamma_j\gamma_k$ pulses through the same quantum-dot paths used for parity readout, followed by native distillation. With $Z=i\gamma_j\gamma_k$ and $\int\epsilon_Tdt=\pi/8$, this gives a raw $T$ rotation. This is a proposed control-sensitive source, not measured pulse fidelity. [Karzig et al.](https://arxiv.org/html/1511.05161) give geometric control alternatives, and the [three-Majorana cotunneling proposal](https://arxiv.org/html/2506.03553v5) supplies continuous geometric coupling paths. A geometric phase is not automatically a quantized protected exchange.

| Interface | Ideal delivered endpoint | Charged primitive ledger and qualification |
| --- | --- | --- |
| Protected Ising braids and fusion | Stabilizer output only | No magic in any nonzero branch of the stated resources. |
| Pauli-valued full-loop order | Pauli and controller sign | Two loops; (6) supplies no magic. |
| Ideal two-exchange order | Unknown-input $G$ with $p=3/4$ | Mean $8/3$ slot exchanges for ideal retries, $4/3$ helper cycles and $1/3$ actual Pauli recoveries or specified frame adaptation; all routing/storage charged. |
| Clean controlled-$S$ state factory | Same two flagged raw states | One controlled exchange plus fixed $S^\dagger$ data Clifford, which is an inverse exchange if executed; conditional native interface. |
| Pure-Ising closed-loop factory | Topological $T^\dagger|+\rangle$ | One full loop, one spin preparation/readout and recorded $Z$ correction; unit ideal yield requires the full phase in (7) and no loss. |
| Two-impurity half-exchange | Phase-compensated $T$ rotation on valid outputs | One exchange per attempt, two impurities, four spin $\pi/2$ pulses, phase setting and two spin readouts; all four valid outcomes give yield $1/2$. If physical $B=S$, its two plus outcomes give the same $|g\rangle$ with yield $3/8$ plus fixed $S^\dagger$. |
| Timed pair-coupling source | Raw $T$ state | Calibrated unprotected pulse, followed by code-native distillation and injection; no quantum trajectory router assumed. |

These are counts of mathematical primitives, not a hardware timing table. A fair comparison needs common measured adiabatic gaps, binding/recombination fidelity, positional coherence, loss, parity poisoning, readout/reset errors and actuator cost. Fusion and position records, continuously controlled geometry, logical transfer and all rejections belong in the ledger. A classical record identifying the history cannot be erased merely by relabelling the final helper outcome. Distillation must use the actual raw-error correlations; it does not make an uncharacterized process independent for free.

A positive device result would specify a full anyon model including its charge sector and a microscopic three-anyon spin/position Hamiltonian realizing (2) at common final positions on reference-entangled inputs. It would characterize both CP branches and leakage/failure, then compare distilled or injected magic at the same logical error and total factory space-time against (11), ordinary partial/exchange interferometry and the available direct coupling source. The algebra alone supplies no native advantage or cost ordering.

### Executable verification and limits

[verify_braided_magic.py](checks/architecture/verify_braided_magic.py) uses only Gaussian rational fractions, rejects optimized Python execution and writes JSON to standard output. It checks (3)'s gate probabilities, (5)'s extremal stabilizer overlaps, both flagged states in (16) for five rational visibilities, their probabilities and (17), the physical-$S$ half-exchange yield/exposure arithmetic, and all sixteen one-qubit Pauli pairs in (6). It also runs [uniform_noise_magic.py](checks/architecture/uniform_noise_magic.py), checking the full H/S source, joint parity/decoder moments, all eight matched-CS histories, the ordinary Clifford-mixture Pauli action and exact distillation-entry arithmetic. It needs no data file or third-party dependency. Run it with `python -S -B research/topics/nr-noisy-recovery/checks/architecture/verify_braided_magic.py`.

The protected-resource closure, native trajectory assumptions, physical Abelian phases, collision/loss completion, continuous-charge model and fault-tolerant cost comparison remain analytic arguments and interface conditions. Finite matrix replay is not a hardware realization, an optimized factory converse or a Lean proof.
