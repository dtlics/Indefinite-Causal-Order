# Braided magic, coherent trajectory resources and ordinary factories

[Architecture assessment](architecture.md) · [Recorded-measurement baselines](architecture-baselines.md#nr-r08) · [References](references.md) · [Exact checker](checks/architecture/verify_braided_magic.py)

<a id="nr-r17"></a>

## NR-R17 — An ideal non-Clifford branch does not supply its native router

Coherent order of two Ising exchanges can herald a non-Clifford gate on an unknown logical input. The complete router required for that construction is outside protected Ising braiding and fusion operations. A native hybrid trajectory interface may provide such an additional resource, but it can also provide ordinary magic factories. The results below identify those comparisons without asserting a native advantage, a measured hardware fidelity, or a reduction in fault-tolerant factory cost. They are analytic identities and scoped obstructions, complemented by a finite exact replay; they have not been formalized in Lean.

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

[verify_braided_magic.py](checks/architecture/verify_braided_magic.py) uses only Gaussian rational fractions, rejects optimized Python execution and writes JSON to standard output. It checks (3)'s gate probabilities, (5)'s extremal stabilizer overlaps, both flagged states in (16) for five rational visibilities, their probabilities and (17), the physical-$S$ half-exchange yield/exposure arithmetic, and all sixteen one-qubit Pauli pairs in (6). It needs no data file or third-party dependency. Run it with `python -S -B research/topics/nr-noisy-recovery/checks/architecture/verify_braided_magic.py`.

The protected-resource closure, native trajectory assumptions, physical Abelian phases, collision/loss completion, continuous-charge model and fault-tolerant cost comparison remain analytic arguments and interface conditions. Finite matrix replay is not a hardware realization, an optimized factory converse or a Lean proof.
