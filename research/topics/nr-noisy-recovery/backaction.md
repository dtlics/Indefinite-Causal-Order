# Quantum-bath backaction and ordinary control baselines

[Application assessment](architecture.md) · [Ordinary baselines](architecture-baselines.md) · [Dispatch](dispatch.md) · [Checks](checks/README.md)

<a id="nr-r14"></a>

## NR-R14 — Shared-bath calibration transfer and exact ordinary echo/instrument baselines

A complete one-time noise calibration need not predict performance under a different control history. The examples below reverse the preferred storage schedule while preserving an entire one-time calibration. They therefore describe useful architecture decisions. In the stated native central-spin model, ordinary Hahn echo already implements the proposed coherent bath-order experiment, including its conditional quantum output. A separate excitation-exchange example goes beyond pure dephasing: its full order-controlled output distinguishes the hidden coupling phase, but an ordinary serial survival test attains exactly the same optimal distinguishability. Known sensor-only measurement and reset interventions have a related ordinary controlled-dilation implementation.

These are analytic identities and scoped counterexamples. The elementary proofs below are not claims of a new echo, spectroscopy, or bath-control mechanism. Their finite exact replay is [verify_backaction.py](checks/architecture/verify_backaction.py); it checks signs, normalization and specified examples, rather than proving the general statements by enumeration. NR-R14 has not been formalized in Lean or externally peer reviewed.

### Native interface and the full bath

Let $S$ be an accessible sensor qubit and $E$ a persistent, inaccessible bath. For one free-evolution window of duration $\tau$, assume the **actual joint evolution** is

$$
H_{SE}=|0\rangle\langle0|\otimes H_0
       +|1\rangle\langle1|\otimes H_1,
\qquad
V=\begin{pmatrix}A&0\\0&B\end{pmatrix},
\quad A=e^{-i\tau H_0},\quad B=e^{-i\tau H_1}.
\tag{1}
$$

The same bath persists between windows. Its state $\rho_{ER}$ may be entangled with an arbitrary passive reference $R$. Every identity below acts as the identity on $R$; neither strategy gains access to it. Ordinary controls include known sensor pulses, initialization, reset, phase-resolved readout, clean ancillary memories, retained records and adaptive processing. No bath inverse, bath reset, matrix description of $A,B$, or separate controlled bath oracle is supplied.

Conditional nuclear Hamiltonians of this form motivate central-spin models. Control-dependent failure of a single classical noise description has been observed in an NV environment by [Hernández-Gómez et al.](https://arxiv.org/abs/1808.08222). More generally, [Burgelman et al.](https://arxiv.org/html/2407.04766v2) analyze control-history-dependent dephasing errors that survive perfect sensor resets. These works motivate the decision problem; they are not switch-advantage claims.

Equation (1) is a microscopic premise. One-time reduced channels on $S$ do not specify it. Spectators, retained apparatus and external fields must be included in the joint description when they matter. Time-dependent fields, finite pulse durations and control errors require their actual clock-dependent operations.

### Exact echo identity, including the conditional quantum output

Write $F=X_S\otimes I_E$. Direct block multiplication gives

$$
FVFV=|0\rangle\langle0|\otimes BA
     +|1\rangle\langle1|\otimes AB=:C.
\tag{2}
$$

Thus two ordinary free windows separated by a sensor $X$, followed by the known restoring $X$, implement the full controlled order of $A,B$ on the bath. This is the Hahn-echo circuit. The daggers that appear in its readout overlap come from a measurement bra, not physical time reversal.

For $S$ initially $|+\rangle$, put $W_0=BA,W_1=AB$. The entire final state is

$$
\frac12\sum_{a,b=0}^1 |a\rangle\langle b|_S\otimes
 (W_a\otimes I_R)\rho_{ER}(W_b^\dagger\otimes I_R).
\tag{3}
$$

Measuring in $|s_\theta\rangle=(|0\rangle+s e^{i\theta}|1\rangle)/\sqrt2$, $s\in\{+1,-1\}$, gives the exact bath instrument

$$
K_{s,\theta}=\frac{BA+s e^{-i\theta}AB}{2},
\qquad
\sum_s K_{s,\theta}^\dagger K_{s,\theta}=I.
\tag{4}
$$

Its flagged output is $\sum_s |s\rangle\langle s|\otimes (K_{s,\theta}\otimes I_R)\rho_{ER}(K_{s,\theta}^\dagger\otimes I_R)$. This is exactly the corresponding ideal unitary-switch instrument on the bath. Equality holds for every input and reference, so it preserves every record probability, conditional bath state and subsequent adaptive utility. Keeping the control coherent or swapping it into a clean memory also preserves the equality; the extra memory and swaps count on both sides. Repeating the instruments proves the same claim for persistent-bath trajectories by induction on their records.

For $L=\operatorname{Tr}[\rho_E(AB)^\dagger BA]$, $X$ readout gives

$$
p_- = \frac{1-\operatorname{Re}L}{2}
     =\frac14\operatorname{Tr}\!\left[\rho_E[A,B]^\dagger[A,B]\right].
\tag{5}
$$

Changing the readout phase obtains $\operatorname{Im}L$. Ordinary phase-resolved sensing can access response information as well as decay: [Wang and Clerk](https://arxiv.org/abs/2104.02047) develop quench-based noise spectroscopy, and [Jerger et al.](https://arxiv.org/html/2303.02233) measure nuclear-bath polarization using phase-resolved NV spin echoes.

The comparison uses two free windows and the same known sensor pulses, preparation and readout. With different early and late blocks $A_1,B_1,A_2,B_2$, the actual echo instead produces $\operatorname{diag}(B_2A_1,A_2B_1)$. Replacing this by $\operatorname{diag}(BA,AB)$, or replacing the persistent bath by independent channel environments, needs additional assumptions. Neither strategy receives perfect routing, pulses, retained coherence or rejected runs free of their physical costs.

### Identical Ramsey calibration, reversed storage choice

Consider two explicit models, with initially uncorrelated sensor and bath.

* **Quantum bath:** $E$ is a spin with $\rho_E=I/2$, $H_0=(\omega/2)X$ and $H_1=(\omega/2)Z$.
* **Static classical bath:** a retained frequency is $0$ with probability $1/2$ and $\pm\omega$ with probability $1/4$ each. A joint embedding has $H_0=0$, $H_1=\operatorname{diag}(-\omega,0,\omega)$ and bath probabilities $(1/4,1/2,1/4)$.

For every duration $t$, both give the same complete reduced Ramsey channel: populations are fixed and sensor coherence is multiplied by

$$
L_{\rm FID}(t)=\cos^2(\omega t/2)=\frac{1+\cos\omega t}{2}.
\tag{6}
$$

For the quantum model this follows by tracing $e^{-i\omega tX/2}e^{i\omega tZ/2}/2$; for the classical model it is the frequency characteristic function. Thus even exact one-time Ramsey tomography at all durations does not distinguish them. This does not assert equality of their multitime processes or conditioned record laws.

Every static classical phase is refocused by echo. For the quantum model, multiplication of the two Pauli rotations in (2) gives

$$
L_{\rm echo}(\tau)=1-2\sin^4(\omega\tau/2).
\tag{7}
$$

At $\omega\tau=\pi$ the two ideal $X$ outcomes are opposite. A more direct storage decision uses $\omega\tau=2\pi/3$, with total storage time $T=2\tau$. No pulse gives coherence $1/4$ in both models. The classical calibration predicts echo coherence $1$, whereas the quantum bath gives $-1/8$. Even after the best known $Z$ phase correction, echo preserves magnitude $1/8$, below the no-pulse $1/4$. Their identity-memory entanglement fidelities after that correction are respectively $9/16$ and $5/8$. The preferred choice between these two schedules is reversed. This is a prediction of storage error, not an optimization over all DD schedules or a native-device parameter claim.

The decision rejects the specified static-noise model. It does not distinguish quantum mechanics from every classical nonstationary or control-responsive source. Its useful diagnostic is already ordinary echo by (2).

### A commutator signal alone does not certify bath backaction

There is a passive classical temporal-noise counterexample. Let a classical bath bit flip after each native interval and choose the joint embedding

$$
A=X_Ee^{-i\alpha Z_E},\qquad B=X_Ee^{i\alpha Z_E},
\qquad\rho_E=I/2.
\tag{8}
$$

Both sensor branches induce the same bath-population permutation. Starting from a diagonal bath state, any sensor-only intervention preserves a classical–quantum state $\sum_\lambda p_\lambda\rho_S(\lambda)\otimes|\lambda\rangle\langle\lambda|$. After averaging intervention outcomes, trace preservation leaves the bath population law independent of sensor settings. This is an exogenous alternating random phase, even though

$$
(AB)^\dagger BA=e^{-4i\alpha Z_E},\qquad L=\cos4\alpha.
\tag{9}
$$

At $\alpha=\pi/8$, echo visibility vanishes. Hence noncommuting conditional operators and echo loss alone do not rule out passive classical temporal noise. Selective records add another caution: a changed future conditioned on a past outcome can be ordinary Bayesian updating about a passive source. An outcome-averaged dependence on an independently chosen intervention context is a stronger response test.

### Ordinary pump/reset/read and recorded-context tests

Prepare the sensor in $a=0$ or $1$ for a pump window, so the bath becomes $A_a\rho_EA_a^\dagger$, where $A_0=A,A_1=B$. Reset and prepare $S$ in $|+\rangle$, then use a read window with conditional bath unitaries $D_0,D_1$. Its Ramsey coherence is

$$
L_a=\operatorname{Tr}\!\left[\rho_E A_a^\dagger D_1^\dagger D_0 A_a\right].
\tag{10}
$$

This follows by propagating the sensor off-diagonal block through the read window. Comparing $L_0,L_1$ uses two ordinary windows, reset and $X/Y$ readout. A passive source whose trajectory law and initialization are unaffected by the pump setting predicts equality. A difference rejects that model, while allowing control leakage or a classical source with active backaction as alternatives. The test can be null for a quantum bath, for example $\rho_E=I/d$.

For native pump branches $e^{-iz\epsilon G}$ and read overlap $e^{-i\delta F}$ with bounded generators, expansion of (10) gives

$$
L_+-L_-=2\epsilon\delta\operatorname{Tr}[\rho_E[G,F]]
 +O(\epsilon\delta^2+\epsilon^3\delta).
\tag{11}
$$

This is a commutator expectation, not its squared norm. It presupposes the specified couplings and does not grant general bath kicks or inverses.

A recorded three-window test also works in an explicit maximally mixed example. First prepare $|+\rangle$, run $V$ and measure $X$, giving $m$. Independently select $j=0$ or $1$, prepare that sensor state, run $V$ and reset. Finally prepare $|+\rangle$, run $V$ and measure $X$, giving $n$. Retain both records; never reset the bath. Define

$$
K_m=(A+mB)/2,\quad
M=(A^\dagger B+B^\dagger A)/2,\quad
\mathcal S(\rho)=(A\rho B^\dagger+B\rho A^\dagger)/2.
$$

Since $\sum_m mK_m\rho K_m^\dagger=\mathcal S(\rho)$ and the final measurement's signed effect is $M$, the exact correlation is

$$
C_j=\mathbb E[mn\mid j]
   =\operatorname{Tr}[M A_j\mathcal S(\rho_E)A_j^\dagger].
\tag{12}
$$

For a passive classical trajectory law independent of the middle pointer setting, $C_0=C_1$, even after the first record updates a classical posterior. The setting must be selected independently of $m$; its effect is tested after averaging the records, not selecting favorable outcomes.

Take $A=H$, $B=ZH$, $\rho_E=I/2$, with $H$ the Hadamard. Then $K_m=P_m^ZH$, $M=X$ and $\mathcal S(\rho_E)=Z/2$. The two middle preparations give $A\mathcal S(\rho_E)A^\dagger=X/2$ and $B\mathcal S(\rho_E)B^\dagger=-X/2$, so

$$
C_0=+1,\qquad C_1=-1.
\tag{13}
$$

This ordinary protocol detects intervention-dependent bath response and creates conditional bath states. It costs three native windows and their actual preparation, reset and readout per trial. Bounded $mn$ records allow additive-error estimation with $O(\epsilon^{-2}\log(1/\delta))$ independent trials per setting. Repeated-probe context tests are an established mechanism: [Fink and Bluhm](https://arxiv.org/abs/1402.0235) propose them, and [Bethke et al.](https://arxiv.org/abs/1906.11264) demonstrate a correlation-based backaction experiment in a GaAs nuclear bath. [Meinel et al.](https://www.nature.com/articles/s41467-022-32610-8) experimentally extract higher-order nuclear-spin correlations with sequential weak NV measurements. Equations (10)–(13) supply explicit elementary comparators, not priority claims for those mechanisms.

### First-echo data do not determine a held-out uninterrupted history

Let $\rho_E=I/2$, $A=e^{-iaZ}$ and $B=e^{-ibX}$, and write $t=\sin^2a\sin^2b$, $v=\cos^2a\cos^2b$. Pauli multiplication gives

$$
\begin{aligned}
K_+&=\cos a\cos b\,I
 -i(\cos a\sin b\,X+\sin a\cos b\,Z),\\
K_-&=i\sin a\sin b\,Y.
\end{aligned}
\tag{14}
$$

Consequently $K_-^\dagger K_-=tI$, $K_+^\dagger K_+=(1-t)I$. The first $X$-echo has $L_1=1-2t$ and unnormalized flagged bath states $tI/2$, $(1-t)I/2$. Both conditional bath states are $I/2$ whenever their probabilities are nonzero.

Two **uninterrupted** complete echo cycles instead have paths $(BA)^2$ and $(AB)^2$. To compute their overlap, write $BA=hI-i(\mathbf u+\mathbf w)\cdot\boldsymbol\sigma$ and $AB=hI-i(\mathbf u-\mathbf w)\cdot\boldsymbol\sigma$, where $h=\cos a\cos b$, $\mathbf u=(\cos a\sin b,0,\sin a\cos b)$ and $\mathbf w=(0,-\sin a\sin b,0)$. Squaring multiplies each vector part by $2h$. The scalar parts agree and the vector difference has squared norm $16h^2\|\mathbf w\|^2$. For unit quaternions the half-trace overlap is one minus half this squared difference, giving

$$
L_2=\frac12\operatorname{Tr}[((AB)^2)^\dagger(BA)^2]
   =1-8tv,\qquad F_e=\frac{1+L_2}{2}=1-4tv.
\tag{15}
$$

Models $(\sin^2a,\sin^2b)=(1/2,1/2)$ and $(1,1/4)$ have identical first-$X$-echo flagged bath states, but two-cycle memory fidelities $3/4$ and $1$. An entirely Gaussian-rational instance uses

$$
\begin{array}{c|cc|cc}
 &\cos a&\sin a&\cos b&\sin b\\\hline
1&15/17&8/17&56/65&33/65\\
2&0&1&1073/1105&264/1105
\end{array}
$$

Both have $p_-=69696/1221025$; their held-out fidelity gap is $7868399616/59636082025>0.13$, with model 2 perfect. The check compares the complete first-$X$-echo flagged bath density matrices for this specified high-temperature input. It does **not** assert equal instruments on every bath input, equal phase-resolved data, or indistinguishability against all ordinary experiments. Measuring/resetting between the two cycles changes the history and is not a test of the uninterrupted task.

### Direct calibration and measurement-record prediction

For a specified pure-dephasing control word $y$, restore its known sensor frame and write its actual joint evolution as $\operatorname{diag}(U_{y,0},U_{y,1})$. Ordinary preparation in $|+\rangle$ and $X/Y$ readout measure

$$
L_y=\operatorname{Tr}[\rho_EU_{y,1}^\dagger U_{y,0}],
\qquad F_e(\text{identity memory})=\frac{1+\operatorname{Re}L_y}{2}.
\tag{16}
$$

The $X$-plus outcome is itself a Bernoulli sample with mean $F_e$. With independent repeatable initial bath/history preparations, $n\ge\log(2/\delta)/(2\epsilon^2)$ trials estimate it within $\epsilon$ with failure probability at most $\delta$. A known target **unitary** can instead be tested by a clean calibration Bell pair and the corrected Bell projector; that reference is held during the sequence and measured afterwards. This does not grant access to the arbitrary passive $R$ in (3). A finite list of $M$ schedules needs at most $O(M\epsilon^{-2}\log(M/\delta))$ direct trials by a union bound. Each trial pays for the actual schedule, pulses, duration and history preparation.

This comparator avoids full bath tomography. It is not an optimal sample bound. A held-out history that cannot be run or reproduced is a distinct prediction task whose restriction must be stated. Reproducing a history of probability $p_h$ can add a factor of order $1/p_h$ in attempts. Uncontrolled persistent drift invalidates an i.i.d. error bar. A switch diagnostic consumes and changes the same bath and must establish its own transfer to the target history.

Recorded interventions also have an exact, potentially expensive baseline. An ignored projective $X$ measurement is $\mathcal D_X=(\mathrm{id}+\operatorname{Ad}_X)/2$, including on an entangled sensor/bath state. Therefore

$$
\operatorname{Ad}_X=2\mathcal D_X-\mathrm{id}.
\tag{17}
$$

Expanding (17) at $m$ pulse cuts writes any DD observable as a signed sum over the $2^m$ experiments that measure-and-ignore $X$ at a chosen subset of cuts and leave other cuts untouched. Linearity proves the equality for arbitrary joint dynamics between cuts. The coefficients have total absolute weight $3^m$, so naive signed importance sampling of bounded outcomes can have variance up to $9^m$. This is a constructive upper bound, not a lower bound on all reconstruction methods. Related DD/measurement relations are prior work of [Sakuldee and Cywiński](https://arxiv.org/abs/1907.05165).

One fixed all-cuts record does not implement all these experiments merely by forgetting outcomes: summing an outcome leaves $\mathcal D_X$, whereas omitting the physical measurement requires $\mathrm{id}$. An informationally complete collection of measure/prepare interventions can reconstruct the corresponding finite process and predict in-span controls, but its settings, variance and storage must be counted.

### Known nonunitary interventions have a full ordinary simulation

Let $G_{SE}$ be an arbitrary unknown shared-bath evolution at one fixed clock window. Let $\mathcal A,\mathcal B$ be known sensor-only CPTP interventions, tensor identity on $E$, with known unitary Stinespring extensions $U_A$ on $S,a$ and $U_B$ on $S,b$. The clean buffers $a,b$ are distinct, start in their prescribed states, and remain coherent until the experiment ends. For unread $Z$ measurement choose $U_A=\mathrm{CNOT}(S\!\to a)$ with $a=0$; for preparation of $|+\rangle$ choose $U_B=\mathrm{SWAP}(S,b)$ with $b=+$.

Define known controlled operations

$$
V_{\rm pre}=|0\rangle\langle0|_C\otimes U_A+|1\rangle\langle1|_C\otimes U_B,
\quad
V_{\rm post}=|0\rangle\langle0|_C\otimes U_B+|1\rangle\langle1|_C\otimes U_A.
$$

Then

$$
V_{\rm post}(I_C\otimes G)V_{\rm pre}
 =\operatorname{diag}(U_BGU_A,U_AGU_B).
\tag{18}
$$

This ordinary chronological circuit uses $G$ once and exactly reproduces the entire coherent intervention-order output on $C,S,E,a,b,R$, including all later readouts and rejections. The proof is block multiplication and holds for arbitrary $G$, without learning its matrix, reversing it or resetting the bath. A CPTP $G$ follows by including its dilation environment, or by applying the identity to each of its Kraus operators.

The physical ledger is one shared-bath interval, one order memory, two coherent record buffers and four candidate controlled local intervention gates across the early/late placements; each coherent history contains two occupied interventions. A native realization of that same process needs the same placements. Counting only abstract occupied calls while denying ordinary access to its actual known coherent gates compares different hardware. Conversely, an irreversible unknown black-box intervention does not automatically supply its controlled Stinespring unitary. Equation (18) does not simulate a coherent permutation of two unrelated unknown joint bath interactions.

An ignored optical outcome need not be a coherent record. If the two histories emit distinguishable timing states $|T_0\rangle,|T_1\rangle$, tracing them multiplies the order off-diagonal block by $\langle T_1|T_0\rangle$. Orthogonal tags yield exactly a classical random order; outcome-dependent tags require their full overlap matrix. Delayed module-labelled readout can retain interference, but its quantum buffer, erasure and losses are resources. Intermediate detector logs and accessible records belong to both strategies. Unknown intervention-induced bath kicks likewise require a complete joint model; the reduced sensor CPTP maps do not specify the coherent temporal experiment.

### Exchange backaction: identical isolated channels, opposite good schedules

The following finite model includes energy exchange with an inaccessible two-level defect, rather than a sensor-controlled pure-dephasing bath. It isolates a scheduling decision and its strongest full-output discrimination baseline. It is not a fitted processor model or a model of irreversible leakage reset.

Let $S,E$ be qubits, use the joint basis $|s,e\rangle$, and let $A,B_+,B_-$ act as identity on $|00\rangle,|11\rangle$. On the one-excitation subspace, **ordered as** $(|10\rangle,|01\rangle)$, define

$$
A=\frac{2I-iX-2iZ}{3},\qquad
B_\pm=\frac{2I\mp iY-2iZ}{3}.
\tag{19}
$$

The two hypotheses are the signs in $B_\pm$, fixed across a trial. Since $\|(1,0,2)\|=\|(0,\pm1,2)\|=\sqrt5$, these blocks are unitary rotations with $\cos\theta=2/3$. For example, with $J>0$, interaction time $\tau=\arccos(2/3)/(\sqrt5J)$ and $\hbar=1$, the full Hamiltonians are

$$
\begin{aligned}
H_A&=\frac J2(X_SX_E+Y_SY_E)+J(Z_E-Z_S),\\
H_{B_\pm}&=\pm\frac J2(X_SY_E-Y_SX_E)+J(Z_E-Z_S).
\end{aligned}
\tag{20}
$$

They vanish on the zero- and two-excitation sectors and restrict to $J(X+2Z)$ and $J(\pm Y+2Z)$ on the stated subspace. The bath persists coherently through both windows. No bath inverse, readout, reset between windows, or access to its purification is supplied. This two-qubit model has no leakage level, emitted reset field, fitted relaxation/dephasing rates or demonstrated coherent routing interface; its reduced sensor channels are nonunitary because the defect is traced out.

For the calibration and discrimination statements, initialize $E=|0\rangle$. Tracing it after **any one** of $A,B_+,B_-$ gives the identical complete sensor channel

$$
\mathcal E(\rho)=K_0\rho K_0^\dagger+K_1\rho K_1^\dagger,
\qquad K_0=\operatorname{diag}\!\left(1,\frac{2-2i}{3}\right),
\quad K_1=\frac13|0\rangle\langle1|.
\tag{21}
$$

Only the irrelevant phase of $K_1$ differs among the three dilations. Thus even exact isolated-channel tomography, including entangled sensor probes, does not identify the sign. Equation (21) does not determine their joint two-window process.

Pauli multiplication in the one-excitation subspace gives

$$
\begin{array}{c|cc}
&AB_\pm&B_\pm A\\\hline
+&-iZ&-i(4X+4Y+7Z)/9\\
-&-i(4X-4Y+7Z)/9&-iZ.
\end{array}
\tag{22}
$$

Apply the same known final sensor phase $Q=\operatorname{diag}(1,i)$ in both hypotheses. In the good named order,

$$
(Q\otimes I_E)AB_+=I_S\otimes Q_E,
\qquad (Q\otimes I_E)B_-A=I_S\otimes Q_E.
\tag{23}
$$

This is a full joint identity: the good corrected schedule preserves every sensor/reference state even for an arbitrary initial correlated bath, while applying only $Q_E$ to the bath. With a cold bath, the opposite order instead induces ordinary amplitude damping $\mathcal D_a$ with

$$
a=\frac79,\quad
D_a=\operatorname{diag}(1,a),\quad
\mathcal D_a(\rho)=D_a\rho D_a+(1-a^2)J_0\rho J_0^\dagger,
\quad J_0=|0\rangle\langle1|.
\tag{24}
$$

Its identity-memory entanglement fidelity is $(1+a)^2/4=64/81$, versus $1$ for the good schedule; excited-state survival is $49/81$ versus $1$. The preferred named order reverses between hypotheses despite identical isolated calibrations. This is an elementary joint-memory counterexample, not a lower bound against direct sequence calibration.

The unknown relative exchange phase is a substantive premise. In fact
$B_-=(Q\otimes I)A(Q^\dagger\otimes I)$ and
$B_+=(Q^\dagger\otimes I)A(Q\otimes I)$: the conjugation orientation depends on the hidden sign, so there is no single fixed known sandwich that realizes the actual $B$ uniformly over this promise. If the hardware defines $B$ solely by a **known** sensor phase conjugation of $A$, its relative phase is known and the claimed unknown family is not supplied. Two physical coupling paths or control settings must justify what remains unknown. The algebra alone does not establish an inexpensive coherent selector between them.

### Order-only data miss the phase; full output matches an ordinary test

Consider the actual joint controlled histories
$W_\pm=|0\rangle\langle0|_C\otimes B_\pm A+|1\rangle\langle1|_C\otimes AB_\pm$,
with $C=+$ initially. This is coherent order of two interactions with the **same** bath, not a switch of two independent copies of (21). The effect controlling the off-diagonal $C$ block is identical in both models:

$$
\langle0_E|(AB_\pm)^\dagger B_\pm A|0_E\rangle
 =\operatorname{diag}(1,7/9).
\tag{25}
$$

Consequently every reduced $C$ state is identical between hypotheses. The same is true for $C$ together with any passive reference after tracing out $S,E$, since the effect (25) is the same operator on $S$. For a maximally mixed sensor the $X$ fringe is $8/9$ and $p_-=1/18$ in both. Phase-resolved order readout alone cannot select the good named schedule.

Keeping the sensor changes this conclusion, but gives no discrimination advantage. Let $\Phi_\pm$ denote the complete corrected channel from arbitrary input $C,S$ to output $C,S$, with $E=0$ and the known $Q$ applied after the histories. It has equivalent Kraus operators

$$
\begin{array}{c|cc}
&K_{0,\pm}&K_{1,\pm}\\\hline
+&\operatorname{diag}_C(D_a,I)&\sqrt\gamma\,P_0^C\otimes J_0\\
-&\operatorname{diag}_C(I,D_a)&\sqrt\gamma\,P_1^C\otimes J_0,
\end{array}
\qquad \gamma=1-a^2=\frac{32}{81}.
\tag{26}
$$

The phases of the two displayed jump Kraus operators are separately immaterial. This description permits arbitrary initial control encoding and entanglement with a reference; it is stronger than a fixed-$+$ input comparison.

Write $t=1-a=2/9$, $b=(1+a)/2=8/9$, $D=\operatorname{diag}(1,b)$, $P=|1\rangle\langle1|$ and $Z_C=P_0^C-P_1^C$. The full channel difference has the exact factorization

$$
\begin{aligned}
\Delta&:=\Phi_+-\Phi_-=T_Z+T_Z^\sharp,\\
T_Z(\rho)&=tb(I_C\otimes J_0)\rho(Z_C\otimes J_0)^\dagger
       -t(I_C\otimes D)\rho(Z_C\otimes P)^\dagger,\\
T_Z^\sharp(\rho)&=[T_Z(\rho^\dagger)]^\dagger.
\end{aligned}
\tag{27}
$$

Indeed, the two no-jump Kraus operators have average $I_C\otimes D$ and difference $-tZ_C\otimes P$. Their outer-product difference gives the two terms proportional to $-t$ in (27). The jump difference is
$\gamma[(I\otimes J_0)\rho(Z_C\otimes J_0)^\dagger+(Z_C\otimes J_0)\rho(I\otimes J_0)^\dagger]/2$;
this is the remaining part because $\gamma=2bt$.

For completeness, an elementary completely bounded trace-norm inequality is

$$
\left\|\sum_i L_i(\cdot)R_i^\dagger\right\|_\diamond
\le\left\|\sum_iL_i^\dagger L_i\right\|^{1/2}
    \left\|\sum_iR_i^\dagger R_i\right\|^{1/2}.
\tag{28}
$$

To prove it, use trace-norm duality at any reference dimension. The adjoint elementary map sends a norm-one test operator $Y$ to $\sum_iR_i^\dagger YL_i$. Write this as a block row of $R_i^\dagger$, a block diagonal array of $Y$, and a block column of $L_i$. Their operator norms multiply to the right side of (28), unchanged by an identity reference. Taking the supremum proves the inequality.

In (27) take
$L_1=I\otimes bJ_0$, $R_1=Z_C\otimes tJ_0$,
$L_2=I\otimes D$, $R_2=-Z_C\otimes tP$. Then

$$
\sum_iL_i^\dagger L_i=I_C\otimes\operatorname{diag}(1,2b^2),
\qquad
\sum_iR_i^\dagger R_i=I_C\otimes2t^2P.
\tag{29}
$$

Since $2b^2=128/81>1$, (28) gives $\|T_Z\|_\diamond\le2bt=\gamma$. Exchanging $L_i,R_i$ gives the same bound for $T_Z^\sharp$, hence $\|\Delta\|_\diamond\le2\gamma$. Sensor input $|1\rangle$, even with fixed control $+$, attains it: the difference of output diagonal probabilities has total variation $\gamma$. Therefore

$$
\frac12\|\Phi_+-\Phi_-\|_\diamond=\frac{32}{81}.
\tag{30}
$$

Now run just the fixed ordinary word $AB$ and the same $Q$. Its two hypothesis channels are $\mathrm{id}$ and $\mathcal D_a$. Dropping $C,Z_C$ from (27) gives a factorization of $\mathcal D_a-\mathrm{id}$, up to sign, with the same two norm factors (29). Thus its half-diamond distance is at most $\gamma$, attained by $|1\rangle$ followed by an ordinary survival measurement. It equals (30). Both have equal-prior optimal one-trial success probability $(1+\gamma)/2=113/162$, including all accessible full-output measurements and arbitrary reference-entangled input encodings for the specified channels. No optimization over all adaptive ordinary two-interaction protocols is needed for this exclusion: one allowed serial strategy already matches the optimal discrimination score of the complete controlled-order channel.

An entangled calibration Bell input is suboptimal here. Let $J(\Phi)$ denote a **normalized** Choi state. For the full input $C,S$, its two no-jump vectors have squared norm $n=292/81$ and mutual inner product $m=32/9$ before division by input dimension $4$. The jump vectors have squared norm $\gamma$, lie in orthogonal sectors, and are orthogonal to the no-jump vectors. The rank-two no-jump difference has trace norm $2\sqrt{n^2-m^2}$ and $n^2-m^2=16\cdot145/81^2$. Thus

$$
\frac12\|J(\Phi_+)-J(\Phi_-)\|_1
 =\frac{\gamma+\sqrt{n^2-m^2}}4
 =\frac{8+\sqrt{145}}{81}<\frac{32}{81}.
\tag{31}
$$

For fixed input $C=+$ and a Bell sensor/reference probe, stacking the two history Kraus blocks gives the same Gram data and overall factor $1/4$, hence the same distance. The ordinary $\mathrm{id}$ versus $\mathcal D_a$ Choi difference also has this value: its no-jump vectors have squared norms $2,1+a^2$ and inner product $1+a$, so the rank-two trace norm is $\sqrt{(3+a^2)^2-4(1+a)^2}$ before division by $2$, with an additional jump eigenvalue $\gamma/2$. These Choi values are not diamond distances; (30) already optimizes reference-assisted discrimination.

Conditional control readout can reveal differences that disappear on tracing the sensor, but conditioning does not improve the all-launch binary decision beyond (30). Its success probabilities, rejected outcomes and output state are already included in the full channel. This conclusion concerns the specified two-model decision; it neither proves equality of the two processes nor simulates every controlled-order channel by a serial one.

### Native coherent settings, records and the physical ledger

The preceding order-controlled channel needs a microscopic implementation. A separate exact baseline applies when native hardware actually supplies a coherent setting selector. Let $D_{A,r},D_{B,r}$ be its unknown joint dilations at window $r=1,2$, including sensor, leakage levels, persistent bath, apparatus and emitted reservoir modes. Let $G$ be their actual intervening joint evolution. If the hardware supplies

$$
M_r=P_0^C\otimes D_{A,r}+P_1^C\otimes D_{B,r},
$$

and helper flips that do not disturb those systems, direct multiplication gives the ordinary chronological identity

$$
X_C M_2 X_C(I_C\otimes G)M_1
 =\operatorname{diag}_C(D_{B,2}GD_{A,1},D_{A,2}GD_{B,1}).
\tag{32}
$$

No matrix description, inverse, bath reset, independence or sensor-only assumption is used. Equation (32) holds on every input/reference and retains the complete apparatus records, conditional bath output, future adaptive utility and rejections. Applying it at each cycle also retains persistent histories. It is a fixed-clock use of the **supplied selector**, not a construction of that selector from classically selectable unknown channels. A classical microwave waveform does not supply $M_r$; a reduced Lindblad generator for each setting does not determine its off-diagonal action. Conversely, when an experiment already provides $M_r$, its ordinary comparator receives that same native resource. A spatial carrier router requires its own matched analysis; (32) does not replace it by cheap local pulses.

The costs for the exchange example and its diagnostics are explicit:

| Resource | Ordinary serial survival test | Coherent-order experiment |
|---|---|---|
| Joint interactions | Two occupied windows, each of duration $\tau$ in (20) | Two occupied windows of the same joint model |
| Preparation | Sensor $|1\rangle$ and the stipulated cold bath/history | Sensor probe, same bath/history, plus coherent helper |
| Final operation | Known $Q$ and sensor survival readout; $Q$ is unnecessary for populations | Same $Q$; joint helper/sensor readout if the full output is used |
| Coherent control | No superposition of settings | Realize and retain a selector/router across both windows; (32) applies when it is natively supplied |
| Persistent memory | Bath retained between interactions | Same bath retained, with no unpriced reset or fresh-environment substitution |
| Repeated trials | Reproduce the stated cold bath/history and pay reset/cooling/delay costs | The same preparation cost, plus helper preparation, coherence and readout |

Equation (20) leaves no unmodelled idle interval. A nonzero physical delay inserts its actual $G$ and changes (22) unless refocusing or compensation is justified. $J$ sets a time scale, not a measured device rate. Real defect dephasing, control noise, helper memory volume, pulse duration and measurement backaction must be added to the actual dilation before claiming the numerical fidelities. Cold-bath preparation is an experimental premise, not a consequence of sensor reset; successive trials through a persistent bath need not be independent.

In a simple record model where the histories leave normalized payload-independent tags $|T_0\rangle,|T_1\rangle$, order coherence is multiplied by $\zeta=\langle T_1|T_0\rangle$. For coherent output fields $\beta_0(t),\beta_1(t)$ in photon-normalized units,

$$
|\zeta|=e^{-\|\beta_0-\beta_1\|_2^2/2}.
\tag{33}
$$

For disjoint early/late windows carrying $\beta_A,\beta_B$ in opposite orders, the squared difference is $2\|\beta_A-\beta_B\|_2^2$. A perfectly resolved photon in nonoverlapping time modes can instead give orthogonal tags and no interference. These follow from the record inner product; they are not universal reset models. Input-dependent emissions require their full overlap kernel. Forgetting a detector timestamp does not erase the environmental record. A claimed eraser must specify the accessible quantum record, storage time, operation, failure and residual inaccessible information. If both strategies use the same imperfect selector, (32) reproduces its actual record physics rather than recovering an ideal switch.

There are substantial ordinary native comparators. [Zhuang et al.](https://arxiv.org/abs/2503.16381) experimentally use two-timescale fluxonium relaxometry, with repeated preparation followed by short relaxation probes, to study slowly relaxing defect environments; their treatment includes preparation/readout effects. This motivates history-aware calibration, not the coherent two-window model (20). [Xin et al.](https://arxiv.org/html/2511.17460v1) demonstrate leakage reduction concurrent with transmon measurement and logical-memory/stability improvement without postselection. Their driven resonator and measured output cannot be assumed to provide coherent setting records. Ordinary multitime characterization and control are also established, for example [White et al.](https://doi.org/10.1038/s41467-020-20113-3). These works are physical motivation and baseline mechanisms; equations (19)–(33) are the elementary deductions here, with no priority or implementation claim.

### Scope of the obstruction and a falsifiable next target

The native central-spin commutator candidate supplies no advantage over the ordinary full instrument (2)–(4). The known-intervention construction is closed by (18). Equations (6)–(7) show useful control-dependent model failure, while (8)–(17) delimit what partial statistics certify and provide stronger ordinary tests. The excitation-exchange models (19)–(24) extend the calibration failure beyond pure dephasing, but their full-output decision is already matched by an ordinary serial test, (30). The chronological selector identity (32) is a separate, explicitly conditional native-interface baseline.

A remaining positive target must specify an unknown joint intervention family and an implementable coherent temporal interface, then identify a storage, gate or calibration decision that ordinary echo, phase cycling, pump/reset/read, retained records, entangled probes and direct target-sequence calibration cannot match at the same cost. A concrete falsifiable benchmark is lower prediction error or lower all-attempt cost for a stated held-out control family, with bath initialization/drift, inaccessible histories, coherent buffers, readout inefficiency and rejections charged. A nonzero commutator signal or a favorable conditional bath state alone does not establish that benchmark.

The [exact checker](checks/architecture/verify_backaction.py) replays finite reference-inclusive $X/Y$ echo instruments, the rational held-out counterexample, the maximal ordinary record contrast, polynomial identities for the calibration/storage example, and all input matrix units for the exchange-channel factorization with its Choi Gram data. The all-dimension operator, norm and linearity arguments are the proofs above; the finite cases are not a general formalization, a hardware demonstration, a sample-optimality theorem, or a no-go for every shared-bath application.

<a id="nr-r19"></a>
## NR-R19 — Unknown odd couplers: exact correction and expected-query fidelity limits

This is a separate unknown-gate benchmark, rather than a strengthening of the shared-bath claims in NR-R14. Two commuting Hermitian couplers admit exact correction of unknown static station phases with two queries and a surviving order helper. For data dimension $d\ge3$, the full ordinary circuit model specified below cannot implement the same unknown target exactly with a hard cap of two named queries. A separately certified qutrit prior gives a quantitative ordinary fidelity bound even for arbitrary variable-length receivers with expected cost two. An ordinary three-query construction is exact. Known couplers, restricted qubit links and supplied coherent selectors have stronger ordinary baselines. A native device advantage remains unestablished.

### Coupler family and the complete corrected output

Let $C$ be a two-level physical address, $D$ a $d$-dimensional data register, $U\in U(d)$ unknown, and $H=H^\dagger=H^{-1}$ an unknown involution. In the address basis define

$$
A=\begin{pmatrix}0&U^\dagger\\ U&0\end{pmatrix},\qquad
B=\begin{pmatrix}0&HU^\dagger\\ UH&0\end{pmatrix},\qquad
W=AB=BA=\operatorname{diag}(H,UHU^\dagger).
\tag{34}
$$

Both couplers square to $I$ and anticommute with the known $Z_C$. A station supplies $A_\alpha=e^{i\alpha Z_C}A$ or $B_\beta=e^{i\beta Z_C}B$, with unknown phases static throughout one job. These are again Hermitian involutions. With $\delta=\beta-\alpha$, the two temporal products are

$$
P_0=B_\beta A_\alpha=e^{i\delta Z_C}W,\qquad
P_1=A_\alpha B_\beta=e^{-i\delta Z_C}W.
\tag{35}
$$

Prepare an independent order helper $O$ in $+$, realize $\operatorname{diag}_O(P_0,P_1)$, and measure $O$ in $X$. The two target Kraus operators are

$$
K_+=\cos\delta\,W,\qquad K_-=i\sin\delta\,Z_CW.
\tag{36}
$$

Apply the known $Z_C$ after the minus outcome. The two corrected Kraus operators are scalar multiples of $W$ whose squared moduli sum to one. Thus the **all-outcome, surviving-output** channel is exactly $\operatorname{Ad}_W$, on every input including arbitrary references. No phase estimation or accepted-outcome normalization is used. Equivalently, apply a Hadamard to $O$ and then controlled-$Z_C$: the output factors as $W|\psi\rangle\otimes(\cos\delta|0\rangle+i\sin\delta|1\rangle)$. This endpoint needs an independent surviving helper or a coherent equivalent. Destructive detection of the payload's path does not implement it. The target is an unknown gate; interpreting it as a measurement of $H$ or a holonomy expectation requires a further specified interferometric interface.

For the isolated model of input-independent order dephasing with visibility $0\le\nu\le1$, the same correction gives

$$
\left[\frac{1+\nu}{2}\,\mathrm{id}
      +\frac{1-\nu}{2}\operatorname{Ad}_{Z_C}\right]
\circ\operatorname{Ad}_W.
\tag{37}
$$

Its target entanglement fidelity is $(1+\nu)/2$ and its half-diamond error is $(1-\nu)/2$. To verify (37), decompose the helper state as $\nu|+\rangle\langle+|+(1-\nu)I/2$; the latter component gives the equal mixture of corrected address phases and completely dephases $C$. This formula does not model input-dependent emissions or correlated payload errors. If phases instead vary between early and late windows, the two histories have $\theta_0=\beta_2-\alpha_1$ and $\theta_1=\alpha_2-\beta_1$. Factoring their mean shows that the same correction leaves $e^{imZ_C}W$, where $m=(\theta_0+\theta_1)/2=[(\alpha_2-\alpha_1)+(\beta_2-\beta_1)]/2$. Static cancellation therefore does not establish cancellation of temporal drift.

### Ordinary controls, repeated queries and calibration

Several ordinary closures are essential to the scope of the task.

* If the useful address is classical, (35) differs from $W$ only by a sectorwise global phase. The task must preserve coherence between the two address sectors.
* An executable address-selective reflection $M=\operatorname{diag}(H,I)$ gives an ordinary two-query wrapper even when its matrix is unknown; see (NC1) and the [native-interface comparison](#nr-r19-native-interface). Its actual controls and primitive costs belong to both strategies.
* Even unknown $H$ does not save a natural Abelian qubit family. Let $U=e^{i\varphi Z}$ with unknown $\varphi$ and let unknown $H$ anticommute with the known $Z$. Hold the useful logical address in ordinary memory. A fixed physical input address $1$ at $A$ supplies $P=U^\dagger$, and input address $0$ at $B$ supplies $Q=UH$, each up to a harmless global station phase. For known logical-controlled $X$, $C_X$, use $Q$ first, then $C_X$, then $P$, then $C_X$. Since $XPX=U$ and $HU^\dagger=UH$,
  $$C_X(I\otimes P)C_X(I\otimes Q)
      =\operatorname{diag}(PQ,UQ)=W.\tag{38}$$
  This preserves all logical address/data/reference coherences with two ordinary queries and no knowledge of $H$ or $\varphi$.
* If a native coherent setting selector is supplied, the same selector is available to the ordinary comparator. Equation (32), with the actual records and delays, then gives the two-window controlled products. Classical query-name choice alone does not supply that selector.

There is a general exact **three-query ordinary upper bound** with static station unitaries, arbitrary known controlled swaps and one full-size dummy register. Query $A$ in the first and third slots and $B$ in the middle slot. On helper branch $0$, route the payload through the first $A$ and $B$, and the dummy through the last $A$; on branch $1$, route the dummy through the first $A$, and the payload through $B$ and the last $A$. The output is $\operatorname{diag}_O(B_\beta A_\alpha,A_\alpha B_\beta)$ on the payload, while the dummy is the identical state $A_\alpha|\eta\rangle$ on both branches. It decouples without a record of the branch. Applying (36) gives $W$ deterministically. The dummy, known routing and storage have costs; this is a query upper bound. It assumes identical repeated $A$ operations, with no additional timing record or changed environment. Giving new independent noise only to ordinary repeated visits changes the comparison.

Direct ordinary calibration also limits interpretation. A raw serial pair has target entanglement fidelity $\cos^2\delta$ and half-diamond error $|\sin\delta|$; the uniform-phase fidelity $1/2$ is **not** an optimal-ordinary bound. Because $W^2=I$, two serial pairs give $P_0^2=e^{i2\delta Z_C}I$, costing four station visits. Ramsey readout of this gate learns $\delta$ only modulo $\pi/2$. The ambiguity is real for a balanced involution: choose $RHR^\dagger=-H$, set $U'=UR$ and $\delta'=\delta+\pi/2$. Then $W'=Z_CW$ but $P_0'=iP_0$, so whole-pair channels cannot distinguish two orthogonal target Choi states. Any whole-pair-only common output has average target fidelity at most $1/2$. This is not a bound for separated access to $A$ and $B$. A prior branch interval of width less than $\pi/2$ removes this ambiguity; precision-dependent calibration costs and stability then permit an amortized ordinary approximate production strategy. It is not exact finite-query phase learning.

### Full ordinary hard-two obstruction for $d\ge3$

**Statement and interface.** Allow arbitrary finite clean memory, known joint data/controller operations, reference entanglement, coherent routing of each fixed-name query through program or data registers, adaptive instruments, and classical choices of query name. Advice must be independent of $U,H,\alpha,\beta$; learning them is charged. The oracle space is precisely $\mathbb C^2\otimes\mathbb C^d$. A free coherent selector between names or an additional known coherent vacuum extension is a different interface. In this model, for $d\ge3$, no deterministic ordinary protocol with **at most two total named queries** implements $\operatorname{Ad}_W$ for every $U,H,\alpha,\beta$. Together with the construction above, the minimum hard query cap for exact implementation is three. The proof below concerns exact implementation, not a numerical approximation gap or a hardware cost advantage.

It suffices to restrict $H$ to the connected orbit of rank-one reflections $H_h=I-2|h\rangle\langle h|$. Its trace is $d-2\ne0$. Allowing $U(d)$ is legitimate even if a constituent native link is presented as $SU(d)$: a scalar phase in $U$ can be absorbed in the unknown station phases while leaving $W$ unchanged.

**1. Every surviving path must use both stations.** Refine all classical outcomes and final discarded helpers into Kraus paths. Exact unitary output has rank-one Choi support, so every path operator is proportional to $W$. A path using only $A$, including repeated $AA$, is independent of $H$, whereas $W$ varies nonproportionally with $H$; that path must be zero. For a path using only $B$, fix $V=UH$ and vary $H$ with $U=VH$. The complete oracle $B_\beta$ is fixed, but $W=\operatorname{diag}(H,VHV^\dagger)$ again varies nonproportionally. This path is also zero. Zero-query and early-stop paths are included. This step uses actual **static** station phases, not independent phase noise on repeated visits. Consequently any exact hard-two protocol queries one of each almost surely.

Now average $\alpha,\beta$ independently uniformly on the circle. Exactness is preserved. For one use per station the averaged Kraus operators are

$$
\begin{array}{ll}
A_0=|1\rangle\langle0|\otimes U,&A_1=|0\rangle\langle1|\otimes U^\dagger,\\
B_0=|1\rangle\langle0|\otimes UH,&B_1=|0\rangle\langle1|\otimes HU^\dagger.
\end{array}\tag{39}
$$

The address is measured in $Z$ before its unknown data action and then flipped. Grant that direction record to the ordinary circuit; this can only strengthen the comparator. One may refine all direction and known-operation Kraus labels. For a fixed $U$, every resulting path $K_\sigma(U,H)$ is complex-linear in $H$, since it uses exactly one $B$ action.

**2. Linearity fixes every path's dependence on $H$.** Define the injective linear map $J_U(X)=\operatorname{diag}(X,UXU^\dagger)$. Exactness says $K_\sigma(U,H)=c_\sigma(U,H)J_U(H)$. The reflection orbit spans $M_d(\mathbb C)$: $\sum_jH_{e_j}=(d-2)I$, and differences of projectors onto basis vectors and their real/imaginary pair superpositions span the traceless matrices. Hence the range of the linear map $K_\sigma(U,\cdot)$ lies in $J_U(M_d)$, and $T=J_U^{-1}K_\sigma(U,\cdot)$ is a linear endomorphism of $M_d$. Every promised $H$ is an eigenvector with eigenvalue $c_\sigma(U,H)$. That eigenvalue is continuous, as extracted by Hilbert–Schmidt pairing with $J_U(H)$ divided by its squared norm $2d$. A finite-dimensional linear map has a finite spectrum; a continuous function on the connected orbit into that spectrum is constant. Therefore

$$
K_\sigma(U,X)=c_\sigma(U)J_U(X)
\quad\text{for every }X\in M_d(\mathbb C).
\tag{40}
$$

Vanishing at one reflection implies vanishing throughout the orbit. Finite-dimensional finite-query combs admit finite Kraus refinements. For continuous classical randomization the same reasoning holds almost everywhere, using a countable dense parameter subset and continuity; an unrecorded random choice does not evade rank-one output support.

**3. Equal query directions have zero probability.** For directions $A_0,B_0$, in either causal order, each entry of $K_\sigma(U,X)$ is a homogeneous holomorphic polynomial of degree two in the entries of $U$, linear in $X$. All adaptive programs and routing are known coefficient contractions. At $X=I$, (40) gives $K_\sigma(U,I)=c_\sigma(U)I$, so $c_\sigma$ is also a degree-two homogeneous polynomial. The $C=1$ block obeys, on unitaries,

$$
(\det U)K_{11}(U,X)
   =c_\sigma(U)UX\operatorname{adj}(U).
\tag{41}
$$

Both sides are holomorphic polynomials, so the identity extends to all complex matrices. To see the needed density without an oracle assumption, substitute $U=\exp(i\sum_jt_jE_j)$ in a Hermitian matrix basis. Vanishing for real $t_j$ implies vanishing for complex $t_j$ by repeated analytic continuation, hence in a complex neighborhood and then identically as a polynomial.

At any rank-$(d-1)$ matrix $U$, the adjugate is nonzero and some $X$ makes $UX\operatorname{adj}(U)\ne0$: map its nonzero image outside $\ker U$. Thus $c_\sigma(U)=0$ on every such matrix. These matrices are dense in the determinant-zero hypersurface. This hypersurface is irreducible: its dense rank-$(d-1)$ part is parameterized by products of full-rank $d\times(d-1)$ and $(d-1)\times d$ matrices, an irreducible parameter space. The determinant is reduced (at a rank-$(d-1)$ point it has a nonzero first derivative). It therefore divides $c_\sigma$. Since $2<d$, $c_\sigma=0$. For directions $A_1,B_1$, set $T=U^\dagger$; the same reasoning uses $(\det T)K_{11}=c_\sigma(T)\operatorname{adj}(T)XT$ and gives zero. All final Kraus labels were retained, so equal directions have zero **total probability**, not just zero amplitude after a selected readout.

**4. Normalize a first direction before extending the promise.** Choose a nonzero first-name-and-direction record. It is selected before any unknown data action. Unitary final output makes its probability independent of the logical input; its timing makes it independent of unknown parameters. Dividing this known preprocessing instrument by its constant probability therefore gives a genuine trace-preserving preprocessing channel.

The first selected data unitary ranges over all $U(d)$, including a first $B$ action by holding one promised $H$ fixed and varying $U$. A decision to repeat the first station has zero probability by step 1; a decision to use the same second direction has zero probability by step 3. Both decisions occur **before** the second unknown action, and depend only on the first unitary and known operations. Since that first unitary ranges over all unitaries, these forbidden decisions vanish for every possible first unitary regardless of the second oracle. They can be replaced operationally by the fixed other station and opposite direction. The result is already a valid trace-preserving fixed-slot ordinary circuit for arbitrary independent unitaries in its two data slots, before any off-promise extension. This prevents a discarded repeated-station branch from reappearing when $H$ is extended.

**5. The normalized circuit would implement a forbidden universal SWITCH.** Apply (40) with an arbitrary unitary $X=V$. Only the selected $B$ direction is queried, so no promise about its unused reverse block is needed. The coefficients are independent of $V$ and retain their original normalized squared sum. Consequently the conditioned circuit implements $J_U(V)$ deterministically, rather than as a heralded outcome. If $A$ is first, the two opposite-direction cases give

$$
\begin{array}{c|c|c}
\text{data slots}&\text{independent change of variables}&J_U(V)\\\hline
P=U,\ Q=VU^\dagger&U=P,\ V=QP&\operatorname{diag}(QP,PQ)\\
P=U^\dagger,\ Q=UV&U=P^\dagger,\ V=PQ&\operatorname{diag}(PQ,QP).
\end{array}\tag{42}
$$

For $B$ first, name its first slot $P$ and the later $A$ slot $Q$. Directions $B_0,A_1$ give $P=UV,Q=U^\dagger$; setting $U=Q^\dagger,V=QP$ yields $J_U(V)=\operatorname{diag}(QP,PQ)$. Directions $B_1,A_0$ give $P=VU^\dagger,Q=U$; setting $U=Q,V=PQ$ yields $\operatorname{diag}(PQ,QP)$. Thus either first-name branch would implement universal coherent controlled order with one query each in an ordinary fixed order.

The prior impossibility used here is [Chiribella et al., *Quantum computations without definite causal structure*, Phys. Rev. A **88**, 022318 (2013)](https://doi.org/10.1103/PhysRevA.88.022318), [full text §§III.7–IV, Lemma 4 and Theorem 3](https://arxiv.org/html/0912.0195v4). Theorem 3 excludes the one-call-each fixed-order classical SWITCH; Lemma 4 starts from unitary inputs and its following remark extends the argument beyond qubits. For completeness, the unitary-to-channel qualification can also be bridged directly. Any alleged ordinary universal unitary SWITCH has path operators bilinear in $P,Q$, proportional to $\operatorname{diag}(QP,PQ)$ on unitaries. At fixed $P$, the connected spanning set $U(d)$ and the eigenvector argument of step 2 make each scalar independent of $Q$; fixing $Q$ makes it independent of $P$. Bilinearity therefore extends the identity with a constant scalar to all complex $P,Q$. Substituting arbitrary channel Kraus operators gives the usual SWITCH channel, and discarding the surviving control gives precisely the forbidden classical supermap. This proves that the independent-unitary circuit obtained in (42) contradicts the cited theorem and completes the hard-two obstruction.

<a id="nr-r19-mean-query"></a>

### A quantitative qutrit bound with arbitrary expected-query stopping

A separate expected-query theorem adds a quantitative finite-dimensional
comparison under a specified prior. Set $d=3$,
$H=I-2|h\rangle\langle h|$, with $h$ Haar, and take independent Haar
$U\in U(3)$ and independent uniform $\alpha,\beta$. Each station phase
is **static for the entire job**, including repeated visits. Let
$j_{\mathcal E}=(\mathrm{id}\otimes\mathcal E)(\Phi_6)$ and define

$$
F=\mathbb E_{U,h,\alpha,\beta}
  \operatorname{Tr}(j_{\mathcal E}j_{\operatorname{Ad}_W}).
\tag{Q1}
$$

This is the unconditional Bell entanglement fidelity on the complete
useful address/data input. Every outcome counts. A terminating TP output
process is required; an identifiable rejection can be completed by any
output. Permit arbitrary clean memory, known joint instruments, coherent
routing of each fixed-name query, classical adaptive query names and
stopping, and arbitrarily long later rounds. Initial advice and memory
are independent of the sampled oracles. All training and repeated visits
within the job count in $N$. The budget $\mathbb E N\le2$ may be averaged
over this prior and the maximally mixed logical input, the marginal of
the Bell test. Consequently the result also covers the stronger uniform
per-instance/per-input mean-budget requirement. A free coherent selector
between names or a known coherent vacuum extension remains outside the
specified interface.

For every such ordinary receiver,

$$
F\le B_3:=\frac{1316218008181259}{1728000000000000}
       <0.761701.
\tag{Q2}
$$

This is a conservative certified ceiling, not an optimized mean-cost
frontier. Its proof consists of the following analytic reduction and one
[standard-library exact certificate replay](checks/coupler/verify_mean_query_certificate.py)
with a [single current witness](checks/coupler/mean_query_certificate.json).
No numerical solver or third-party library is needed to verify (Q2).

**Missing-station paths retain their actual static noise.** For a fixed
reflection signature put $t=\operatorname{Tr}H/d$. Conjugation averaging
gives, on the Hilbert--Schmidt vector space,

$$
\mathbb E_H\frac{|H\rangle\!\rangle\langle\!\langle H|}{d}
 =t^2\frac{|I\rangle\!\rangle\langle\!\langle I|}{d}
 +\frac{1-t^2}{d^2-1}
  \left(I-\frac{|I\rangle\!\rangle\langle\!\langle I|}{d}\right).
\tag{Q3}
$$

Indeed, write $H=tI+H_0$. The traceless part has zero mean and its
conjugation representation is irreducible. Schur averaging is scalar on
that sector; trace one fixes its coefficient. Equivalently, expanding
$H=I-2|h\rangle\langle h|$ and the pure-state second moment gives (Q3)
directly. The map $L_U(X)=\operatorname{diag}(X,UXU^\dagger)/\sqrt2$
is a Hilbert--Schmidt isometry and sends the averaged Choi operator in
(Q3) to $\mathbb E_H j_W$. For the qutrit rank-one orbit both eigenvalues
in (Q3) equal $\lambda=1/9$. Thus any CP subchannel that depends on
$U,\alpha$ but not on $H$ has averaged Bell-good weight at most
$\lambda\operatorname{Tr}j_{\rm CP}$. This grants the complete $A$
matrix for free and includes arbitrary genuine repeated-$A$ histories.
For $B$-only histories set $V=UH$: $V$ is Haar and independent of $H$,
the complete $B$ oracle depends only on $V,\beta$, and
$W=\operatorname{diag}(H,VHV^\dagger)$. The same bound applies.
Probabilities are unnormalized Choi probabilities; no input-independent
acceptance or vanishing of approximate missing-station paths is assumed.

**First names and the exact covariance.** Swapping $A,B$ sends
$U\mapsto UH$, $H\mapsto H$ and exchanges $\alpha,\beta$, leaving $W$
and the complete prior unchanged. Rename the oracle calls inside every
first-$B$ classical instrument branch. Its average score and cost become
those of a first-$A$ branch under this parameter bijection. Combining
these pre-query instruments permits first $A$ without loss, while
retaining their initial classical labels. Their probabilities may depend
on the input; no scalar first-branch assumption is used.

Take independent Haar $P,Q$, set $U=QP^\dagger$, $H=PH_*P^\dagger$,
where $H_*=\operatorname{diag}(-1,1,1)$, and write
$G=\operatorname{diag}(P,Q)$. All of $A,B,W$ are simultaneous conjugates
by $G$ of their values at $U=I,H=H_*$. This generates exactly the stated
independent $U,H$ prior. Random known port conjugations twirl a receiver
under $U(3)\times U(3)$ while preserving its average score, cost and
ordinary resources. The invariant comb's objective is therefore evaluated
at that single canonical point, rather than by a sampled Haar integral.
Complex conjugation is also feasible and preserves the real canonical
objective and constraints, so averaging permits real symmetric invariant
variables without losing an optimum.

**All two-query instruments and control sectors.** For an $AB$ prefix,
independently averaging its once-used station phases measures the query
address direction before each unknown data action. Grant these records.
Direction $j=0$ goes from physical address $0$ to $1$, and $j=1$ reverses
it. The initial direction instrument and the second direction choice may
depend arbitrarily on the input and first output. This averaging is used
only for the different-name prefix and for probabilities at a cut before
a repeated query; it does not replace repeated static phases by iid noise.

For each $j_0,j_1$ let $R_{j_0j_1}$ be a terminal comb with data ports
$[D_{\rm out},O_2,I_2,O_1,I_1,D_{\rm in}]$. Retain **all four** useful
control blocks $(c_{\rm out},c_{\rm in})\in\{0,1\}^2$, including wrong
control outputs. On one such block its representation assignments are

$$
[(c_{\rm out},+),(1-j_1,-),(j_1,+),
 (1-j_0,-),(j_0,+),(c_{\rm in},-)],
\tag{Q4}
$$

where a pair specifies which $U(3)$ group acts and whether it acts in
the fundamental or conjugate representation. In particular the query
outputs carry the link-dual representations. Independent group phases
make the intermediate tester matrices block diagonal in $c_{\rm in}$;
the surviving terminal control coherences remain in $R$. There is no
restriction to logical-control-preserving circuits.

Let $S_{j_0j_1,c}$ have ports $[I_2,O_1,I_1,D_{\rm in}]$, let $T_{j_0,c}$
have $[I_1,D_{\rm in}]$, and let $A_{j_0,c}$ have
$[O_1,I_1,D_{\rm in}]$. The latter tester aggregates the post-first-query
decision to stop or use only $A$ before a possible third visit. Let
$C_{j_0j_1,c}$ have $[O_2,I_2,O_1,I_1,D_{\rm in}]$ and represent an $AB$
continuation beyond two queries; let $Z_c$ be an initial zero-query
tester. All are PSD, with inherited representations from (Q4), and
the complete causal constraints are

$$
\begin{aligned}
\sum_{c_{\rm out}}\operatorname{Tr}_{D_{\rm out}}
 R_{j_0j_1}[c_{\rm out},c]+C_{j_0j_1,c}
 &=I_{O_2}\otimes S_{j_0j_1,c},\\
\sum_{j_1}\operatorname{Tr}_{I_2}S_{j_0j_1,c}+A_{j_0,c}
 &=I_{O_1}\otimes T_{j_0,c},\\
\sum_{j_0}\operatorname{Tr}_{I_1}T_{j_0,c}+Z_c&=I_{D_{\rm in}}.
\end{aligned}
\tag{Q5}
$$

These are unrestricted memory-comb and instrument constraints after the
stated grants. At the canonical point $A$ acts as $I$ and $B$ as $H_*$
in either data direction. For $R$, the target vector has entries
$z[(c,c);a,q,q,p,p,a]=(H_*)_{aa}(H_*)_{qq}$ and zero elsewhere. Its
terminal score is $z^TRz/(2d)^2$. For the $A$ tester use vectors
$v_a[p,p,a]=1$; for $C$ use $v_a[q,q,p,p,a]=(H_*)_{qq}$. Each tester
probability is $\sum_a v_a^T(\cdot)v_a/(2d)$, while the zero-query
probability is $\operatorname{Tr}Z/(2d)$. Thus both the objective and
the budget use the complete Bell test and its input marginal.

**The unbounded stopping reduction.** Write $p_R,p_A,p_C,p_Z$ for the
four unnormalized Bell-input probabilities, which sum to one. Fix
$\mu\ge0$. After the first $A$, any eventual terminal history still
missing $B$ has score at most $\lambda$ times its probability and cost
at least one. A history choosing another $A$ and eventually using $B$
has $N\ge3$; grant it perfect output at cost three. Whatever the stopping
decision after the second $A$, the whole aggregated tester therefore has
reward at most $\max(\lambda-\mu,1-3\mu)p_A$ in $F-\mu\mathbb EN$.
For an $AB$ prefix, retain its actual terminal score $F_R$ at cost two;
grant every continuation perfect output at cost three. Initial stops
have reward at most $\lambda p_Z$. Consequently

$$
F-\mu\mathbb EN\le F_R-2\mu p_R
 +\max(\lambda-\mu,1-3\mu)p_A+(1-3\mu)p_C+\lambda p_Z.
$$

Using $\mathbb EN\le2$ and eliminating $p_R$ gives the exact objective
upper relaxation

$$
F\le F_R+\max(\lambda+\mu,1-\mu)p_A
 +(1-\mu)p_C+(\lambda+2\mu)p_Z.
\tag{Q6}
$$

No later query cap or independent-repeat assumption appears. Later phase
recurrence, arbitrarily long adaptive rounds and their postprocessing
are covered by the perfect-output continuation grant. At
$\mu=13/40$, $\lambda=1/9$, the three probability rewards in (Q6) are
$27/40,27/40,137/180$ respectively.

**Complete invariant positivity, rather than a circuit ansatz.** The
witness specifies real symmetric contraction diagrams: each fundamental
tensor index is paired with a conjugate index of the same group, with
the transpose added when required. These are invariant operators. Their
integer Gram matrices are rebuilt by counting connected components of
paired diagrams, and full rank modulo an integer proves independence.

For each representation, the replay verifies integer highest-weight
vectors. Their weights are dominant, their columns are independent, and
every simple-root raising generator annihilates them. The fundamental
raising action replaces $i+1$ by $i$ with coefficient one; the conjugate
action replaces $i$ by $i+1$ with coefficient minus one. The sum of each
multiplicity times its exact Weyl dimension equals the entire port-space
dimension, proving completeness. If these multiplicities are $m_\gamma$,
restriction of an invariant real symmetric operator to these spaces is
injective into $\bigoplus_\gamma\operatorname{Sym}_{m_\gamma}(\mathbb R)$.
The chosen independent diagram count equals
$\sum_\gamma m_\gamma(m_\gamma+1)/2$, so it spans the **entire** real
symmetric commutant. No allowed invariant circuit direction is omitted.
Positivity on every highest-weight multiplicity space is equivalent to
positivity of the full invariant matrix. Nonorthogonal vector bases are
used as congruences; they are not treated as orthonormal.

**Exact dual and residual verification.** There are 30 matrix families,
740 independent diagram coefficients and 220 highest-weight blocks. The
single witness stores 90 genuine scalar rows of (Q5) by their port
addresses. The replay reconstructs their coefficients and right sides,
so selecting those rows can only relax the full physical constraints.
It rebuilds all highest-weight projections and the objective above.

Let $x$ collect the diagram coefficients, $Ex=b$ the retained equations,
and $P_j(x)\succeq0$ their highest-weight positivity constraints. The
witness gives rational $y$ and positive definite rational $Y_j$, checked
by exact LDL arithmetic. Rebuild the rational residual
$r=E^Ty-c-\sum_jP_j^*(Y_j)$. Weak duality gives
$c^Tx\le b^Ty+|r^Tx|$. For each matrix family with diagram Gram $G$,
the witness supplies $h$ satisfying **exactly** $Gh=r$. Its operator
representer $K=\sum_i h_iB_i$ obeys
$\|K\|_{\rm HS}^2=r^TG^{-1}r=r^Th$ and
$r^Tx=\operatorname{Tr}(K R)$. The full physical constraints (Q5) give
the trace bounds

$$
\operatorname{Tr}R_{j_0j_1}\le2d^3,\quad
\operatorname{Tr}S,\operatorname{Tr}A\le d^2,\quad
\operatorname{Tr}T,\operatorname{Tr}Z\le d,\quad
\operatorname{Tr}C\le d^3.
\tag{Q7}
$$

For fixed $c$, taking traces in (Q5) gives
$\sum_{j_0}\operatorname{Tr}T_{j_0,c}+\operatorname{Tr}Z_c=d$,
$\sum_{j_1}\operatorname{Tr}S_{j_0j_1,c}
+\operatorname{Tr}A_{j_0,c}=d\operatorname{Tr}T_{j_0,c}$, and
$\sum_{c_{\rm out}}\operatorname{Tr}R_{j_0j_1}[c_{\rm out},c]
+\operatorname{Tr}C_{j_0j_1,c}=d\operatorname{Tr}S_{j_0j_1,c}$.
Every term is nonnegative. Bounding each term by its containing sum
gives (Q7), with the factor two for $R$ coming from its two input-control
sectors.

Positivity bounds the residual contribution by
$\|K\|_{\rm HS}\operatorname{Tr}R$ family by family. Integer square
roots with outward rational rounding bound each norm. This certificate
uses the physical trace bounds, even if the selected scalar equations
alone describe a larger artificial relaxation. The exact dual objective
is $1316216539325963/1728000000000000$ and the complete residual allowance
is $53127/62500000000$; their sum is (Q2). Solver convergence, floating
point eigenvalues and a numerical primal optimum are not proof inputs.

**Achievable comparisons and the remaining application gap.** Ordinary
serial order followed by useful-address dephasing gives $F=1/2$ for
every phase and unknown target. Running the exact three-query ordinary
construction with probability $2/3$ and otherwise returning the input
gives mean two and
$F=2/3+(\operatorname{Tr}H/d)^2/3=19/27$ for this prior. Thus it is
included below the conservative ceiling (Q2). Under only the declared
helper-dephasing model (37), the switch has $F=(1+\nu)/2$, and exceeds
every ordinary receiver in this expected-query model whenever
$\nu>2B_3-1$, approximately $0.523400473$. This is a finite oracle
fidelity separation with arbitrarily long ordinary rounds already
included, rather than an inference from the exact two-call cap.

The prior is a substantive premise. An executable conditional $H$ gate
closes the task even if its classical matrix is unknown, and a training
state learned from persistent devices changes initial independence.
Learning must be charged across the actual reuse window. The rank-one
family also has zero-query fidelity $(1-2/d)^2\to1$ in large dimension;
this qutrit certificate supplies no constant asymptotic advantage.
Routing loss, phase drift, helper gates, coherent storage and a physical
unknown-coupler pair remain additional native requirements. The theorem
does not establish their availability or a laboratory-time saving.

### Dimension, physical assumptions and verification boundary

The full qubit problem is unresolved by the exact proof above. Its rank-one reflection orbit is traceless and spans only $\mathfrak{sl}_2$, so step 2 cannot reach $I$ or all unitary $V$. Also $\deg\det U=2$, so step 3 does not force a degree-two coefficient to vanish. The $SU(2)$ identity $YU^TY=U^\dagger$ does not itself grant an ordinary physical transpose query. Equation (38) is a real ordinary qubit closure, rather than a general qubit converse. The quantitative certificate (Q2) concerns only its stated qutrit prior, and does not optimize an approximate-fidelity or expected-cost frontier.

<a id="nr-r19-native-interface"></a>

### Native reflection access, persistent calibration and physical couplers

**An unknown executable reflection already suffices.** Matrix knowledge
of $H$ is stronger than the ordinary wrapper needs. If the native
address-selective operation $M=\operatorname{diag}(H,I)$ is executable,
even with unknown $H$, then

$$
MAM=B,\qquad MA_\alpha MA_\alpha=W,
\qquad MB_\beta MB_\beta=W.
\tag{NC1}
$$

The first identity is direct block multiplication. Since $[M,Z_C]=0$
and $\{A,Z_C\}=\{B,Z_C\}=0$, the two station phase factors cancel in
each repeated-query word, leaving $MAMA=BA$ or $MBMB=AB$. This is a full
operator identity for every input/reference; it does not estimate any
matrix. An unknown $H$ oracle on $D$ alone does not automatically provide
this address-selective $M$: controlled access to an unknown operation is
additional phase-sensitive data.

If $B_\beta$ is physically synthesized as $MA_\beta M$, switching it with
$A_\alpha$ consumes two hopping-core pulses and two $M$ pulses in each
history. Equation (NC1) uses exactly the same primitive counts, without
order routing or an extra helper. It requires the repeated $A_\alpha$
stability already used by the three-query upper bound. Timing, faulty
pulses, leakage, records and idle noise can change the actual comparison;
equal ideal counts are not equality of noisy instruments. Conversely, a
sealed opaque $B$ does not expose $M$ merely because its matrix factors
this way. A positive native proposal must specify which access is real.

Bright-state reflections supply a concrete ordinary primitive. The
[quantum Householder proposal](https://doi.org/10.1103/PhysRevA.74.022323)
([explicit $N$-pod model, §II.3](https://arxiv.org/html/0708.2811v1))
couples degenerate ground states to one excited level with a common
envelope and fixed relative amplitudes/phases. A resonant rms area
$2(2k+1)\pi$ returns the excited population and produces
$I-2|h\rangle\langle h|$ on the ground manifold. Repeating that pulse
need not require knowing the stable bright vector. Implementing $M$
still requires actual selectivity to the $C=0$ manifold. The proposal
does not demonstrate a full unknown NR-R19 pair or its router.

**Persistent $H$ has an ordinary calibration port.** Prepare physical
address $C=0$ and run $B_\beta A_\alpha$. Its action on $D$ is
$e^{i\delta}H$, hence exactly the channel $\operatorname{Ad}_H$,
independent of the unknown station phase. Ordinary channel calibration
can therefore learn a persistent $H$ without first learning $U$ or
$\delta$, provided its preparation, reference and readout ports are
available and every training visit is charged. No optimal sample bound
is asserted.

The unavoidable global-sign ambiguity is harmless. If two involutions
have the same unitary channel, $H'=e^{i\theta}H$ and Hermiticity forces
$H'=\pm H$. Replacing $H$ by $-H$ changes the wrapper output to $-W$,
the same target channel. More quantitatively, let an executable compiled
involution $\widehat H$ satisfy
$\min_{s=\pm1}\|\widehat H-sH\|\le\epsilon$, and set
$\widehat M=\operatorname{diag}(\widehat H,I)$. Unitary telescoping gives

$$
\|\widehat M A_\alpha\widehat M A_\alpha-sW\|
 \le2\epsilon,\qquad
\frac12\|\operatorname{Ad}_{\widehat M A_\alpha\widehat M A_\alpha}
                 -\operatorname{Ad}_W\|_\diamond\le2\epsilon.
\tag{NC2}
$$

The operator bound replaces the two $\widehat M$ factors one at a time;
all other factors have norm one. The channel bound follows from
$\|\operatorname{Ad}_V-\operatorname{Ad}_{V'}\|_\diamond
\le2\|V-V'\|$, with global sign discarded. Converting an experimental
calibration error into the stated operator estimate and pricing controlled
gate synthesis require their actual model. Once compiled, the wrapper
can tolerate a new unknown $U$ and static station phase in each job if
$H$ persists and $A$ repeats within that job. Rapid phase drift alone is
therefore insufficient for a durable advantage; its $H$ drift window,
training and helper cost must be compared explicitly.

**A general hopping matrix has extra spectral requirements.** For an
invertible coupling $K=L\Sigma R^\dagger$ between two $d$-state
manifolds, the resonant constant Hamiltonian
$G_K=\left(\begin{smallmatrix}0&K^\dagger\\K&0\end{smallmatrix}\right)$
has propagator

$$
e^{-itG_K}=\begin{pmatrix}
R\cos(t\Sigma)R^\dagger&-iR\sin(t\Sigma)L^\dagger\\
-iL\sin(t\Sigma)R^\dagger&L\cos(t\Sigma)L^\dagger
\end{pmatrix}.
\tag{NC3}
$$

Conjugation by $\operatorname{diag}(R,L)$ reduces the Hamiltonian to
independent blocks $\sigma_jX$, proving the formula. Complete exchange
of both arbitrary manifolds requires $\cos(t\sigma_j)=0$ for every $j$:
$t\sigma_j=(2n_j+1)\pi/2$. A flat spectrum is sufficient; special
odd-commensurate spectra also work, with their sine signs included in
the transfer unitary. Generic unknown spectra do not obey a common
exact pulse condition. A rank-one bright-state reflection is not an
exchange of two full $d$-dimensional manifolds. The
[multimanifold Morris--Shore treatment](https://arxiv.org/html/0802.4246v1)
explicitly has generally different bright-pair couplings. Adiabatic or
composite pulse constructions can change this constant-coupling screen,
but need full-input propagators, durations and ordinary controls.

**Stationary settings and reciprocal optical ports are distinct interfaces.**
If the physical order helper coherently selects two coupling settings on
the same stationary register, its supplied selector is subject to the
chronological identity (32). It already implements the two controlled
products in two ordinary windows, retaining the actual bath and records.
A mobile packaged-gate implementation instead has to receive and return
the complete useful $C\otimes D$ register. Hopping of a particle between
two laboratory sites does not by itself provide that port.

Nor does reversing a generic reciprocal multimode device provide an
adjoint. In orthonormal reciprocal propagating port bases, a reflectionless
lossless forward matrix $T$ has scattering matrix
$S=\left(\begin{smallmatrix}0&T^T\\T&0\end{smallmatrix}\right)$, by
[Lorentz reciprocity](https://doi.org/10.1103/PhysRevA.87.013838)
([complete modal qualifications](https://arxiv.org/html/1301.2458v1)).
If this equals $e^{i\gamma}A_\alpha(V)$, block comparison gives
$T=e^{i(\gamma-\alpha)}V$ and

$$
T^T=e^{2i\gamma}T^\dagger,
\qquad T=e^{i\gamma}O,\quad O\text{ real orthogonal}.
\tag{NC4}
$$

Transposing the first relation gives $T=e^{2i\gamma}T^*$, so
$e^{-i\gamma}T$ is real and unitary, proving the second. Thus generic
reciprocal transport does not supply the full unknown $U(d)$ family by
opposite propagation alone. Generalized/nonorthogonal or evanescent modes
need their actual weighted reciprocity relation; nonreciprocal engineering
is a separate possibility. The present full-$U(d)$ converse does not
automatically settle a real-orthogonal subfamily.

Finally, passive number-preserving mobile gates have a vacuum sector.
If a coherent stationary vacuum-preserving extension is actually available,
the ordinary three-query construction can use a vacuum dummy. Each
history then has only two occupied module traversals despite three query
windows; the extra cost can be coherent delay and routing rather than
an unavoidable third photon-medium interaction. Active noise, input-dependent
records or different repeated interactions require a complete dummy model.
These native screens preserve the opaque-port exact query theorem and
give stronger comparators for specified hardware. They establish no
physical impossibility for every coupler family or measured architecture
advantage.

The remaining architecture target must specify that pair, a useful coherent address input, full temporal dilations and emitted records, an independent surviving helper, all routing/storage/control costs, phase stability across repeats and any calibration reuse. Pulse, idle, preparation, cooling, leakage and rejected launches enter the same physical ledger on both sides. Known $H$, classical addresses, a supplied selector, or destructive helper/payload readout changes or closes the endpoint. A significant finite advantage on such a native workload remains open.

The shared [exact checker](checks/architecture/verify_backaction.py) separately reports NR-R19. It replays noncommuting rational examples in data dimensions two and three, all address/data matrix units for the corrected and visibility-limited channels, phase drift, known-$H$ wrappers, whole-pair ambiguity, selector compilation, and the unknown-$H$ Abelian qubit counterprotocol. These finite identities support transcription and scope checks. The connected-orbit, determinant, operational normalization and no-SWITCH reduction above are analytic proofs, not conclusions inferred from a finite optimizer or the replay.

The separate [mean-query certificate](checks/coupler/verify_mean_query_certificate.py)
reconstructs the complete finite invariant bases, highest-weight kernels
and dimensions, scalar causal rows, objective, rational positive duals
and residual Gram equations for (Q2). The analytic prior, covariance,
stopping inclusion and trace bounds (Q3)--(Q7) supply its connection to
all ordinary receivers; the replay does not establish hardware access,
an amortized calibration advantage or a new Lean theorem.
