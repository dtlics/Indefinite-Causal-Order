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
