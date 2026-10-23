# Quantum-bath backaction and ordinary control baselines

[Application assessment](architecture.md) · [Ordinary baselines](architecture-baselines.md) · [Dispatch](dispatch.md) · [Checks](checks/README.md)

<a id="nr-r14"></a>

## NR-R14 — Shared-bath calibration transfer and exact ordinary echo/instrument baselines

A complete one-time noise calibration need not predict performance under a different control history. The example below reverses the preferred choice between two storage schedules while preserving the entire Ramsey calibration. It therefore describes a useful architecture decision. In the stated native central-spin model, however, ordinary Hahn echo already implements the proposed coherent bath-order experiment, including its conditional quantum output. Known sensor-only measurement and reset interventions have a related ordinary controlled-dilation implementation.

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

### Scope of the obstruction and a falsifiable next target

The native central-spin commutator candidate supplies no advantage over the ordinary full instrument (2)–(4). The known-intervention construction is closed by (18). Equations (6)–(7) show useful control-dependent model failure, while (8)–(17) delimit what partial statistics certify and provide stronger ordinary tests.

A remaining positive target must specify an unknown joint intervention family and an implementable coherent temporal interface, then identify a storage, gate or calibration decision that ordinary echo, phase cycling, pump/reset/read, retained records, entangled probes and direct target-sequence calibration cannot match at the same cost. A concrete falsifiable benchmark is lower prediction error or lower all-attempt cost for a stated held-out control family, with bath initialization/drift, inaccessible histories, coherent buffers, readout inefficiency and rejections charged. A nonzero commutator signal or a favorable conditional bath state alone does not establish that benchmark.

The [exact checker](checks/architecture/verify_backaction.py) replays finite reference-inclusive $X/Y$ echo instruments, the rational held-out counterexample, the maximal ordinary record contrast, and polynomial identities for the calibration/storage example. The all-dimension operator and linearity arguments are the proofs above; the finite cases are not a general formalization, a hardware demonstration, a sample-optimality theorem, or a no-go for every shared-bath application.
