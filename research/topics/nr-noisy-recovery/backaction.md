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

<a id="nr-r14-high-order-transfer"></a>

### High-order bath correlations and a complete-output transfer obstruction

High-order quantum bath information is accessible with ordinary native
controls. [Xia et al., PRL **134**, 253601
(2025)](https://doi.org/10.1103/4fdk-dblq)
([primary paper](https://iop.cas.cn/xwzx/kydt/202507/P020250711340279270998.pdf))
isolate second- and fourth-order time-ordered correlations of $^{13}$C
spins near an NV center. Their fourth-order spectrum fingerprints spins
with the same unresolved precession frequency. The model uses
noninteracting high-temperature nuclei, DD-selected longitudinal contacts,
sensor rotations and optical readout; it is not a demonstration for an
arbitrary strongly interacting bath. [Meinel et al.](https://doi.org/10.1038/s41467-022-32610-8)
also demonstrate fourth-order quantum correlations through sequential weak
NV measurements. [Wu et al., PRL **132**, 200802
(2024)](https://doi.org/10.1103/PhysRevLett.132.200802)
demonstrate an ordinary sensor-channel construction selecting a fourth-order
time-ordered correlation, with a quantum-control application. A comparison
only to a Gaussian power-spectrum fit omits these physical alternatives.

For the displayed fourth-order protocol of Xia et al., three intermediate
sensor-channel blocks contain

$$
\mathcal P_j=\mathcal R_y(\pi/2)
\frac{\mathcal R_x(\pi/2)-\mathcal R_{-x}(\pi/2)}2,
$$

where $\mathcal R$ denotes conjugation by a known rotation. These signed
maps are implemented by phase cycling, rather than treated as standalone
CPTP operations. Expanding the three differences gives eight ordinary
chronological pulse strings, each with four bath contacts, with coefficients
$\pm1/8$. Choosing the three signs uniformly and multiplying the terminal
bounded sensor outcome by their product is exactly unbiased for that signed
finite-strength sequence functional: multilinearity proves the identity
for arbitrary intervening joint bath dynamics and reference. The measured
functional has a leading fourth-order contribution proportional to the
fourth power of the short contact duration. Extracting its coefficient
still requires bounds on higher orders, DD/control errors, readout
contrast and repeated-history preparation. For an outcome in $[-1,1]$,
Hoeffding gives raw additive accuracy $\epsilon_{\rm raw}$ after
$N\ge2\epsilon_{\rm raw}^{-2}\log(2/\delta)$ independent trials.
This is not an exact finite-strength fourth derivative, nor an independent
sample bound for an unreset persistent bath. The longitudinal port also
retains the complete ordinary echo identity proved above.

The following counterexample makes the missing calibration information
precise, including the complete conditional quantum output. It concerns a
stipulated untouched or freshly prepared target history, not active bath
preparation or optimization over all protection strategies. Let an
inaccessible four-qubit bath start in one of the pure states

$$
|G_h\rangle=\frac{|0000\rangle+h|1111\rangle}{\sqrt2},
\qquad h\in\{+1,-1\},
$$

and supply four separate sensor/bath contact ports

$$
U_j(\theta)=\exp[-i\theta Z_S\otimes X_j],\qquad j=1,\ldots,4.
\tag{HO1}
$$

There is no additional free bath evolution spreading a selected port's
support to the other bath qubits. A passive reference can be entangled
with the sensor input; the bath itself is the specified pure state.
Known sensor $X$ pulses reverse a contact's sign and restore its frame.
The bath is not reset between contacts in a run.

Every proper bath marginal of $G_+$ equals that of $G_-$: for nonempty
$J\subsetneq\{1,2,3,4\}$ it is
$\bigl(|0_J\rangle\langle0_J|+|1_J\rangle\langle1_J|\bigr)/2$.
Consequently every calibration instrument whose entire interaction is
supported on the sensor, arbitrary accessible memories and one proper
subset $E_J$ gives exactly the same accessible flagged quantum output
under the two hypotheses. To prove this, include all controls, record
buffers and measurements in a joint instrument
$\Lambda_{SAE_J}\otimes\mathrm{id}_{E_{\bar J}}$. Its accessible output
depends only on the common initial marginal on $SAE_J$. The argument
allows arbitrary memory, repeated contacts, adaptive processing and coherent
order superpositions of contacts within that same subset. It compares
complete instruments, not only a fringe mean or an isolated sensor map.

Classical adaptive choice of at most three contact ports also cannot
distinguish the hypotheses. Refine its classical records into leaves;
each leaf's joint Kraus operators have support on at most three bath
qubits, so its probability and accessible state agree. Different proper
subsets queried on independent fresh copies likewise give identical data.
Applying enough different contacts to the same unreset bath that their
union contains all four is outside the premise. So is a free coherent
selector over all four port names: its ket and bra histories can jointly
cover all four qubits with fewer calls. This is a support-based
nonidentifiability statement, not a general three-query lower bound with
an arbitrary coherent name selector.

Now run all four contacts for storage. If $y_j\in\{+1,-1\}$ is the
sign of contact $j$ after restoring the known sensor frame, the reduced
sensor channel is dephasing with coherence

$$
\begin{aligned}
L_h(y)
&=\left\langle G_h\left|
\prod_{j=1}^4(cI-is y_jX_j)\right|G_h\right\rangle\\
&=c^4+h\left(\prod_{j=1}^4y_j\right)s^4,
\qquad c=\cos(2\theta),\quad s=\sin(2\theta).
\end{aligned}
\tag{HO2}
$$

Indeed every nonempty proper $X$-string has expectation zero, while
$\langle X_1X_2X_3X_4\rangle=h$. Compare the two named schedules
$I:y=(+,+,+,+)$ and $E:y=(-,+,+,+)$, with known sensor $X$ pulses
around the first contact for $E$. At $\theta=\pi/8$, their identity-memory
entanglement fidelities are

$$
\begin{array}{c|cc}
 &F_e(I)&F_e(E)\\ \hline
h=+1&3/4&1/2\\
h=-1&1/2&3/4.
\end{array}
\tag{HO3}
$$

The preferred named schedule reverses with gap $1/4$. A known final
sensor phase correction cannot improve either zero coherence or the
positive coherence $1/2$. Extra echo pulses have real costs; this is
not an optimum over all DD, encoding or recovery strategies. The pure
entangled bath is operationally equivalent to a classical parity-correlated
field for these commuting contact ports, so the example does not certify
genuinely noncommuting quantum backaction. Its role is the stronger
complete-output insufficiency of a specified calibration interface.
Calibration can also disturb or steer the bath; the argument does not
prohibit deliberately changing the later storage environment. In
particular it is not an impossibility theorem for bath cooling or joint
state preparation.

The [exact high-order guard](checks/architecture/verify_high_order_bath.py)
checks all 15 proper GHZ marginals, 32 $X$ moments and 32 normalized
logical Choi cases. At its rational phase point $c=3/5,s=4/5$, the
optimally phase-corrected fidelities are $481/625$ and $16/25$, reversed
by $h$, with gap $81/625$. The all-instrument support proof and the
$\pi/8$ values above are analytic arguments, not inferences from those
finite cases.


<a id="nr-r14-pair-qualification"></a>

### Ordinary qualification of labelled pair memories

The concrete decision is which physical memory and phase correction to
use for one unknown logical qubit at a fixed storage time $T$. Local
product probes suffice for the following restricted catalogue. The
calibration model must transfer to production; identifying an aggregate
noise statistic alone does not establish that transfer.

**Dedicated pair, general Schur channel.** Assume the same
population-preserving two-qubit CPTP map in calibration and production:

$$
\mathcal E(|u\rangle\langle v|)=C_{uv}|u\rangle\langle v|,
\qquad C\succeq0,\quad C_{uu}=1,
\quad u,v\in\{00,01,10,11\}.
\tag{DQ1}
$$

This is a specified single-use channel with an input-independent initial
bath preparation. It permits within-storage bath memory and need not be
Gaussian, Markovian or a mixture of classical phases. Leakage, different
spectator preparations and control histories are not silently included.
The probes below do not independently certify the entire Schur promise.

Let $V_+|b\rangle=|b,b\rangle$ and
$V_-|b\rangle=|b,1-b\rangle$. Their coherence factors are
$L_+=C_{00,11}$ and $L_-=C_{01,10}$. Prepare $|++\rangle$ and retain the
local outcomes in settings $XX,YY,XY,YX$. With their respective parity
means $a,b,c,d$, and $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$,

$$
L_+=(a-b)-i(c+d),\qquad L_-=(a+b)+i(c-d).
\tag{DQ2}
$$

Indeed $2a=\operatorname{Re}(L_++L_-)$,
$2b=\operatorname{Re}(-L_++L_-)$,
$2c=-\operatorname{Im}L_++\operatorname{Im}L_-$ and
$2d=-\operatorname{Im}L_+-\operatorname{Im}L_-$. These traces recover
two complex factors, rather than the complete Schur matrix. The full
bitstrings remain ordinary available records.

For either code, writing an arbitrary logical input/reference state as
$\sum_{i,j}|i\rangle\langle j|\otimes\rho_{ij,R}$ gives, after ideal
encoding, storage and decoding,

$$
\mathcal D_L\otimes\operatorname{id}_R:
\begin{pmatrix}\rho_{00,R}&\rho_{01,R}\\
\rho_{10,R}&\rho_{11,R}\end{pmatrix}
\longmapsto
\begin{pmatrix}\rho_{00,R}&L\rho_{01,R}\\
L^*\rho_{10,R}&\rho_{11,R}\end{pmatrix}.
\tag{DQ3}
$$

This follows on each encoded matrix unit, including all reference
coherences; population preservation keeps the state inside the code.
An output phase $\operatorname{diag}(1,e^{i\theta})$ changes the
multiplier to $e^{-i\theta}L$, so

$$
F_e(L,\theta)=\frac{1+\operatorname{Re}(e^{-i\theta}L)}2,
\qquad F_e^*(L)=\frac{1+|L|}2.
\tag{DQ4}
$$

The best phase is $\arg L$ when $L\ne0$, with any phase at zero. This
score is optimal over deterministic CPTP recovery for each declared code
without an additional noise record: after phase alignment the channel is
$p\operatorname{id}+(1-p)\operatorname{Ad}_Z$,
$p=(1+|L|)/2\ge1/2$. For recovery Kraus operators $A_j$ put
$f_P=\sum_j|\operatorname{Tr}(A_jP)|^2/4$. Pauli Parseval and trace
preservation give $\sum_{P\in\{I,X,Y,Z\}}f_P=1$, and the recovered Bell
fidelity is $pf_I+(1-p)f_Z\le p$. An arbitrary physical decoder restricted
to the preserved code is such a logical recovery. This does not optimize
over all encodings or extra records and protected helpers.

**Finite data and ordinary single-site alternatives.** Take $n$
independent launches for each of the four settings, with the same channel
and trusted specified measurement means. Hoeffding and a union bound give
all four parity errors at most
$e=\sqrt{2\log(8/\delta)/n}$ with probability $1-\delta$. Thus both
complex errors are simultaneously at most

$$
\beta=2\sqrt2e=4\sqrt{\log(8/\delta)/n}.
\tag{DQ5}
$$

Choose the larger $|\widehat L|$ and apply its estimated phase, taking
phase zero if the estimate is zero. For every phase the estimated and
true fidelity differ by at most $\beta/2$. Maximizing the empirical score
therefore gives actual fidelity at least $\max_\pm F_e^*(L_\pm)-\beta$,
and at least $(1+|\widehat L_{\rm chosen}|-\beta)/2$. There is no
division by a small coherence. In particular,
$n\ge16\epsilon^{-2}\log(8/\delta)$ suffices for fidelity regret
$\epsilon$, using $4n$ actual storage launches; this constant is not
claimed optimal.

The strongest ordinary comparator also includes the four unencoded
options: store in one site with its spectator fixed in $|s\rangle$,
$s=0,1$. Their factors are $C_{0s,1s}$ and $C_{s0,s1}$. Product probes
$|+s\rangle$ or $|s+\rangle$ and local $X/Y$ readout give
$L=\langle X\rangle-i\langle Y\rangle$ in the same prepared context.
One simple six-option budget uses $n$ launches for each of twelve
preparation/readout groups. Union over twelve means replaces $\beta$ by
$4\sqrt{\log(24/\delta)/n}$, which also bounds each single-site error.
The same joint choice-and-phase regret proof applies. These are the six
computational-basis two-state subspaces, not every two-qubit code.

Identical one-shot marginals alone do not justify independent-sample
confidence. Bath/history resets or a separately justified conditional-mean
martingale model must support it. SPAM bias and calibration/production
drift require explicit bounds. Preparation, reset, local readout and the
actual $T$ count on every launch. Production parity codes need ancilla
preparation and an encoding and decoding CNOT; the odd code uses an
initial $|1\rangle$ target. Singles need no such entangling gates. Phase
tracking must be resolved before an incompatible endpoint. Gate errors,
latency and calibration amortization can change the preferred physical
memory; (DQ4) is the ideal storage score, not a whole-pipeline optimum.

**Why labelled records matter.** A finite example separates the useful
decision from a coarse aggregate. On four sites let

$$
\mathcal E_s=\tfrac12\operatorname{id}+\tfrac12\operatorname{Ad}_{U_s},
\qquad U_s=e^{-i\pi\sum_j s_jZ_j/4},
\quad s_A=(+,+,-,-),\quad s_B=(+,-,+,-).
\tag{DQ6}
$$

The two models are related by swapping sites 2 and 3. On $|+\rangle^4$
every common-angle aggregate parity is identical: for
$M_\phi=\cos\phi X+\sin\phi Y$,
$\langle M_\phi^{\otimes4}\rangle=(\cos^4\phi+\sin^4\phi)/2$.
But labelled pair $(1,2)$ has $(L_+,L_-)=(0,1)$ in A and $(1,0)$ in B.
The wrong parity code has fidelity $1/2$ instead of $1$.
Ordinary full records already resolve this: pair $XX$ is $1/2$ in both,
while pair $YY$ is $+1/2$ versus $-1/2$. Global $YYYY$ is $1/2$ in both.
The insufficiency belongs to discarding labels, not to the underlying
ordinary measurement interface. This example supplies no switch benefit.

<a id="nr-r14-parallel-phase-qualification"></a>

**Parallel catalogue under a stronger classical-phase promise.** Suppose
an $N$-site register instead has the state-independent channel

$$
\Phi(\rho)=\int U_\varphi\rho U_\varphi^\dagger p(d\varphi),
\qquad U_\varphi=\bigotimes_{j=1}^N e^{-i\varphi_j Z_j/2}.
\tag{DQ7}
$$

Spatial correlations and non-Gaussian distributions are allowed. The
classical field is independent of the supplied state/reference, and the
same distribution, storage interval and controls apply to independent
calibration launches and production. Tensor locality makes each reduced
candidate channel spectator independent. A general register Schur map
does not grant this: deterministic $CZ$ is diagonal, but one site's
channel is identity with spectator $|0\rangle$, $Z$ with $|1\rangle$,
and dephasing with a discarded $|+\rangle$ spectator. Quantum bath-induced
interactions and changed production contexts need their actual joint model.

Select among $K=N+2P$ options: all $N$ singles and both parity codes on
$P$ eligible edges. The corresponding factors are
$L_j=\mathbb E e^{-i\varphi_j}$ and
$L_{jk,\pm}=\mathbb E e^{-i(\varphi_j\pm\varphi_k)}$.
Their full logical/reference channels are (DQ3), with optimal
deterministic recovery score (DQ4) for each fixed candidate.
Prepare $|+\rangle^N$ on each launch and choose each site's readout axis
independently and uniformly from $X,Y$, independently of the noise.
Retain all axes and outcomes $x_j\in\{-1,+1\}$. A single-site unbiased
complex estimator is $2x_j$ for $X$ and $-2ix_j$ for $Y$.
For an edge, let $r=x_jx_k$ and use:

| Axes on $j,k$ | Estimator for $L_{jk,+}$ | Estimator for $L_{jk,-}$ |
| --- | --- | --- |
| $XX$ | $4r$ | $4r$ |
| $YY$ | $-4r$ | $4r$ |
| $XY$ | $-4ir$ | $4ir$ |
| $YX$ | $-4ir$ | $-4ir$ |

Conditioned on $\varphi$, the $X/Y$ means are $\cos\varphi_j$ and
$\sin\varphi_j$. Averaging the table, with each axis pair having
probability $1/4$, yields the stated exponentials. The same shot supplies
every edge, including overlapping edges; estimates need not be independent
across candidates. Each real/imaginary component lies in $[-4,4]$.
For $M$ independent launches, Hoeffding with component tolerance
$\epsilon/\sqrt2$ and a union bound over $2K$ components gives

$$
\Pr\{\max_q|\widehat L_q-L_q|>\epsilon\}
\le4K e^{-M\epsilon^2/64},\qquad
M\ge\left\lceil64\epsilon^{-2}\log\frac{4(N+2P)}\delta\right\rceil.
\tag{DQ8}
$$

Empirical maximum magnitude plus its estimated phase has actual fidelity
regret at most $\epsilon$: writing
$\widehat R=\max_q|\widehat L_q|$, the best true factor is at most
$\widehat R+\epsilon$ and the chosen true aligned factor at least
$\widehat R-\epsilon$. This also covers a zero estimate.
If every production factor differs from its calibration factor by at most
$\kappa$, replace $\epsilon$ by $\epsilon+\kappa$ in that regret and in
the fidelity lower certificate
$(1+\widehat R-\epsilon-\kappa)/2$. A separately certified complex bias
bound adds likewise. Matching only single-site marginals does not bound
edge drift. The noise-model, sampling and SPAM promises require evidence;
the protocol does not establish them from its own output.

This uses $M$ storage waits, $MN$ local preparations/readouts and random
axis choices, $O(MP+MN)$ direct processing, and $O(MN)$ retained axis/outcome
bits plus metadata. Streaming candidate sums reduces storage but forfeits
the full records for later questions. It is logarithmic in the number of
candidates only in launch count, not total hardware/readout work.
Eligible edges, encoding gates, state transfer, drift windows, inter-shot
decorrelation and recalibration all count. Optimizing a grid of storage
times needs its additional data. Pair scores do not certify a joint
fault-tolerant architecture or every alternative encoding.

**Prior and switch boundary.**
[Gulácsi, Kattemölle and Burkard, PRResearch **7**, L042067 (2025)](https://doi.org/10.1103/k2lx-vfqp)
use product preparation and local readout for correlated-noise diagnostics;
their dephasing parity harmonics recover aggregate coherence sums. The
published Eq. (12) relates short-time log-ratio slope (white noise) or
curvature (colored noise) to aggregate correlation strength within the
paper's weak-coupling model. The earlier
[arXiv v1](https://arxiv.org/abs/2502.09706v1) has the title *Revealing
correlated noise with single-qubit operations*; the published title is
*Characterizing correlated noise with single-qubit operations*.
Their aggregate characterization is not a claim to infer every labelled
code choice or certify (DQ7).
[Huang, Kueng and Preskill](https://doi.org/10.1038/s41567-020-0932-7)
already provide simultaneous local-observable prediction from randomized
measurement records. The algebra above supplies an application-specific
conditional memory score and transfer certificate, with no priority claim
for randomized measurement or a logarithmic-observable-count method.

For independent channels with diagonal Kraus operators, every $A_a,B_b$
commutes. Each switch Kraus operator is exactly
$|0\rangle\langle0|\otimes B_bA_a+
|1\rangle\langle1|\otimes A_aB_b=I_C\otimes B_bA_a$.
An initially $|+\rangle$ control stays $|+\rangle$ and the target/reference
undergoes ordinary composition. This excludes no order-sensitive
persistent quantum-bath dilation: reduced diagonal channels alone do not
specify that joint instrument. The next useful test must supply such
actual noncommuting interactions, a production decision and a comparison
with full-record ordinary learning within the same priced drift window.

The [pair-memory guard](checks/architecture/pair_memory_qualification_guards.py)
is included in the backaction job. It replays exact finite Schur,
encoded-channel, record, estimator and scope fixtures. The recovery,
concentration and model-transfer arguments above remain analytic;
no physical noise model, native advantage or new Lean proof is certified.


<a id="nr-r14-loss-memory"></a>

### Ground-preserving memory and recovery with retained order control

The next memory decision is a ground-plus-collective-excitation code at a
specified storage deadline. The following comparison retains the order
control, every loss outcome and an arbitrary passive reference. It closes
one ground-preserving fidelity candidate under explicitly paid ordinary controls;
it does not exclude every dual-rail, thermal or postselected application.

**Physical access and the ordinary dark code.**
[Filipp et al.](https://doi.org/10.1103/PhysRevA.84.061805) and
[Zanner et al.](https://doi.org/10.1038/s41567-022-01527-w) demonstrate
ordinary phase-sensitive dark-state preparation and coherence tests.
Zanner's [published supplement, S3](https://media.springernature.com/original/springer-static/esm/art:10.1038%2Fs41567-022-01527-w/MediaObjects/41567_2022_1527_MOESM1_ESM.pdf)
reports ground/dark $T_1=1.71\pm0.06\,\mu$s and
$T_2=0.58\pm0.06\,\mu$s. The coherence cannot be inferred from radiative
population lifetime alone. Neither population readout nor destructive
emission tomography supplies a retained-output survival herald.

[Shah et al., PRX Quantum **5**, 030346 (2024)](https://doi.org/10.1103/PRXQuantum.5.030346)
stabilize one prescribed entangled state through waveguide dissipation;
this is a preparation service, rather than an arbitrary-input memory
experiment. In the ideal model $\mathcal L=\gamma\mathcal D[J]$,
$J=\sigma_1^-+\sigma_2^-$, both
$|G\rangle=|gg\rangle$ and
$|D\rangle=(|eg\rangle-|ge\rangle)/\sqrt2$ lie in its kernel.
Consequently $\mathcal D[J]$ vanishes on every encoded matrix unit,
including reference coefficients. An ordinary encoder and decoder preserve
that qubit exactly in this idealization. The source's drive and relative
detuning must **both** be off ($\Omega=\delta=0$); otherwise a coherent
term can mix dark and bright states. A remaining known code-preserving
Hamiltonian must be corrected. Unknown dephasing, heating, leakage and
coupling errors require their actual channel. The experiment does not
supply a coherent history selector or a nondestructive jump port.

**Ground-preserving words, bath records and probes.** Let the input code
lie in vacuum $G$ plus $N$ labelled single excitations. Each complete
physical word $c=0,1$ has the full input-independent prepared-bath dilation

$$
\begin{aligned}
V_c|G,0_B\rangle&=|G,e_0\rangle,\\
V_c|j,0_B\rangle&=\sum_i|i\rangle|\eta_{c,ij}\rangle
                    +|G\rangle|\ell_{c,j}\rangle,\\
\langle e_0|\ell_{c,j}\rangle&=0,\qquad
(K_c)_{ij}=\langle e_0|\eta_{c,ij}\rangle.
\end{aligned}
\tag{LM1}
$$

The common **pure vacuum record** $e_0$, including the vacuum arm phase,
is essential. A known relative phase may instead be removed by a paid
control. Arbitrarily many survivor records and loss/survivor-record
overlaps are allowed. Only the complete word's final output on this input
space must lie in vacuum plus one excitation; intermediate sectors can
be arbitrary. Isometry gives the displayed orthogonality. In particular,
$\mathcal E_c(|j\rangle\langle G|)=K_c|j\rangle\langle G|$, but
$\mathcal E_c(|j\rangle\langle j|)$ can contain vacuum/excitation
coherence. Each ordinary word must reproduce the same
initial bath preparation, pulse/clock history and output modes as its
coherent alternative. Equal deadlines include any actual idle evolution.
The selector must implement these full dilations coherently, with the
vacuum arms as displayed. Reduced channels or a master equation alone do
not establish that interface. Independent loss-only ports give
$K_0=K_BK_A$, $K_1=K_AK_B$ as a special case, not a model for every reused
waveguide.

Choose an independent random sign $\xi\in\{-1,+1\}$ and prepare the
product probe $(G+\xi|j\rangle)/\sqrt2$, with the other sites ground.
Retain that sign and all local outcomes. Phase-cycled readout gives

$$
(K_c)_{ij}=\mathbb E[\xi X_i]+i\mathbb E[\xi Y_i].
\tag{LM2}
$$

The sign differs from the upper-off-diagonal Schur convention in (DQ2).
A coherent vacuum/excitation phase reference and calibrated readout phases
are resources. The random sign cancels the entire diagonal-input output,
including any vacuum/excitation coherence. An uncycled probe can be biased.
These means identify the coherent transfer matrix under (LM1); they do
not verify the model or identify its full channel. For example, scalar amplitude damping with survival
amplitude $a$ and occupancy dephasing with coherence $a$ have identical
local $X/Y$ responses, but excited populations $a^2$ and $1$. At $a=3/5$
their uncorrected $F_e$ are $16/25$ and $4/5$. Population records distinguish
them. The matrix nevertheless suffices for the paid collector below.

**Pure-loss specialization and decoder options.** If every survivor has
the same bath state $e_0$, then
$\eta_{c,ij}=(K_c)_{ij}e_0$ and
$\langle\ell_{c,i}|\ell_{c,j}\rangle
=\delta_{ij}-(K_c^\dagger K_c)_{ij}$. In this stricter model the
uncycled version of (LM2) is unbiased. It is not implied by system
excitation preservation; additional bath records can dephase survivors.
Encode $|0\rangle\mapsto G$, $|1\rangle\mapsto v$, with $\|v\|=1$.
Rotate a selected unit output mode $u$ to one output qubit and trace the
other modes. The complete logical/reference channel is amplitude damping
with amplitude $h=u^\dagger K_cv$: its off-diagonal multipliers are $h^*$
and $h$, and its excited population is $|h|^2$. This follows from the
dilation $|0\rangle\mapsto|0\rangle|e_0\rangle$,
$|1\rangle\mapsto h|1\rangle|e_0\rangle+|0\rangle|\xi\rangle$,
where $\langle e_0|\xi\rangle=0$ and
$\|\xi\|^2=1-|h|^2$. Its $F_e=|1+h|^2/4$ becomes
$(1+|h|)^2/4$ with the known output phase
$\operatorname{diag}(1,e^{-i\arg h})$. Exact leading singular modes attain
$h=\|K_c\|$. This optimizes the specified rotate/discard family only;
retained flags and other recovery maps must still be considered.

**Full retained-control upper bound.** With an initially independent
$|+\rangle$ order control, put

$$
|c_0\rangle=|+,G\rangle,\qquad
T v=\frac{|0\rangle K_0v+|1\rangle K_1v}{\sqrt2}
       =|\psi\rangle.
\tag{LM3}
$$

Tracing the bath gives the following four logical input matrix units:
$S_{00}=|c_0\rangle\langle c_0|$,
$S_{10}=|\psi\rangle\langle c_0|$, $S_{01}=S_{10}^\dagger$, and
$S_{11}=M\succeq0$, with $\operatorname{Tr}M=1$. This includes all
survivor/loss states, their coherences and cross-history record overlaps.
Tensor each term with the
corresponding arbitrary input/reference coefficient $\rho_{ij,R}$.
This specifies the full input/reference map without discarding $M$.

For any deterministic joint CPTP decoder $\mathcal R$,

$$
F_e(\mathcal R S)=\frac{A+B+2\operatorname{Re}z}{4},\quad
A=\langle0|\mathcal R(S_{00})|0\rangle\le1,\quad
B=\langle1|\mathcal R(S_{11})|1\rangle\le1,
\tag{LM4}
$$

where $z=\langle1|\mathcal R(|\psi\rangle\langle c_0|)|0\rangle$.
For decoder Kraus operators $R_j$, Cauchy--Schwarz gives

$$
|z|\le
\sqrt{\sum_j|\langle1|R_j\psi\rangle|^2}
\sqrt{\sum_j|\langle0|R_jc_0\rangle|^2}
\le\|\psi\|.
$$

Thus arbitrary fresh decoder ancillas and joint control/target processing
are included in the bound

$$
F_e(\mathcal R S)\le\frac{1+\|Tv\|}{2},\qquad
\|Tv\|\le\max_c\|K_cv\|,\qquad
\|T\|^2=\left\|\frac{K_0^\dagger K_0+K_1^\dagger K_1}{2}\right\|
\le\max_c\|K_c\|^2.
\tag{LM5}
$$

This is an all-attempt deterministic-fidelity comparison within the
ground-plus-one-mode family and the stipulated selector. It is not a
conditional-fidelity/yield frontier, an equality of flagged instruments,
or a bound on encodings that put the input into a helper before exposure.

The common-record premise cannot be replaced by reduced ground
preservation. For orthogonal bath states $e_0,e_1$, define code isometries
$W_0|0\rangle=|0,e_0\rangle$, $W_0|1\rangle=|1,e_1\rangle$ and
$W_1|0\rangle=|0,e_1\rangle$, $W_1|1\rangle=|1,e_0\rangle$.
Both reduced words are complete dephasing, with coherent transfer zero,
but coherent selection followed by control $X$ readout gives visible maps
$\rho/2$ and $Z\rho Z/2$, including every reference. Correcting the
minus flag recovers identity. The two words' vacuum bath records differ,
so this does not satisfy (LM1).

This particular exception also has a paid ordinary compiler:
$W_1=(X_L\otimes I_E)W_0X_L$ on the code. Known controlled-$X_L$ gates
before and after one actual $W_0$ execution therefore give exactly the
same joint control/logical/bath isometry and corrected flags. The logical
number-changing drive, coherent controlled port, helper lifetime, phase,
clock, readout/reset and correction must be supplied and priced. The
identity grants no extension outside the code or unseen bath access.
It is a necessity witness, not a native advantage from unequal records.

**Paid ordinary attainment.** Supply one protected meter and known
controlled excitation parity $C_\Pi$, with
$\Pi=\prod_j Z_j$ equal to $+1$ on $G$ and $-1$ on every excitation.
Apply $C_\Pi$ before and after the complete chosen ordinary word.
In an environment basis containing $e_0$, write each Kraus operator as
$L_\alpha=\delta_{\alpha0}|G\rangle\langle G|
 +S_\alpha+|G\rangle\langle\ell_\alpha|$, with
$S_0=K_c$ and $\ell_0=0$. The two flag Kraus operators are
$(L_\alpha\pm\Pi L_\alpha\Pi)/2$: their plus parts are vacuum/survivor
blocks and their minus parts are final-loss rows.
The standard [ordinary parity sandwich](architecture-baselines.md#nr-r06-cat-reservoir-parity)
therefore leaves the helper plus on final survival and minus on final
loss, without measuring the unknown initial logical parity. This can
remove loss/survivor coherence from $\mathcal E_c(|v\rangle\langle v|)$;
it preserves $\mathcal E_c(|v\rangle\langle G|)$. No equality with the
original unflagged channel is asserted in this noncovariant case.
It includes unresolved records and internal reabsorption. This is an
application of an established check primitive; see
[Gonzales et al.](https://doi.org/10.1038/s41598-023-28109-x).

For $s=\|K_cv\|$, rotate $K_cv/s$ to the output mode, choosing any mode
when $s=0$. Collect every surviving excitation into that output qubit:
after alignment, apply CNOT from each other site into output site $t$,
then discard/reset the other sites. On the input vacuum/one-excitation
space this implements the trace-preserving decoder
$D_0=|0\rangle\langle G|+|1\rangle\langle t|$ and
$D_i=|1\rangle\langle i|$ for $i\ne t$. The literal CNOT circuit sends
$|i\rangle$ to the **two-excitation** garbage state $|i,t\rangle$.
These $N-1$ gates are not passive mode merging or number-preserving optics.
Finally re-excite the output on the loss flag. With
$p_S=\sum_\alpha\|S_\alpha v\|^2$ and $p_L=1-p_S$, the exact maps are

$$
\begin{aligned}
\mathcal O_+(\rho)&=|0\rangle\langle0|\otimes\rho_{00,R}
 +s|1\rangle\langle0|\otimes\rho_{10,R}
 +s|0\rangle\langle1|\otimes\rho_{01,R}
 +p_S|1\rangle\langle1|\otimes\rho_{11,R},\\
\mathcal O_-(\rho)&=p_L|1\rangle\langle1|\otimes\rho_{11,R}.
\end{aligned}
\tag{LM6}
$$

Since $p_S\ge s^2$, the plus map is CP: its logical Kraus can be
$\operatorname{diag}(1,s)$ and $\sqrt{p_S-s^2}|1\rangle\langle1|$.
Their sum is dephasing with coherence $s$, giving $F_e=(1+s)/2$ on
every attempt. Choosing the better actual word already reaches or exceeds
(LM5) for the **same input mode**; optimizing modes preserves the
inequality. No negative flag is discarded. The meter must be available in
addition to any routing degree that must stay fixed to implement the
ordinary word. Neither a path qubit nor demonstrated local drives alone
grant these controlled parity gates. A supplied logical SWAP gives direct
helper storage; the conditional one-bit transfer below needs less than a
SWAP but requires a spectator-safe input readout instrument.
For an unflagged endpoint, a supplied coherent helper-conditional active
recovery followed by helper discard replaces intermediate readout; its
gate and reset costs remain. In the pure-loss case $p_S=s^2$, and the
collector is unnecessary with the exact output mode: the simpler
rotate/discard decoder gives the same two flags.

Retaining control genuinely matters to the proof. For two scalar
amplitude-damping contacts with amplitude $3/5$, passive no-loss output
alignment gives $F_e=289/625$. Re-exciting only the native minus loss flag
gives $297/625$; its loss probability is $(32/625)\rho_{11}$.
Therefore the passive amplitude-damping value is **not** a bound on joint
decoding. Ordinary (LM6) instead attains $17/25$, the valid (LM5) bound in
this example.

**Calibration and the complete ledger.** A sufficient matrix-learning
schedule uses $n$ independent launches for each of $N$ probes and all-$X$
or all-$Y$ readout, with the independent sign on each launch. Signed local
outcomes remain in $[-1,1]$. Hoeffding over $2N^2$ means gives

$$
\|\widehat K-K\|\le\|\widehat K-K\|_F
\le2N\sqrt{\log(4N^2/\delta)/n}.
\tag{LM7}
$$

Taking $n\ge4N^2\eta^{-2}\log(4N^2/\delta)$ suffices for operator error
$\eta$, at $2Nn$ actual storage launches, $2N^2n$ local outcomes and
one retained sign per launch. Empirical singular modes give
$|h-\|K\||\le2\eta$; since $|1+h|^2/4$ is 1-Lipschitz on the unit disk,
their pure-loss rotate/discard fidelity regret is at most $2\eta$.
Learning both actual words changes the logarithm to
$\log(8N^2/\delta)$ and doubles the setting groups. For (LM6), choosing
the larger empirical singular value gives
$\operatorname{Re}h\ge s_{\rm best}-2\eta$. The population collector
restores both logical populations exactly even with a nonexact output
mode. Thus its score $(1+\operatorname{Re}h)/2$ is at least
$(1+s_{\rm best})/2-\eta$. Without the collector, the stricter pure-loss
parity/re-excitation decoder can instead lose an uncollected surviving
component of norm at most $\eta$; its bound is
$(1+s_{\rm best})/2-\eta-\eta^2/4$. These are different control families.
These are sufficient bounds, not sample optimality or free matrix advice.
For a supplied fixed production encoder, targeted logical-plus probes can
learn just $K_0v,K_1v$; full matrix learning is not compulsory. Such a
known phase-cycled probe can be entangled across sites, using the paid encoder, though
it needs no held reference.

Charge every word's actual contact count, elapsed time and bath/history
preparation; two contacts apply only to the two-slot specialization.
The ordinary recovery additionally pays two controlled global parities
(one implementation has $2N$ controlled-$Z$ gates), coherent meter
storage, $N-1$ full population-collection CNOTs when needed, active
excitation and its energy, garbage reset, and either coherent feedback or
readout latency. Mode preparation/rotation, discarded modes,
phase references, $N$ local readouts per training launch and classical
matrix storage/decomposition count. Native routing, buffers and all
rejected attempts count too. Independent launches, SPAM, drift and model
transfer require validation; a single-shot channel marginal does not
justify calibration reuse. These ideal endpoint inequalities alone do
not establish a native wall-clock or gate-cost optimum.

<a id="nr-r14-helper-transfer"></a>

**Input transfer and the retained-helper readout port.** A one-qubit
memory can have a stronger ordinary comparator than (LM6). Suppose a
known, paid, vacuum-preserving input mode operation sends $v$ to one
site $j$; no such operation is needed for a localized input. Suppose also
that phase-resolved $X_j$ readout can leave a separate helper's unknown
state intact, that the helper admits the indicated Clifford corrections
and independent storage channel, and that it can be the delivered logical
output. These are joint production ports, not consequences of (LM2)'s
calibration means or of an alignment gate supplied only at the output.

Prepare the helper in $+$, apply one controlled excitation parity and
measure $X_j$ before the waiting interval. For result $a=0,1$, its raw
logical-input-to-helper Kraus operator and correction are

$$
T_a=H_C Z^a/\sqrt2,\qquad R_a=Z_C^a H_C,\qquad
R_aT_a=I/\sqrt2.
\tag{LM8}
$$

Thus each recorded branch is exactly $\rho_{LR}/2$, with the logical
output now in $C$. The measured payload is independent of that unknown
state; any subsequent channel confined to it can be discarded. If the
corrected helper has storage channel $\Lambda_C$, each branch instead
is $(\Lambda_C\otimes\mathrm{id}_R)(\rho_{LR})/2$. No noisy-word
calibration, population collector or target-to-helper SWAP is needed for
this identity. This is the established
[one-bit teleportation primitive of Zhou, Leung and Chuang, Section II](https://arxiv.org/pdf/quant-ph/0002039v2),
applied to the stated memory interface, not a new teleportation mechanism.

The complete readout instrument matters even when its POVM is known.
Follow the good $X_j$ instrument by $Z_C$ dephasing before $R_a$.
Every flag probability is unchanged for every joint data/helper input,
yet $R_a Z_C T_a=(-1)^a X/\sqrt2$ makes the corrected branch
$\Delta_X(\rho_{LR})/2$, where
$\Delta_X(\rho)=(\rho+X\rho X)/2$. Its summed logical channel is
entanglement breaking, with $F_e=1/2$. A helper used or reset by the
payload readout therefore cannot silently be treated as a spectator.
More generally, raw helper $Z$ dephasing of visibility $r$ becomes
logical $X$ dephasing. Follow it by corrected-helper storage $Z$
dephasing of visibility $\kappa$; the all-attempt fidelity is
$(1+r)(1+\kappa)/4$. The axes depend on when the noise occurs.

Charge input alignment, one controlled parity (or one site-selective CZ
when that port exists), the payload readout, one classical bit, helper
correction/reset, its complete protected lifetime and delivery. Include
all transfer and waiting times in the same deadline. Returning the state
to a prescribed physical target requires an additional supplied transfer;
delivering $C$ does not prove that endpoint. For independently certified
half-diamond transfer error at most $\epsilon$ and actual helper
entanglement fidelity $f_C$, contractivity and the Bell-test bound give
$F_e\ge f_C-\epsilon$. Transfer error includes SPAM, spectator
disturbance, gates and feedforward. It must be certified on the joint
instrument, not estimated from the flag counts. When
$f_C-\epsilon\ge(1+s_{\rm best})/2$, this paid bypass already reaches
the ideal-selector upper bound (LM5). For ideal transfer and the stated
$Z$-dephasing helper this sufficient condition is $\kappa\ge s_{\rm best}$.
This is a conditional cost comparison, not an assertion that any cited
dark-state experiment provides that helper or readout port.

<a id="nr-r14-two-qubit-deadline"></a>

**Two logical qubits at a fixed storage deadline.** Increasing the input
size avoids storing the entire input in one helper, but still requires
ordinary codes and partial helper storage. A concrete next model is
[Du, Guo and Ma's four-transmon array, v1](https://arxiv.org/html/2605.12442v1).
Its strong waveguide decay is enabled by flux modulation, so storage with
that modulation off must be compared at the same deadline. The reported
hold excludes two 244 ns ramps. The supplement's S10/A.1 and E.3 use
different intrinsic Purcell rates, about $2\pi\times2$ and
$2\pi\times10$ kHz; S13 omits local dephasing. Those passages do not
fix one predictive arbitrary-input storage channel without reconciling
the rate convention and measuring the relevant joint dephasing process.
Known-state preparation does not supply an unknown-state encoder or a
coherent order selector.

There is an exact ordinary limiting comparison. On four two-level spins,
write $J_-=\sum_i\sigma_i^-$ and $J_+=J_-^\dagger$. The orthogonal vectors

$$
\begin{aligned}
u_0&=|0101\rangle-|0110\rangle-|1001\rangle+|1010\rangle,\\
u_1&=2|0011\rangle-|0101\rangle-|0110\rangle
      -|1001\rangle-|1010\rangle+2|1100\rangle
\end{aligned}
$$

have squared norms 4 and 12. Thus
$P=u_0u_0^\dagger/4+u_1u_1^\dagger/12$ is a rank-two projector and
$J_\pm P=0$. Every collective dissipator
$\gamma_-(t)\mathcal D[J_-]+\gamma_+(t)\mathcal D[J_+]$ vanishes on
all four code matrix units. If the Hamiltonian preserves $P$, correct
its known logical action. One logical qubit in this standard singlet
code and another in an actually protected helper then preserve all two-
logical-qubit/reference operators. This ideal noiseless-code comparison
is not a claim about the complete transmon device.

Indeed, its nominal hopping already breaks that simple code. In
$\widetilde H=\sum_{i<j}j_{ij}
(\sigma_i^+\sigma_j^-+\sigma_i^-\sigma_j^+)$, use the dimensionless
numerical Table S1 cycles-MHz values $j_{01}=j_{23}=5.86$, $j_{12}=5.89$,
$j_{02}=j_{13}=0.60$, $j_{03}=0$. The exact projected identity is

$$
\|(I-P)\widetilde H P\|^2=\frac{277759}{15000}>0.
\tag{LM9}
$$

To check it directly, the complementary-pair cut weights are
$A=7.09$, $B=17.61$, $C=12.92$ for $01|23$, $02|13$, $03|12$.
The leakage Gram has range along the normalized two-excitation Dicke
vector and nonzero eigenvalue
$(B-C)^2/6+(2A-B-C)^2/18$, giving (LM9). The hopping Hamiltonian obeys
$H_{\rm XY}/\hbar=2\pi\,\mathrm{MHz}\,\widetilde H$. This is a coherent leakage
coefficient, not a logical lifetime or fidelity curve. A known final
inverse does not remove records acquired while a state leaves the code.
In the full three-level model, additional double-occupancy outputs are
orthogonal to this binary-sector leakage, so they cannot cancel it.

A measured single-target channel gives another paid two-qubit benchmark:
store one logical qubit in the helper and the other in that target. For a
declared stationary two-level thermal-relaxation/phase model, let $0\le p\le1$ be
the stationary excited population, $0\le r\le1$ the relaxation amplitude
and $|\chi|\le1$ the additional coherence factor. Its complete images are

$$
\begin{aligned}
E_{00}&\mapsto[1-p(1-r^2)]E_{00}+p(1-r^2)E_{11},\\
E_{11}&\mapsto(1-p)(1-r^2)E_{00}+[p+(1-p)r^2]E_{11},\\
E_{10}&\mapsto r\chi E_{10},\qquad
E_{01}\mapsto r\chi^*E_{01}.
\end{aligned}
\tag{LM10}
$$

Tensoring the helper identity specifies all 16 logical matrix-unit images
and all reference extensions. It gives
$F_{e,4}=(1+r^2+2r\operatorname{Re}\chi)/4$, independent of $p$;
a learned phase replaces $\operatorname{Re}\chi$ by $|\chi|$.
Measuring the second input in $Z$, saving its bit and preparing it at
delivery instead gives the distinct classical fallback
$\mathrm{id}\otimes\Delta_Z$ with $F_{e,4}=1/2$. Both require actual
helper transfer/storage and all encoder, reset, readout and timing costs.
A Ramsey $T_2^*$ alone determines neither $\chi$ for the production
waveform nor echo performance.

For the independent product-slot model with at least one entanglement-
breaking slot, the [retained-output rank bound](communication.md#nr-r10)
gives $F_{e,4}\le1/2$ after arbitrary receiver decoding, even in each
normalized accepted branch. The paid partial-helper/classical fallback
therefore saturates that endpoint when its transfer ports exist. The
rank premise concerns the complete available slot, including useful
records; an averaged marginal or a shared bath does not establish it.
No such slot decomposition is inferred for the four-transmon device.

The intrinsic two-level jump model itself offers a rate-disambiguation
test: from the all-ground state, its initial excitation-number slope is
$4n_p\gamma_p+\sum_i n_i\gamma_{{\rm nr},i}$ for collective upward
coefficient $n_p\gamma_p$ and the four local upward coefficients.
Measure that heating together with decay under the same modulation-off
conditions; do not fit a logical score by silently selecting one rate
recipe. Finite readout time, resonator dynamics and the validity of this
reduced model also require checks.

The next useful decision is the complete two-logical-qubit retention
channel at a fixed wall time under modulation-off storage, calibrated
code/helper encodings, refocusing and programmed schedules. Include loss,
thermal events and leakage in the full channel and keep all available
flags and rejects. Use held-out drift
episodes and include preparation, both ramps, decoding, helper survival,
calibration and reset. Only an actual pair of full history dilations
with their cross-history records can add a coherent-order comparison;
the source's Lindblad marginal is insufficient. These exact limits and
declared channel fixtures establish no device fidelity or switch win.
The [ordinary symmetry-control component](methods/collective-memory-control.md)
supplies the next conditional comparator: finite-period/pulse errors,
full three-level subsystem decoding, residual local-loss limits and
an explicit control/deadline ledger. Its ideal permutations are
additional paid ports, not demonstrated gates on this device.

**Fresh-slot flags, prior and remaining scope.** For independent loss-only
ports, $M_{ij,-}=(B_jA_i-A_iB_j)/2$ kills $G$. On a ground-plus-mode code
every such Kraus operator has only its logical-$1$ column, so the minus
map is $\Xi\otimes\rho_{11,R}$ and is entanglement breaking. It cannot
herald a uniform positive-weight unknown-qubit unitary. This does not
make the entire retained-control channel entanglement breaking. A zero
minus rate is also insufficient: collective contacts on the same bright
mode preserve a different dark mode, while contacts on two orthogonal
bright modes can damp it with the same zero flag. Ordinary production
population and Ramsey probes resolve that example.

For rank-one collective bright projectors $P_a,P_b$ with survival
amplitudes $x,y$, the no-jump minus operator on a wholly one-excitation
code is $(1-x)(1-y)[P_b,P_a]/2$. Its rank is at most two and its nonzero
squared singular value is
$(1-x)^2(1-y)^2z(1-z)/4\le1/16$,
$z=|\langle a|b\rangle|^2$. Such a dual-rail branch is outside the
ground-plus-mode entanglement-breaking statement. The following separate
comparison includes its vacuum background and ordinary on-carrier modes;
no unrestricted rank-one-channel bound follows.

<a id="nr-r14-dualrail-projector-routes"></a>

**Dual-rail projector filters and the complete carrier.** Let the unknown
qubit lie entirely in two one-excitation modes, take $K_A=P_a$, $K_B=P_b$
to be rank-one Hermitian projectors, and initialize an independent order
control plus. Write $c=|\langle a|b\rangle|$. The direct-switch survivor
isometry and its effect are

$$
N=\frac{|0\rangle P_bP_a+|1\rangle P_aP_b}{\sqrt2},
\qquad N^\dagger N=\frac{c^2}{2}(P_a+P_b).
\tag{DR1}
$$

If the order control is a **separate surviving register**, loss to system
vacuum can still map the input coherently into that register. In general
its loss Kraus maps are the two-row matrices
$J_{A,\mu}=(a_\mu,a_\mu K_B)^T/\sqrt2$ and
$J_{B,\nu}=(b_\nu K_A,b_\nu)^T/\sqrt2$, where the symbols inside each
parenthesis are rows and
$\sum_\mu a_\mu^\dagger a_\mu=I-K_A^\dagger K_A$,
and likewise for $B$. They need not have rank one. Hidden records are
summed as CP maps, not amplitudes. The ground-plus-mode minus argument
must not be applied to this different code and output.

For **one physical photon** carrying both binary degrees, the space is
$\mathbb C|{\rm vac}\rangle\oplus(C\otimes D)$: absorption removes both
registers. A compatible completion has survivor $N$ and vacuum loss effect
$I-N^\dagger N$. On every input/reference state, its rejected block is
$|{\rm vac}\rangle\langle{\rm vac}|\otimes
\operatorname{Tr}_D[((I-N^\dagger N)\otimes I_R)\rho_{DR}]$.
There is no retained path qubit in that block. An actual timed router can
have further records or loss; a reduced target channel does not specify it.

Any exact heralded recovery of the full unknown qubit from the survivor,
allowing arbitrary joint output processing and many corrected success
records, has total effect $pI\preceq N^\dagger N$. Indeed each corrected
success Kraus composed with $N$ must be proportional to identity, and
their total recovery effect is at most identity. Vacuum-loss Kraus maps
have rank one; they cannot contribute a nonzero rank-two identity Choi
branch without extra coherent environment access or surviving memory.
Consequently

$$
p\le\lambda_{\min}(N^\dagger N)
   =\frac{c^2(1-c)}2\le\frac{2}{27},\qquad
\frac2{27}-\frac{c^2(1-c)}2
   =\frac{(3c-2)^2(3c+1)}{54}\ge0.
\tag{DR2}
$$

This fixes the direct-switch input control and code; it does not bound
protocols that first put data into the control. The selected minus
survivor has weight at most $1/16$, but minus alone also has a vacuum
background. For $P_a=P_0$, $P_b=P_+$, its survivor is $-iY/4$, while its
total flag effect is $\left(\begin{smallmatrix}2&-1\\-1&4\end{smallmatrix}\right)/16$,
rather than $I/16$. A retained-survival herald or an explicitly late
erasure endpoint must distinguish those outcomes; a destructive click
consumes the payload. The projector constants are not bounds for all
rank-one contractions: $K_A=|0\rangle\langle1|$,
$K_B=|1\rangle\langle0|$ give $M_+=I/2$, $M_-=-Z/2$.

There is a stronger ordinary comparator when the following **success-port
and codec premise** is supplied. The same four modes admit known logical
$\operatorname{SWAP}(C,D)$ and local mode Paulis; a fixed-route contact
has selected block $I_C\otimes K$. Accepted bath/clock records and phases
must preserve coherence between the data-carrying $C$ modes. One explicit
complete single-carrier slot is

$$
F_0=1_{\rm vac}\oplus(I_C\otimes K),\qquad
F_{c,\mu}=|{\rm vac}\rangle(\langle c|\otimes q_\mu),
\quad\sum_\mu q_\mu^\dagger q_\mu=I-K^\dagger K.
\tag{DR3}
$$

Lost path labels can remain in the environment; no controller survives
rejection. Four modes or equal pass probabilities alone do not grant
(DR3). A time-bin realization can need stationarity, buffers and path-phase
matching. A distinct matter control instead needs a paid coherent transfer
port; a provider-owned inaccessible control is a different access model.

Move unknown $D/R$ into $C$ by SWAP, leaving the old known control state
$\chi$ in $D$. Independently choose Paulis $P,Q$ uniformly from
$I,X,Y,Z$; apply $P$, filter $A$, $Q$, filter $B$, and SWAP back. For each
retained seed pair the success output is exactly
$|\xi_{PQ}\rangle\langle\xi_{PQ}|_{\rm junk\,C}\otimes\rho_{DR}/16$,
where $\xi_{PQ}=K_BQK_AP\chi$. Pauli twirling gives

$$
\mathcal S_{\rm ordinary}(\rho_{DR})
 =\frac{\operatorname{Tr}(K_A^\dagger K_A)
              \operatorname{Tr}(K_B^\dagger K_B)}4\rho_{DR}
 =\tfrac14\rho_{DR}
\tag{DR4}
$$

for unit-strength rank-one blocks, including fresh unknown correlated
axes independent of the input and random seeds. The proof uses
$\sum_PP|\chi\rangle\langle\chi|P=2I$ and
$\sum_QQXQ=2\operatorname{Tr}(X)I$. It retains all 16 classical seed
records and the aggregate erasure probability $3/4$. Independent seeds
matter; reusing one can give zero transmission for orthogonal filters.
Thus this qualified ordinary interface gives ideal exact-qubit weight
$1/4$, exceeding (DR2) for the direct projector switch. With calibrated
bright modes, ordinary alignment before each filter instead gives weight
$1$. Scaled projectors multiply these weights and (DR2) by their two
intensity transmissions.

This comparison charges two SWAP permutations, two Pauli choices and their
records, fixed-route optics, both occupied contacts, every buffer/clock
and phase requirement, filter/router loss and the same retained-survival
herald or erasure endpoint. Optional harmful contacts may also be avoided.
It establishes no actual hardware winner, arbitrary-code/fidelity/capacity
frontier, or extension to a separately surviving control after absorption.

Perfect quantum communication activated by switching entanglement-breaking
channels is already established [prior](https://doi.org/10.1088/1367-2630/abe7a0),
including a provider-owned control. This bounded loss/codec comparison
does not claim a new activation mechanism or impose that control-access
restriction on local memory hardware.

[Goswami et al.'s archived v1 amplitude-damping calculation](https://arxiv.org/abs/1807.07383v1)
already retains control/target information; that subsection is absent from
the publication-associated v5. Complete damping loses phase while full
control records can retain population. [Liu, Ebler and Dahlsten](https://doi.org/10.1103/PhysRevLett.129.230604)
study full-output classical information with thermodynamic control costs.
[Tang et al.](https://arxiv.org/abs/2406.02236v1) simulate thermalization
using a surviving photon's path and polarization. Physical absorption
destroys both on-carrier optical registers; it does not leave a separate
path qubit. A separate surviving control, or a different controlled
vacuum/loss instrument, must be physically supplied and priced. These
results and the ordinary parity-check prior preclude a novelty claim
based merely on retaining the control or detecting amplitude damping.

The [loss-memory guard](checks/architecture/loss_memory_qualification_guards.py)
replays finite channel, encoded/reference, flag and recovery fixtures in
the existing backaction job. The general shared-history, arbitrary-decoder,
concentration and physical-access arguments remain analytic. The next
candidate must supply a useful task beyond this family, distinct vacuum
bath histories, final leakage or other justified structure, its full
selector and a benefit after ordinary learning, memory, checks and routing
have been priced. Extra survivor records alone do not evade the paid
population-collection comparison; departures from its premises do not by
themselves establish an advantage.

### Direct calibration and measurement-record prediction

For a specified pure-dephasing control word $y$, restore its known sensor frame and write its actual joint evolution as $\operatorname{diag}(U_{y,0},U_{y,1})$. Ordinary preparation in $|+\rangle$ and $X/Y$ readout measure

$$
L_y=\operatorname{Tr}[\rho_EU_{y,1}^\dagger U_{y,0}],
\qquad F_e(\text{identity memory})=\frac{1+\operatorname{Re}L_y}{2}.
\tag{16}
$$

The $X$-plus outcome is itself a Bernoulli sample with mean $F_e$. With independent repeatable initial bath/history preparations, $n\ge\log(2/\delta)/(2\epsilon^2)$ trials estimate it within $\epsilon$ with failure probability at most $\delta$. A known target **unitary** can instead be tested by a clean calibration Bell pair and the corrected Bell projector; that reference is held during the sequence and measured afterwards. This does not grant access to the arbitrary passive $R$ in (3). A finite list of $M$ schedules needs at most $O(M\epsilon^{-2}\log(M/\delta))$ direct trials by a union bound. Each trial pays for the actual schedule, pulses, duration and history preparation.

This comparator avoids full bath tomography. It is not an optimal sample bound. A held-out history that cannot be run or reproduced is a distinct prediction task whose restriction must be stated. Reproducing a history of probability $p_h$ can add a factor of order $1/p_h$ in attempts. Uncontrolled persistent drift invalidates an i.i.d. error bar. A switch diagnostic consumes and changes the same bath and must establish its own transfer to the target history.

For a known finite-dimensional target unitary $W$, a direct logical Bell
test also gives a background-free ordinary alarm. Run the actual complete
production word on one half of a clean logical Bell pair, include its
specified decoder and exposed records, correct the known target in the
test, and measure the Bell projector. The failure probability is
$e=1-F_e$, independent of any microscopic bath representation. Under
the promise $e=0$ versus $e\ge\epsilon$, declaring failure at the first
rejected Bell test has one-sided error at most
$(1-\epsilon)^N\le e^{-N\epsilon}$. Thus

$$
N\ge\frac{\log(1/\delta)}{\epsilon}
\tag{HO4}
$$

actual production words suffice, given independent repeated histories.
Preparation, logical Bell gates/readout, the known target test and the
word's execution remain charged; identity storage needs no unknown
inverse. If the word itself heralds, the pass probability is the
unnormalized Bell-good weight $q$, and rejection counts in $e=1-q$.
Conditional accepted fidelity is not this Bernoulli mean. This ordinary
null must be included when comparing a rare-event switch signal with a
constant-variance overlap estimator. In (HO3), ordinary sensor $X$
readout already has means $3/4$ and $1/2$, so a separate Bell reference
is unnecessary. Threshold $5/8$ has error at most $e^{-N/32}$; hence
$N\ge32\log(1/\delta)$ direct four-contact words identify the preferred
schedule. This is an achievable count, not a claim of sample optimality
or independence for one unreset bath.

For prediction across many histories, the ordinary comparator is also
stronger than full tomography. [White, Jurcevic, Hill and Modi, PRX
**15**, 021047 (2025)](https://doi.org/10.1103/PhysRevX.15.021047)
([primary version](https://arxiv.org/html/2312.08454v2)) learn
self-consistent tensor-network models including control correlations and
bath spillage, test held-out circuits and optimize DD on IBM devices.
One numerical example uses $6000\times1024=6{,}144{,}000$ training
windows before validation. Useful compressed structure and variational
fit are substantive assumptions; this is not a worst-case polynomial
sample theorem for every bath. These costs and the actual drift window
can be measured rather than replaced by a full-bath tomography estimate.

A concrete native comparison can select two named memory/DD histories,
use held-out logical Bell performance as the decision endpoint, and
compare the candidate diagnostic with phase-cycled fourth-order
spectroscopy, direct target nulls and a validated compressed-memory
predictor. It must establish transfer across the same conditional bath
histories, including sensor disturbance and history preparation. A
candidate beyond the ordinary identities here needs two actual unknown
joint sensor/bath ports outside the longitudinal echo and known-local-
intervention closures, with a coherent routing instrument and all
emitted-time records. Classically choosing two microwave waveforms does
not supply that off-diagonal interface. Contact duration, readout,
reset, helper lifetime and routing faults enter the same ledger; a
different high-order correlator alone does not establish a cheaper
production decision.

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

<a id="nr-r14-record-overlap-qualification"></a>

### Inaccessible records bound the complete coherent-history output

There is a quantitative version for an actual controlled-history
interface. Fix its two branch isometries $W_0,W_1$, their common finish,
and the same initial state, including the physical bath and all
route/vacuum inputs. The independent selector starts in $|+\rangle$.
Purify the initial state and write the normalized branch vectors as
$|a\rangle,|b\rangle$ on $A\otimes E$. Here $A$ comprises the actual
retained output and coherent record systems, together with any **passive**
reference kept for analysis. The decoder never accesses that reference.
The inaccessible environment $E$ includes every discarded purifier,
emitted field, reset/amplifier copy and unavailable record. These are
the **actual joint branch dilations**; reduced channel maps alone do
not specify their cross term.

Put $X=\operatorname{Tr}_E|a\rangle\langle b|$. The controlled output
and its dephased-selector comparator have identical diagonal blocks,
so their half trace distance is
$$
\Delta=\frac12\left\|
\frac12\begin{pmatrix}0&X\\X^\dagger&0\end{pmatrix}
\right\|_1
=\frac12\|X\|_1.
\tag{RO1}
$$
The equality follows because the off-diagonal Hermitian block has
singular values equal to those of $X$, each repeated twice.
The comparator is an ordinary fair random choice of the two actual
native histories, retaining its classical selector and every output.

For complete orthogonal pointer projectors $\{\Pi_r\}$ on $E$
(including an unrecorded complement when needed), $\sum_r\Pi_r=I_E$, let
$|a_r\rangle=(I_A\otimes\Pi_r)|a\rangle$ and similarly $|b_r\rangle$,
with actual tag probabilities
$P_0(r)=\|a_r\|^2$, $P_1(r)=\|b_r\|^2$. Distinct pointer sectors have
zero cross partial trace. Variational trace norm and Cauchy–Schwarz give
$$
\begin{aligned}
\|X\|_1
&\le\sum_r\|\operatorname{Tr}_E|a_r\rangle\langle b_r|\|_1\\
&=\sum_r\sup_{U_A\ {\rm unitary}}
 |\langle b_r|(U_A\otimes I_E)|a_r\rangle|\\
&\le\sum_r\sqrt{P_0(r)P_1(r)},\qquad
\boxed{\Delta\le\frac12\sum_r\sqrt{P_0(r)P_1(r)}.}
\end{aligned}
\tag{RO2}
$$
The variational unitary is a mathematical norm certificate, not access
to the passive reference or the environment. Mixed inputs are already
covered by including discarded purifiers in $E$. Keeping an extra
purifier first and later discarding it instead gives an upper bound
by trace-distance contractivity.

Any common subsequent CPTP decoding/instrument, tensored with identity
on the passive reference, preserves the bound. Every bounded
$[0,1]$ **all-launch** payoff differs by at most $\Delta$, including
accepted Bell-good weight when leakage and rejection remain part of
the instrument. Conditional accepted fidelities require an additional
positive-yield normalization bound. For a declared channel interface
with fixed input-independent environment, a bound uniform over inputs
and passive references gives the corresponding half-diamond bound;
a one-input estimate is only that input's statement.

Disjoint inaccessible order/timing-tag laws give $\Delta=0$ and exact
equality with the ordinary mixture. Independent tensor-factor tags
with branch-state overlaps $\gamma_\ell$ contribute a factor
$\prod_\ell|\gamma_\ell|$. That factorization is an extra physical
premise: a one-cycle visibility does not establish an exponential
multi-cycle law for a correlated bath. Conversely, identical coarse
visible histograms do not certify interference; unobserved orthogonal
timing tags can still make $X=0$.

This bound does not assert that every dynamic-QEC or reset selector
has orthogonal records. A native proposal must supply its complete
cross-history instrument, with coherent buffers or erased records
actually available and charged to both strategies. The
[logical-policy qualification application](methods/memory-code-verification.md#nr-r20-logical-policy-qualification)
separates that requirement from ordinary measured syndrome/reset
policies. Finite tag/cross-block and accepted logical-map fixtures are
checked in the existing [memory-qualification replay](checks/architecture/verify_memory_qualification.py);
(RO1)–(RO2), contractivity and physical interface assumptions remain
analytic.

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

<a id="nr-r14-recovery-records"></a>
#### Recovery records: module labels, clock labels and a monitored baseline

The complete-record premise in (32) matters for adaptive recovery. For two nominal rank-two instruments $A=\{K_a\}$ and $B=\{L_b\}$, a standard independent-module switch with initial helper $+$ has recorded trajectory maps generated by

$$
W_{ab}=\frac{|0\rangle\otimes L_bK_a+|1\rangle\otimes K_aL_b}{\sqrt2}.
\tag{RR1}
$$

The same module outcomes $a,b$ are paired between histories. Instead suppose a reused detector writes only first-window and second-window outcomes into orthogonal chronological registers. Its declared pure-ready record dilation gives

$$
T_{ab}=\frac{|0\rangle\otimes L_bK_a+|1\rangle\otimes K_bL_a}{\sqrt2}.
\tag{RR2}
$$

Thus its off-diagonal cross map is $\sum_{ab}L_bK_a\rho(K_bL_a)^\dagger/2$, whereas (RR1) gives $\sum_{ab}L_bK_a\rho(K_aL_b)^\dagger/2$. The ordered diagonal target channels agree; the complete helper/target instruments need not. Chronological records alone cross-pair module outcomes. They do **not** discard all unequal-label cross terms. If an independent module-labelled copy already exists and an additional chronological copy is discarded, the tags $|a,b\rangle$ and $|b,a\rangle$ instead keep only $a=b$ cross terms. These are different specified dilations. Extra axis-dependent tags can further distinguish the histories; none of these record models follows from two fitted reduced channels.

In the stated pure-ready dilation, a helper-controlled swap of the complete two chronological record registers in history $1$ converts (RR2) into (RR1), by relabelling $a,b$ in that history. This is a physical quantum record operation. Relevant purifications, copied timestamps and emitted fields must also be included; merely swapping two mixed outgoing bath marginals or deleting a classical log does not supply it. A proposed implementation must pay for capturing, storing, routing or erasing those records, including failures and inaccessible copies. Equation (32) remains valid for the actual chronological dilation without any such operation.

A sharp consistency test selects the **same actual instrument** at both windows, $K=L$. Every $T_{ab}$ then factors a helper $+$, for every input/reference. The independent-module self-switch instead has minus subchannel

$$
\Gamma_-(\rho)=\frac14\sum_{ab}[K_b,K_a]\rho[K_b,K_a]^\dagger.
\tag{RR3}
$$

On an admitted input subspace with projector $P$, the two constructions agree exactly if and only if $[K_b,K_a]P=0$ for all $a,b$. Necessity follows because zero minus probability on every pure input in $P$ is a sum of squared commutator norms; sufficiency follows by substituting the equal products in every trajectory. This tests the interface, not the usefulness of the minus flag.

There is also a full-output ordinary comparator beyond a code-input-only code-fixing argument. Let $\mathcal H=(|C\rangle\oplus|E\rangle)\otimes\mathcal L$, with arbitrary unknown logical payload $\mathcal L$ and an arbitrary passive reference. Define $V=|C\rangle\langle E|\otimes I_{\mathcal L}$, $D=P_C+sP_E$, $t=\sqrt{1-s^2}$, and one monitored correction round $K_0=D$, $K_1=tV$, where $0\le s<1$. Inputs may contain arbitrary code/error coherences; this channel does not fix them. The relations $DV=V$, $VD=sV$ and $V^2=0$ give the entire independent-module self-switch instrument:

$$
\begin{aligned}
\Gamma_{00}(\rho)&=|+\rangle\langle+|\otimes D^2\rho D^2,\\
\Gamma_{10}(\rho)&=\frac{t^2}{2}|v_{10}\rangle\langle v_{10}|\otimes V\rho V^\dagger,
&v_{10}&=(1,s)^T,\\
\Gamma_{01}(\rho)&=\frac{t^2}{2}|v_{01}\rangle\langle v_{01}|\otimes V\rho V^\dagger,
&v_{01}&=(s,1)^T,\\
\Gamma_{11}(\rho)&=0.
\end{aligned}
\tag{RR4}
$$

The displayed $v$ vectors are unnormalized. Two ordinary monitored correction calls have the same no-jump map and aggregate any-jump map
$J(\rho)=t^2(1+s^2)V\rho V^\dagger=(1-s^4)V\rho V^\dagger$.
On no jump, prepare helper $+$ and synthetic label $00$. On any jump, choose labels $10,01$ with equal classical probabilities and prepare respectively $v_{10}/\sqrt{1+s^2}$ or $v_{01}/\sqrt{1+s^2}$. Substitution reproduces every subchannel in (RR4), for every initial code/error/logical/reference state. The original ordinary clock records can be retained as extra side information or processed and discarded when the declared output consists of the synthetic module labels. This is equality of that accessible instrument; it does not assert equality of discarded purifications, a future persistent bath, or a separately required original timing-record output.

This comparator uses the same two correction calls, actual syndrome readout, calibrated $s$, a classical coin and final helper preparation. It does not protect the helper through the calls or store a copy of the unknown payload there. Measurement/reset errors, controller memory, erasure, calibration, final preparation and their elapsed time remain paid resources. Nonproportional logical kicks or hidden trajectory indices invalidate the specified one-way model. A non-code-fixing population transfer by itself therefore does not establish a recovery advantage. In this model, (RR3) is simply the ordinary any-jump map thinned by $(1-s)^2/[2(1+s^2)]$.

At $s=3/5$, $t=4/5$, a pure error input gives minus probability $32/625$ for (RR1), zero for (RR2), and $272/625$ when both independent module and chronological copies are present. The module-switch minus probability on a maximally entangled gauge/reference probe is $16/625$; it is a flag probability, not a Bell-good weight. All three instruments retain total attempt mass one and identical ordered target diagonals. The [exact checker](checks/architecture/verify_backaction.py) verifies all $16$ matrix units of gauge times logical qubit, all $64$ recorded subchannel equalities of (RR4), the coherent record-swap identity, and these three distinct probabilities. These finite fixtures do not fit an oscillator experiment.

The concrete recovery application remains conditional. [Sivak et al.](https://arxiv.org/html/2211.09116v1), SI S4.2–S4.3 and S20–S22, implement finite-energy GKP sBs correction through ECD pulses, qubit rotations, measurement/reset and outcome-conditioned virtual cavity rotation. Their nominal rank-two rounds gradually transfer error populations; $gg$ is not a code projection. Each reported half-cycle lasts $4.924\,\mu\mathrm{s}$, including $2.332\,\mu\mathrm{s}$ reset. Leakage and residual record correlations require a joint temporal model. The measured/reset transmon and classical pulse control do not demonstrate an independent surviving order helper or complete coherent reset-record router.

The ordinary comparison should include full-history feedback: [Puviani et al.](https://arxiv.org/html/2312.07391v2) simulate recurrent Feedback-GRAPE, adjusting $15$ parameters per sBs half-cycle using the binary history, at fixed $10\,\mu\mathrm{s}$ full cycles. Their model omits leakage and SPAM and uses ideal parameterized gates plus noisy idles and numerical reset. It is a concrete controller class, not an experimentally calibrated global optimum. Training, feedback latency and classical memory remain charged. The next decisive test is to identify the actual complete sBs reset-field instrument and its cross-history overlaps, then compare full retained logical output and a declared decoder against paid history-dependent control. Neither noncommuting nominal Kraus operators nor an optimized abstract switch of two reduced round maps supplies that missing interface or a logical advantage.

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

<a id="nr-r19-holonomic-controls"></a>

**A paired holonomic construction exposes a direct two-loop target.**
The primary proposal of
[Axelsson et al., *d-pod realization of nonadiabatic holonomic quantum
computation*, arXiv:2609.16216v2, §II](https://arxiv.org/html/2609.16216v2)
uses one auxiliary excited state and individually driven computational
ground levels. In its resonant convention, normalize
$|b\rangle=\sum_j\omega_j^*|j\rangle$ by $\sum_j|\omega_j|^2=1$,
with fixed complex ratios and real common envelope:
$G(t)=\Omega(t)(|e\rangle\langle b|+|b\rangle\langle e|)$.
Dark vectors remain fixed. On $\operatorname{span}\{e,b\}$ the
propagator is $\exp[-iX\int\Omega(t)dt]$, so a cyclic area $\pi$
pulse gives minus identity there and ground action
$F_b=I-2|b\rangle\langle b|$, returning every computational input
from the excited level. This area's factor differs from the preceding
Householder source's Rabi convention. A two-segment loop gives
$I-(1+e^{-i\eta})|b\rangle\langle b|$; $\eta=0$ is the reflection.

Consider a $2d$-ground-state extension, with $d=3$ requiring six ground
states and one auxiliary. This is a proposed extension of that model,
not an experimental NR-R19 module. Assume stable orthonormal bright
frames $\{r_j\}$ and $\{l_j\}$ in the two known address manifolds
are actually available, even if their data matrices are unknown. Define

$$
U=\sum_j|l_j\rangle\langle r_j|,\qquad
v_j^-=(|0,r_j\rangle-|1,l_j\rangle)/\sqrt2.
$$

The bright vectors are orthonormal, so the d commuting reflections
$F_j^-=I-2|v_j^-\rangle\langle v_j^-|$ multiply to
$I-2\sum_j|v_j^-\rangle\langle v_j^-|=A(U)$ by block expansion.
Replace just $v_k^-$ by
$v_k^+=(|0,r_k\rangle+|1,l_k\rangle)/\sqrt2$. This reverses the
swap sign in that paired channel, giving $B=A(UH)$ with
$H=I-2|r_k\rangle\langle r_k|$. Thus the special correlation is
constructed explicitly, rather than inferred from two independent
converters. A common relative phase between the address-leg groups,
constant across a station's d loops and static within the job, gives
the opposite off-diagonal station phases in (34). For example replacing
each lower leg by $e^{i\phi}l_j$ gives $e^{-i\phi Z_C}A(U)$.
Different unknown phases per paired channel or within a pulse do not
automatically preserve this family.

Within individually cyclic rank-one loops, each station needs at least
d loops, even up to global phase. Indeed
$\operatorname{rank}(I-F)\le1$ for every elementary rank-one phase;
the telescoping identity for $I-F_m\cdots F_1$ bounds its rank by m.
But $A(U)$ has eigenvalues $\pm1$, each d times, so
$\operatorname{rank}(I-e^{i\gamma}A(U))\ge d$ for every $\gamma$.
The displayed construction attains this count. It is not a lower bound
on moving-bright paths, overlapping noncyclic controls or other ancillas.

The same native field controls can make the useful target much cheaper.
If the address-1 legs of the selected k-th pulse can actually be
disabled, a normalized cyclic pulse implements
$M_0=I-2|0,r_k\rangle\langle0,r_k|$. Disabling address-0 instead
implements $M_1=I-2|1,l_k\rangle\langle1,l_k|$. Therefore

$$
M_1M_0=\operatorname{diag}(H,UHU^\dagger)=W.
\tag{HC1}
$$

This ordinary construction needs two native loops, versus $2d$ loops
for the switched A,B histories. It uses selective physical legs,
not a controlled call to an otherwise unknown reflection. Matrix
knowledge of either frame is unnecessary. A common optical phase
constant during a pulse cancels from its bright projector; the one-leg
operations need no relative phase between addresses.

Pulse normalization is a real cost. Removing half of a normalized
paired vector while holding its remaining physical leg amplitudes
fixed reduces the rms coupling by $\sqrt2$. Stretching each pulse
by $\sqrt2$ restores area $\pi$ without raising those amplitudes;
alternatively increase them by $\sqrt2$ if allowed. With equal original
loop duration T, the first choice costs $2\sqrt2T$ for (HC1), versus
$2dT$ for the two stations before reconfiguration, routing, storage and
faults. On-resonance conditions, fixed retained-leg ratios, zero
coupling before/after each loop, light shifts and auxiliary decay must
all be checked in the actual instrument. No noisy-device timing
optimum follows merely from this ideal duration comparison.

The source programs bright states with Rabi controls; it does not give
a fresh Haar-distributed unknown frame. A common unknown unitary basis
change preserves orthonormality and could arise in a restricted
degenerate-manifold rotation family. Generic dipole, amplitude or
crosstalk errors do not preserve it or the exact A/B promise. Actual
unknown-frame normalization is required by both strategies. The
pointwise identity (HC1) applies whenever the paired pulses and
leg-disable controls exist, with no distributional assumption. A sealed
device exposing only A,B need not expose these operations; its matrix
factorization alone does not invalidate the opaque-port theorem.

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

**Physical drift clocks require a source-specific access model.** The
following interfaces illustrate why controller timing, measured drift and
the lifetime of a reusable calibration must be distinguished. They do not
establish a retained-output advantage for coherently ordered couplers.

| Primary source and version | Actual access and timing | Qualification for the application |
| --- | --- | --- |
| [Tan et al., *Communications Engineering* **3**, 57 (22 March 2024)](https://doi.org/10.1038/s44172-024-00198-0) | The fiber simulation assumes 0.5 ms detector acquisition and 0.5 ms EPC braking; its reference drift is a 1% average QBER rise within one minute. The experiments are explicitly quasistatic classical laser, polarizer and power-meter analogues. | Supplies ordinary Mueller estimation and waveplate compensation, not a measured fast calibration-expiry window or an unknown retained-payload test. |
| [Herrera Valencia et al., *Nature Photonics* **20**, 202–207 (2026), online 26 November 2025](https://doi.org/10.1038/s41566-025-01806-x) | An $8\times8$ multimode-fiber circuit routes and swaps entanglement after classical transmission-matrix characterization and inverse design of its phase planes. Routing stability is tested over two weeks without realignment or matrix recharacterization, with the fiber mechanically fixed. Output phase planes also perform projective measurements. | Genuine quantum mode processing does not itself supply coherent order of two unknown processors. Preserve the measured calibration reuse and programmed optical controls in the ordinary comparator. |
| [Tagliavacche et al., *npj Quantum Information* **11**, 60 (6 April 2025)](https://doi.org/10.1038/s41534-025-00991-5) | Frequency-bin fiber-spool phase drift is followed over about 600 s, with ordinary RF/pilot phase correction about every 2 s and stability tested up to one hour. The demonstrated endpoint is destructive BBM92 detection. | Slow scalar phase tracking does not establish two indispensable unknown noncommuting kernels or a heralded service retaining an arbitrary input. |

These are source-specific exclusions of the proposed application, not a
universal obstruction to drifting interfaces or an exhaustive literature
claim. In particular, a fast assumed detector or controller does not
measure a fast loss of usable calibration. The measured matrix or channel
must remain valid for the proposed workload, and its expiry must be
compared with the actual ordinary update and reuse schedule.

A useful next test would supply a dynamic transfer-map record together
with the required two-module workload and its physical output ports.
Compare both strategies on that same record, charging training visits,
pilots, reconfiguration and readout while amortizing reusable calibration.
Allow ordinary calibrated mode processing, temporal returns and
entanglement-first alternatives whenever the same ports permit them;
price their propagation loss, delays, storage and extra modes explicitly.
The score must count every attempt and test the complete conditional
output on an arbitrary unknown input entangled with a passive reference,
including inaccessible frequency, bath and loss records. A consumed
unknown input cannot be replaced for a free retry. Normalized coincidence
fidelity or a known-state fringe alone does not specify that service.
No source in the table supplies the full fast-window access model needed
to proceed from this qualification test to a physical advantage claim.

<a id="nr-r19-private-programs"></a>

**A private program is a different access premise.**
[Wei et al., Science **388**, 509–513 (2025), primary v2](https://arxiv.org/html/2412.03020v2)
hide client-selected operations using photon measurements and private
correction records. For the ideal resource isometry
$|j\rangle_S\mapsto|j\rangle_S|j\rangle_\gamma$, choose the client
bra $(\langle0|+(-1)^s e^{i\phi}\langle1|)/\sqrt2$. Its exact
conditional operator on arbitrary data/reference input is
$K_s=Z^s\operatorname{diag}(1,e^{i\phi})/\sqrt2$; forgetting $s$
instead gives $\sum_s\operatorname{Ad}_{K_s}=(\operatorname{Id}
+\operatorname{Ad}_Z)/2$, independent of $\phi$. The conditional
unitary and the server's unkeyed channel are different interfaces.
This honest ideal identity is not a composable security proof or a
complete physical loss instrument. Calibrating the hardware does not
reveal the client's current private program, so the ordinary comparison
must preserve that privacy and its allowed adaptive measurements.
[Drmota et al., PRL **132**, 150604 (2024)](https://doi.org/10.1103/PhysRevLett.132.150604)
demonstrate ordinary memory, local gates and feedback;
[Baranes et al.'s proposal, arXiv:2505.21621v1](https://arxiv.org/html/2505.21621v1)
adds loss-protected resource preparation under its stated model.
Their photons, retries, data idling,
local gates and messages must be charged. These three sources do not
identify that private-program service with the present arbitrary-data
coupler pair, coherent order port or fresh qutrit prior. Such an
identification would need an explicit assignment of secrets, quantum and
classical ports, program consumption/reuse, full transcripts and output
corrections to each party. This bounded screen does not exclude a
separately engineered private-oracle architecture or blind computing.

The ideal resource model permits a more explicit comparison. Let a,b
be fresh photon qubits, and use the mathematical extensions
$U_A=\operatorname{CNOT}_{S\to a}$ and
$U_B=H_S\operatorname{CNOT}_{S\to b}H_S$ of its two copy isometries.
Private photon measurements give $Z^sA/\sqrt2$ and $X^tB/\sqrt2$ on S,
where $A=\operatorname{diag}(1,e^{i\phi})$ and
$B=H\operatorname{diag}(1,e^{i\theta})H$.
If their resource interactions are coherently ordered, the actual
fine-key operator on arbitrary C/S/reference input is

$$
F_{st}=\tfrac12\operatorname{diag}_C(X^tBZ^sA,\,Z^sAX^tB).
\tag{PP1}
$$

Every key has probability $1/4$. To obtain the desired
$W_{AB}=\operatorname{diag}_C(BA,AB)$, its required arm corrections are
$L_0=BZ^sB^\dagger X^t$ and $L_1=AX^tA^\dagger Z^s$.
Multiplication gives $\operatorname{diag}(L_0,L_1)F_{st}=W_{AB}/2$.
They generically depend on private angles and are not a common final
Pauli. Even $A=B=I$, $s=t=1$ gives
$F_{11}=Z_C\otimes X_SZ_S/2$: dropping separate arm phases destroys
order coherence. Keeping only key 00 gives weight $1/4$, but announcing
that key mask is not automatically a private service. A terminal
measurement may admit its own frame rule; that endpoint must be specified.

An ordinary raw-instrument compiler keeps the same two photons and
private measurements. In their joint X basis, $U_A$ acts as $Z_S^u$
and $U_B$ as $X_S^v$. Hence

$$
U_AU_B=K_{ab}U_BU_A,\quad
K_{ab}=I-2|--\rangle\langle--|=H_aH_b\operatorname{CZ}_{ab}H_aH_b,
\qquad
\operatorname{diag}_C(U_BU_A,U_AU_B)
=\operatorname{ctrl}_C(K_{ab})(I_C\otimes U_BU_A).
\tag{PP2}
$$

Run the two fresh-photon isometries in fixed order, retain C,a,b, then
apply the known joint gate
$\operatorname{ctrl}_C(K_{ab})=H_aH_b\operatorname{CCZ}_{Cab}H_aH_b$
before client readout. Restricting (PP2) to fresh photon columns proves
equality on every C/S/reference input, so every later fixed or adaptive
client instrument, including all private keys, also matches. No extra
phase-program photon or angle disclosure is required. The three-register
gate and coherent storage/interface are substantial additional resources;
this identity does not supply them from two separate photon analyzers.
It is an honest ideal instrument equality, not a security proof or a
comparison of complete physical loss maps.

**A concrete factory endpoint has a stronger ordinary comparison.**
Define the encoding isometry
$E|c\rangle=\operatorname{ctrl}_C(K_{ab})(|c\rangle_C|00\rangle_{ab})$.
With S initialized to 0, the native coherent order followed by S-X
readout has two Kraus maps $E/\sqrt2$ and $X_bE/\sqrt2$ on arbitrary
C/reference input. Indeed
$U_BU_A|0,00\rangle=(|+\rangle_S|00\rangle+|-\rangle_S|01\rangle)/\sqrt2$;
the other order inserts K, which commutes with $X_b$.
Both flags have probability $1/2$; correcting the minus by $X_b$ yields E.
This uses only fresh-source columns. For C initialized to plus, it gives

$$
|\Omega\rangle=E|+\rangle=H_aH_b\operatorname{CCZ}|+++\rangle.
\tag{PP3}
$$

An ordinary factory avoids a joint photonic CCZ: start with S=0 and
fresh a=b=0; apply controlled-$H_{C\to S}$, copy S to a, apply
controlled-$H_{C\to S}$, then copy S to b in fixed order. Read S in X
and correct the minus by $Z_b$. For C=0 the photons remain 00. For C=1,
the H–copy–H–copy sequence gives $\operatorname{CZ}|++\rangle$ on plus
and $Z_b\operatorname{CZ}|++\rangle$ on minus. Since $K|00\rangle$
is that same graph state, its two maps are exactly $E/\sqrt2$ and
$Z_bE/\sqrt2$, including every C/reference coherence. A supplied X-copy
source can be converted to Z-copy by known S Hadamards.
Controlled H is non-Clifford and needs a real local C–S port. For example,
$\operatorname{CH}=R_{y,S}(\pi/4)\operatorname{CZ}_{CS}R_{y,S}(-\pi/4)$;
two such gates use two local CZs and four rotations in this compilation.
Their pulse, error and storage costs are not inferred from logical counts.

An already delivered resource $|\Omega\rangle_{cab}$ can also inject E
onto an unknown C without a joint photonic correction. Apply
$\operatorname{CNOT}_{C\to c}$ and measure c in Z. Its two maps are
$E/\sqrt2$ and $(I_C\otimes K_{ab})E/\sqrt2$. The latter could be
corrected by the joint Clifford K; instead, measure a and b in X
and discard those two photons. With outcome bras
$\langle s_X|=(\langle0|+(-1)^s\langle1|)/\sqrt2$ and
$\langle t_X|=(\langle0|+(-1)^t\langle1|)/\sqrt2$, one has
$\langle s_X,t_X|00\rangle=1/2$ and
$\langle s_X,t_X|K|00\rangle=(-1)^{st}/2$.
Each failed fine record therefore acts on C as
$\operatorname{diag}((-1)^{st},1)/(2\sqrt2)$.
The Pauli correction $Z_C^{st}$ restores the same unknown
C/reference state exactly. Each such record has probability $1/8$;
the total failure probability is $1/2$, independent of that input.
Measuring b first saves a readout: if t=0, a is already 0 and C is
restored; if t=1, measure a in X and apply $Z_C^s$. The two t values
are equally likely on a failed injection, giving 1.5 photon readouts
on average per rollback. Both failed photons are discarded.
This adaptive option must hold a until b's flag is available or supply
an equivalent selection port; two fixed X readouts avoid that dependency.
Retrying with a fresh resource gives the complete capped instrument

$$
\mathcal S_J(\rho)=(1-2^{-J})E\rho E^\dagger,\qquad
\mathcal R_J(\rho)=2^{-J}\rho.
\tag{PP4}
$$

The cap uses $2(1-2^{-J})$ delivered resources on average. The infinite
retry process uses two,
or four fresh-copy calls if each ideal factory succeeds in its two calls.
It also averages two input-to-resource CNOTs, two c readouts and 1.5
photon readouts with the adaptive option (two with fixed readout), plus
memory and feedback. The Z frame commutes with later C-to-c CNOTs, so
it can be tracked across retries; its record must be available before an
incompatible use of C. Real factory losses and storage add further costs;
a destructive click does not herald retained output photons. Undetected
loss after injection is outside the ideal instrument (PP4).
This comparison needs an actual C-to-c gate and reliable retained-resource
availability. It does not grant those ports from separate client analyzers.
Resource-first preparation and retrying teleportation are already explicit
ordinary methods in [Wei et al., Supplement I.8](https://arxiv.org/html/2412.03020v2);
this is a scoped exact graph-resource construction, not a priority claim
or a compiler for the full arbitrary-S instrument (PP1).

Moving the joint gate in (PP2) before arbitrary resource calls is a
different option: it feeds entangled, nonblank photon inputs into the
extensions. Agreement on a fresh-source isometry alone does not grant
that port. Neither fresh-column factory nor the resource injection above
needs it. Such factories must count failed preparations, adapters,
readout, corrections and memory. General magic
generation from coherent order is established by
[Mo et al., PRA **109**, 062428 (2024), v2](https://arxiv.org/html/2311.15494v2);
the [braided-magic comparison](braided-magic.md#nr-r17) likewise prices
the additional non-Clifford interface. No priority claim is made for this
specialization or a hardware factory advantage.

The physical distinction matters in the cited emitters. Wei's prepared
photon/spin resource does not establish arbitrary-input CNOT; its
Supplement II.6 limits even ideal-contrast average cavity reflection to
50%. The stationary spin is not routed through two modules by a photon
path alone. A native realization needs a coherent spin basis/time
selector, preserved photon labels, common output modes and no leaked
emission-order timestamp. The ordinary two-controlled-H factory instead
needs C local to S, or a priced coherent adapter if C is a flying path.
Both must retain actual success filters, lost photons and bath records;
two ideal source calls alone do not imply equal noisy yield. Delivering
retained $|\Omega\rangle$ needs storage and physical or supported frame
corrections. Destructive client readout changes that endpoint. Encoding
two photons into one four-mode carrier also changes source, loss and
client-control ports; dimension alone does not supply that conversion.

<a id="nr-r19-reflected-source"></a>

**A source-backed finite-contrast comparison.** The [author-deposited
simulation, version 2](https://zenodo.org/records/14854711), linked through
concept DOI [10.5281/zenodo.14769739](https://doi.org/10.5281/zenodo.14769739),
allows a more specific accepted-sector test. Static inspection of
`SimulationCode/SiVgates.py` and `BlindGatesSimulation.py` gives an
early reflection, a spin pi pulse, late reflection and another pi pulse.
Its ideal pulses are both $-iY$, leaving the common spin factor $-I$.
This is a simulation convention, not a reconstruction of every hardware
phase in the pulse drawing. In general, two equatorial pi pulses leave
a known frame $D=P_2P_1$: the early component sees $DR_E$, and the late
component sees $D(XR_LX)$. Remove D coherently or retain it through both
order arms; separate arm phases cannot be discarded.

For balanced single-photon bins, stationary spin-preserving reflection
and one pure selected field record, let $h_0,h_1$ be the actual reflected
one-photon amplitudes in a fixed phase convention. The deposited
beam-splitter convention conjugates its named cavity-reflection parameter;
using transfer amplitudes h avoids silently changing their phases.
After the known spin frame, the selected fresh columns are

$$
J_Z|s\rangle=|s\rangle
 \frac{h_s|0\rangle+h_{1-s}|1\rangle}{\sqrt2}
=(I_S\otimes F)J_Z^{\rm ideal}|s\rangle,\quad
F=\frac{h_0I+h_1X}{\sqrt2},\quad
F^\dagger F=\eta I+\kappa X,\quad
J_Z^\dagger J_Z=\eta I,
\quad \eta=\frac{|h_0|^2+|h_1|^2}{2},\quad
\kappa=\operatorname{Re}(h_0^*h_1).
\tag{PP5}
$$

Here $J_Z^{\rm ideal}|s\rangle=|s,s\rangle$ and
$J_X=H_SJ_ZH_S$. Finite contrast gives wrong-bin amplitudes, rather
than necessarily unequal logical input weights. The 50% ideal-contrast
reflection ceiling alone does not imply such an imbalance. F is an
algebraic factor on the copy code, not a supplied photon channel:
$h_0=h_1=1$ gives $\|F\|=\sqrt2$ while J is still an isometry.
Unequal early/late responses instead give
$F_{EL}=\left(\begin{smallmatrix}h_0^E&h_1^E\\h_1^L&h_0^L\end{smallmatrix}\right)/\sqrt2$;
the scalar input effect and X-commuting structure need not survive.

Let $L=I_C\otimes F_a\otimes F_b$. Since K is a function of $X_a,X_b$,
it commutes with $F_aF_b$. Thus (PP2)'s ordinary compiler persists on
these selected fresh columns for every C/S/reference input, with total
input effect $\eta_a\eta_bI_{CS}$. For the known-S factory, the native
$X_b$ correction commutes with $F_b$, whereas the ordinary $Z_b$ flips
its X term. The complete corrected flags are

$$
N_+=N_-=LE/\sqrt2,\qquad O_+=LE/\sqrt2,\qquad
O_-=(I_C\otimes F_a\otimes ZF_bZ)E/\sqrt2.
\tag{PP6}
$$

Both $|00\rangle$ and $K|00\rangle$ have zero $X_a,X_b,X_aX_b$
expectations. Orthogonal retained C sectors therefore give every flag
effect $\eta_a\eta_b I_C/2$. Equal selected mass does not identify
the two corrected instruments; the ordinary record must be kept.
If a populated coherent $C\to a$ CNOT is separately supplied, the
ordinary minus is corrected to $LE/\sqrt2$ by
$\operatorname{CNOT}_{C\to a}Z_b$, using
$Z_bE=\operatorname{CNOT}_{C\to a}E$. This is an extra joint port,
not a final photon-local Pauli granted by a fresh-copy source.

There is also a matching photon-local inverse construction. Write
$\mu_j^2=\sigma_{\min}(F_j)^2=\eta_j-|\kappa_j|$. When both are
positive, $Q_j=\mu_jF_j^{-1}$ is a contraction. Apply $Q_a,Q_b$ after
native flags or ordinary plus, and $Q_a,ZQ_bZ$ after ordinary minus.
Every accepted map becomes $\mu_a\mu_bE/\sqrt2$, for total exact
encoding weight $\mu_a^2\mu_b^2$. This includes the selected source
attenuation and filter rejects; it is a feasible comparison, not an
optimum over all output operations. If $\kappa_j=0$, F is scaled unitary
and known local unitary inverses suffice. If either nonzero F has rank
one, its selected C=1 photon state is product across that photon, so
photon-local filters, product ancillas and classical communication cannot
restore the entangled $K|00\rangle$. Extra joint interactions change
that restriction. Ideal contrast $h_0=1,h_1=0$ gives two-source weight
$1/4$ before other losses. None of these sector weights supplies an
event-ready retained photon herald.

Reflection amplitudes also leave the rejected map undetermined. One
compatible bin-resolved completion for $|h_s|\le1$ has vacuum-output
Kraus operators $L_0=\operatorname{diag}(\ell_0,\ell_1)/\sqrt2$ and
$L_1=\operatorname{diag}(\ell_1,\ell_0)/\sqrt2$, where
$\ell_s=\sqrt{1-|h_s|^2}$. Together with J they are trace preserving.
Their rejected spin coherence coefficient is $\ell_0\ell_1$; retaining
an orthogonal bath record of the spin instead makes it zero at the
same reflected amplitudes and rejection probability. Thus an
input-independent success rate does not prove harmless retries.
The deposited weak-coherent/Fock-space simulation has additional
photon-number sectors; the single-photon specialization above is not
its full experimental instrument. Actual pulse errors, frequency modes,
loss records and a coherent source selector still need a joint model.

**A sufficient stationary-emitter selector already exposes ordinary
controls.** With matched source columns at successive emissions p,q,
the chronological sequence

$$
\operatorname{CH}_{C\to S},\quad J_{Z,p},\quad H_S,\quad J_{Z,q},\quad
\operatorname{CH}_{\neg C\to S},\quad
\operatorname{ctrl}_C\operatorname{SWAP}_{pq}
\tag{PP7}
$$

gives $J_{X,b}J_{Z,a}$ for C=0 and $J_{Z,a}J_{X,b}$ for C=1 after
the actual photon swap assigns p=b,q=a in the second arm. This uses
only fresh columns on arbitrary C/S/reference input. It is one
sufficient construction, not a lower bound on all native selectors.
It already grants both local controlled-H gates used by the ordinary
factory and adds a Hadamard and coherent photon routing. Unequal temporal
response ratios require balancing or an explicit controlled-source
argument; relabelling photons does not relabel inaccessible loss/time
records. Common output modes and a matched full dilation remain required.

<a id="nr-r19-retained-carrier"></a>

**Reversing the physical allocation changes the endpoint costs.** If S
is a flying photon's polarization, C its path and a,b stationary targets,
a path router can order the carrier's contacts. This is a different
phase-gate interface: assume full arbitrary-input spin/photon CZs, so
$U_A=H_a\operatorname{CZ}_{Sa}H_a$ and
$U_B=H_SH_b\operatorname{CZ}_{Sb}H_bH_S$. The
[Daiss phase-gate predecessor](https://arxiv.org/html/2103.13095v1)
supports that mechanism, but does not demonstrate the required four-mode
carrier, coherent revisit and retained-resource apparatus. Wei's fresh
amplitude-copy columns do not grant these full gates.

In this allocation the two ordinary controlled-H gates are known
path-selective polarization optics; their transmission and relative
phase control must be priced. Destructive S readout would also destroy
the retained path C. Before readout the native and ordinary states are
$(|+\rangle_SE+|-\rangle_SX_bE)/\sqrt2$ and
$(|+\rangle_SE+|-\rangle_SZ_bE)/\sqrt2$, respectively. One additional
full $U_B$ contact cleans the former to $|0\rangle_SE$; one additional
$H_S\operatorname{CZ}_{Sb}H_S$ cleans the latter to the same state.
Both use three occupied contacts, including a revisit of b. Alternatively,
the terminal polarization filter $|+\rangle\langle+|$ gives both a
retained forward map $|+\rangle_SE/\sqrt2$ in two contacts. Its ideal
weight is $1/2$; no dump click certifies that carrier only with a known
input photon, no other loss and reliable dump detection. A QND readout,
state transfer or later erasure-aware endpoint is a separate priced port.

A narrow two-contact obstruction helps delimit that comparison. Suppose
the atoms start in a pure product state, only one full CZ with each is
allowed in fixed order, and all remaining controls are carrier unitaries
and local atom unitaries, with no ancilla, measurement, reset or
postselection. At the last CZ, write its carrier projectors as $\Pi_k$.
After discarding the carrier, the atomic state has the separable form
$\sum_k\operatorname{Tr}_P(\Pi_k\rho_{Pa}\Pi_k)
\otimes Z_b^k|\beta\rangle\langle\beta|Z_b^k$.
It cannot be the desired fixed-resource marginal
$\rho_{ab}^{\Omega}=(|00\rangle\langle00|+|g\rangle\langle g|)/2$,
$g=K|00\rangle$: for $v=(0,1,1,1)^T$,
$v^\dagger(\rho_{ab}^{\Omega})^{T_b}v=-3/8$.
This excludes that unitary-only one-visit model, including fixed Omega;
the two-contact filtered branch is explicitly outside it. Other
interactions, ancillas, pre-existing entanglement and heralded protocols
remain available ordinary alternatives. Logical contact counts alone
do not compare the actual routing, loss, memory or delivery clocks.

The [exact private-program guard](checks/architecture/private_program_guards.py)
replays the fixed resource matrices, keyed instruments, relative phases,
both fresh-column factories, the injection/rollback branches and a
nonblank-extension counterexample. It also checks the declared balanced
reflection model, selected-sector compiler and inverse filters, plus
the reversed-role three-contact cleanups and common two-contact forward
branch. The general separability and local-recovery obstructions and
record-completion arguments remain analytic.
Physical success/loss maps, timing, security and hardware costs remain
outside that finite replay.

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

<a id="nr-r19-natural-exchange"></a>

**Natural atomic exchange still needs the complete port.** A bounded
three-primary screen distinguishes useful exchange dynamics from the
specific two-manifold oracle required here. These sources do not establish
that pair or its coherent order interface.

| Primary source and version | Demonstrated interaction | Missing premise for this application |
| --- | --- | --- |
| [Scazza et al., Nature Physics **10**, 779–784 (2014), corrected v3](https://arxiv.org/html/1403.4761v3) | SU(6) orbital exchange studied by spectroscopy and lossy ensemble equilibration; coherent confined-pair preparation and fast switching were unavailable. | The ideal homogeneous zero-field distinct-label model gives $(VI_2+JX_C)\otimes I_{15}$, with $J=-V_{\rm ex}$ in a fixed fermionic creation-operator convention. This is known label transport, without a fresh $U(15)$ or correlated sign station. |
| [Widera et al., PRL **95**, 190405 (2005), v2](https://arxiv.org/html/cond-mat/0505492v2) | Coherent collisions conserve total magnetization; the $f=2$, zero-magnetization sector has three symmetrized pair states. Populations are measured after release. | One three-dimensional sector is not two complete three-dimensional endpoint manifolds. A separately prepared exchange oscillation does not certify arbitrary-input transfer, retained address coherence or the required second station. |
| [Emperauger et al., PRA **111**, 062806 (2025), v3](https://arxiv.org/html/2503.15034v3) | Selected direct, indirect and light-shift-resonant Rydberg pair exchanges, with diagonal shifts, motion and decay included in their assessment. Microwave and local addressing controls prepare and probe the states. | Four named atomic levels in a selected pair resonance are not four parallel transfer channels. Neither two full qutrit endpoint manifolds nor the correlated $A(U),A(UH)$ pair is demonstrated. Preserve the actual ordinary controls and complete motional/loss output. |

The Scazza single-band model also gives a simple detuning guard. Within
one distinct-spin pair, write its Hamiltonian as
$(V+\bar z_{\mu\nu})I+JX+\Delta_{\mu\nu}Z$, where
$\Delta_{\mu\nu}=\delta g\mu_BB(\mu-\nu)/2$ and
$\bar z_{\mu\nu}=\delta g\mu_BB(\mu+\nu)/2$ after subtracting the
common ground-orbital nuclear energy. Pauli-vector exponentiation bounds
its single-hold transfer probability by
$J^2/(J^2+\Delta_{\mu\nu}^2)<1$ for nonzero detuning. The pair-dependent
scalar is not a global phase on coherent superpositions of different
labels. Equal-label occupancy, motional bands and loss need their actual
model; neither a composite-control impossibility nor coherent selective
control follows from this calculation.

There is a sharper spectral guard for a **declared ideal vector model**,
rather than the selected Rb levels in the third source. Assume a scalar
$J=0$ state and a degenerate Cartesian $J=1$ manifold, equal reduced
dipole elements, common endpoint energies and no other resonant channels.
The dipole tensor then gives $K(n)=g(I-3P_n)$ between
$\{|p_j,s\rangle\}_j$ and $\{|s,p_j\rangle\}_j$, with
$g\in\mathbb R\setminus\{0\}$ and $P_n=|n\rangle\langle n|$ for a
real unit bond vector. Its singular
strengths are $|g|(1,1,2)$, so (NC3) cannot vanish on every channel:
$\cos(gt)=0$ forces $\cos(2gt)=-1$. More quantitatively,

$$
\max_t\min_{\|v\|=1}\Pr\{\text{opposite endpoint}\mid v\}
 =1-\min_\theta\max\{\cos^2\theta,\cos^2(2\theta)\}
 =\frac34,\qquad \theta=gt.
\tag{NC4}
$$

Indeed, put $y=|\cos\theta|$. If $y\ge1/2$, the maximum cosine
magnitude is at least $1/2$; otherwise
$|\cos2\theta|=1-2y^2>1/2$. Equality holds at $\theta=\pi/3$.
This bounds transfer from either prepared endpoint, not all-output gate
fidelity: the untransferred amplitude remains quantum output. At positive
time $t=\pi/(3|g|)$ the full propagator actually factors as
$e^{-i\operatorname{sgn}(g)\pi X_C/3}\otimes(I-2P_n)$; at
$t=\pi/|g|$ it is
$-I_C\otimes(I-2P_n)$. Natural reflection operations therefore survive
this failed full-swap test. Their calibrated area, physical address
controls, phases and noise remain resources. Composite pulses or an
engineered spectrum can change the single constant-hold premise.

If a repair supplies complete exchange through constant resonant hopping,
with only common diagonal phases and each **cross-manifold kernel** real
symmetric in one common identified data basis, its sine transfer matrices
are real symmetric involutions. This does not follow for arbitrary
composite sequences of such kernels. The existing ordinary
[common-symmetry construction (BD1)](#nr-r19-bdi-controls) then applies
under the stated Hermitian relative-$H$ promise, with clean address
storage and its actual adapters charged. Symmetry of the full hopping
Hamiltonian alone does not imply that cross-kernel condition, since
$\left(\begin{smallmatrix}0&K^T\\K&0\end{smallmatrix}\right)$ is
real symmetric for every real $K$. Generic reciprocity supplies no such
shortcut or Haar prior by itself. A successor needs both full endpoint
maps, their physical correlated sign change and a required retained-output
task before comparing ordinary recoupling, direct reflection, calibration
reuse and routing on the same device.

<a id="nr-r19-adiabatic-port"></a>

**Adiabatic dark transfer supplies one endpoint, not automatically both.**
[Kis et al., Phys. Rev. A **70**, 053405 (2004)](https://arxiv.org/abs/quant-ph/0412086)
analyze STIRAP between degenerate manifolds and give conditions for
removing an arbitrary pure or mixed input from the starting manifold.
An explicit useful case avoids the constant-coupling condition (NC3).
Take equally sized g,e,f manifolds, zero one-photon detuning,
two-photon resonance, real envelopes p,s, and unknown invertible
$J=L\Sigma R^\dagger$:

$$
G(t)=\begin{pmatrix}0&pI&0\\pI&0&sJ\\0&sJ^\dagger&0\end{pmatrix}.
$$

In the fixed frame $\operatorname{diag}(L,L,R)$, singular channel k
has pump p and Stokes $s\sigma_k$. Under counterintuitive passage set
$\tan\theta_k=p/(s\sigma_k)$, going from 0 to $\pi/2$.
Its dark state is $D_k=\cos\theta_k g_k-\sin\theta_k f_k$ and
bright state $Q_k=\sin\theta_k g_k+\cos\theta_k f_k$.
The dark energy is zero, while $(Q_k\pm e_k)/\sqrt2$ have energies
$\pm\Omega_k$, $\Omega_k=(p^2+s^2\sigma_k^2)^{1/2}$.
Real fixed frames give zero Berry phase. Retaining the dynamical
$\Phi_k=\int\Omega_kdt$, the ideal adiabatic propagator is therefore

$$
g_k\mapsto-f_k,\qquad
f_k\mapsto\cos\Phi_k g_k-i\sin\Phi_k e_k,\qquad
e_k\mapsto-i\sin\Phi_k g_k+\cos\Phi_k e_k.
\tag{AD1}
$$

Thus arbitrary g input transfers by the unknown polar-frame isometry
$-RL^\dagger$, independently of singular strengths in this ideal
limit. But initial f input is bright, with leakage $\sin^2\Phi_k$;
adiabaticity does not suppress its dynamical phase. On the complete
useful $g\oplus f$ port the projected propagator is

$$
T=\begin{pmatrix}0&L\cos\Phi R^\dagger\\-RL^\dagger&0\end{pmatrix}.
\tag{AD2}
$$

Complete exchange first requires every $\sin\Phi_k=0$. Even then
$T^2=\operatorname{diag}(-L\cos\Phi L^\dagger,
-R\cos\Phi R^\dagger)$ is scalar only if all cosine signs agree,
as required for the NR-R19 adjoint-reverse involution up to common
phase. A channel with $\Phi_k=\pi/2\pmod{2\pi}$ transfers g
perfectly but sends its reverse f input entirely into e. Such large
odd-half-integer phases are compatible with an adiabatic limit; a short
$\pi/2$-area passage is not asserted adiabatic. Finite-time evolution
adds nonadiabatic and decay errors. Composite, echoed or counterdiabatic
protocols can change this screen but need both endpoint blocks and
their duration and controls. Two independent devices also do not
automatically provide the correlated second station. A finite test
must use all three inputs in **both** endpoint manifolds and their
reference-entangled superpositions, not just g-transfer populations.

<a id="nr-r19-passive-converter"></a>

**Stationary passive conversion has a weighted matching condition.**
The timed Hamiltonian in (NC3) is not a traveling-wave scattering
matrix. For a separate, on-resonance Markov model take two equal
$d$-mode manifolds, number-preserving coupling
$K=(\begin{smallmatrix}0&J^\dagger\\J&0\end{smallmatrix})$, positive
diagonal external linewidths
$\Gamma=\operatorname{diag}(\Gamma_L,\Gamma_R)$, no internal loss,
no detuning and no conjugate-mode amplification terms. Use the
input/output convention

$$
\dot a=-(\Gamma/2+iK)a+\sqrt\Gamma\,b_{\rm in},\qquad
b_{\rm out}=b_{\rm in}-\sqrt\Gamma\,a.
\tag{SC1}
$$

These assumptions are a passive specialization of the
[coupled-mode input/output formalism of Naaman and Aumentado,
PRX Quantum **3**, 020201 (2022), §§II.1–II.3](https://arxiv.org/html/2109.11628).
They exclude the internal dissipative and sum-frequency/conjugate
couplings included in that general treatment. At steady state set
$C=\Gamma_R^{-1/2}J\Gamma_L^{-1/2}$ and
$\widetilde K=(\begin{smallmatrix}0&C^\dagger\\C&0\end{smallmatrix})$.
Factoring
$\Gamma/2+iK=\sqrt\Gamma(I/2+i\widetilde K)\sqrt\Gamma$ gives

$$
S=I-\sqrt\Gamma(\Gamma/2+iK)^{-1}\sqrt\Gamma
 =I-(I/2+i\widetilde K)^{-1}.
\tag{SC2}
$$

Write $C=L\operatorname{diag}(s_j)R^\dagger$, $s_j\ge0$.
Conjugation by $\operatorname{diag}(R,L)$ reduces $\widetilde K$ to
independent $s_jX$ blocks. Inverting $I/2+is_jX$ yields

$$
S_j=\begin{pmatrix}r_j&it_j\\it_j&r_j\end{pmatrix},\qquad
r_j=\frac{s_j^2-1/4}{s_j^2+1/4},\quad
t_j=\frac{s_j}{s_j^2+1/4},\quad r_j^2+t_j^2=1.
\tag{SC3}
$$

The same-band blocks vanish on **every** input iff every $s_j=1/2$,
equivalently

$$
J^\dagger\Gamma_R^{-1}J=\Gamma_L/4.
\tag{SC4}
$$

In that case $S=iA(LR^\dagger)$; its common $i$ is irrelevant on the
fixed one-excitation channel. Thus the unweighted J need not have a
flat spectrum when external linewidths differ. With equal linewidth
$\kappa$, (SC4) becomes $J^\dagger J=(\kappa/2)^2I$. For dimensionless
singular values $(1/2,1,3/2)$, (SC3) instead gives reflection
$(0,3/5,4/5)$ and conversion $(1,4/5,3/5)$: the worst singular input
converts with probability $9/25$, and their uniform mean is $2/3$.
Changing the unknown internal frame does not remove this reflection.
These are single-station acceptance tests, not bounds on every recovery
protocol. Finite bandwidth, internal loss, active pumps and temporal
drift require their complete scattering/noise instruments.

For example, the primary
[41-mode microwave-comb experiment of Bock et al., Physical Review
Applied **24**, 014027 (2025), §§II–III](https://arxiv.org/html/2501.09453)
uses a mode vector containing both $a_m$ and $a_m^*$ and low- and
high-frequency pumps. Its measured coherent-tone scattering therefore
does not by mode count alone certify a passive full exchange on two
three-mode single-photon manifolds, or the correlated second station
in (34). Ordinary pump-programmed nonreciprocal routing and amplifier
backaction control remain meaningful device tasks with different
Gaussian input/output comparators.

<a id="nr-r19-bragg-rank"></a>

**Equal-power N-way Bragg scattering has only one inter-band bright mode.**
[Oliver et al., *N-Way Frequency Beamsplitter for Quantum Photonics*,
§II and Supplement §1](https://arxiv.org/html/2405.02453)
give an all-to-all BS-FWM propagation generator with off-diagonal
entries proportional to $A_i^*A_j$ and demonstrate three-frequency
multiphoton interference. Consider its ideal constant, undepleted,
equal-power pumps, common effective nonlinearity, negligible residual
phase mismatch, and no loss. If $A_j=a e^{i\theta_j}$, define
$w_j=e^{-i\theta_j}/\sqrt N$ and the dimensionless interaction length
$\phi=2\gamma a^2L$. The generator is
$\phi(N|w\rangle\langle w|-I)$, so its propagator is exactly

$$
V_N=e^{-i\phi}\left[I+(e^{iN\phi}-1)|w\rangle\langle w|\right].
\tag{BF1}
$$

The common phase can be suppressed when discussing a fixed
one-photon channel. For a physical split into two disjoint $d$-frequency
bands, $N=2d$, let $w_0,w_1$ be the components in those bands.
The transfer block is

$$
(V_N)_{10}=e^{-i\phi}(e^{iN\phi}-1)|w_1\rangle\langle w_0|,
\quad \operatorname{rank}(V_N)_{10}\le1.
\tag{BF2}
$$

Both $\|w_0\|^2=\|w_1\|^2=1/2$, so $d-1$ independent inputs in
each band are dark to inter-band transfer. No $d>1$ instance of this
single interaction is the full exchange (34). Each physical frequency
input transfers probability
$|e^{iN\phi}-1|^2/(4d)\le1/d$ to the opposite band. Thus in the
ideal six-frequency extension the maximum is $1/3$ per frequency
input, although the collective bright input can transfer completely.
This is a deduction about the model, not a measured six-mode efficiency.
Arbitrary pre/post unitaries acting separately within the two bands
preserve the rank obstruction; the per-frequency bound refers to the
displayed frequency basis, not arbitrary such pre-mixing.

There is also a common-encoding obstruction: (BF1) has eigenvalues
$e^{-i\phi}$ with multiplicity $N-1$ and $e^{i(N-1)\phi}$ once, hence
$|\operatorname{Tr}V_N|=|N-1+e^{iN\phi}|\ge N-2>0$ for $N>2$.
An odd exchange has zero trace, so a common unitary basis change and
common scalar phase cannot turn this family into (34). Unequal
input/output phase legs can change that spectral argument; diagonal
legs in the physical frequency bands still preserve the rank bound.
Unequal pump powers, additional phase mismatch, independently
engineered pair couplings, multiple interactions, encodings that mix
the two physical bands differently at input and output, or ancillas
require a new propagator and are not excluded here.

At $N\phi=\pi\pmod{2\pi}$, (BF1) instead gives the rank-one reflection
$I-2|w\rangle\langle w|$ up to its common scalar phase. If an actual
band-selective version supplies the executable M used to synthesize B,
the ordinary wrapper (NC1) applies; compensation of an address-relative
scalar phase must also be priced. Algebraic factorization alone does
not expose that control in a sealed device. The
[exact finite converter checks](checks/architecture/native_converter_guards.py)
replay unequal-linewidth (SC2)–(SC4), the mismatch example and the
six-frequency rank-one case. Their universal derivations and the
primary device assumptions remain analytic; no native advantage or
ordinary optimum follows.

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

<a id="nr-r19-andreev"></a>

### Andreev reflection supplies a different unknown involution

Coherent electron/hole conversion is a concrete device task in electron
quantum optics. [Burset et al.](https://arxiv.org/html/2312.13145v2)
propose a driven, flux-tunable converter and explicitly model its
Floquet--Nambu scattering, source pulses and superconducting gap.
Coherent electron/hole inputs are meaningful resources; there is no
general superselection exclusion of this application. A sealed
superconducting contact is therefore a motivated source to test, but
an unknown Hermitian reflection does not automatically supply (34).

**A single Majorana mode has the wrong exchange rank.** In the
wide-band, subgap model of [Haim et al., Phys. Rev. B **92**, 245112
(2015)](https://doi.org/10.1103/PhysRevB.92.245112)
([Supplement IV, (24)--(26)](https://arxiv.org/html/1509.00463v2)), one
isolated Majorana mode coupled to $N$ electronic channels has reflection
matrix on $2N$ electron/hole channels

$$
r(E)=I-\frac{2i\Gamma}{E+i\Gamma}P,\qquad
P=\frac{w^\dagger w}{ww^\dagger},\quad
\operatorname{rank}P=1,\quad \Gamma=\pi ww^\dagger.
\tag{AM1}
$$

The row $w$ contains paired electron/hole couplings
$(\lambda,\lambda^*)$, with the corresponding density-of-states factors.
Thus $r(0)=I-2P$ is an unknown Hermitian involution, with one negative
and $2N-1$ positive eigenvalues. By contrast, (34) anticommutes with
$Z_C$, which maps its positive eigenspace isometrically onto its negative
eigenspace. Both have dimension $N$, and its trace is zero. For $N>1$,
$r(0)$ therefore cannot equal (34) after any unitary change of basis
and common scalar phase. In the physical electron/hole split,
$r_{\rm he}(0)$ has rank one and $r_{\rm ee}(0)$ has rank $N-1$:
only one bright combination converts, while the other modes normally
reflect. Selecting the bright electron/hole pair leaves data dimension
one, where this benchmark's target channel is trivial.

The trace argument allows a common basis change. Fixed, unrelated
input/output unitaries do not repair the entire unknown-coupling family
either. Let $m=2N>2$, let $Z$ be any fixed grading with two
$N$-dimensional sectors, and suppose fixed unitaries $L,R$ made every
$K_x=L(I-2|x\rangle\langle x|)R$ odd for all real unit vectors
$x\in\mathbb R^m$. Summing over a real orthonormal basis gives
$\sum_iK_{e_i}=(m-2)LR$. Hence $LR$ is odd and so is every rank-one
$L|x\rangle\langle x|R$. Put $u=Lx$, $v=R^\dagger x$. Its two diagonal
blocks vanish:

$$
u_0v_0^\dagger=0,\qquad u_1v_1^\dagger=0.
\tag{AM2}
$$

If both components of $u$ were nonzero, both components of $v$ would
vanish, a contradiction. Thus every $Lx$ lies entirely in one grading
sector. The basis vectors $Le_i$ span the whole space, so some are in
opposite sectors. Their normalized real sum is another allowed $Lx$
with both components nonzero, again a contradiction. This proves the
fixed-pre/post-unitary obstruction.

The physical paired-coupling family supports this real-vector premise:
after absorbing positive density-of-states factors into $\lambda$, the
fixed unitary
$2^{-1/2}\left(\begin{smallmatrix}I&iI\\I&-iI\end{smallmatrix}\right)$
maps real vectors $(a,b)$ onto all paired vectors
$(a+ib,a-ib)/\sqrt2$. It is a Majorana-basis change and can be absorbed
into $L,R$. The obstruction excludes neither controls calibrated to one
specific $P$, nor restricted coupling sets, ancillas, heralded mode
selection or different interacting devices. Their actual yields,
calibration and memory change the comparison.

**Particle-hole symmetry also restricts hypothetical full converters.**
In a conventional fixed Nambu basis, zero-energy particle-hole symmetry
is $\tau_xr^*\tau_x=r$. Allow the physically irrelevant scalar
$r=e^{i\gamma}A_\alpha$. Comparing its off-diagonal blocks gives
$U^T=e^{2i\gamma}U$. Transposing twice forces $e^{4i\gamma}=1$, so $U$
is symmetric or antisymmetric. An odd-dimensional antisymmetric matrix
has zero determinant and cannot be unitary. For the qutrit benchmark,
therefore, $U^T=U$. The second converter likewise requires
$(UH)^T=UH$, which implies $H^TU=UH$ and

$$
UHU^\dagger=H^T=H^*,\qquad W=\operatorname{diag}(H,H^*).
\tag{AM3}
$$

The station phases cancel under this conjugation comparison.
Takagi-factor $U=VV^T$ and write $H=V^*hV^T$. Then
$(UH)^T=UH$ makes $h$ symmetric; Hermiticity makes it real, and
$H^2=I$ makes $h^2=I$. This is a correlated symmetric-$U$/real-reflection
family. Neither the full-family hard-two converse nor the independent
Haar-$U(3)$/complex-reflection certificate automatically transfers to
this restricted family. Even-dimensional antisymmetric branches require
separate analysis; symmetric-only is not asserted for every dimension.

The chiral-symmetry source supplies another distinction.
[Diez et al., (3)--(7)](https://arxiv.org/html/1206.3079v2) identify the
protected Hermitian involution as $\tau_xr$, rather than generally $r$;
normal-reflection blocks remain in the physical scattering matrix.
At the insulating-wire limit, end reflections are unitary and
transmission vanishes. A full exchange through that same two-port
device instead needs unitary transmission and zero reflection. If
$t_{\rm LR}$ denotes transmission from the chosen input, unitarity gives
$r^\dagger r+t_{\rm LR}^\dagger t_{\rm LR}=I$. The source's
infinitesimal-transmission relation between end indices is not an
arbitrary-input unitary transport gate. At finite transmission, use the
complete device scattering matrix.

<a id="nr-r19-bdi-controls"></a>

**Full-bright BDI contacts have a further common-symmetry closure.**
Multiple perfectly converted channels are possible, beyond the
single-Majorana rank screen. The multichannel model of
[Meidan, Romito and Brouwer, Phys. Rev. Lett. **113**, 057003 (2014)](https://arxiv.org/html/1312.6367)
has one perfect Andreev channel per protected Majorana in its
noninteracting BDI regime. Its interacting four-channel Kondo-like
resonance has $r_{\rm ee}=0$, $r_{\rm he}=I_4$ at zero temperature
and energy. These are low-energy scattering statements, not a
finite-wavepacket router. Opposite-type Majoranas can gap under
allowed couplings, so a mixed-sign full-conversion matrix is not
guaranteed by the topological index alone.

There is a useful restricted ordinary result when the contacts share
a **known** symmetry basis. In the phase-stripped BDI cores, (5) of
the Diez source gives $T=r_{\rm he}=T^\dagger$ and
$r_{\rm eh}=T^*$. If a full-Andreev core also has the NR-R19
Hermitian odd form, its upper block must be $T^\dagger$; comparison
forces $T^*=T$. Its data matrix O is consequently real symmetric
orthogonal. This is an intersection of promises: a generic complex
Hermitian BDI T does not satisfy this odd-core condition. In the
symmetric/qutrit branch write

$$
A=X_C\otimes O_A,\qquad B=X_C\otimes O_B,
\quad O_s^T=O_s,\quad O_s^2=I.
$$

The NR-R19 relative $H=O_AO_B$ is Hermitian iff
$O_AO_B=O_BO_A$. It then satisfies $O_AHO_A^T=H$, so

$$
W=I_C\otimes H.
\tag{BD1}
$$

Hold the useful address in ordinary clean memory, send the data through
A then B at fixed physical address 0, and return the address. The
product acts as $e^{i(\beta-\alpha)}H$ on that data, an irrelevant
global phase, giving (BD1) exactly on every reference-entangled input
with two named queries. Neither H nor the internal real frame must be
learned, and no unknown address-selective reflection is invoked. The
core model separates condensate phases as known-grading dressings
$e^{i\alpha Z_C}$ and $e^{i\beta Z_C}$; their chiral symmetry operators
may rotate with condensate phase. It does not impose unrotated BDI
relations on every dressed matrix. This requires a justified common
phase-stripped data symmetry, rather than two unrelated contact bases.
Actual electron/hole memory and coherent data routing remain physical
costs. No closure for every even-dimensional antisymmetric branch is
inferred from this symmetric-core argument.

A known common complex basis admits a related two-query wrapper.
For electronic basis V and conjugate hole basis $V^*$, the real-frame
target h is represented as $H=VhV^\dagger$ and
$W=\operatorname{diag}(H,H^*)$. The transformed first transfer block
is $U'=V^*O_AV^\dagger$, consistent with (AM3). With known
$S=VV^T$, direct multiplication gives
$S^\dagger HS=V^*hV^T=H^*$. Hence, for
$C_S=\operatorname{diag}(I,S)$,

$$
C_S^\dagger(I\otimes H)C_S=W.
\tag{BD2}
$$

The same fixed-physical-address two-query H action, surrounded by
these known controlled S gates on stored address/data, implements W.
Knowing S suffices without knowing V or H separately. If S or the
common symmetry frame is genuinely unknown and inaccessible, (BD2)
is not an available control; learning and reuse need their actual cost
and drift model. A same-sign contact is $O=\pm I$ in its symmetry
basis, but an inaccessible unknown complex basis is not thereby known.
Neither a restricted BDI prior nor a pair of independently changing
symmetries inherits the Haar certificate above. A finite candidate
must establish its full-band conversion, common symmetry action and
coherent address/storage interface before claiming a native margin.
The [exact matter-coupler guards](checks/architecture/native_matter_guards.py)
replay finite holonomic, ideal-adiabatic and BDI identities. The general
control proofs, physical symmetry/phase assumptions and finite-time
errors remain analytic.

**Finite bandwidth and the specified commutator statistic.** Directly
subtracting the zero-energy limit in (AM1) gives

$$
\|r(E)-r(0)\|=\frac{2|E|}{\sqrt{E^2+\Gamma^2}}.
\tag{AM4}
$$

The coefficient difference is $2E/(E+i\Gamma)$ times the rank-one
projector. On the entire input space supported in $|E|\le E_{\max}$,
its uniform operator-norm error is the maximum of (AM4). An error at
most $0<\epsilon<2$ requires
$E_{\max}\le\Gamma\epsilon/\sqrt{4-\epsilon^2}$. A fixed pulse
envelope can have smaller integrated error than this worst-band bound.
Source temperature, above-gap components, timing, helper storage and
readout still need their complete model; the $E=0$ matrix alone does
not certify a finite-pulse gate.

For two ideal rank-one reflectors $r_p=I-2P$, $r_q=I-2Q$ on $m=2N$
dimensions, put $s=|\langle p|q\rangle|^2$. Their maximally mixed
minus probability is

$$
p_- = \frac{\|[r_q,r_p]\|_{\rm HS}^2}{4m}
    = \frac{8s(1-s)}m\le\frac2m=\frac1N.
\tag{AM5}
$$

Indeed $[r_q,r_p]=4(QP-PQ)$, and rank-one multiplication gives
$\|QP-PQ\|_{\rm HS}^2=2s(1-s)$. Thus this low-rank model supplies no
constant maximally mixed commutator signal as the channel count grows.
The bound concerns that observable; it excludes neither state-dependent
probes nor other switch tasks.

A surviving superconducting candidate needs a finite-bandwidth
multichannel converter with enough bright modes for a full balanced
exchange, a justified correlated second converter and a useful coherent
address output. Its symmetry-restricted prior must be analyzed directly.
The ordinary reflection wrapper, persistent calibration and complete
three-window routing comparisons above still apply when their ports
exist. These analytic screens rule out the specified single-Majorana
implementation of NR-R19, not superconducting switches in general.

The remaining architecture target must specify that pair, a useful coherent address input, full temporal dilations and emitted records, an independent surviving helper, all routing/storage/control costs, phase stability across repeats and any calibration reuse. Pulse, idle, preparation, cooling, leakage and rejected launches enter the same physical ledger on both sides. Known $H$, classical addresses, a supplied selector, or destructive helper/payload readout changes or closes the endpoint. A significant finite advantage on such a native workload remains open.

The shared [exact checker](checks/architecture/verify_backaction.py) separately reports NR-R19. It replays noncommuting rational examples in data dimensions two and three, all address/data matrix units for the corrected and visibility-limited channels, phase drift, known-$H$ wrappers, whole-pair ambiguity, selector compilation, and the unknown-$H$ Abelian qubit counterprotocol. These finite identities support transcription and scope checks. The connected-orbit, determinant, operational normalization and no-SWITCH reduction above are analytic proofs, not conclusions inferred from a finite optimizer or the replay.

The separate [mean-query certificate](checks/coupler/verify_mean_query_certificate.py)
reconstructs the complete finite invariant bases, highest-weight kernels
and dimensions, scalar causal rows, objective, rational positive duals
and residual Gram equations for (Q2). The analytic prior, covariance,
stopping inclusion and trace bounds (Q3)--(Q7) supply its connection to
all ordinary receivers; the replay does not establish hardware access,
an amortized calibration advantage or a new Lean theorem.
