# Noisy phase calibration: certified two-call benchmark and native-memory boundary

[Application assessment](architecture.md) · [Bath backaction](backaction.md) · [Ordinary baselines](architecture-baselines.md) · [Checks](checks/README.md)

<a id="nr-r15"></a>

## NR-R15 — A finite phase-information separation and its physical boundary

Two independent amplitude-damping phase queries admit a switch protocol with attainable classical Fisher information $566/215$, while every ordinary strategy with a hard two-query cap has quantum Fisher information at most $64/25$. This is a certified instance of the established finite-query metrology separation of [Liu, Hu, Yuan and Yang, PRL **130**, 070803 (2023)](https://doi.org/10.1103/PhysRevLett.130.070803), not a new metrological mechanism. The proof below gives an explicit probe/readout and an exact feasible ordinary upper certificate.

A retained cold collision ancilla changes the comparison. If the same station can be visited twice before resetting that ancilla, an ordinary sensor echo has attainable information greater than $2.79$, exceeding even the ideal all-input, all-operating-phase optimum of the specified plain switch. Equal one-use reduced channels therefore do not justify importing the independent-channel bound into that native device. Neither result establishes a calibration-throughput advantage, a mean-query theorem or an asymptotic precision advantage. These analytic results and exact finite checks have not been formalized in Lean or externally peer reviewed.

At the benchmark decay $p=2/5$, the relevant resource distinctions are:

| Interface and budget | Verified comparison | Consequence |
| --- | --- | --- |
| Independent opaque channels, hard two-call cap | Explicit switch $F=566/215$; every ordinary strategy $J\le64/25$ | A finite local-information separation |
| Same independent channels, mean cost two | Ordinary three-call rounds launched with probability $2/3$ have $F>3$; the plain two-call switch has $J<66/25$ | The hard-cap result is not a mean-cost advantage |
| Cold ancilla retained across two native visits | Ordinary echo attains $F>2.79$ | The independent-channel comparator does not describe that hardware |
| Distinguishable jump times, coherent no-jump paths | An ordinary two-call check reproduces the full switched map | Reduced-channel equality alone does not preserve the metrology resource |

### Parameter, queries and information metric

Let $p\in[0,1]$ be the **known decay probability**, $s=1-p$, and

$$
\mathcal E_\phi=\mathrm{AD}_p\circ\operatorname{Ad}_{U_\phi},
\qquad U_\phi=e^{-i\phi Z/2}.
\tag{1}
$$

Each query has unit signal exposure. Amplitude damping is phase covariant, so reversing the two reduced-channel factors gives the same channel. The unknown parameter is only $\phi$; unknown damping would require a nuisance-parameter or multiparameter analysis. All Fisher information below is local at a specified nominal phase, with the input and measurement held fixed when taking the derivative.

For an outcome distribution $P_j(\phi)$, $F=\sum_j\dot P_j^2/P_j$. Quantum Fisher information $J$ is the supremum over final measurements. The independent-channel ordinary class allows arbitrary clean ancillary quantum memory, entangled inputs, parameter-independent intermediate controls, measurements/feedforward and a joint final readout. Controls may use the nominal operating point, not the unknown infinitesimal deviation. Each round has at most two queries to the opaque system-only channel, with fresh independent inaccessible environments. Early stopping can be padded by unused queries on a discarded register. All outcomes, including failure flags, belong in the information measure.

The **plain switch** has Kraus operators

$$
W_{ij}=|0\rangle\langle0|_C\otimes K_jK_i
       +|1\rangle\langle1|_C\otimes K_iK_j,
\tag{2}
$$

arbitrary initial target/control/reference state, and no intermediate operation between its two slots. Its target, reference and control outputs are all available at the end. This is the $\mathsf{SWI}$ class of [Liu et al., Appendix E.3](https://arxiv.org/html/2203.09758v3), distinct from larger causally superposed strategies with extra intermediate controls.

### Explicit full output and attainable information

A convenient Kraus gauge is

$$
K_0=\operatorname{diag}(1,\sqrt{s}e^{i\phi}),
\qquad K_1=\sqrt p\,|0\rangle\langle1|.
$$

Changing individual Kraus phases does not change (2), because both orders acquire the same product of phases. Put $V=K_0^2=\operatorname{diag}(1,se^{2i\phi})$. Then $K_0K_1=K_1$, $K_1K_0=\sqrt{s}e^{i\phi}K_1$ and $K_1^2=0$.

With initial control $|+\rangle$, any target/reference input $\rho_{TR}$, and parameter-independent control dephasing of visibility $\nu\in[0,1]$, the complete output is

$$
V\rho_{TR}V^\dagger\otimes\frac{I+\nu X}{2}
 +|0\rangle\langle0|_T\otimes\rho_{11,R}\otimes
 p\left[\frac{1+s}{2}I+\nu\sqrt{s}\cos\phi\,X\right],
\tag{3}
$$

where $\rho_{11,R}=\langle1|_T\rho_{TR}|1\rangle_T$. This follows by summing the no-jump and the two one-jump Kraus pairs in (2); no branch is discarded.

Choose

$$
|\psi_x\rangle_{TR}=\sqrt{1-x}|00\rangle+\sqrt{x}|11\rangle,
\qquad0\le x\le1.
\tag{4}
$$

The no-jump vector is $|w\rangle=\sqrt{1-x}|00\rangle+s e^{2i\phi}\sqrt{x}|11\rangle$, with weight $n_0=1-x+s^2x$. The jump sector is the orthogonal state $|01\rangle_{TR}$ with weight $j=xp(1+s)$. Both weights are phase independent. The no-jump pure-state information, multiplied by its weight, is $16s^2x(1-x)/n_0$. The normalized jump control has Bloch coordinate $2\nu\sqrt{s}\cos\phi/(1+s)$; its information is $\dot r^2/(1-r^2)$. Consequently

$$
J(x;p,\phi,\nu)=\frac{16s^2x(1-x)}{1-x+s^2x}
 +\frac{4xps(1+s)\nu^2\sin^2\phi}
 {(1+s)^2-4s\nu^2\cos^2\phi}.
\tag{5}
$$

At $p=2/5$, $x=2/3$ and nominal $\phi=\pi/2$, the following fixed four-outcome measurement attains (5): distinguish the jump state from the no-jump span; on no-jump measure the logical $Y$ vectors $(|00\rangle\pm i|11\rangle)/\sqrt2$, ignoring $C$; on jump measure $X_C$. Extend the measurement arbitrarily off this state's support. The no-jump probabilities are

$$
P_{Y,\pm}=\frac{n_0}{2}\pm s\sqrt{x(1-x)}\sin2\phi,
$$

and the jump probabilities are $P_{C,\pm}=xp[(1+s)/2\pm\nu\sqrt{s}\cos\phi]$. At the nominal phase they are $43/150,43/150,16/75,16/75$, with derivative magnitudes $2s\sqrt{x(1-x)}$ and $xp\nu\sqrt{s}$ respectively. Summing all four contributions gives

$$
F_{\rm fixed}=\frac{96}{43}+\frac25\nu^2,
\qquad F_{\rm fixed}(1)=\frac{566}{215}>\frac{64}{25},
\tag{6}
$$

with gap $78/1075$. This is a joint target/reference/control readout, not probe-only or a postselected control statistic.

### Exact upper bound for every ordinary two-query strategy

The proof uses the purification/comb method underlying [Liu et al., Theorem 1 and Appendix E.2](https://arxiv.org/html/2203.09758v3). Its feasible-upper-bound implication also has a direct weak-duality proof, given here to specify what the certificate establishes.

Use output-first, row-major vectorization and wire order $(o_2,i_2,o_1,i_1)$. At $\phi=0$, use the physical Kraus gauge $K_i(\phi)=D_iU_\phi$, with $D_0=\operatorname{diag}(1,\sqrt{s})$, $D_1=\sqrt p|0\rangle\langle1|$. For $a=(i,j)\in\{0,1\}^2$, let $n_a=\operatorname{vec}(D_i)\otimes\operatorname{vec}(D_j)$. Coordinate $\xi=(o_2,i_2,o_1,i_1)$ has derivative

$$
\dot n_a[\xi]=i\,d_\xi n_a[\xi],\qquad d_\xi=i_2+i_1-1.
$$

Choose a real diagonal environment gauge $h=\operatorname{diag}(h_a)$, and define the real $8\times8$ matrix

$$
T_{(i_2,o_1,i_1),(a,o_2)}=(h_a-d_\xi)n_a[\xi].
\tag{7}
$$

The gauged derivative is $-iT$ after slicing its last output. Purify the initial input with amplitudes $\alpha_{i_1m_0}$ and the intermediate control into an isometry $B_{i_2m_1;o_1m_0}$. Put $w_{i_2o_1i_1;m_1}=\sum_{m_0}B_{i_2m_1;o_1m_0}\alpha_{i_1m_0}$ and $R_{rs}=\sum_{m_1}\overline{w_{r;m_1}}w_{s;m_1}$. Isometry normalization gives

$$
R\ge0,\qquad\operatorname{Tr}_{i_2}R=I_{o_1}\otimes\rho_{i_1},
\qquad\operatorname{Tr}\rho=1.
\tag{8}
$$

Here $\rho$ may be the transposed initial marginal under this vectorization convention; it is still positive with unit trace. Gauge rotation of the inaccessible environment changes only the purification. The state-purification bound $J\le4\|\dot\Psi\|^2$, followed by contraction of these amplitudes, gives

$$
J\le\operatorname{Tr}(R\,4TT^\mathsf T).
\tag{9}
$$

Arbitrary CPTP controls and classical feedforward can be purified into $B$ and retained memory; discarding records or final measurement cannot increase $J$.

Suppose a real symmetric $4\times4$ matrix $Q$ satisfies $\operatorname{Tr}_{o_1}Q=I_{i_1}$ and

$$
\mathcal A=\begin{pmatrix}
\lambda I_8/4&T^\mathsf T\\T&I_{i_2}\otimes Q
\end{pmatrix}\succeq0.
\tag{10}
$$

The Schur complement implies $4TT^\mathsf T\preceq\lambda(I_{i_2}\otimes Q)$. Equations (8)–(9) then give $J\le\lambda\operatorname{Tr}[\rho\operatorname{Tr}_{o_1}Q]=\lambda$. Only feasibility is needed; the optimizer's claimed optimum is not trusted.

For $p=2/5$, an exact feasible witness has $\lambda=64/25$,

$$
h=\operatorname{diag}\left(-\frac{220013}{10^6},\frac{436492}{10^6},\frac{785524}{10^6},1\right),
$$

and $Q=(1-\epsilon)Q_0+(\epsilon/2)I_4$, where $\epsilon=1/10000$ and

$$
Q_0=\begin{pmatrix}
1&0&0&-6767/10^6\\
0&149/1250&0&0\\
0&0&0&0\\
-6767/10^6&0&0&1101/1250
\end{pmatrix}.
\tag{11}
$$

The partial-trace constraint is exact. The [certificate](checks/architecture/metrology_sequential_certificate.json) supplies these rational data. The [standard-library checker](checks/architecture/verify_metrology.py) rebuilds (7)–(10), encloses $\sqrt{2/5},\sqrt{3/5}$ by rational intervals of width $10^{-30}$, and forms a rational center $A_c$ and row-sum error bound $\delta$. It verifies all 16 strictly positive pivots and reconstructs every coordinate of an exact $LDL^\mathsf T$ factorization of $A_c-\delta I$. Since $\|\mathcal A-A_c\|\le\delta$, this proves (10) for the exact radicals. It is an exact certificate, not a floating-point solver tolerance.

Finally, $\mathcal E_{\phi_0+\theta}=\operatorname{Ad}_{U_{\phi_0}}\circ\mathcal E_\theta$; known phase compensation gives a bijection of the ordinary local strategy classes. Thus

$$
J_{\rm Seq}^{(2)}(p=2/5)\le64/25
\tag{12}
$$

at every operating point. The general metrology mechanism, strategy definitions and author implementation are from [Liu et al.](https://arxiv.org/abs/2203.09758) and their [MIT-licensed code](https://github.com/qiushi-liu/strategies_in_metrology). The certificate records the source commit and hashes; the verifier relies on the mathematical data, not provenance metadata or an installed optimizer.

### Why the plain-switch optimum includes every initial input

For a channel, let $f(\sigma)$ be the output QFI when it acts on a purification of input marginal $\sigma$. Different purifications differ by a parameter-independent reference isometry, so $f$ is well defined. It is **concave in the reduced input marginal**: purify a mixture with an extra coherent reference flag; dephasing that flag yields the flagged ensemble of output states, whose QFI is the average of the component values. Data processing therefore gives $f(\sum_a t_a\sigma_a)\ge\sum_a t_af(\sigma_a)$. This is not a claim that unpurified state QFI is concave.

The identical-slot channel (2) is covariant under $Z_C$, under $X_C$ by exchanging the two Kraus labels, and under target $Z$ rotations. The parameter-independent control dephasing has these same covariances. Concavity and covariance let us twirl any target/control input marginal to

$$
\operatorname{diag}(1-x,x)_T\otimes I_C/2
\tag{13}
$$

without reducing extended QFI. Purify it by (4) and a Bell state of $C,R_C$. Every $W_{ij}$ is diagonal on $C$, so the fixed isometry $J_C|c\rangle=|c,c\rangle_{C,R_C}$ carries the plus-control output to the Bell-control output. This also holds after control dephasing. It preserves QFI, proving that (5) already maximizes over all target/control/reference inputs when optimized over $x$.

For $0<p<1$, its phase-dependent term is a positive multiple of $u/(a+bu)$ with $u=\sin^2\phi$ and $a>0$. It is maximized at $\phi=\pi/2$ modulo $\pi$. At ideal visibility, (5) becomes

$$
J(x)=\frac{16s^2x(1-x)}{1-(1-s^2)x}+\frac{4ps}{1+s}x.
\tag{14}
$$

Put $y=1-(1-s^2)x$. Up to a constant independent of $y$, (14) equals $-4sy/p^2-16s^4/[(1-s^2)^2y]$. Its interior maximum is at $y_*=2s^{3/2}/(1+s)\in(s^2,1)$, giving the **all-input and all-phase plain-switch optimum**

$$
J_{\rm SWI,max}^{(2)}(s)
=\frac{4s(1+s-2s^{3/2})^2}{(1-s^2)^2}.
\tag{15}
$$

The endpoints follow by continuity: $J=0$ at $s=0$, $J=4$ at $s=1$. At $s=3/5$, (15) is $321/16-(45/2)\sqrt{3/5}\approx2.6340749421$. This is an upper bound for the specified raw-slot plain switch, not every protocol with extra native memory or interleaved controls.

### Physical jump records, loss and an exact zero-overlap screen

The signal in the jump sector requires coherent overlap between the same physical station's early and late records. Matching reduced amplitude-damping channels does not fix that overlap. Suppose both stations have the same real, locally parameter-independent single-jump overlap $\mu$, independent control dephasing has visibility $\nu$, and the diagonal ordered channels remain $\mathcal E_\phi\circ\mathcal E_\phi$. A calibrated phase-independent no-jump control state does not affect the no-jump QFI. The jump term in (3) then uses $z=\mu\nu$ in place of $\nu$. In particular,

$$
F_{\rm fixed}(z)=96/43+(2/5)z^2,
\qquad z^2>176/215
\tag{16}
$$

is sufficient to beat (12), requiring $|z|>0.9047677\ldots$. Unequal or complex station overlaps require their actual control density matrix; empty-interferometer visibility is not a substitute for $\mu$.

If both jump overlaps vanish and the no-jump histories remain coherent, the full switched map is

$$
(I_C\otimes V)\rho(I_C\otimes V^\dagger)
 +\mathcal D_{Z_C}\!\left[\sum_{(i,j)\ne(0,0)}
 (I_C\otimes K_jK_i)\rho(I_C\otimes K_jK_i)^\dagger\right],
\tag{17}
$$

where $\mathcal D_{Z_C}$ dephases the original control. This identity holds for arbitrary initial target/control/reference input: the two one-jump weights sum equally on both diagonal control blocks, while their cross-history coherence is absent. An ordinary two-query circuit reproduces it. Use a separate syndrome ancilla, controlled target $Z$ before and after fixed-order composition, and read that ancilla in $X$. Since $ZK_0Z=K_0$, $ZK_1Z=-K_1$ and $K_1^2=0$, it flags no jump versus every nonzero jump. On jump apply $\mathcal D_{Z_C}$; otherwise leave $C$ intact. This proves the full instrument equality, including references, without environment access. For initial $C=+$ it simply prepares $+$ on no jump and $I/2$ on jump. A different calibrated parameter-independent no-jump control state can likewise be prepared for that fixed-control experiment. Parameter-dependent no-jump records and arbitrary wavepackets are outside this reduction.

In a simple instantaneous-deposit leaking-cavity model, early/late record overlap has magnitude $e^{-\kappa\tau/2}$, where $\kappa$ is the energy-leakage rate and $\tau$ the visit offset; finite pulses need the full packet overlap. A retained cavity mode can avoid an immediate time record, but it may also supply the ordinary memory discussed next. The [cavity-QED proposal of Castaños-Cervantes, Procopio and Bartley](https://arxiv.org/html/2509.02209v2) retains the cavity fields and proposes coherent atomic routes; it is not a demonstration of this partial-damping phase-calibration benchmark. A detuning inside a Jaynes–Cummings interaction is not automatically an independent phase with fixed $p$.

For parameter-independent flagged survival $\eta$ with uninformative failures, the information per launch is $\eta F_{\rm success}$. For example $z=0.97$, $\eta=0.99$ gives $2.582828958\ldots>64/25$ under precisely that loss/dephasing model. It is not a bound for arbitrary helper noise. If both queries are spent on every launch, a sufficient information-rate comparison with an ideal two-query ordinary round is $T_{\rm SWI}/T_{\rm Seq}<\eta F_{\rm success}/(64/25)$. These are conditional ledger thresholds, not measured device efficiencies or a universal rate theorem. Parameter-dependent loss flags can themselves carry information and must be retained.

### Retained cold ancilla: an ordinary two-visit echo beats (15)

Let a native station contain a cold qubit $E$, initially $|0\rangle$, with exchange angle $\alpha\in[0,\pi/2]$ and interaction

$$
C_\alpha=e^{-i\alpha(\sigma_+^S\sigma_-^E+\sigma_-^S\sigma_+^E)},
\quad p=\sin^2\alpha,\quad s=\cos^2\alpha.
\tag{18}
$$

It fixes $|00\rangle,|11\rangle$ and has one-excitation block $\bigl(\begin{smallmatrix}\sqrt{s}&-i\sqrt p\\-i\sqrt p&\sqrt{s}\end{smallmatrix}\bigr)$. A single visit $C_\alpha(U_\phi\otimes I)$ reduces to (1). The native model here retains this same cold ancilla coherently across two ordinary visits and resets it only between independent statistical rounds. The physical graph must permit a return to that station; otherwise that is a separate access restriction. No direct measurement or pulse on $E$ is used.

Use known local phase compensation to write $\theta=\phi-\phi_0$, holding $\phi_0$ fixed. Sensor $Z$ reverses the exchange Hamiltonian, so $Z_SC_\alpha Z_S=C_\alpha^\dagger$ and

$$
V_\theta Z_SV_\theta Z_S=C_\alpha U_\theta C_\alpha^\dagger U_\theta,
\qquad V_\theta=C_\alpha U_\theta.
\tag{19}
$$

The physical left side uses two forward native visits and known sensor pulses, not an inverse-interaction port. Applied to $|+\rangle_S|0\rangle_E$, it gives

$$
\frac1{\sqrt2}\left[e^{-i\theta}|00\rangle+
 (p+se^{i\theta})|10\rangle+
 i\sqrt{ps}(1-e^{i\theta})|01\rangle\right].
\tag{20}
$$

Tracing $E$ gives $\rho_{11}=|p+se^{i\theta}|^2/2$ and $\rho_{01}=(pe^{-i\theta}+se^{-2i\theta})/2$. The phase-after-exchange visit $U_\theta C_\alpha$ gives the same reduced sensor state: in (20) only the bath-excited amplitude gains $e^{-i\theta}$. Thus this result does not depend on choosing a favorable reduced-channel factor order.

An ordinary sensor $X$ measurement has mean $m(\theta)=p\cos\theta+s\cos2\theta$ and attainable information

$$
F_X(\theta)=\frac{[p\sin\theta+2s\sin2\theta]^2}
 {1-[p\cos\theta+s\cos2\theta]^2},
\qquad\lim_{\theta\to0,\,\theta\ne0}F_X=1+3s.
\tag{21}
$$

The limit follows by expanding numerator and denominator to second order: both contain the factor $(p+4s)\theta^2$, leaving $p+4s=1+3s$. At exactly zero the dark probability vanishes and sign identification is nonregular; the claim uses a nonzero local offset. At $p=2/5$, $\cos\theta=399/401$, $\sin\theta=40/401$ gives

$$
P(X=-)=\frac{5602}{804005}>0,\qquad
F_X=\frac{6249620000}{2236326803}>2.79.
\tag{22}
$$

All quantities follow by rational substitution in (21). Meanwhile (15) is less than $66/25=2.64$: $\sqrt{3/5}>2323/3000$, verified by squaring positive numbers, proves this directly. More generally, for $r=\sqrt{s}$,

$$
\begin{aligned}
&(1+3r^2)(1-r^4)^2-4r^2(1+r^2-2r^3)^2\\
&\quad=(1-r)^4(1+4r+9r^2+16r^3+15r^4+12r^5+3r^6)>0
\end{aligned}
\tag{23}
$$

for $0\le r<1$. Dividing by the positive denominator proves $1+3s>J_{\rm SWI,max}^{(2)}(s)$ for $0\le s<1$; continuity handles the endpoint of (15). For each interior $s$ a sufficiently small nonzero offset retains a strict advantage. Equation (22) supplies a regular explicit point at the benchmark damping.

This is an attainable ordinary lower bound in a **different memory process**, not a counterexample to (12). It compares with the plain independent-slot switch, not every possible protocol using retained bath memory. It requires cold preparation, coherent retention, ordinary return routing and sensor phase pulses, all with their real durations and errors. Coherent access to an exposed environment would enlarge the ordinary class further; classical jump records alone do not imply that stronger access.

### Three ordinary independent queries rule out a mean-two interpretation

Even with fresh inaccessible damping environments, a longer ordinary block can defeat an interpretation based only on mean call count. The following explicit protocol uses three queries and a clean reference/memory $R$. Its code basis is $|0_L\rangle=|00\rangle_{TR}$, $|1_L\rangle=|11\rangle_{TR}$; initialize $|+_L\rangle$. Known phase compensation centers each query at offset $\theta=0$.

After each query, distinguish the code span from jump state $|01\rangle$ by a known joint syndrome measurement. Complete it arbitrarily on the unused $|10\rangle$ state. On jump reprepare $|+_L\rangle$; on no jump apply the fixed real code rotation

$$
B=\frac1{\sqrt{2(1+s)}}
\begin{pmatrix}1+\sqrt{s}&\sqrt{s}-1\\1-\sqrt{s}&1+\sqrt{s}\end{pmatrix}.
\tag{24}
$$

This rotation sends the nominal no-jump vector $(1,\sqrt{s})/\sqrt{1+s}$ back to $|+_L\rangle$. Keep every syndrome and finish with logical $Y$. There is no postselection or environment access.

To prove its information, represent the pre-query local tangent, up to an irrelevant global phase, by $|\dot\psi\rangle=i t(-|0_L\rangle+|1_L\rangle)/\sqrt2$ at nominal $|+_L\rangle$. The no-jump vector and derivative are $(1,\sqrt{s})/\sqrt2$ and $i(-t,\sqrt{s}(t+1))/\sqrt2$. The branch probability $n=(1+s)/2$ has zero derivative. Projecting the normalized derivative orthogonally to that vector, then applying (24), gives the recurrence

$$
t\longmapsto r(t+1/2),\qquad r=\sqrt{s}/n.
\tag{25}
$$

The jump probability $j=p/2$ also has zero derivative. Its one-dimensional state carries only a global phase; repreparation resets $t$ to zero. Logical $Y$ attains conditional information $4t^2$. Thus, at $p=2/5$, $n=4/5$, $j=1/5$ and $r=\sqrt{15}/4$, define $t_k=(r+\cdots+r^k)/2$. Final consecutive no-jump runs of lengths $3,2,1,0$ have probabilities $n^3,jn^2,jn,j$. All records together therefore give

$$
F_3=4(n^3t_3^2+jn^2t_2^2+jnt_1^2)
   =\frac{843+168\sqrt{15}}{320}>\frac92.
\tag{26}
$$

This is an attained classical information, with parameter-independent syndrome probabilities to first order. Launch it with probability $2/3$ and otherwise emit a parameter-independent skip flag. Keeping that flag gives exactly two queries in expectation and information $(2/3)F_3>3$, exceeding the all-input plain-switch value (15), which is less than $66/25$. Its information per query also exceeds $3/2$, whereas the two-query plain switch has less than $33/25$ per query. These are query-count comparisons, not wall-clock rate comparisons: syndrome extraction, feedback, resets and three-query coherence have real costs. The construction establishes a counterbenchmark to those broader interpretations, not the optimal ordinary value under either budget.

<a id="nr-r15-known-control-qec"></a>

### Known auxiliary gates and coherent reversal of the signal

[Xu et al., PRL **137**, 020801 (2026)](https://doi.org/10.1103/9mjc-nhxx)
study error correction by switching known auxiliary gates with noisy
sensing evolution. Their parallel-noise construction additionally uses
coherent forward/backward Hamiltonian evolution. The following comparisons
refer to the explicitly stated map in the
[public preprint, Eqs. (4)--(8)](https://arxiv.org/html/2601.01404v1);
the published supplement's platform constructions were not audited here.
They distinguish known-gate order control from the physical signal-reversal
interface, without contesting the stated restricted comparisons.

**A known-gate switch has an exact ordinary implementation.** Let $V$ be
a known parameter-independent unitary, $K_j$ arbitrary Kraus operators of
one sensing interval, and define
$F_V=P_0^A\otimes V+P_1^A\otimes I$ and
$G_V=P_0^A\otimes I+P_1^A\otimes V$. Direct multiplication gives

$$
P_0^A\otimes VK_j+P_1^A\otimes K_jV
 =F_V(I_A\otimes K_j)G_V.
\tag{IQ1}
$$

The right side is chronological: apply known $V$ controlled on $A=1$,
use the actual sensing interval once, then apply known $V$ controlled on
$A=0$. Each history contains one occupied $V$, with two programmed
placement windows. No inverse of $V$, or matrix description, inverse or
controlled version of the unknown sensing evolution is used. There is no assumption that $V$
commutes with the signal or that the noise is Pauli. The identity holds
for every input and passive reference and, with the bath included in
$K_j$, for the stipulated joint dilation. Consequently it preserves the
entire flagged instrument, subsequent recovery and all parameter
derivatives when these controls are held fixed. It is not only an
agreement of one control fringe or a first-order error expansion.

More generally, if branch $s$ places known products on either side of
one common unknown interval, its Kraus operator is $L_sK_jR_s$. Known
controlled-$R_s$ before the interval and controlled-$L_s$ after it give
the complete superposition of those branches. All known controlled
gates, helper memory, readout and faults have their actual costs. A
temporally different joint bath interaction in the two branches is a
different interface; equality of isolated reduced channels does not
establish the common-dilation premise. Nor does a classically selectable
opaque auxiliary operation automatically provide its controlled unitary.

**Parallel signal and noise require the coherent extension.** To make
the premise concrete, use parameter $\omega$ and signal Hamiltonian
$\omega Z_P$, rather than the dimensionless $\phi Z/2$ convention of
(1). On direction helper $A$ and probe $P$, compare the two exact joint
generators, with $\kappa\ge0$,

$$
\begin{aligned}
\mathcal L_g(\rho)&=-i[\omega Z_AZ_P,\rho]
       +\kappa[(I_AZ_P)\rho(I_AZ_P)-\rho],\\
\mathcal L_b(\rho)&=-i[\omega Z_AZ_P,\rho]
       +\kappa[(Z_AZ_P)\rho(Z_AZ_P)-\rho].
\end{aligned}
\tag{IQ2}
$$

Restrict either generator to classical $A=0$ or $A=1$. Both give exactly
the same probe channel with Hamiltonian $+\omega Z_P$ or $-\omega Z_P$
and dephasing $\kappa(Z_P\rho Z_P-\rho)$, for every time and parameter.
The noise signs disappear because $\mathcal D[Z_P]=\mathcal D[-Z_P]$.
Thus even complete characterization of both classical direction channels
does not determine the coherent direction interface. In $\mathcal L_g$
the same signed noise acts on both branches; in $\mathcal L_b$ a jump
has an additional relative minus sign. This off-diagonal information is
physical, rather than a Kraus representation one may choose freely.

**The same-signed extension already has a simpler ordinary sensor.**
Prepare $P=|0\rangle$ and $A=|+\rangle$. Under $\mathcal L_g$, noise
acts trivially on this probe eigenstate, while the signal acts on $A$:

$$
e^{t\mathcal L_g}(|+\rangle\langle+|_A\otimes|0\rangle\langle0|_P)
 =e^{-i\omega tZ_A}|+\rangle\langle+|e^{i\omega tZ_A}
                         \otimes|0\rangle\langle0|_P.
\tag{IQ3}
$$

Its unconditional quantum Fisher information is $4t^2$, since the pure
state has $4\operatorname{Var}_{+}(tZ_A)=4t^2$. One helper, the same
probe and one sensing interval suffice. There is no syndrome readout,
rejection, encoded entanglement or correction. This is a comparator
when the actual coherent sign-controlled interaction, eigenstate
preparation and helper readout are available. It is not a construction
of that interaction from the two classical probe channels.

For $\mathcal L_b$, the same preparation gives helper visibility
$v=e^{-2\kappa t}$ and QFI $4t^2e^{-4\kappa t}$. Indeed its helper
state has Bloch vector $v(\cos2\omega t,\sin2\omega t,0)$ up to the
chosen sign convention; its radial derivative is zero and the squared
angular derivative is $4t^2v^2$. The two native extensions therefore
have different sensing power despite identical classical channels.
Repeated independent rounds with total exposure $T$ and integer $T/t$
give $4Tt e^{-4\kappa t}$ for this ordinary preparation. In the many-round
limit at $\kappa>0$, its best interrogation time is $t=1/(4\kappa)$
and its information per total exposure tends to $1/(e\kappa)$; finite
budgets retain the integer and end-round constraints. This statement concerns this explicit preparation,
not an optimized all-protocol upper bound. Local QFI also does not
solve global phase unwrapping or price a finite-prior estimation task.

**The error-correction interpretation has the same resource boundary.**
Let $C_X=P_0^A\otimes I+P_1^A\otimes X_P$. Its exact conjugations are

$$
C_X(Z_AZ_P)C_X=I_AZ_P,\qquad
C_X(I_AZ_P)C_X=Z_AZ_P.
\tag{IQ4}
$$

For $p_0=(1+v)/2$, $p_1=(1-v)/2$, a common Kraus family for the
same-signed extension is
$\Omega_j=\sqrt{p_j}(I_A\otimes Z_P^j)e^{-i\omega tZ_AZ_P}$.
Consequently

$$
C_X\Omega_j C_X
 =\sqrt{p_j}\,Z_A^j\otimes
                  [Z_P^je^{-i\omega tZ_P}],\qquad j=0,1.
\tag{IQ5}
$$

Prepare $A=+$, measure it in $X$, and correct $Z_P^j$. This chronological
pre/post check retains every branch and implements the noiseless sensing
unitary exactly in this commuting model, at every time. It uses the
granted coherent sign interaction and known controlled-$X$ gates, with
no inverse of the unknown signal. For the opposite-signed extension
the additional $Z_A^j$ cancels the syndrome in (IQ5); the same procedure
leaves parallel probe dephasing. The two classical direction channels
alone do not justify selecting the correctable extension.

Equivalently, the code
$C_X(|+\rangle_A\otimes\mathcal H_P)$ is spanned by
$|\Phi^+\rangle,|\Psi^+\rangle$ and has stabilizer $X_AX_P$.
In the original same-signed joint model the signal $Z_AZ_P$ acts as
logical $Z$, while $I_AZ_P$ changes the stabilizer and is correctable.
The joint signal lies outside the noise's Lindblad span. This is
consistent with ordinary metrological QEC; the enlarged joint sensing
interface differs from $H=\omega Z_P$, $L=Z_P$ with a spectator helper.
If the same fluctuating physical coefficient $(\omega+b(t))$ multiplies
the generator, coherently reversing its sign reverses signal and noise
together. Separating those two responses needs an actual device model.

If only a sealed higher-order map is provided, ordinary access to its
underlying sign-controlled interaction need not follow automatically.
Its input/output ports and inability to undo known surrounding controls
would need to be stated. Conversely, hardware exposing the interaction
in (IQ2) with its same-signed bath, probe preparation and helper readout
already exposes (IQ3). A matched architecture claim must charge the
physical sign control, bath cross coherence, helper noise, gate and
readout time, phase acquisition and all failed launches for both methods.
These conditional comparisons do not settle every time-direction
process or audit an unexamined implementation in the published supplement.

### Resource boundary and the next test

The two-query certificate cannot be multiplied into a converse for expected query budgets, entangled blocks spanning many rounds, or unrestricted information per query; (24)–(26) explicitly exclude the mean-two and unrestricted per-query interpretations for the plain switch. A persistent calibration source does not force the ordinary receiver into independent two-call rounds. Numerical optimizations at three queries are not exact converse extensions of (12), and no asymptotic or calibration-throughput conclusion is drawn here. Global finite-prior estimation, phase-sign acquisition, adaptive recentering and estimating $p$ as well as $\phi$ require their own costs and error analysis.

A physical implementation must identify the actual signal, its exposure time and drift, the complete early/late noise records, control and reference encodings, return ports, environment-reset policy, loss flags and final joint readout. Ordinary ancilla-assisted noisy optical phase estimation is already experimentally available, for example [Sbroscia et al.](https://arxiv.org/abs/1707.08792); a separate stored reference photon is not an intrinsic universal cost. Polarization-dependent erasure is also not automatically qubit amplitude damping.

The remaining falsifiable target is a named module with independently reset opaque partial damping, sufficient coherent record overlap, an achievable joint readout and routing whose full launch/time cost beats the best ordinary strategy for those same native ports and admissible interrogation lengths. A retained-memory implementation must include repeat-visit echoes and other memory controls; a fresh emitted bath must establish its wavepacket overlap. The [exact replay](checks/architecture/verify_metrology.py) certifies the finite dual, readout arithmetic, robustness identities, regular echo examples and three-query recurrence arithmetic. The covariance/concavity and native-interface arguments are analytic proofs above, not a Lean proof, hardware experiment or claim of a deployed advantage. The architecture question remains open.
