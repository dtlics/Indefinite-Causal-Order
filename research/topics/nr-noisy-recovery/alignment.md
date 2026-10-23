# Drifting measurement alignment: exact two-query limit and reuse costs

[Application assessment](architecture.md) · [Measurement baselines](architecture-baselines.md) · [Metrology](metrology.md) · [Checks](checks/README.md)

<a id="nr-r18"></a>

## NR-R18 — An exact alignment benchmark with a strict query deadline

Two unread qubit dephasers with a fresh unknown common orientation admit an ordinary two-query alignment alarm with exactly zero false positives. The best ordinary alarm has probability $9\sin^2\theta/64$, whereas the ideal switch control alarm has probability $\sin^2\theta/4$. The optimal ordinary one-sided local Fisher-information limit is $9/16$; the switch control readout attains limit $1$. Thus the difference is a constant factor under a hard two-query cap. A proposed vanishing-versus-constant ordinary/switch information scaling is false.

Longer ordinary rounds remove any uniform positive margin inferred from that hard-cap result: a simple family, randomized to have two expected queries, approaches local information $1$. Accessible Lüders records already attain information $1$ with two ordinary queries. Any fixed imperfect switch-control visibility makes its information vanish at alignment. These results do not establish an alignment-throughput advantage or a native hardware application. The fresh-frame, unread-record and coherent-order interfaces require separate physical justification. The analytic proofs and exact rational replay below have not been formalized in Lean or externally peer reviewed.

### Model, parameter and query count

For unit Bloch vectors $n,m$ with $n\cdot m=\cos\theta$, let

$$
\mathcal E_n=\frac{\operatorname{id}+\operatorname{Ad}_{\sigma_n}}2,
\qquad
\mathcal F_m=\frac{\operatorname{id}+\operatorname{Ad}_{\sigma_m}}2,
\qquad \sigma_n=n\cdot\sigma .
\tag{1}
$$

These are unread rank-one Lüders dephasers. In each round a common Haar rotation acts on a pair of axes separated by $\theta$; that rotation is unknown, independent of $\theta$ and freshly redrawn between rounds. It stays fixed throughout all queries in a round. Individual uses have independent inaccessible Kraus records, conditional on the axes. Since an unread axis is unoriented, take $0\le\theta\le\pi/2$; an oriented-label comparison is stated separately below.

The ordinary experiment has a **hard cap of two total named-channel queries**. It permits arbitrary clean ancillary memory, entangled inputs, known intermediate isometries/instruments, classical adaptive choice of channel or stopping, coherent routing of a fixed named query to target registers, and a final joint measurement. All outcomes and failed filters count. It does not supply the off-diagonal extension of a coherently controlled choice between the unknown oracle names; two CPTP maps do not specify that additional interface.

The information quantity is the one-round classical Fisher information
$F=\sum_x\dot p_x^2/p_x$, optimized over the ordinary preparation, controls and final measurement, hence equal to optimized output quantum Fisher information. Controls and measurement may be chosen for a nominal operating point; hold that chosen experiment fixed when differentiating in $\theta$. Independent product repetitions add their classical information. The theorem is not a converse for arbitrary long coherent blocks, collective multi-round processing, or a budget imposed only on the expected total queries.

Exactly at $\theta=0$, the averaged density derivative vanishes, so conventional SLD information at that point is zero. The limits below are from $\theta>0$ at this rank-changing boundary. A regular Cramér–Rao statement evaluated exactly at zero would be inappropriate. The finite-angle zero-false-positive theorem gives a direct testing interpretation without that boundary issue.

### An elementary ordinary null event

Use normalized process kets $|A\rangle\!\rangle=(A\otimes I)|\Phi_2\rangle$, in $(\mathrm{output},\mathrm{input})$ wire order. The ket $|I\rangle\!\rangle$ is orthogonal to the three Pauli kets, and
$\langle\!\langle\sigma_n|\sigma_m\rangle\!\rangle=n\cdot m$. A Bell probe of one dephaser produces

$$
\rho_n=\frac{|I\rangle\!\rangle\langle\!\langle I|
                 +|\sigma_n\rangle\!\rangle\langle\!\langle\sigma_n|}{2}.
$$

Probe each channel once, retaining both references. Define $P=I_4-|I\rangle\!\rangle\langle\!\langle I|$ and

$$
K=(P\otimes P)\frac{I-\mathrm{SWAP}_4}{2}.
\tag{2}
$$

The commuting factors make $K$ a rank-three projector. The two Pauli-sector filters pass with probability $1/4$, and conditional antisymmetric probability is $(1-\cos^2\theta)/2$. Consequently the **unconditioned**, pointwise probability is

$$
\Pr(K)=\frac{\sin^2\theta}{8}.
\tag{3}
$$

This event has zero background for every common frame, without estimating that frame or reading the meters. It already disproves a claim that all ordinary two-query information vanishes near alignment. For $p=c\sin^2\theta$, the binary information is $4c\cos^2\theta/(1-c\sin^2\theta)$, with one-sided limit $4c$.

The complete common-rotation twirl has a parameter-independent total-spin measurement. Conditional on both Pauli flags, its spin-$0,1,2$ weights are respectively
$z/3,(1-z)/2,(3+z)/6$, where $z=\cos^2\theta$. Including the other flags, their probabilities are

$$
\frac14,\ \frac14,\ \frac14,\ \frac z{12},\ \frac{1-z}{8},\ \frac{3+z}{24}.
$$

The resulting full two-Bell-probe output information, attained by this measurement, is

$$
F_{\rm Bell}=\frac{1+z}{3+z}\longrightarrow\frac12.
\tag{4}
$$

### Exact ordinary null-event optimum

Fix port order $(\mathrm{outF},\mathrm{inF},\mathrm{outE},\mathrm{inE})$. Write $P_{00},P_{0t},P_{t0}$ for the identity/Pauli flag sectors and $J_0,K,J_2$ for the spin-$0,1,2$ projectors in the Pauli pair. Their dimensions are $1,3,3,1,3,5$, and they sum to $I_{16}$.

The averaged **unnormalized** two-slot Choi operator has trace four. Its exact form is

$$
\begin{aligned}
C_\theta={}&P_{00}+\frac{P_{0t}+P_{t0}}3
 +\frac z3J_0+\frac{1-z}{6}K+\frac{3+z}{30}J_2\\
={}&(1-s)C_0+sC_{\pi/2},\qquad s=\sin^2\theta,\\
C_0={}&P_{00}+\frac{P_{0t}+P_{t0}}3+\frac13J_0+\frac{2}{15}J_2,\\
C_{\pi/2}={}&P_{00}+\frac{P_{0t}+P_{t0}}3+\frac16K+\frac1{10}J_2.
\end{aligned}
\tag{5}
$$

For example the isotropic fourth moment is
$\mathbb E[n_i m_j n_k m_l]=B\delta_{ik}\delta_{jl}+A(\delta_{ij}\delta_{kl}+\delta_{il}\delta_{jk})$, where $A=(3z-1)/30$ and $B=(2-z)/15$. Its two contractions are $6A+9B=1$ and $12A+3B=z$, giving (5). In particular,
$\ker C_0=\operatorname{ran}K$ and $\operatorname{Tr}(KC_{\pi/2})=1/2$.

An ordinary E-then-F event tester $T$ satisfies

$$
0\le T\le I_{\rm outF}\otimes R,\quad R\ge0,\quad
\operatorname{Tr}_{\rm inF}R=I_{\rm outE}\otimes\rho,\quad
\rho\ge0,\quad\operatorname{Tr}\rho=1.
\tag{6}
$$

If its Haar-average false-positive probability is zero, positivity gives $T=KTK$. Twirling the event and its circuit preserves (6) and its probabilities. The antisymmetric product of two spin-one representations is itself the irreducible spin-one representation, so the twirled event is $T=\alpha K$.

**The largest feasible coefficient is exactly $\alpha=9/32$.** A primal witness has $\rho=I/2$, diagonal

$$
\operatorname{diag}(16R)=(4,5,3,4,4,3,5,4)
$$

and symmetric nonzero off-diagonals
$(16R)_{06}=(16R)_{17}=1$, $(16R)_{14}=(16R)_{36}=-1$. Both $R$ and $I\otimes R-(9/32)K$ are exactly positive semidefinite.

For a matching dual put $H=(aa^T+2bb^T+2dd^T)/96$, with all omitted vector entries zero and

$$
\begin{array}{c|rrrrrr}
 a& a_0=1&a_3=-1&a_6=-4&a_9=4&a_{12}=1&a_{15}=-1\\
 b& b_1=1&b_4=-2&b_7=2&b_{13}=-3&&\\
 d& d_2=3&d_8=-2&d_{11}=2&d_{14}=-1&&
\end{array}
$$

and

$$
Z=\frac3{32}\begin{pmatrix}1&0&0&-1\\0&2&0&0\\0&0&2&0\\-1&0&0&1\end{pmatrix}.
$$

The exact identities are

$$
H\ge0,\quad \operatorname{Tr}(HK)=1,\quad
\operatorname{Tr}_{\rm outF}H=I_{\rm inF}\otimes Z,\quad
\operatorname{Tr}_{\rm outE}Z=\frac9{32}I_{\rm inE}.
\tag{7}
$$

Thus every feasible $\alpha$ obeys
$\alpha\le\operatorname{Tr}[H(I\otimes R)]
=\operatorname{Tr}[Z(I\otimes\rho)]=9/32$.
It follows for **every** $\theta$ that the maximum Haar-average declaration probability among ordinary hard-two-query tests with zero false positives at alignment is

$$
p_{\rm ord,null}^{\max}(\theta)=\frac9{64}\sin^2\theta.
\tag{8}
$$

The upper bound is an average over the unknown common frame; it is not a pointwise upper bound for every deliberately frame-biased circuit. The attaining circuit below has the same probability for every frame.

### A native fixed-order circuit attaining the tester

Prepare a Bell pair on $\mathrm{inE}$ and memory $M$, query E, then apply the **known** isometry

$$
V_{b,z;a,i}=\sqrt2\,(\sqrt R)_{(b,a,i),z},\qquad \dim z=8.
\tag{9}
$$

Here $a$ is E's output, $i$ is the initial Bell memory and $b$ is F's input. Equation (6) with $\rho=I/2$ gives $V^\dagger V=I$. Query F and measure

$$
M_{\rm event}=\frac9{32}(I\otimes R^{-1/2})K(I\otimes R^{-1/2}).
\tag{10}
$$

The witness has spectrum $3/16,1/4,3/8$ with multiplicities $4,2,2$, so its positive square roots are unambiguous known matrices. The exact identity
$K(I\otimes R^{-1})K=(32/9)K$ makes (10) a rank-three orthogonal projector. Its tester is $(9/32)K$ and its event probability is (8) pointwise. This uses one Bell pair, a known isometry with three output-memory qubits and a joint four-qubit projector; those helpers are real implementation resources. No unknown inverse, axis-dependent gate or exposed Kraus flag is invoked.

The resulting binary information is

$$
F_{\rm ord,null}=\frac{36z}{55+9z}\longrightarrow\frac9{16}.
\tag{11}
$$

### Full optimized ordinary local-information limit

Purify ordinary preparation and free intermediate controls and retain their environments. Their outputs are linear contractions of the two channel Choi vectors, so the output ensemble lies in the image of a sixteen-dimensional space. An informative purified output of dimension at most sixteen suffices; its SLD measurement needs at most sixteen outcomes. Pad with zero outcomes if necessary.

For any chosen experiment/measurement let $T_x$ be its event testers, with $\sum_xT_x=I\otimes R$. By (5),

$$
p_x=a_x+s r_x,\qquad
a_x=\operatorname{Tr}(T_xC_0)\ge0,\quad
r_x=\operatorname{Tr}[T_x(C_{\pi/2}-C_0)]\ge-a_x.
$$

Its information is

$$
F_\theta=4s(1-s)\sum_x\frac{r_x^2}{a_x+s r_x}.
\tag{12}
$$

For $r_x<0$, the term is at most $4s a_x$ and vanishes at alignment. For $r_x\ge0$, it is at most $4(1-s)r_x$; if $a_x$ has a nonzero limit the actual term vanishes.

Allow both strategy and measurement to be selected separately at every positive operating point, always holding the selection fixed in (12). Their tester set is compact: $\operatorname{Tr}\rho=1$, $\operatorname{Tr}R=2$, $\sum_x\operatorname{Tr}T_x=4$, and all matrices are positive. Along any sequence $\theta\downarrow0$, choose a convergent subsequence for the at most sixteen effects. Only effects with limiting $a_x=0$ can contribute. Their aggregate $T_{\rm null}$ is feasible in (6) and supported in $K$. Equations (7)–(8) therefore give

$$
\limsup F_\theta\le4\operatorname{Tr}(T_{\rm null}C_{\pi/2})
\le\frac9{16}.
$$

The circuit (9)–(10) attains this limit, establishing

$$
\lim_{\theta\downarrow0}\ \sup_{\text{ordinary, hard two queries}}F_\theta
=\frac9{16}.
\tag{13}
$$

The F-first order has the same value by exchange symmetry. A classical initial choice is a parameter-independent mixture; retaining that choice label makes information its weighted average.

For conditional repeat/stop policies after an E-first call, retain the macro-query-choice flag. Branches that never query F have parameter-independent Haar-averaged subnormalized outputs, including their probabilities, because the marginal law of $n$ is uniform for every $\theta$. Keep the one-E-one-F branch unchanged. On a repeat/stop branch, omit the repeat, retain the actual post-first-call memory, call F on an independent dummy register and discard that output. These other branches are still parameter independent, since F is trace preserving pointwise. The resulting deterministic one-of-each comb preserves the informative branch and its information. For a null test, make the padded branches output no declaration: the original branch's parameter-independent declaration mass is zero at alignment and hence zero everywhere. This preserves the averaged declaration probability without claiming the original measurement is preserved pointwise. This is a statistical upper reduction after Haar averaging; it does not simulate a second E query pointwise or prepare an inaccessible reference state. Thus (8) and (13) cover ordinary classical repeat/stop policies too.

Coherent target routing for a fixed named call is already an allowed isometry. A coherent superposition of the oracle **names**, with prescribed cross-label amplitudes, would supply a further channel extension and is outside (1). A physical route using both named boxes must charge its actual calls.

### Switch control readout and parallel benchmark

With initial control $|+\rangle$, the only noncommuting Kraus pair is $\sigma_n/\sqrt2,\sigma_m/\sqrt2$. Its minus-control amplitude is $[\sigma_m,\sigma_n]/4$, whose squared norm is $\sin^2\theta\,I/4$. Therefore, for every target/reference input,

$$
p_{S,-}=\frac{\sin^2\theta}{4},\qquad
F_{S,X}=\frac{4z}{3+z}\longrightarrow1.
\tag{14}
$$

Equation (14) is an **achieved control-readout** information, not a claimed all-input optimum for every enlarged switched interface. Compared with (8), its zero-false-positive declaration probability is larger by $16/9$ throughout the angle range. Compared with (13), it gives a strict local hard-cap separation.

For context, the optimum ordinary **parallel** null coefficient is slightly below the adaptive optimum. Twirl its two-input state to $\rho=a\Pi_s+b\Pi_t$, $a+3b=1$. After regrouping output and input wires, every vector in $K$ has equal norm in output-triplet/input-singlet and output-singlet/input-triplet sectors. For $a,b>0$, completing $T=\alpha K$ under $G=I_{\rm out}\otimes\rho$ is equivalent to $\alpha\|KG^{-1}K\|\le1$, hence to

$$
\alpha\le\left(\frac1{2a}+\frac1{2b}\right)^{-1}=\frac{2ab}{a+b}.
$$

Its maximum is $2-\sqrt3$, at $a=(\sqrt3-1)/2$, $b=(3-\sqrt3)/6$, giving local information $4-2\sqrt3\simeq0.535898$. The independent-Bell strategy corresponds to $a=b=1/4$, giving $1/2$.

### More calls, records and control visibility

An explicit ordinary family uses $a$ Bell probes of E and $b$ of F, $k=a+b$. Read each known identity-versus-Pauli process flag. Conditional on $A,B$ nonidentity flags, measure the complement of the fully symmetric subspace of $|n\rangle^{\otimes A}|m\rangle^{\otimes B}$. Its symmetric acceptance is

$$
\frac{\sum_{r=0}^{\min(A,B)}\binom Ar\binom Br z^r}{\binom{A+B}{A}}.
$$

The leading rejection coefficient in $\theta^2$ is $AB/(A+B)$, interpreted as zero if $A+B=0$. Since $A\sim\mathrm{Bin}(a,1/2)$ and $B\sim\mathrm{Bin}(b,1/2)$ independently, averaging **all** flags gives

$$
c_{ab}=\frac{ab}{k(k-1)}\left(\frac k2-1+2^{-k}\right),\qquad
\lim F_{ab}=4c_{ab}.
\tag{15}
$$

One proof conditions on $L=A+B$: its hypergeometric law gives
$\mathbb E[AB\mid L]=abL(L-1)/[k(k-1)]$, and
$\mathbb E[(L-1)1_{L\ge1}]=k/2-1+2^{-k}$. Examples $(a,b)=(1,1),(1,2),(2,2)$ give local information $1/2,5/6,17/12$. The last exceeds (14)'s limit but uses four queries.

For even $k$ with $a=b=k/2$, launch the $k$-query round with probability $2/k$ and do nothing otherwise, retaining the launch label. Its expected query count is exactly two, and its local information is

$$
F_{\mathrm{mean}\,2}=1-\frac{1-2^{1-k}}{k-1}\longrightarrow1
\quad\text{from below}.
\tag{16}
$$

Thus no uniform strict positive mean-cost information margin follows from the hard-two theorem. Equation (16) is an achievable family, not an upper bound on all long adaptive strategies. Within-round frame stability, longer latency and memory costs must be specified before excluding such branches. Fresh frames prevent amortizing their common orientation across different rounds; they do not prevent using extra probes inside a stable round.

If consistent oriented Lüders records $a,b\in\{\pm1\}$ are accessible, ordinary E then F on $I/2$ instead has

$$
\Pr(a,b)=\frac{1+ab\cos\theta}{4},\qquad
\Pr(a\ne b)=\sin^2(\theta/2),\qquad F=1.
\tag{17}
$$

Its null probability is at least $\sin^2\theta/4$. The same two visits therefore remove the switch advantage for this labeled task. Fixed label orientation matters; arbitrary unknown relabeling changes that task. A switch implementation that preserves native meter outputs must give the ordinary comparator the same outputs. Native pointer preparation, monitor/pilot ports and known drift-control words similarly belong to both strategies when physically supplied.

For a **pure multiplicative control visibility** $\nu\in[0,1]$, independent of $\theta$, the specified switch readout has

$$
p_{S,-}^{\nu}=\frac{1-\nu}{2}+\frac{\nu\sin^2\theta}{4},\qquad
F_{S,X}^{\nu}=\frac{4\nu^2z(1-z)}{4-\nu^2(1+z)^2}.
\tag{18}
$$

Every fixed $\nu<1$ gives a false-alarm floor and $F_{S,X}^{\nu}\to0$ at alignment. For $0<z<1$, it exceeds even the attainable ordinary readout (11) precisely when $\nu^2>9/(16-7z)$. At $\nu=.97$ this requires $\theta\gtrsim.288$ radians. This is a necessary comparison against one ordinary measurement, not a finite-angle converse for the full optimum. Detector/filter false alarms in the ordinary helpers require the same accounting; subtracting a calibrated mean background does not remove its shot noise. General meter noise need not reduce to the single visibility parameter in (18).

### Physical and verification scope

The model assumes a shared arbitrary orientation that is fresh between rounds yet stable across both order histories; independent unread meters for each query; no accessible frame-control words or reusable pointer records; and coherent recombination of the same slot-labeled meter histories. None is implied merely by observing polarization drift or by fitting two reduced dephasing channels. Unreset shared baths, distinct visit timestamps and chronological records require their full instrument, as discussed in [the bath screen](backaction.md). If the ordinary experiment can fit more probes in the same stability window, a hard two-query deadline needs a measured resource reason. If both outcome labels exist in the switch apparatus, (17) is a mandatory baseline.

The independent-Bell comparator uses two entangled probes and a joint process-sector/interference measurement; the adaptive optimum uses the known memory/isometry/projector in (9)–(10). Their preparations, failures, loss, visibility, latency and readout must be charged against the router and coherent-meter requirements of the switch. This note supplies no measured cost advantage, deployed drift model or fault-tolerance claim. It is an exact statistical benchmark and a counterexample to an overstrong scaling premise.

The standalone [alignment replay](checks/architecture/verify_alignment.py), run with `python -S -B`, uses only Gaussian integers and rational arithmetic. It rebuilds the six complete Bell/spin projectors; both endpoint Choi operators; the primal causal normalization and PSD slacks; the explicit dual Gram factors, directed trace equalities and wire-order conversion; the native spectral/projector identities; the parallel recoupling identity; a rational-axis pointwise null case; 144 multicopy count pairs and balanced mean-cost identities; and rational visibility/Fisher identities. It prints JSON, writes no files and rejects `-O`. The continuous Haar law, representation irreducibility, compact local-information argument, query-tree reduction, all-size combinatorics and physical interface conditions are analytic proofs above, rather than claims established by finite sampling. No numerical optimizer is a verification dependency.

The underlying switch measurement-incompatibility statistic is established
prior work; see the [literature comparison](references.md) and
[measurement baselines](architecture-baselines.md#nr-r08). This exact
small-system optimization is a scoped benchmark, without a source-priority
claim or a new mechanism claim for the control statistic.
