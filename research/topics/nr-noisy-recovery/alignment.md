# Drifting measurement alignment: exact two-query limit and reuse costs

[Application assessment](architecture.md) · [Measurement baselines](architecture-baselines.md) · [Metrology](metrology.md) · [Checks](checks/README.md)

<a id="nr-r18"></a>

## NR-R18 — An exact alignment benchmark with a strict query deadline

Two unread qubit dephasers with a fresh unknown common orientation admit an ordinary two-query alignment alarm with exactly zero false positives. The best ordinary alarm has probability $9\sin^2\theta/64$, whereas the ideal switch control alarm has probability $\sin^2\theta/4$. The optimal ordinary one-sided local Fisher-information limit is $9/16$; the switch control readout attains limit $1$. Thus the difference is a constant factor under a hard two-query cap. A proposed vanishing-versus-constant ordinary/switch information scaling is false.

Long ordinary rounds change the comparison more substantially. Within-round calibration and differential quantum error correction achieve $\Omega(k^2)$ classical information at nominal angle $1/k$ using $O(k)$ calls and one persistent clean memory qubit. Rarely launching such a round gives exactly two expected queries and information $\Omega(k)$, unbounded near alignment. This does not strengthen a fixed-length zero-false-positive alarm: the positive-angle and unbounded-length limits do not commute. Accessible Lüders records already attain information $1$ with two ordinary queries, and any fixed imperfect switch-control visibility makes its information vanish at alignment. These results establish no native throughput advantage; frame lifetime, clean-memory duration, helper gates and readout remain material. The analytic proofs and exact rational replay below have not been formalized in Lean or externally peer reviewed.

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

Thus no uniform strict positive mean-cost information margin follows from the hard-two theorem. Equation (16) is an achievable family, not the ordinary mean-cost frontier: the calibrated coherent strategy below has unbounded optimized information near alignment. Within-round frame stability, longer latency and memory costs must be specified before excluding long branches. Fresh frames prevent amortizing their common orientation across different rounds; they do not prevent using extra probes inside a stable round.

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

<a id="nr-r18-calibrated-reuse"></a>

### Within-round calibration and differential QEC change the mean-cost frontier

For every sufficiently large integer $k$, there is an ordinary experiment
with deterministic cost $N_k=O(k)$ and an averaged binary readout satisfying
$F_k(1/k)\ge k^2/16$. The common frame is freshly redrawn before this
experiment and remains fixed during it. All its calibration calls count.
The result uses no oracle meter records, controlled unknown oracle,
unknown inverse or previous-round calibration. Its persistent quantum
memory is one clean qubit, in addition to the probe qubit.

This is a constructive use of an established metrological mechanism.
[Zhou and Jiang](https://doi.org/10.1103/PRXQuantum.2.010343) prove a
discrete-channel Kraus-span criterion and construct logical-dephasing QEC
reductions. For $K_0=I/\sqrt2$, $K_1=(\cos\theta Z+\sin\theta X)/\sqrt2$
at zero, their generator is $i\sum_jK_j^\dagger\dot K_j=-Y/2$, outside
$\operatorname{span}_{\mathbb R}\{I,Z\}$.
[Liu and Yang, Section 3.3](https://arxiv.org/html/2403.09519v3) explicitly
study dephasing-direction estimation and ordinary control with zero or
one ancilla. [Chen et al.](https://doi.org/10.1103/PhysRevLett.133.190801)
study adaptive QEC for informative parameter-dependent noise. Those
results provide method context. The fresh common-frame localization,
unknown tangent average and mean-budget conclusion require the following
separate proof.

**Exact one-memory code.** Choose a known orthonormal local frame
$(x,y,z)$ and a probe $S$ with memory $A$. Encode

$$
|0_L\rangle=|+y\rangle_S|0\rangle_A,
\qquad |1_L\rangle=|-y\rangle_S|1\rangle_A.
\tag{19}
$$

The stabilizer is $Y_SZ_A$; $Z_S$ takes the code to its orthogonal
syndrome space, and $Y_S$ restricts to $Z_L$. For any unit physical axis
$a=(a_x,a_y,a_z)$, query $\mathcal E_a$, measure that known syndrome and
correct $Z_S$ on the error syndrome. After summing the inaccessible
original Kraus label, the exact logical Kraus operators are

$$
\frac I{\sqrt2},\qquad
\frac{a_yZ_L}{\sqrt2},\qquad
\frac{a_zI+i a_xZ_L}{\sqrt2}.
\qquad
\lambda(a)=a_z(a_z+i a_x).
\tag{20}
$$

Here $\lambda(a)$ multiplies $|0_L\rangle\langle1_L|$, while logical
populations are fixed. Indeed its coherence coefficient is
$[1-a_y^2+(a_z+i a_x)^2]/2=\lambda(a)$.

Only two qubits are needed for an implementation. Prepare $S$ in
$|+y\rangle$, apply controlled-$Z_S$ with control $A$, query the named
dephaser on $S$, undo that controlled-$Z_S$, then read $S$ in $Y$ and
reset it. The $Y=+$ branch has Kraus $I/\sqrt2,a_yZ_A/\sqrt2$; the
$Y=-$ branch has $(a_zI+i a_xZ_A)/\sqrt2$. The logical output is already
in $A$. Thus each query costs two known controlled gates, probe
preparation/readout/reset and persistent memory. Below the probe record
may be discarded after this prescribed decoding.

For a known great circle $a=(\sin\phi,0,\cos\phi)$, the two probe
outcomes are fair: one is identity and the other is
$e^{i\phi Z_L}$. Keeping the outcomes of $k$ calls gives
$M\sim\operatorname{Bin}(k,1/2)$ known phase applications. A logical
plus input has conditional QFI $4M^2$, so

$$
F_{\rm known\ plane}(k)=4\mathbb E M^2=k^2+k.
\tag{21}
$$

This is optimal for that one-parameter known-plane channel family:
granting the hidden fair identity/nonidentity flags strengthens every
ordinary strategy, and $M$ nonidentity unitary queries have generator
norm at most $M$, hence QFI at most $4M^2$. Waiting for one nonidentity
syndrome also supplies a clean logical phase at mean cost two calls,
with harmless identity on every preceding outcome. If a common great
circle is known but its absolute angle $\phi$ is unknown, phases from
$\mathcal E_\phi$ and $\mathcal F_{\phi+\theta}$ cancel that offset
after a logical-$X$ conjugation, at mean cost four calls per relative
phase. The Haar model does not give that known plane.

**Charged covariant localization.** Write
$n=Rz_0$, $t=Rx_0$, and $m_\theta=\cos\theta\,n+\sin\theta\,t$
for Haar $R$. Conditional on $n$, the tangent $t$ is uniform in
$n^\perp$. Use $L$ Bell probes of E only. Read each known
identity-versus-Pauli process flag $h$, with $\Pr(h=1)=1/2$. In the
Pauli sector use the covariant POVM
$3|u\rangle\!\rangle\langle\!\langle u|\,d\mu(u)$ on the real
three-dimensional process space, where $\mu$ is uniform sphere measure.
It is implemented by a known random rotated Pauli process basis and
recording its observed direction $u$. Its normalization follows from
$\int |u\rangle\!\rangle\langle\!\langle u|\,d\mu=I_3/3$.
Conditional on $h=1$, its density is $3(n\cdot u)^2$, giving

$$
\mathbb E[uu^T\mid h=1,n]=\frac{I+2nn^T}{5},\qquad
M_L=\frac1L\sum_{s=1}^L\left(5h_su_su_s^T-\frac I2\right),
\quad \mathbb E[M_L\mid n]=nn^T.
\tag{22}
$$

Each sample matrix entry has range length at most five. Hoeffding on
nine entries and $\|Z\|_{\rm op}\le3\max_{ab}|Z_{ab}|$ imply
$\Pr(\|M_L-nn^T\|_{\rm op}>\epsilon\mid n)
\le18e^{-2L\epsilon^2/225}$.
For $\epsilon\le1/4$ a top eigenvector $\widehat n$ obeys
$\sin\angle(\widehat n,n)\le\epsilon/(1-\epsilon)$: its eigenvalue
is at least $1-\epsilon$, and projecting its eigenvector equation
perpendicular to $n$ gives this inequality. Its distance from one sign
of $n$ is at most $2\epsilon$. Taking $\epsilon=\delta/4$ therefore
gives the uniform conservative bound

$$
\Pr\!\left(\min_{s=\pm1}\|\widehat n-sn\|>\delta\mid n\right)
\le18e^{-L\delta^2/1800}.
\tag{23}
$$

Fix

$$
\delta_k=\frac1{4\sqrt k},\quad \eta=\frac1{1000},\quad
L_k=\left\lceil28800k\log(18000)\right\rceil.
\tag{24}
$$

All $L_k$ queries count, including identity flags. The good localization
event $G_k$ then has probability at least $1-\eta$. Choose the code's
$z=\widehat n$, a known random perpendicular $x$, and $y=z\times x$.
Its axis sign is immaterial. Conditional on the true $n$ and all this
E-only training, $t$ is still uniform in $n^\perp$. The training law is
independent of $\theta$. The matrix in (22) can be accumulated
classically; no growing quantum program is retained.

**Differential accumulation.** Let $\mathcal G_a$ denote (20).
Initialize memory $A$ in logical plus and execute $k$ ordinary cycles
$\mathcal G_{m_\theta}\circ\operatorname{Ad}_{X_L}\circ
\mathcal G_n\circ\operatorname{Ad}_{X_L}$.
Each uses one E and one F call, in fixed chronological order.
Logical-$X$ conjugation replaces $\lambda(n)$ by its complex conjugate.
The exact conditional memory coherence and averaged binary readout are

$$
r_\theta^k=[\lambda(n)^*\lambda(m_\theta)]^k,
\quad C_k(\theta)=\mathbb E\operatorname{Re}r_\theta^k,
\quad p_+(\theta)=\frac{1+C_k(\theta)}2.
\tag{25}
$$

The expectation includes every training and probe outcome. At alignment
the common coherent phase cancels. On $G_k$, choose the harmless sign
with $n_z>0$ and put $a=|\lambda(n)|^2=n_z^2(1-n_y^2)$. Then

$$
a\ge1-2\delta_k^2,\qquad a^k\ge1-2k\delta_k^2=\frac78.
\tag{26}
$$

Thus localization error leaves bounded contrast, rather than being
assumed zero. To bound the actual averaged slope, set
$b(n,t)=d\lambda_n[t]/\lambda(n)$. Parametrize
$t=R_n(\cos\psi\,x+\sin\psi\,y)$, using the continuous minimal
rotation from local $z$ to $n$. Uniformly on $G_k$,
$b=i\cos\psi+O(k^{-1/2})$ and $|\lambda(n)|$ is bounded away from zero.
For $\theta=c/k$, with $c$ in a fixed compact neighborhood of one,
Taylor expansion gives
$\lambda(m_\theta)/\lambda(n)=1+\theta b+O(\theta^2)$ and its
derivative $b+O(\theta)$, uniformly in training data and tangent.
The uniform binomial limit and its derivative therefore yield

$$
\left.\frac1k\partial_\theta\operatorname{Re}r_\theta^k
\right|_{\theta=c/k}
=a^k\operatorname{Re}(e^{cb}b)+O(k^{-1/2}+k^{-1}).
\tag{27}
$$

At $c=1$, tangent averaging makes its main term $-a^k A_1$, where
$A_1=\mathbb E_\psi[\cos\psi\sin(\cos\psi)]=J_1(1)\ge7/16$.
The last inequality follows from
$x\sin x\ge x^2-x^4/6$ for $|x|\le1$ and the moments $1/2,3/8$.
On the bad localization event, $|\lambda|\le1$ and
$|\partial_\theta\lambda(m_\theta)|\le2$, so
$|\partial_\theta\operatorname{Re}r_\theta^k|\le2k$.
This bound also justifies differentiation under all expectations.
The good/bad probabilities are independent of $\theta$, and consequently

$$
\limsup_{k\to\infty}\frac{C_k'(1/k)}k
\le-(1-\eta)\frac78\frac7{16}+2\eta<-0.38.
$$

There is therefore a finite $k_0$ such that, for $k\ge k_0$,

$$
|C_k'(1/k)|\ge\frac k4,\qquad
F_k(1/k)=\frac{C_k'(1/k)^2}{1-C_k(1/k)^2}\ge\frac{k^2}{16}.
\tag{28}
$$

This is the information of the actual averaged binary likelihood,
not an average of inaccessible conditional-frame QFIs. The constants
in (24) are deliberately loose; no numerical $k_0$ or small-$k$ optimum
is asserted.

**Mean-only cost.** The deterministic round costs
$N_k=L_k+2k=O(k)$. Launch it with probability $\pi_k=2/N_k$ and otherwise
use no queries, retaining the launch bit. At the chosen operating point
hold $k,L_k,\pi_k$ and the complete adaptive algorithm fixed when
differentiating. All launch, training and readout outcomes count. Then

$$
\mathbb E N=2,\qquad
F_{\rm mean\,2}(1/k)=\pi_kF_k(1/k)
\ge\frac{k^2}{8N_k}=\Omega(k).
\tag{29}
$$

The uniform proof also applies with $k=\lfloor1/\theta_0\rfloor$ at
any sufficiently small positive nominal $\theta_0$, since
$k\theta_0\to1$. Thus optimized ordinary information at mean cost two
is at least $\Omega(1/\theta_0)$ near alignment. A finite first resource
moment alone need not bound local Fisher information; see also the
distinct phase-estimation context of
[Rivas and Luis](https://doi.org/10.1088/1367-2630/14/9/093052).
Equation (29) does not claim uniform global mean-square precision with
two expected calls.

For every fixed $k$, finite localization has a nonzero residual
dephasing background, $C_k(0)<1$. Evenness gives $C_k'(0)=0$ and
$F_k(\theta)\to0$ as $\theta\to0$. Equation (29) chooses a longer
experiment for a smaller positive nominal angle; it does not interchange
these limits or give a zero-false-positive alarm. The all-length exact-null
optimization remains a different question.

<a id="nr-r18-recorded-photonic"></a>

### Recorded photonic measurement: a calibration comparison

This compares a
declared known-anchor calibration family using the accepted measurement
primitive of the 2026 experiment. It is not a QKD/security statement, a
physical throughput certificate, or a converse for optimized native
strategies or NR-R18's fresh-Haar-frame model.

#### What the new sources actually supply

[Experimental Quantum Key Distribution in an Indefinite Causal Order](https://arxiv.org/html/2608.13561v1),
III.1–III.2, uses Alice's chosen polarization filters and Bob's ancilla-PBS
measurement. SPDC path pre-entanglement and ancilla-path recombination
erase the order information. The final control record resides in both
photons' paths; final detections also reveal Bob's pointer polarization.
The work explicitly uses post-selection and describes a proof of principle.
Its reported 0.964 key agreement and 0.033 false-positive probability are
conditional statistics, not an all-launch pair yield or process fidelity.
The text does not give a complete preparation/loss/reset/clock ledger for
a drift-calibration service. Its scanned angle describes an inserted
attack; the Bob drift angles below are our different proposed experiment.

The underlying
[measurement-primitive experiment](https://arxiv.org/html/2604.11878v1),
Sec. II, explicitly allows different waveplate angles before and after
the PBS, setting measurement and re-preparation bases separately.
Its Sec. III reports passive interferometer stability beyond 30 minutes;
this supplies no measured short calibration deadline.

The distinct
[2026 three-kilometer witness](https://arxiv.org/pdf/2506.20516)
uses the recorded measure-and-prepare operators
$M_{a|x}=|x\rangle\langle a|$. Forgetting a produces a replacement
channel, not NR-R18's unread Lüders dephaser. It uses spools simulating
separation and a stated 20-microsecond trial with 1-microsecond bins;
these are not the QKD apparatus's clock. Its stable-interference record
over 15 minutes also supplies no fresh-Haar two-query drift deadline.

#### A precise two-angle instrument model

Fix a known laboratory Z anchor and a real rotation plane. Let
$R(\theta)=\exp(-i\theta Y/2)$ and

$$
 P_a=(I+aZ)/2,\qquad
 M_b=R(\theta_o)|b_Z\rangle\langle b_Z|R(\theta_i)^\dagger,
 \qquad a,b\in\{+1,-1\}.
$$

Here $\theta_i$ is Bob's input POVM angle and $\theta_o$ the output
preparation angle. This is a complete recorded projective measurement:
$\sum_b M_b^\dagger M_b=I$. Independent drift of a measurement's pre-
and post-rotation need not preserve the one-angle Lüders relation
$\theta_i=\theta_o$. The accepted ideal PBS primitive has Kraus
operators $M_b/\sqrt2$, giving intrinsic success 1/2. Its rejected
complement has effect $I/2$; this does not specify all failed-photon maps.

For the source-style native rule, prepare the signal in Y+, choose a
uniformly at random, use the corresponding Alice filter $P_a$, and read
the order control in X after Bob's pointer erasure. Include the actual
classical-choice and PBS amplitudes. The accepted refined operators are

$$
 K_{ab,s}=(M_bP_a+sP_aM_b)/4,\qquad s=\pm1.
$$

Put $c_j=\cos\theta_j$ and $t_j=(1+ab c_j)/2$. Since these matrices are
real, their probabilities on Y+ equal those on I/2. Direct multiplication
gives

$$
 p_{ab,s}=\frac{t_i+t_o+2s t_i t_o}{32},\qquad
 \sum_{a,b,s}p_{ab,s}=\frac14.
 \tag{PA1}
$$

All unaccepted intrinsic filter/PBS events count as rejects. After
normalizing by this constant success probability, the minus probability
is $(1-c_i c_o)/4$.

**Identification obstruction for this readout.** The entire probability
law (PA1), including a and b, is invariant under
$\theta_i\leftrightarrow\theta_o$. Thus these records cannot distinguish
an input-measurement rotation from the same output-preparation rotation.
On the diagonal $\theta_i=\theta_o$, the two derivative columns coincide,
so the local Fisher matrix has a null direction for their difference.
This is an obstruction for the stated source-style records, not for a
native protocol augmented with additional preparations or target readout.

#### An ordinary probe separates the two drifts

Prepare $|0_Z\rangle$, pass it through the same recorded Bob primitive,
retain b, and measure the retained signal in Z with outcome z=±1.
No Bell input, quantum memory or inaccessible Kraus record is required.
The unnormalized measured probabilities are

$$
 p_{b,z}^{O}=\frac{(1+b c_i)(1+bz c_o)}8,\qquad
 \sum_{b,z}p_{b,z}^{O}=\frac12. \tag{PA2}
$$

Conditional on acceptance, b has Fisher information 1 about
$\theta_i$, and z conditional on b has information 1 about $\theta_o$.
Their score cross term vanishes by conditional normalization. The
all-prepared-pair Fisher matrix is therefore

$$
 F^O=\frac12\begin{pmatrix}1&0\\0&1\end{pmatrix}.
 \tag{PA3}
$$

This holds at interior angles; singular alignment endpoints require
one-sided limits. The final two-outcome Z readout and Bob's successful
retained-target instrument must actually be available and priced. If
desired, an Alice $P_+$ filter may remain before Bob: the known input
passes it intrinsically with probability one, while insertion loss counts.

For the tied one-angle Lüders family, (PA1) gives conditional information
$12/(9-\cos^2\theta)$. After its success 1/4, the actual displayed
record rule has

$$
 F^S_{\mathrm{pair}}=\frac3{9-\cos^2\theta}\le\frac38,
 \qquad F^O_{\mathrm{pair}}=1. \tag{PA4}
$$

The first expression is not a native QFI optimum. It includes more than
the native control alone, but not an added polarization tomography of
the target. The ordinary result uses the already accessible Bob record
and a standard terminal readout; cryptographic restrictions on who may
inspect a secret bit are not a measurement-calibration restriction.

There is a still simpler comparison if only input-POVM alignment matters.
Retain b and use the signal detection only to identify successful PBS
events, without resolving its output polarization. Then
$p_b^O=(1+b\cos\theta_i)/4$ and its information per prepared pair is
1/2, independent of $\theta_o$. Even this pointer-only result exceeds
the tied-angle native record rule's bound 3/8. It does not separately
calibrate the output preparation; (PA2)–(PA3) supply that additional task.

#### Physical rate cut and next experiment

The pair in (PA1)–(PA4) is a prepared ideal two-photon input, not a pump pulse
or a detected coincidence. Let $\eta_O,\eta_S$ include extra pair
preparation, routing, collection and detector efficiencies, and let
$T_O,T_S$ be their complete average trial clocks. If these efficiencies
are parameter independent and other errors are absent, the information
rates are $\eta_O/T_O$ and
$3\eta_S/[(9-\cos^2\theta)T_S]$. The ordinary readout wins whenever

$$
 \frac{\eta_O/T_O}{\eta_S/T_S}\ge
 \frac3{9-\cos^2\theta}.
$$

Unknown or parameter-dependent loss instead requires the full count
likelihood and nuisance-parameter fit. The paper's conditional agreement
and control visibility do not determine these quantities. Extra source
readiness, reset, pointer-photon production, output readout, no-clicks,
false heralds, finite visibility and frame stability all remain charged.
For the pointer-only ordinary rule the sufficient rate condition becomes
$(\eta_O/T_O)/(\eta_S/T_S)\ge6/(9-\cos^2\theta)\le3/4$.

The discriminating same-apparatus test is a two-dimensional sweep of
Bob's pre- and post-rotation angles. Measure the source-style native
records and the ordinary (b,z) records at the same pair supply. Retain
all clock, source-herald, detector and rejection counts, rather than
renormalizing independent successful subsets. Verify the swap symmetry
and the separately identifiable ordinary likelihood, then compare
information per elapsed time with fitted loss/background nuisance
parameters. A hard two-query cap needs a measured drift/deadline reason;
neither source establishes NR-R18's fresh common orientation.

The standard-library [photonic alignment guard](checks/architecture/photonic_alignment_guards.py) verifies five rational
one-angle matrix fixtures and nine two-angle fixtures, including success
weights, derivatives, the swap-symmetric native law and ordinary Fisher
matrix. Its matrices retain the complete intrinsic reject weight;
continuous identities (PA1)–(PA4) are the analytic derivation above. No
physical phase/bath/record overlap, full failed-photon instrument or
hardware advantage is certified by these finite checks.

### Physical and verification scope

The model assumes a shared arbitrary orientation that is fresh between rounds yet stable across both order histories; independent unread meters for each query; no accessible frame-control words or reusable pointer records; and coherent recombination of the same slot-labeled meter histories. None is implied merely by observing polarization drift or by fitting two reduced dephasing channels. Unreset shared baths, distinct visit timestamps and chronological records require their full instrument, as discussed in [the bath screen](backaction.md). If the ordinary experiment can fit more probes in the same stability window, a hard two-query deadline needs a measured resource reason. If both outcome labels exist in the switch apparatus, (17) is a mandatory baseline.

The independent-Bell comparator uses two entangled probes and a joint process-sector/interference measurement; the adaptive optimum uses the known memory/isometry/projector in (9)–(10). Their preparations, failures, loss, visibility, latency and readout must be charged against the router and coherent-meter requirements of the switch. This note supplies no measured cost advantage, deployed drift model or fault-tolerance claim. It is an exact statistical benchmark and a counterexample to an overstrong scaling premise.

The calibrated strategy additionally needs $O(k)$ preparation/readout/reset steps and known two-qubit gates, one memory kept coherent through the signal stage, and the same common frame throughout all $N_k$ calls. Its training and signal stages can reuse the same two qubits. Persistent helper noise or a fixed per-cycle phase error can destroy the contrast in (26); the proof assumes those helpers are ideal. Long latency, frame stability and clean-memory time are free only in the query-count model. A physical deadline, bounded frame lifetime or charged helper operations can exclude the rare long branches in (29), but those restrictions require a separate device model and comparison.

The standalone [alignment replay](checks/architecture/verify_alignment.py), run with `python -S -B`, uses only Gaussian integers and rational arithmetic. It rebuilds the six complete Bell/spin projectors; both endpoint Choi operators; the primal causal normalization and PSD slacks; the explicit dual Gram factors, directed trace equalities and wire-order conversion; the native spectral/projector identities; the parallel recoupling identity; a rational-axis pointwise null case; 144 multicopy count pairs and balanced mean-cost identities; and rational visibility/Fisher identities. Its QEC extension checks the complete two-controlled-gate syndrome circuit, all general-axis matrix-unit coefficients in (20), the differential coherence identity in (25), known-plane conditional QFI and finite binomial moments. It prints JSON, writes no files and rejects `-O`. The continuous Haar law, representation irreducibility, compact local-information argument, query-tree reduction, all-size combinatorics, covariant concentration bound, uniform Taylor/derivative estimates and resulting asymptotic guarantee are analytic proofs above, rather than claims established by finite sampling. In particular the replay supplies no numerical value of $k_0$. No numerical optimizer is a verification dependency.

The underlying switch measurement-incompatibility statistic is established
prior work; see the [literature comparison](references.md) and
[measurement baselines](architecture-baselines.md#nr-r08). This exact
small-system optimization is a scoped benchmark, without a source-priority
claim or a new mechanism claim for the control statistic.
