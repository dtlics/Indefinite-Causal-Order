# Ordinary baselines for architecture applications

[Application audit and next tests](architecture.md) · [Recovery theorem](theorem.md) · [Topic](README.md)

These scoped results screen candidate applications against ordinary
methods with quantum memory, accessible records, calibration reuse and
known processing. They do not contradict the fresh-frame recovery game.
They also do not establish a hardware-runtime winner: ideal known
operations in a query model must be replaced by an explicit native cost
and noise model before making that comparison.

<a id="nr-r06"></a>

## NR-R06 — Native checks, calibrated faults and ordinary path baselines

### Physical hypothesis

In cycle $t$, module-labelled faults realize known unitaries
$E_{a_t}=P_{a_t}U_t$ and $F_{b_t}=Q_{b_t}V_t$. Here $U_t,V_t$ are
calibrated ideal layers and $P_a,Q_b$ are known Pauli strings. More
generally assume the known unitary families satisfy

$$
\operatorname{Tr}(E_a^\dagger E_{a'})=D\delta_{aa'},
\qquad
\operatorname{Tr}(F_b^\dagger F_{b'})=D\delta_{bb'}.
$$

The unknown law of the classical trajectory
$(a_1,b_1,a_2,b_2,\ldots)$ may include spatial correlations, persistent
latent parameters, temporal memory and drift. Its conditional law at
each selected classical setting is independent of the quantum probe.
Within one cycle the same module-labelled pair is realized in both
coherent-order arms, and an ordinary pair of probe calls samples that
same joint law with matched physical times and settings.

This is an **exogenous classical fault-trajectory model**. It does not
include a bath updated differently by the two orders, input-dependent
faults, or coherent superpositions of different fault labels. Those
cases require a separate physical model. Arbitrary correlations do not
make this distinction disappear.

### Construction and proof

For a fixed pair $a,b$, define

$$
W_{ab}=|0\rangle\langle0|_C\otimes F_bE_a
      +|1\rangle\langle1|_C\otimes E_aF_b.
$$

The complete switched output on any control-data-reference state is
the channel $\sum_{ab}p(a,b)\operatorname{Ad}_{W_{ab}}$.
An ordinary circuit reproduces it:

1. Store the actual control and data, including reference correlations.
2. Prepare two normalized Bell pairs; call each module once, on one half
   of its pair, in definite order.
3. Measure the known process-state bases
   $|e_a\rangle=(I\otimes E_a)|\Phi_D\rangle$ and
   $|f_b\rangle=(I\otimes F_b)|\Phi_D\rangle$.
   Orthogonality gives the exact labels $a,b$ with their original joint
   distribution, without assuming it factors.
4. Apply the known controlled unitary $W_{ab}$ to the stored input.

Thus equality holds for the full channel, not merely a scalar or a
conditional fidelity. Every later instrument, erasure flag and reference
correlation is reproduced. Conditional on the entire classical fault
trajectory the equality holds cycle by cycle. Induction therefore
preserves adaptive settings, intercycle memory, stopping times and all
classical transcripts. For diagnostics the label transcript statistically
dominates the switched transcript: the latter is obtained from the former
by a parameter-independent randomized quantum preparation and readout.

There is one call per module and no postselection. No prediction of a
later independent error is assumed: the sampled realized unitaries are
synthesized on the stored data. Known synthesis and clean storage are
essential premises. A physical device whose desired layer cannot be
cleanly compiled must cost that limitation explicitly.

### Resource consequences

The simple implementation uses two $D$-dimensional Bell pairs, storage
of the actual data/control, known process-basis readout and feedforward.
A Pauli label takes $2\log_2D$ bits per module. For calibrated Clifford
layers these known operations have efficient descriptions. For arbitrary
known layers this is a query theorem, not an efficient-compilation claim.
Bell memories, reset and decoding can be noisy or expensive. Their
hardware cost must be compared with coherent order routing; neither is
assumed physically free by an architecture conclusion.

This excludes a fundamental query/statistical advantage for the switch
in this model, including persistent classical Pauli cross-talk and
correlation alarms. It does not exclude a native-device advantage where
one implementation has demonstrably cheaper or cleaner memory/control.
Bell-assisted Pauli learning is established prior work; see
[Seif et al.](https://arxiv.org/abs/2408.03376).
The complete trajectory and output simulation above are direct deductions
from the orthogonal process-state observation, without a novelty claim.

### Two further coherent-error screens

For persistent $E_\theta=e^{-i\theta X}$ and $F_\phi=e^{-i\phi Z}$,
the minus Kraus operator is, up to global phase,
$-\sin\theta\sin\phi\,ZX$. Hence

$$
p_-=\sin^2\theta\sin^2\phi.
$$

For arbitrary jointly distributed classical angles, two ordinary Bell
probes give a nonidentity label after each module with joint probability
$\mathbb E[\sin^2\theta\sin^2\phi]$, exactly the switch's minus
probability. This scalar comparison uses matched probe-independent
exposures as above; it does not reconstruct or exactly simulate the full
continuous-angle switch. The statistic also loses the signs of the
angles. Rotations about a common axis commute for every realization,
so their minus probability is zero even with strong phase correlations.

At $\theta=\phi=\epsilon$, detecting a minus click needs
$\Theta(\epsilon^{-4})$ independent cycles. Ordinary Bell tests have
nonidentity probability $1-\cos^4\epsilon=\Theta(\epsilon^2)$.
For the promised fixed magnitude, repeated coherent calls amplify the
rotation to constant signal using $O(1/\epsilon)$ calls. This screens the
minus-click alarm; it is not an optimal-metrology theorem for the full
switched output.

Static unknown unitaries also have an exact three-call ordinary
full-switch simulator: use slots $E,F,E$, let $F$ act on the data, and
route the two $E$ calls between data and a dummy using the control.
One branch applies $E$ to data first, the other last. The dummy receives
one $E$ in either branch, so its final state factors identically.
This gives $FE$ and $EF$ coherently. The argument requires the two $E$
calls to be the same repeatable unitary. It is not valid for fresh
unobserved Kraus labels or independently drifting first/last calls.

### Known Clifford layers admit cheaper ordinary parity checks

Full clean synthesis and process-basis readout are not always needed. Let
the total ideal data operation be a **known Clifford** $C$ on $n$ qubits,
while the actual fixed physical block is any CPTP map
$\mathcal G=\mathcal N\circ\operatorname{Ad}_C$. This includes arbitrary
coherent or non-Pauli faults inside the block; it does not assume a final
Pauli noise layer. The physical map must remain $\mathcal G$ when the
helper checks are present. Unmodelled helper-induced crosstalk is excluded.

Choose a uniform Hermitian Pauli $Q$ and compute the known Pauli
$P=C^\dagger QC$. Prepare an ancilla in $|+\rangle$, apply controlled-$P$
before $\mathcal G$ and controlled-$Q$ after it, and accept the $X=+1$
outcome. If $E_i$ are Kraus operators of $\mathcal N$, the accepted
relative Kraus operator is

$$
\mathsf P_Q(E_i)=\frac{E_i+QE_iQ}{2},
$$

because $Q(E_iC)P=QE_iQC$. The circuit keeps the native oracle order
fixed and uses no controlled unknown oracle, inverse module, error record
or full clean $C$ implementation. For $k$ checks around the same execution,
use $k$ ancillas and opposite pre/post ordering. Pauli conjugations commute
as superoperators, so each relative Kraus operator is projected by the
$k$ maps $\mathsf P_{Q_j}$ even when the checks anticommute as matrices.

Expand $E_i=\sum_T e_{iT}T$ in the orthonormal Pauli basis, with
$e_{iT}=D^{-1}\operatorname{Tr}(T^\dagger E_i)$. Trace preservation gives
$\sum_{iT}|e_{iT}|^2=1$. The identity coefficient survives every check;
each nonidentity Pauli commutes with an independent uniform check with
probability $1/2$. For Bell input, Pauli orthogonality removes all coherent
cross terms in the acceptance trace. Consequently, writing
$f=F_e(\mathcal N)=\sum_i|e_{iI}|^2$, the averaged accepted Bell metrics are

$$
q=f,\qquad p=f+2^{-k}(1-f),\qquad
\mathsf S=2q-p=(1+2^{-k})f-2^{-k}.
$$

These equalities hold for arbitrary fixed CPTP noise. Its conditional
accepted channel need not be a Pauli channel, and its success probability
can depend on the payload; $p$ here is the Bell-input acceptance. For
example, one-qubit reset noise has $f=1/4$ and one-check Bell acceptance
$5/8$, while its acceptance is $3/4$ on $|0\rangle$ and $1/2$ on
$|1\rangle$. Thus these scalars do not imply an arbitrary-input
conditional-channel or diamond-distance guarantee.

For $f\ge0.81$, one check scores at least $0.715$ and two at least
$0.7625$, using the same native block calls. These compare guaranteed
scores with NR-R01's switch lower bound; they do not assert superiority
over the actual optimized switch for every known instance. Publishing
the Clifford target also changes NR-R01's information assumptions.

With arbitrary connectivity, each controlled Pauli string costs at most
$n$ CNOT-equivalent gates plus one-qubit basis changes. Thus the extra
entangling cost is at most $2kn$, with $k$ ancillas and $k$ readouts,
independent of the compiled depth of $C$. Connectivity, ancilla retention,
readout latency and helper errors remain physical costs. Independent
ancilla phase dephasing with visibility $\nu$, and $a=(1+\nu)/2$, gives

$$
q=fa^k,\qquad p=fa^k+2^{-k}(1-f),\qquad
\mathsf S=fa^k-2^{-k}(1-f).
$$

At $f\ge0.81$ and $\nu=0.97$, the one/two-check lower bounds are
$0.70285$ and $0.73838225$. This is a scalar control-phase model, not
a general fault-tolerance statement. Extra helper-location half-diamond
errors $\epsilon_\ell$ decrease the score by at most
$2\sum_\ell\epsilon_\ell$, by telescoping the complete flagged circuit
and using a score observable of norm at most one.

The filtering mechanism is established
[Pauli check sandwiching](https://www.nature.com/articles/s41598-023-28109-x)
and [coherent Pauli checks](https://arxiv.org/abs/2212.03937).
[Spatio-temporal stabilizers](https://arxiv.org/html/2112.13904v2) likewise
use known circuit symmetries for input-independent checks. Their helper
accuracy assumptions must be costed alongside switch routing. Ordinary
[black-box error filtration](https://arxiv.org/html/2210.10733v2) and
[superposed computation](https://arxiv.org/html/2304.08529v2) also produce
physical quantum outputs using coherent paths. A two-copy filter of the
complete $AB$ computation uses four primitive module calls, so it is not
a two-call simulator, but it belongs in a throughput or expected-cost
comparison.

Two implementation boundaries are immediate. If a public Clifford frame
$U$ conjugates single-qubit $X,Y,Z$, then the target $UZU^\dagger$ is a
known Pauli string and needs at most $n$ clean single-qubit Paulis. If
the native modules literally compile $UXU^\dagger$ and $UYU^\dagger$
from the same available length-$G$ word for $U$, direct
$UZU^\dagger$ uses $2G+1$ gates, versus $4G+2$ for an unfused execution
of both modules before routing. The boundary-noise theorem does not turn these counts into an
internal-gate noise theorem. Generic non-Clifford targets can lack cheap
transported checks, but expensive full synthesis alone does not establish
a native-device advantage.

### Transported Pauli checks also screen SPAM-gauge calibration

Unlearnable Pauli components in Clifford-gate calibration are a real
application bottleneck. [Cheng et al.](https://arxiv.org/html/2606.29638v2)
resolve additional components using mid-circuit measurements, with
explicit preparation assumptions and tests of Markovianity. Their
ordinary measurement-based method belongs in this comparison. The
coherent-check interface above supplies another ordinary comparator
when its helper and controlled Paulis are available; using PCS outcomes
for characterization is already an
[established application](https://paragon.cs.northwestern.edu/papers/2024-QCE-PCSCharacterization.pdf).

For a fixed physical channel
$\mathcal E=\Lambda\circ\operatorname{Ad}_G$, with known Clifford $G$
and Pauli noise $\Lambda(\cdot)=\sum_a p_aP_a(\cdot)P_a$, let $P$ be
the desired Pauli and $Q=G^\dagger PG$. The ordinary controlled-$Q$ /
$\mathcal E$ / controlled-$P$ sandwich has branch relation

$$
P(P_aG)Q=\chi(P,P_a)P_aG,
\qquad \lambda_P=\sum_ap_a\chi(P,P_a).
$$

Consequently its reduced control cross block is multiplied by $\lambda_P$
for every input data block, including a passive reference. Repeating the
same sandwich $m$ times under independent, fixed Pauli noise gives
$\lambda_P^m$, so fixed endpoint helper SPAM has the form
$A\lambda_P^m+B$. Learning from this model requires nonzero contrast
$A$, stationary endpoint maps and a stationary repeated instrument.
The eigenvalue is signed: negative $\lambda_P$ alternates with length
parity, and even lengths alone cannot determine its sign. Each round
uses one actual $\mathcal E$ call and
$\operatorname{wt}(P)+\operatorname{wt}(Q)$ local controlled-Pauli gates;
transport through an entangling $G$ can make $Q$ high weight.

In contrast, the switch of $\mathcal E$ with the known $P$, in the cross
orientation $L_a=PP_aG$, $R_a=P_aGP$, has reduced cross effect
$\sum_ap_aR_a^\dagger L_a=\lambda_P P Q$. A maximally mixed data probe
therefore has zero fringe whenever $Q\ne\pm P$, including the
support-changing cases that motivate the gauge problem. A known
eigenprobe supplies a different preparation reference, which must be
costed. This calculation excludes that mixed-probe proposal; it is not
a converse for all switch-assisted calibration protocols.

Unknown per-round helper visibility $h$ yields $(h\lambda_P)^m$, which
length fitting alone cannot separate: $(\lambda_P,h)=(3/5,5/6)$ and
$(2/3,3/4)$ both give $1/2$ per round. Temporal correlations also invalidate
the power law: an anticommuting error persistent over both rounds with
probability $1/5$ gives two-round coherence $1$, whereas independent
errors with the same marginal give $9/25$. Thus the ordinary check does
not remove the need for an actual helper-noise and temporal-process
model. No native switch advantage follows from the restricted
tomographic gauge alone.

### Read-only bit-query QRAM has cheap common checks

Consider classical Boolean read-only query oracles
$O_f|x,y\rangle=|x,y\mathbin\oplus f(x)\rangle$, with $a$ address
qubits and one target qubit. Set $A=O_f$, $B=O_g$ and $C=BA=AB$ for
arbitrary unknown functions $f,g$. These are commuting Hermitian
involutions. This model does not describe writable quantum memory or
loading arbitrary quantum amplitudes.

Every such oracle commutes with the $a+1$ known checks
$Z_{\mathrm{address},j}$ and $X_{\mathrm{target}}$. Their common
eigenbasis is $|x\rangle\otimes|\pm_X\rangle$. Let $H$ be the
$D=2^{a+1}$-element group they generate and let

$$
\Pi_H(E)=D^{-1}\sum_{h\in H}hEh
$$

be the Hilbert-Schmidt orthogonal projection onto the maximal abelian
algebra diagonal in that basis. This algebra contains $A,B,C$ without
requiring their truth tables. Pre/post controlled checks around the native
order $A$ then $B$, accepting all plus outcomes, implement $\Pi_H$ on
the relative error. The cost is exactly the same two native calls,
$2(a+1)$ CNOT-equivalent check gates, $a+1$ ancillas and their readout;
no database-dependent synthesis, inverse or calibration is used. Ideal
helpers and sufficient connectivity are explicit premises.

For accepted relative Kraus operators $L_i$, the target-$C$ Bell metrics are

$$
q=D^{-2}\sum_i|\operatorname{Tr}L_i|^2,\qquad
p=D^{-1}\sum_i\|L_i\|_2^2,\qquad \mathsf S=2q-p.
$$

Suppose only $A$ is noisy, with arbitrary CPTP error Kraus operators
$E_i$ after $A$, and $B$ is ideal. The plain plus-port switch has accepted
Kraus operators

$$
\frac{BE_iA+E_iAB}{2}
=\mathsf S_B(E_i)C,\qquad
\mathsf S_B=\frac{\mathrm{id}+\operatorname{Ad}_B}{2}.
$$

Because $B$ is a Hermitian involution, $\mathsf S_B$ is the orthogonal
projection onto its commutant. The ordinary checker's relative operators
are $\Pi_H(BE_iB)=\Pi_H(E_i)$. The range of $\Pi_H$ is contained in
that of $\mathsf S_B$, so
$\|\Pi_H(E_i)\|_2\le\|\mathsf S_B(E_i)\|_2$.
Both preserve $\operatorname{Tr}E_i$. Therefore the ordinary checker
has exactly the same $q$ and no larger $p$, giving at least as high a
Bell score. If only $B$ is noisy, the proof uses $\mathsf S_A$ instead.
With no fault both implement $C$ with $p=q=1$.

For independent module mixtures

$$
\mathcal E=(1-\epsilon_A)\operatorname{Ad}_A
 +\epsilon_A\mathcal N_A\circ\operatorname{Ad}_A,
\qquad
\mathcal F=(1-\epsilon_B)\operatorname{Ad}_B
 +\epsilon_B\mathcal N_B\circ\operatorname{Ad}_B,
$$

where $\mathcal N_A,\mathcal N_B$ are fixed CPTP maps, the no-fault
and two single-fault branches obey this dominance. Only the double-fault
branch remains, with probability $\epsilon_A\epsilon_B$. Each flagged
score lies in $[-1,1]$, hence

$$
\mathsf S_{\mathrm{switch},+}-\mathsf S_{\mathrm{checks}}
\le2\epsilon_A\epsilon_B.
$$

The $\epsilon$'s are stochastic mixture weights, not arbitrary diamond
errors. Thus the plain plus switch has no first-order advantage over
these checks in this model; this is not an upper bound on every ICO
protocol. Helper deviation $\delta_{\mathrm{check}}$ in half-diamond
distance adds at most $2\delta_{\mathrm{check}}$ to the right side.
The noise maps must remain fixed when the helpers are added.

The double-fault residual is necessary. With one address qubit,
$f=0$, $g(x)=x$, and a post-target-$Z$ fault on both modules, the ordinary
relative error is $Z_{\mathrm{address}}$ and passes all checks, with
$(p,q,\mathsf S)=(1,0,-1)$. The plus-switch relative Kraus operator is
$(I+Z_{\mathrm{address}})/2$, with $(p,q,\mathsf S)=(1/2,1/4,0)$.
This refutes all-orders dominance of this checker; it does not show
advantage over all ordinary strategies for that simple instance.

For post-module **single-site Pauli** faults, the one string
$Q=(\prod_j Z_{\mathrm{address},j})X_{\mathrm{target}}$ reduces the
helper requirement to one ancilla and $2(a+1)$ check gates. It
anticommutes with every detectable single-site fault (address $X/Y$ or
target $Y/Z$); the remaining address $Z$ and target $X$ faults commute
with both oracles and pass the plus switch too. Conjugating a fault through
the other oracle preserves this check syndrome. Thus the same branchwise
and finite-residual comparison holds when each conditional fault map is
a mixture of those weight-one Paulis. This refinement does not cover
arbitrary single-module noise or faults propagated through unspecified
internal QRAM gates; use the full algebra checker for the former.

These are ordinary symmetry-check consequences, not a new QRAM correction
mechanism. QRAM is also a motivation in the
[ordinary black-box filtration analysis](https://arxiv.org/html/2210.10733v2),
which explicitly prices memory and control faults. Neither unknown
database size nor a deep native query alone excludes a cheap ordinary
check. A hardware comparison must include connectivity, helper memory,
router loss and latency, plus the desired physical-output metric.

### Qutrit-router address checks do not require a Clifford payload

The logical router in
[Zhang et al., Eq. (1)](https://arxiv.org/abs/2505.13958) is

$$
R=|L\rangle\langle L|\otimes\operatorname{SWAP}_{I,L}
 +|R\rangle\langle R|\otimes\operatorname{SWAP}_{I,R},
$$

with the two address values encoded in qutrit levels $0,2$. It leaves the
address unchanged, so every address-diagonal Hermitian involution $Q$
commutes with the ideal logical gate. A chosen full-space completion may
leave leakage level $1$ alone. This does not require $R$ to be Clifford.
For any fixed actual route channel with Kraus operators $K_i$, switching
that channel with the known $Q$ and measuring the order control in $X$
gives $(QK_i\pm K_iQ)/2$. A fixed output $Q$ transforms these into

$$
\frac{K_i\pm QK_iQ}{2}.
$$

These are exactly the two Kraus families from one ordinary route call
between controlled-$Q$ gates on a single plus-prepared helper, followed by
its $X$ measurement. The complete flagged quantum instrument agrees,
including arbitrary reference entanglement. This is the transported-check
baseline above, specialized to a cheap native symmetry. It assumes that
the same actual route map applies in the tested contexts; helper noise and
control-induced crosstalk require a joint model in both implementations.

For leakage detection, take
$Q_{\rm er}=|0\rangle\langle0|-|1\rangle\langle1|+|2\rangle\langle2|$.
On code-supported input, the pre-check is the identity and can be omitted.
One ordinary controlled-$Q_{\rm er}$ **after** the route, with helper
$X$ readout, yields $P_{02}K_i$ or $P_1K_i$. Its successful code projection
preserves coherence between levels $0,2$; no address value is read.
This is a proposed nondestructive binary check, not a demonstrated ability
to recycle the experiment's terminal address readout. Its controlled
qutrit phase, helper, measurement and delay all count in a hardware budget.
Conversely, pure address-diagonal phase faults commute with these checks
and with the logical router. Neither their switch commutator nor this
ordinary check supplies a phase-fault syndrome.

The native-check replay verifies twenty exact paired flagged-Kraus
identities for a full qutrit-address/three-qubit-bus router, including
coherent address mixing, a bit flip, diagonal phase noise and nonunital
$2\to1$ leakage. It also checks the one-postcheck projection and absence
of a diagonal-phase alarm. These operator equalities imply complete-channel
equalities on the tested examples; the general algebra is given above.

### Distinct commuting layers in a known basis admit ordinary fault checks

Let $A=\operatorname{diag}(a_x)$ and $B=\operatorname{diag}(b_x)$ be two
distinct ideal unitaries in a **known executable basis**, with target
$W=BA=AB$ on a $D$-dimensional payload. Their phases need not be known,
learned or cleanly synthesized. For accepted Kraus operators $L_k$, write

$$
p=\frac1D\sum_k\operatorname{Tr}(L_k^\dagger L_k),\qquad
q=\frac1{D^2}\sum_k|\operatorname{Tr}(W^\dagger L_k)|^2,
\qquad \mathsf S=2q-p.
$$

These are the acceptance, Bell-good weight and signed Bell reward used
above. They count rejection as zero reward. A conditional Bell fidelity
$q/p$ is defined when $p>0$; these scalars do not imply an arbitrary-input
conditional-channel or diamond-distance guarantee.

Use the standard independent-slot channel model for the switch and the
same fixed native maps for the ordinary execution. The helper interactions
must leave those maps unchanged. A retained shared bath, order-dependent
arrival times or helper-induced crosstalk needs a joint physical process
model; marginal channels alone do not establish this comparison.

Prepare a clean $D$-level syndrome register and use
$C_{\rm cp}|x\rangle|r\rangle=|x\rangle|r+x\bmod D\rangle$
before an ordinary $A$-then-$B$ execution, followed by
$C_{\rm cp}^\dagger$. Accept syndrome zero. For any physical Kraus matrix $M$,

$$
\langle0|C_{\rm cp}^\dagger(M\otimes I)C_{\rm cp}|0\rangle
=\mathsf D(M),\qquad
\mathsf D(M)=\sum_x|x\rangle\langle x|M|x\rangle\langle x|.
$$

The input label is never measured. In a no-fault execution the syndrome
returns to a fixed pure state, preserving arbitrary payload/reference
coherences. For a computational-basis $n$-qubit block, $n$ data-to-ancilla
CNOTs before and after implement the same zero-syndrome projection by
copying XOR labels, with $n$ clean ancillary qubits.

Suppose only $A$ is faulty, with native channel
$\mathcal N_A\circ\operatorname{Ad}_A$ and arbitrary Kraus $E_k$ for
$\mathcal N_A$; $B$ is ideal. The switch-plus Kraus is

$$
K_k=\frac{BE_kA+E_kAB}{2}
=\frac{BE_kB^\dagger+E_k}{2}W.
$$

Its diagonal part is $D_k=\mathsf D(E_k)W$, exactly the accepted ordinary
Kraus $\mathsf D(BE_kA)$. Write $K_k=D_k+O_k$, where $O_k$ is strictly
off-diagonal. Hilbert--Schmidt orthogonality gives
$\operatorname{Tr}(D_k^\dagger O_k)=0$, while diagonality of $W$ gives
$\operatorname{Tr}(W^\dagger O_k)=0$. Hence

$$
q_{\rm ord}=q_{\rm sw},\qquad
p_{\rm sw}-p_{\rm ord}=\frac1D\sum_k\|O_k\|_{\rm HS}^2\ge0.
$$

The same proof holds when only $B$ is faulty, interchanging $A$ and $B$;
the ordinary order remains $A$ then $B$. No inverse native call, error
record or knowledge of either phase spectrum is needed. The fault can
occur inside the module: the representation relative to its unitary
ideal is always a CPTP channel. These are Bell-metric identities, not a
CP decomposition: diagonal/off-diagonal Choi cross terms may remain.

If actual independent stochastic fault events have probabilities
$\epsilon_A,\epsilon_B$, with the ideal unitary on each no-fault event,
the no-fault and single-fault sectors obey
$\mathsf S_{\rm ord}\ge\mathsf S_{\rm sw}$. Every Bell reward is in
$[-1,1]$, so the double-fault sector yields the all-orders bound

$$
\mathsf S_{\rm ord}\ge\mathsf S_{\rm sw}-2\epsilon_A\epsilon_B.
$$

This removes a leading-order switched signed-Bell improvement in that
stochastic model; it does not compare arbitrary coherent systematic
fault amplitudes, optimize double-fault processing, or bound all protocols
that recover from both switch outcomes. The check costs $2n$ CNOTs in
the stated bit basis, plus syndrome storage/readout. An arbitrary unknown
common eigenbasis is outside that inexpensive implementation. Helper
noise, connectivity, crosstalk and the native routing cost remain material.

### Number-diagonal nonlinear layers admit an exact loss check

The comparison strengthens for number-diagonal gates with only loss and
diagonal phase noise. Let $N$ have nonnegative integer eigenvalues up to
$N_{\max}$ on the allowed input space, and assume a Kraus representation
refined into definite nonnegative shifts,

$$
[N,A_i]=-\ell_i A_i,\qquad [N,B_j]=-m_jB_j,
\qquad \ell_i,m_j\ge0.
$$

Require every zero-shift $A_i,B_j$ to be diagonal in the same complete
basis as the ideal $A,B$. For several modes this can be the joint
occupation basis, with $N$ total photon number. Total-number preservation
alone does not ensure the required joint diagonality.

These hypotheses include pure loss **during** number-diagonal Kerr,
SNAP or cross-Kerr evolution: no-jump propagators are diagonal,
annihilation jumps lower number, and intervening diagonal factors do
not change that shift. Diagonal phase-noise trajectories remain diagonal.
They do not include heating, return leakage, number-preserving mode
mixing, or every error of a driven nonlinear ancilla.

The switch-plus Kraus
$K_{ij,+}=(B_jA_i+A_iB_j)/2$ has shift $\ell_i+m_j$. If this is zero,
both labels are zero and their commuting Kraus give $K_{ij,+}=B_jA_i$.
If it is positive, $K_{ij,+}$ is strictly lowering, so
$\operatorname{Tr}(W^\dagger K_{ij,+})=0$ for diagonal $W=BA$.

For an ordinary check choose $M>N_{\max}$, coherently add the initial
$N\bmod M$ to a clean $M$-level register, execute the same two native
modules in fixed order, and coherently subtract the final number. Accept
syndrome zero. Each surviving trajectory writes
$\ell_i+m_j\bmod M$ to the register. A nonzero lowering trajectory loses
at most $N_{\max}$ photons, so zero syndrome is precisely no loss.
The procedure reads neither the initial nor the final number separately;
successful trajectories preserve input-number superpositions.

Let $\mathcal F_0$ be the accepted ordinary operation. The **complete**
accepted switched map has the reference-preserving CP decomposition

$$
\mathcal F_{{\rm sw},+}=\mathcal F_0+\mathcal G_{\rm loss},
$$

where the lowering Kraus of $\mathcal G_{\rm loss}$ have zero target
Bell overlap. Thus at every noise strength in this model,

$$
q_0=q_{{\rm sw},+},\qquad p_0\le p_{{\rm sw},+},\qquad
\mathsf S_0\ge\mathsf S_{{\rm sw},+},\qquad
\frac{q_0}{p_0}\ge\frac{q_{{\rm sw},+}}{p_{{\rm sw},+}}
$$

when the denominators are nonzero. The signed-reward comparison counts
rejection as zero; the conditional-fidelity comparison is reported together
with its acceptance probability. They compare zero-loss acceptance with
the switch's plus filter; they do not exclude recovery of loss sectors using a bosonic code,
or assert optimality over both switched flags and arbitrary recovery.

For a multimode code with fixed total number $N_0$, every loss maps into a
sector orthogonal to the ideal output. The same good-weight identity then
holds for **every pure encoded payload/reference**, and a final
nondestructive number check suffices. Fixed-total-number dual-rail codes
with nonlinear entangling phase gates are nontrivial examples; a
single-mode fixed-number phase alone would only be a global phase.
For arbitrary-number inputs the Bell statement above is the asserted
fidelity comparison, since a lowering operator can have nonzero overlap
with an individual number-superposed payload.

One clean parity ancilla gives a cheaper first-order comparator: coherently
copy parity before and uncopy after, accepting no parity change. This
rejects every single loss. For weak **single-photon** damping with the
probability of two or more losses $O(\epsilon^2)$, missed positive even
loss is second order. A two-photon jump of probability $O(\epsilon)$ does
not meet that premise. On a fixed-parity code, only the final check is
needed. The full number check needs a register of at least
$\lceil\log_2(N_{\max}+1)\rceil$ qubits or its oscillator equivalent,
with coherent number-controlled interactions, decoding and readout; it
is not a free operation on traveling light.

[Heeres et al.](https://arxiv.org/abs/1503.01496) demonstrate nonlinear
number-selective cavity phase control, including Kerr-phase compensation.
[Sun et al.](https://arxiv.org/abs/1311.2534) demonstrate repeated QND
photon-parity monitoring with a dispersive ancillary qubit.
[de Graaf et al.](https://arxiv.org/abs/2406.14621) demonstrate a mid-circuit
erasure check on a dual-rail cavity qubit with an explicit error budget.
These make ordinary charge checks relevant native comparators, without
establishing a noiseless coherent before/after gadget or a stored-state
quantum router. Ancilla-record correction and
[path-independent gates](https://arxiv.org/abs/1911.12240) also belong in a
cavity comparison. The checks above are applications of established
[spatiotemporal circuit checks](https://arxiv.org/abs/2112.13904) and
[symmetric channel verification](https://arxiv.org/abs/2503.13114), without
a mechanism-priority claim. Native helper faults, time/energy, actual
coherent order routing and the complete environmental history determine
the remaining hardware frontier.

### Matched noisy copies admit an ordinary same-order path comparator

An unknown many-body matrix is not enough to establish a self-switch
protection advantage. Consider two matched stations $A,B$, each implementing
the same unknown unitary $U$ on a $d$-dimensional payload. An occupied visit
has error $Z^eU$, where $Z=Z^\dagger$, $Z^2=I$, $\operatorname{Tr}Z=0$ and
$e\in\{0,1\}$. Specify the **amplitude-level** empty-port extension as

$$
\widehat V_e=|\mathrm{vac}\rangle\langle\mathrm{vac}|\oplus Z^eU.
$$

The classical fault bits are pre-existing potential-slot variables,
unaffected by whether the payload occupies that port. Empty visits leave no
additional occupancy or timing record. The station implementations have
aligned occupied/vacuum phases. These are physical premises: the same
occupied CPTP channel and an unchanged vacuum density matrix alone do not
specify the required coherence.

With two time windows, write the four bits as $(a_1,a_2,b_1,b_2)$. The switch
routes through $A$ then $B$ or $B$ then $A$. An ordinary coherent path
instead visits $A$ twice or $B$ twice, using fixed chronological order.
Both use two occupied native visits per payload and one retained path
control; their branch unitaries are

$$
\begin{array}{ll}
S_0=Z^{b_2}UZ^{a_1}U,&S_1=Z^{a_2}UZ^{b_1}U,\\
O_0=Z^{a_2}UZ^{a_1}U,&O_1=Z^{b_2}UZ^{b_1}U.
\end{array}
\tag{N1}
$$

For independent identically distributed clock bits, exchanging $a_2,b_2$
preserves the probability law and maps the entire ordinary controlled
unitary $\operatorname{diag}(O_0,O_1)$ to
$\operatorname{diag}(S_0,S_1)$. Averaging therefore gives **identical full
control/payload channels**, before any control readout. Every instrument,
external-reference output and later utility then agrees. Independence is
a sufficient condition; the proof only requires the stated late-slot
exchange symmetry of the complete classical noise law.

There is also a useful exact correlated example. Suppose each station's
bit is quasistatic across its two windows, $a_1=a_2=a$ and $b_1=b_2=b$,
with independent station bits of probability $\epsilon$. The target is
$W=U^2$. Prepare the path control in $+$ and retain only its $X=+$ output,
so the accepted operators are $(S_0+S_1)/2$ and $(O_0+O_1)/2$. Define

$$
r=\frac1d\operatorname{Tr}(U^\dagger ZUZ)\in[-1,1].
$$

It is real because it is the trace inner product of the Hermitian operators
$Z$ and $U^\dagger ZU$, and the bound follows from their Hilbert–Schmidt
norms. Use the full target-$W$ Bell metrics $p,q$ defined above. Direct
multiplication gives the following complete event table:

| Station faults | Common $p_+$ | Switch $q_+$ | Ordinary $q_+$ |
| --- | ---: | ---: | ---: |
| Neither | $1$ | $1$ | $1$ |
| Both | $1$ | $r^2$ | $r^2$ |
| Exactly one | $(1+r)/2$ | $0$ | $(1+r)^2/4$ |

For the last row, the ordinary operator is
$[(ZU)^2+U^2]/2$, whose normalized target trace is $(1+r)/2$.
The switch operator is $[UZU+ZU^2]/2$; both summands have zero target
trace because $\operatorname{Tr}Z=0$. Their acceptance probabilities
are equal. More strongly, for each four-bit realization in (N1),

$$
S_c=Z^{a_2\mathbin\oplus b_2}O_c\quad(c=0,1).
\tag{N2}
$$

Thus both plus and minus acceptance **effects** agree for every input,
not only for the Bell experiment. Their conditional payloads need not
agree in the correlated model, because the common output Pauli is hidden.

Weighting the table by $(1-\epsilon)^2$, $\epsilon^2$ and
$2\epsilon(1-\epsilon)$ gives exactly

$$
\begin{aligned}
p_{\rm O}&=p_{\rm S}=1-\epsilon(1-\epsilon)(1-r),\\
q_{\rm S}&=(1-\epsilon)^2+\epsilon^2r^2,\\
q_{\rm O}-q_{\rm S}&=\tfrac12\epsilon(1-\epsilon)(1+r)^2,\\
\mathsf S_{\rm O}-\mathsf S_{\rm S}
 &=\epsilon(1-\epsilon)(1+r)^2\ge0.
\end{aligned}
\tag{N3}
$$

This holds for **every** $U$ and $\epsilon\in[0,1]$, without learning $U$
or taking a Haar average. At the same Bell yield, ordinary routing also
has no lower conditional Bell overlap $q/p$ when $p>0$. The conclusion
concerns this plus-port target-$U^2$ metric and signed reward. It is not
CP-map dominance, a diamond-distance comparison, a statement for every
payload fidelity, or an optimization over both flagged outputs and
feedback. Arbitrary quantum baths, nonclassical noise and unmatched
stations need their own analysis.

The access and cost boundaries matter. The ordinary path needs two return
visits to a chosen station; an abstract budget of one call to each named
box is a different constraint. Both routes must price their actual vacuum
loops, losses, timing, coherent control and resets. A processor without
those empty-port/return modes does not inherit this photonic-style
comparator automatically, and a switch does not receive such routing free.
Even $A=I$, $B=iI$ have identical occupied channels but give switch arms
$iI,iI$ and ordinary arms $I,-I$; their control interference differs.
Relative station phases, occupancy records or fresh unknown phase drift
cannot be omitted from the native model.

Ordinary coherent-path protection is established prior, including the
[black-box gate error filtration of Lee et al.](https://arxiv.org/html/2210.10733v2),
which does not require learning the protected operation. Equations
(N1)–(N3) are an explicit model screen, not a claim of mechanism priority
or a general hardware-cost advantage. The native checker replays thirty
exact quasistatic full-Bell-Choi metric cases and twenty-four independent-
clock full-control/payload Choi equalities at $d=2,4$, including commuting,
anticommuting and non-Clifford examples. It also checks the relative-vacuum
phase counterexample; the general proofs are the algebra above.

<a id="nr-r06-passive-reordering"></a>

### Ordinary passive probes for a two-photon reordering certificate

For repeatable unitaries $A,B$ on a declared code $H$ of dimension $d$,
a useful compilation metric is

$$
W=(BA)^\dagger AB,\qquad f=|\operatorname{Tr}W/d|^2.
\tag{PR1}
$$

It is the process fidelity of the two ordered channels and ignores their
irrelevant global phase. Equivalently,
$\min_\theta\|AB-e^{i\theta}BA\|_{\rm HS}^2/d=2(1-\sqrt f)$.
A switch on $I/d$ gives real and imaginary parts of
$\operatorname{Tr}W/d$. However the usual commuting-versus-anticommuting
promise gives $f=1$ in both cases, so its query lower bound is not a lower
bound for this compilation endpoint. Nor does $f$ alone certify a
dimension-independent worst-input or diamond error.

There is a strong ordinary constant-sample comparator for two photons in
$M\ge2$ accessible modes. Put $V=\mathbb C^M$, $H=\operatorname{Sym}^2V$,
$d=M(M+1)/2$, and let $\Gamma(U)$ be the passive two-boson action of
$U\in U(M)$. Only two known Fock seeds are needed:
$C=|2_1\rangle$ and $D=|1_1,1_2\rangle$. Let $O_C,O_D$ denote their
Haar-$U(M)$ orbit second moments. Then

$$
aO_C+bO_D=\frac{I+\operatorname{SWAP}_H}{d(d+1)},\qquad
a=\frac{-M^2+3M+2}{M^2+M+2},\quad
b=\frac{2M(M-1)}{M^2+M+2}.
\tag{PR2}
$$

**Proof of the moment identity.** The representation on the symmetric
two-copy space decomposes, with multiplicity one, as

$$
\operatorname{Sym}^2(\operatorname{Sym}^2V)
=\operatorname{Sym}^4V\oplus S_{(2,2)}V,
$$

with dimensions
$d_4=M(M+1)(M+2)(M+3)/24$ and
$d_{22}=M^2(M^2-1)/12$, whose sum is $d(d+1)/2$.
One way to obtain the decomposition is Schur--Weyl duality: symmetry
within each pair and under exchanging the pairs selects the invariant
subspace of $S_2\wr S_2\subset S_4$. Its induced representation is the
three-dimensional permutation representation on the three pairings of
four labels, which splits into the trivial $(4)$ representation and the
two-dimensional $(2,2)$ representation. This gives exactly the two
displayed multiplicity-one sectors; the dimensions follow by the hook
formula.

For a normalized symmetric pair $\psi$, let $\rho_1$ be its normalized
one-particle reduction and $\kappa=\operatorname{Tr}\rho_1^2$.
The full four-particle symmetrizer has expectation
$w_4=(1+2\kappa)/3$ on $\psi\otimes\psi$: eight of its 24 permutation
terms exchange only whole pairs or particles within pairs and contribute
one; the other sixteen contract one particle across the copies and
contribute $\kappa$. Schur averaging is scalar within each sector, so
these two weights determine the complete orbit moment. The seeds have
$\kappa_C=1$ and $\kappa_D=1/2$.
The full Haar-$H$ second moment has weight
$2d_4/[d(d+1)]$ in the first sector. Its corresponding effective purity
is $\kappa_*=2(M+1)/(M^2+M+2)$. Solving
$a+b=1$, $a\kappa_C+b\kappa_D=\kappa_*$ gives (PR2), hence matches
both sector weights and proves the complete operator identity.
For $M=2,3$ its coefficients are positive; for $M\ge4$ the coefficient
$a$ is negative. This is then a signed statistical identity, not a
physical probability ensemble. $M=1$ is trivial and has no $D$ seed.

Prepare two independent copies of the same $\Gamma(U)C$ or
$\Gamma(U)D$, and apply $BA$ to one and $AB$ to the other. A destructive
SWAP measurement has mean
$|\langle\psi|W|\psi\rangle|^2$. If its seed-conditioned means are
$q_C,q_D$, contraction of (PR2) with $W\otimes W^\dagger$ gives

$$
q_*=aq_C+bq_D=\frac{d+|\operatorname{Tr}W|^2}{d(d+1)},\qquad
f=\frac{(d+1)q_*-1}{d}.
\tag{PR3}
$$

No generic nonlinear preparation of Haar states on $H$ is needed.
Mixing each pair of corresponding copy modes on a real-Hadamard 50:50
beam splitter and measuring total photon-number parity in one output
register implements SWAP: at the one-particle level
$H_2^\dagger\operatorname{diag}(1,-1)H_2=X$, and second quantization
gives the full Fock-space register exchange. Other beam-splitter phase
conventions require their known phase corrections. Two-copy mixing and
number-parity readout have established
[bosonic-purity precedent](https://doi.org/10.1103/PhysRevLett.109.020505);
this is not a priority claim for the complete estimator above.

For an explicit sampling bound let $S=|a|+|b|$, choose the seed with
probability proportional to its absolute coefficient, and score a SWAP
outcome $Z\in\{-1,1\}$ as $T=S\operatorname{sgn}(a\text{ or }b)Z$.
Then $\mathbb ET=q_*$, and
$F=(1+1/d)T-1/d$ estimates $f$ without bias. For $M=2,3$, $S=1$ and
$(1+1/d)S\le4/3$. For $M\ge4$,

$$
(1+1/d)S=3-(4M+1)/d<3,
\qquad \operatorname{Var}F\le9.
\tag{PR4}
$$

Thus $n$ independent trials have mean-square error at most $9/n$,
independent of the two-photon Hilbert dimension. Signed scores may be
negative even though $f\ge0$.

**Noisy channels require a different target.** Let $\Phi,\Psi$ be CP
trace-nonincreasing maps on $H$ (including channels), with Kraus operators $L_i,M_j$,
and set $W_{ij}=L_i^\dagger M_j$. The launch-normalized same-input
output SWAP mean is $\sum_{ij}|\langle\psi|W_{ij}|\psi\rangle|^2$.
Equation (PR2) therefore gives

$$
q_* =\sum_{ij}\frac{\operatorname{Tr}(W_{ij}W_{ij}^\dagger)
                    +|\operatorname{Tr}W_{ij}|^2}{d(d+1)}.
$$

Each passive orbit is also a first design because
$\operatorname{Sym}^2V$ is irreducible. Using independent orbit inputs
on the two copies gives
$q_{\rm ind}=\operatorname{Tr}[\Phi(I/d)\Psi(I/d)]
=\sum_{ij}\operatorname{Tr}(W_{ij}W_{ij}^\dagger)/d^2$.
Consequently, with $j_\Phi=(\mathrm{id}\otimes\Phi)(\Phi_d)$ in the
normalized Choi convention,

$$
(1+1/d)q_*-q_{\rm ind}
=\sum_{ij}|\operatorname{Tr}(L_i^\dagger M_j)|^2/d^2
=\operatorname{Tr}(j_\Phi j_\Psi).
\tag{PR5}
$$

For trace-decreasing maps the Choi operator is not renormalized on
success. Failed/erased trials score zero; a conditional surviving-output
SWAP mean must first be multiplied by its actual joint survival
probability. The total absolute statistical coefficient is at most
$(1+1/d)S+1\le4$, giving variance at most 16. Independent channel uses
conditional on the fixed device instance and identifiable output/failure
sectors are premises. The statistic (PR5) is not generally the switch's
Kraus-interference visibility: complete qubit $Z$ and $X$ dephasers have
the same depolarizing ordered channel with Choi overlap $1/4$, while their
switch visibility is $1/2$.

Each ordinary two-copy trial uses four photons, four occupied pair-module
traversals, and eight individual photon/module passages, plus the passive
preparations and destructive parity measurement. The switch uses a
different control/routing resource. Neither count establishes total
runtime or source cost. Preparing the seeds, matching the copies, source
heralds, losses, number resolution and every launch must be charged.
A weak-coherent two-photon input split on one beam splitter contains a
split-pair term and does not supply collective two-arm order control for
free. Conversely source multiplexing, buffers and parallel copies can
change an assumed squared two-copy preparation penalty. A finite passive
design needs its own approximation bound if replacing Haar randomization.
This is a known-probe scalar comparison, not a delivered unknown-data
gate, an ordinary lower bound or a demonstrated native switch advantage.

<a id="nr-r06-bosonic-compilers"></a>

### Calibrated bosonic noise admits full ordinary switch compilers

Two broad bosonic memory models have exact ordinary implementations of
their full switched channel. These implementations use the same two
chronological noise calls, the same independent control qubit, two known
controlled gates and classical randomization. They do not detect a lost
photon or an actual displacement, and equality precedes any code projection.
Thus arbitrary finite-energy cat, binomial or GKP encodings, reference
correlations, recoveries and acceptance instruments can be attached identically.
The conclusion assumes calibrated parameters and the stated ideal helper
gates. It does not establish a hardware winner or an unknown-parameter
metrology converse.

**Two independent pure-loss channels.** Write $N=a^\dagger a$ and use the
standard attenuator Kraus operators

$$
A_l(\eta)=\sqrt{\frac{(1-\eta)^l}{l!}}\,\eta^{N/2}a^l,
\quad
A_l(\eta)|n\rangle=\sqrt{\binom nl}(1-\eta)^{l/2}
\eta^{(n-l)/2}|n-l\rangle.
\tag{BOS1}
$$

The representation and its amplifier dual are standard
[Gaussian-channel Kraus identities](https://doi.org/10.1103/PhysRevA.84.042311).
Let $\tau=\eta_1\eta_2$, $B_q=A_q(\tau)$ and

$$
\zeta=\frac{\sqrt{\eta_1}+\sqrt{\eta_2}}{1+\sqrt\tau}\in[0,1].
\tag{BOS2}
$$

For $q=l+m$, normal ordering gives
$A_m(\eta_2)A_l(\eta_1)=c_{lm}B_q$ and
$A_l(\eta_1)A_m(\eta_2)=d_{lm}B_q$, with

$$
\begin{aligned}
c_{lm}^2&=\binom ql\frac{(1-\eta_1)^l(1-\eta_2)^m\eta_1^m}{(1-\tau)^q},\\
d_{lm}^2&=\binom ql\frac{(1-\eta_1)^l(1-\eta_2)^m\eta_2^l}{(1-\tau)^q}.
\end{aligned}
$$

Both coefficients are nonnegative. The binomial theorem gives
$\sum_{l+m=q}c_{lm}^2=\sum d_{lm}^2=1$ and

$$
\sum_{l+m=q}c_{lm}d_{lm}
=\left[\frac{(1-\eta_1)\sqrt{\eta_2}+
 (1-\eta_2)\sqrt{\eta_1}}{1-\eta_1\eta_2}\right]^q
=\zeta^q.
\tag{BOS3}
$$

For example, the normal-ordering identity used here is
$a^m\eta^{N/2}=\eta^{m/2}\eta^{N/2}a^m$. The last simplification
in (BOS3) factors the numerator as
$(\sqrt{\eta_1}+\sqrt{\eta_2})(1-\sqrt\tau)$.

For an arbitrary input $\sum_{a,b=0}^1|a\rangle\langle b|_C\otimes\rho_{ab}$,
where each block may include an arbitrary reference, the switch consequently
applies $\mathcal L_\tau$ to both diagonal blocks and applies

$$
\mathcal J_\zeta(X)=\sum_{q\ge0}\zeta^q B_qXB_q^\dagger
\tag{BOS4}
$$

to both off-diagonal blocks. This specifies the entire channel, including
control/payload entanglement. With a plus control its measured-$X$ maps
are $\sum_q(1\pm\zeta^q)B_q\rho B_q^\dagger/2$: the flag only
reweights total-loss sectors, while retaining their full no-jump attenuation.

For $0\le\zeta<1$ sample a known phase from the Poisson-kernel density

$$
p_\zeta(\phi)=\frac{1-\zeta^2}
 {2\pi(1-2\zeta\cos\phi+\zeta^2)},\qquad
\mathbb E e^{ir\phi}=\zeta^{|r|}.
\tag{BOS5}
$$

The moment identity follows by multiplying the two geometric series for
$(1-\zeta e^{i\phi})^{-1}$ and its conjugate. Let
$R_\phi=e^{i\phi N}$ and
$U_\phi=|0\rangle\langle0|\otimes I+|1\rangle\langle1|\otimes R_\phi$.
Apply $U_\phi$, the two actual loss calls in serial order, then
$U_\phi^\dagger$, and discard the sampled phase. Since
$R_\phi^\dagger B_qR_\phi=e^{iq\phi}B_q$, its effective Kraus is
$(|0\rangle\langle0|+e^{iq\phi}|1\rangle\langle1|)\otimes B_q$.
Averaging (BOS5) gives exactly (BOS4) and the same diagonal blocks.
This proves full channel equality without syndrome readout or a
Knill--Laflamme assumption.

If a slot is identity, $\zeta=1$ and use the point mass $\phi=0$.
At $\tau=0$ take $B_q=|0\rangle\langle q|$, with $0^0=1$ for its
$q=0$ sector; the displayed equality also follows by continuous limits on
finite Fock inputs. Finite-Fock projections and trace-norm contraction of
all the channels extend the proof to every trace-class input/reference.
Finite energy is needed for a physical implementation, not for this
abstract channel equality. The argument uses independent vacuum-loss slots.

**Two quantum-limited amplifier channels.** For finite gain $G\ge1$,

$$
H_l(G)=G^{-1/2}A_l(1/G)^\dagger,\qquad
H_l(G)|n\rangle=\sqrt{\binom{n+l}l}
(G-1)^{l/2}G^{-(n+l+1)/2}|n+l\rangle.
$$

Adjointing the preceding product calculation proves the same full-channel
compiler, now with combined gain $G_1G_2$ and
$\zeta=(\sqrt{G_1}+\sqrt{G_2})/(1+\sqrt{G_1G_2})$.
The total-added-photon Kraus has the opposite number charge; the real
moments in (BOS5) are unchanged by this sign. This statement does not
include a mixed amplifier/attenuator pair or a thermal attenuator.

**Two centered isotropic Gaussian displacement channels.** Use
$D(\alpha)=e^{\alpha a^\dagger-\alpha^*a}$ and independent
$\alpha\sim\mathrm{CN}(0,v_A)$, $\beta\sim\mathrm{CN}(0,v_B)$, with
$\mathbb E|\alpha|^2=v_A$. Put $\gamma=\alpha+\beta$ and
$w=v_Av_B/(v_A+v_B)$, with $w=0$ when both variances vanish.
The Weyl relation gives order amplitudes
$e^{\pm i\chi}D(\gamma)$, where
$\chi=\operatorname{Im}(\beta\alpha^*)=\operatorname{Im}(\gamma\alpha^*)$.
Conditional on $\gamma$,
$\alpha=v_A\gamma/(v_A+v_B)+\delta$, with
$\delta\sim\mathrm{CN}(0,w)$. Thus $\chi$ is centered real Gaussian of
variance $w|\gamma|^2/2$, and

$$
\mathbb E[e^{2i\chi}\mid\gamma]=e^{-w|\gamma|^2}.
\tag{BOS6}
$$

The diagonal control blocks are the net-displacement channel of variance
$v_A+v_B$. Both off-diagonal blocks are
$\int p_{v_A+v_B}(\gamma)e^{-w|\gamma|^2}
D(\gamma)X D(\gamma)^\dagger\,d^2\gamma$.

The conditional variance gain has a closed quantitative limit. Put
$v=v_A+v_B>0$ and $c=(1+v_Av_B)^{-1}$. Multiplying the Gaussian density
by the (BOS6) kernel gives
$p_v(\gamma)e^{-w|\gamma|^2}=c\,p_{cv}(\gamma)$.
For an initially plus helper and $X$ flags, the exact unnormalized maps
are $\mathcal F_\pm=(\mathcal N_v\pm c\mathcal N_{cv})/2$ and
$p_\pm=(1\pm c)/2$, where $\mathcal N_s$ denotes additive complex
Gaussian displacement noise of variance $s$. The maps are CP because
they arise from the displayed physical flag instrument. Their conditional
added displacement variances are

$$
V_+=v\frac{1+c^2}{1+c},\qquad V_-=v(1+c),\qquad
p_+V_++p_-V_-=v.
\tag{BOS6a}
$$

The minus variance is asserted only when $p_->0$; otherwise its
unnormalized contribution is zero. Gaussian integration proves these
identities directly from the second displacement moment. They concern
the added classical displacement variance, not the entire variance of an
arbitrary input state. Moreover

$$
\frac{V_+}{v}-(2\sqrt2-2)
=\frac{[c-(\sqrt2-1)]^2}{1+c}\ge0.
\tag{BOS6b}
$$

Equality occurs at $c=\sqrt2-1$, so the largest plus-flag variance
reduction relative to the serial variance is $3-2\sqrt2$, about 17.16%.
This is a variance-only comparison to serial noise, not a Fisher
information, readout-error or rate bound. The ordinary calibrated
controlled-displacement compiler (BOS7) reproduces the same flags and
conditional output. The distinct [full-support
obstruction](obstructions.md#nr-r04-gaussian-displacement) addresses
exact heralded code recovery; approximate utility remains a separate
task.

Ordinarily sample a known $z\sim\mathrm{CN}(0,w)$, apply controlled
$D(z)$, the same two serial displacement channels, then the inverse
controlled displacement. The conjugation identity

$$
D(z)^\dagger D(\gamma)D(z)
=e^{2i\operatorname{Im}(\gamma z^*)}D(\gamma)
\tag{BOS7}
$$

gives the same real averaged multiplier $e^{-w|\gamma|^2}$ in every
off-diagonal block. All four control blocks therefore agree, for arbitrary
payload/reference inputs. The actual hidden area need not be recoverable
from a final GKP syndrome; the circuit reproduces its averaged instrument
without learning either actual shift. General anisotropic or non-Gaussian
shift laws are not covered: their conditional area kernel need not be the
characteristic function of an independently sampled displacement.

**Native resources and parameter scope.** Known conditional number phases
and conditional displacements are established ordinary cavity-ancilla
primitives, respectively used in
[autonomous cat recovery](https://doi.org/10.1038/s41586-021-03257-0) and
[GKP syndrome/control](https://doi.org/10.1038/s41586-020-2603-3), including
[beyond-break-even GKP memory](https://doi.org/10.1038/s41586-023-05782-6).
These experiments do not demonstrate either compiler or a coherent-order
encoded memory. The two gates, their refocusing, duration, drive energy,
helper noise and storage loss during execution must be charged. For
example the cat-recovery device reports $\chi/(2\pi)=1.32$ MHz, so positive
dispersive angles $\phi$ and $2\pi-\phi$ alone take $2\pi/\chi\simeq0.758$
$\mu$s after known unconditional phase compensation. This excludes pulses,
decoupling, Kerr terms and decoherence; it is not a complete performance estimate.

The Gaussian helper displacement adds ensemble mean photon number $w$
on its displaced branch and has an unbounded ideal amplitude. Replacing
the sampled tail $|z|>R$ by an admitted operation changes the full channel
in half-diamond norm by at most its classical probability $e^{-R^2/w}$.
This follows by coupling identical samples on the unchanged part and
bounding two TP channels by diamond distance two on the tail. It makes no
unbounded-energy operator-norm claim for nearby displacements; finite
precision within the retained disk still needs its physical error bound.

The control is a separate $C\otimes\mathrm{Fock}$ factor through vacuum.
A lost optical packet does not automatically leave a usable path qubit.
For a communication cut the same control must be available at both helper
gates; any transport of it is an explicitly charged quantum resource.
These local-circuit identities are not automatically receiver-local LOCC
reductions. Code decoding or storing a logical qubit in an ideal control
is an additional bypass baseline only when those physical operations and
memory quality are actually available.

The phase law in (BOS5) and variance $w$ depend on calibrated noise
parameters. Pointwise equality of known channels does **not** give equality
of Fisher information for unknown parameters: the helper settings must be
held fixed in such a derivative. Bath reuse, thermal noise, nonlinear
engineered recovery, correlated/nonstationary errors and actual gate faults
require their complete model. No native timing or logical-performance
advantage, or general no-go for encoded dissipative switches, is inferred.

<a id="nr-r06-cat-reservoir-parity"></a>

### Non-Gaussian cat reservoirs retain an ordinary jump-parity check

**Device problem and task.** A non-Gaussian stabilizer is a meaningful
memory candidate outside the additive-Gaussian compiler. It does not,
however, make every commutator flag new error information.
[Rousseau et al., arXiv:2502.07892
(2025)](https://arxiv.org/html/2502.07892), implement a deformed cat
reservoir with memory-buffer coupling
$H/\hbar=g_2F(a)b^\dagger+g_2^*F(a)^\dagger b$,
$F=a^2-\alpha^2+\lambda(n-\alpha^2)$, $n=a^\dagger a$.
Reported parameters include memory loss $\kappa_1/(2\pi)=2.3$ kHz,
thermal occupation $n_{\rm th}=0.93$, buffer loss
$\kappa_b/(2\pi)=18.2$ MHz and $g_2/(2\pi)=1.3$ MHz.
The quoted $\kappa_2/(2\pi)=0.37$ MHz is an estimate from buffer
elimination. At fitted deformation $\lambda=1.04$ and mean photon number
4.1, the measured bit-flip time is 22 s while phase-flip time is
$1.3\,\mu$s. Their photon-number/parity tomography uses buffer readout
and a deflation map; it does not demonstrate a retained qubit's coherent
controlled-parity gate. Long bit-flip lifetime alone is therefore not
the fidelity of an arbitrary unknown stored qubit.

A second primary device,
[Adinolfi et al., arXiv:2511.01027
(2025)](https://arxiv.org/html/2511.01027), combines Kerr-cat
Hamiltonian confinement with selective single-photon cooling through a
lossy cavity. The measured oscillator $T_1$ is $55.7\pm0.7\,\mu$s;
ordinary echo improves Ramsey coherence from $13.2\pm0.5$ to
$40.9\pm1.3\,\mu$s. Cooling lowers leakage population but can worsen
logical tunneling through warm-cavity excitation. At one stated working
point it increases bit-flip time from 240 to $610\,\mu$s. The paper's
effective cavity populations 0.025 for a population fit and 0.004 for a
tunneling-threshold fit are model parameters, not one directly measured
universal bath temperature. Its protocol waits $1.2\,\mu$s after a
dissipation pulse for cavity photons to decay. These are real cooling,
dephasing and reset constraints, rather than independent freely
reorderable noise boxes.

[Putterman et al., Nature **638**, 927–934
(2025)](https://doi.org/10.1038/s41586-025-08642-7), supply a stronger
ordinary quantum-memory comparator on a different chip: five cat storage
modes and four transmon syndrome ancillas implement a distance-five
repetition memory. Average bare storage $T_1$ exceeds $60\,\mu$s.
At cat size two, measured bit-flip times exceed 1 ms and phase-flip times
are 27–33 $\mu$s, versus 2–3 $\mu$s correction cycles. Minimum measured
logical error per cycle is 1.65(3)% for distance five and 1.75(2)% for
the distance-three sections. These additional modes, couplers, ancilla
readout/reset and cycles are priced resources, not controls silently
available to a single moon-cat device.

Fix a normalizable, calibrated orthonormal code isometry $V$ and its
physical encoding/decoding. For example, normalized even/odd cats at
finite $\alpha\ne0$ define an orthonormal two-dimensional target code;
the deformed device requires its own calibrated code. The formal dark
state recurrence in the primary paper's Appendix H.2.1 is
$\mu_{n+2}/\mu_n=[\alpha^2(1+\lambda)-\lambda n]/
\sqrt{(n+2)(n+1)}$. For a nonterminating parity sequence its magnitude
tends to $|\lambda|$; at generic $|\lambda|>1$ that series is not
normalizable. Exact termination of a nonzero parity sequence requires
$\alpha^2(1+\lambda)/\lambda$ to be a nonnegative integer of that
parity; at most one parity can terminate. Consequently $|\lambda|>1$
cannot give a two-dimensional normalizable dark kernel of this
simplified $F$. Thus a fitted $\lambda=1.04$ or a truncated dark vector
does not supply two exact infinite-Fock dark states. The measured
finite-energy metastable code and the well-defined physical channel
must be established with their actual high-energy completion. Let
$J_r=(\mathrm{id}_R\otimes\Lambda_r)(\Phi_2)$ be the complete logical
Choi output for record $r$, with actual preparation, control, noise and
decoding included. Report $p_r=\operatorname{Tr}J_r$ and
$q_r=\langle\Phi_2|J_r|\Phi_2\rangle$, all rejected records, elapsed
time and reset. For an accepted set $A$, the pair
$(p_A,q_A)=(\sum_Ap_r,\sum_Aq_r)$ gives conditional fidelity $q_A/p_A$;
$q_A$ charges every unsuccessful launch. Input-dependent acceptance
also requires its success effect and worst-case success probability.
This is distinct from one logical-Pauli decay time.

**The complete idle dynamics and symmetry.** Retain memory $a$, buffer
$b$, every output line and a purification of each thermal input. The
declared rotating-wave model uses

$$
\begin{aligned}
H_{ab}/\hbar&=H_{\rm even}/\hbar+g_2F(a)b^\dagger+g_2^*F(a)^\dagger b,\\
L_b&=\sqrt{\kappa_b}\,b,\qquad
L_\downarrow=\sqrt{\kappa_1(n_{\rm th}+1)}\,a,\qquad
L_\uparrow=\sqrt{\kappa_1n_{\rm th}}\,a^\dagger.
\end{aligned}
\tag{CAT1}
$$

Here $H_{\rm even}$ commutes with memory parity $\Pi=e^{i\pi n}$.
Number detuning, Kerr terms and even-photon drives obey this premise;
a single-photon memory drive during a gate does not. Buffer heating
adds a jump proportional to $b^\dagger$ without changing its memory
parity. Dephasing jumps proportional to $n$ are also even. Pump
imperfections that add odd Hamiltonian terms must be measured and
included rather than being called harmless calibration noise.

Equation (CAT1), or its well-defined unitary field dilation, retains
the finite buffer bandwidth and records. Only in the declared
adiabatic-elimination regime may it be replaced by
$L_2=\sqrt{\kappa_2}F$, $\kappa_2=4|g_2|^2/\kappa_b$; the primary
paper states $8|g_2\alpha|\ll\kappa_b$. The estimate is not a
uniform theorem about the full measured circuit or its strong-pump
corrections. The Kerr-cat device's exchange term
$a b^\dagger+a^\dagger b$ instead commutes with **joint** parity
$\Pi_a\Pi_b$, not memory parity alone; using the theorem there requires
joint controlled parity or an independently justified effective map.

**Finite-time ordinary syndrome, including all no-jump evolution.**
More generally let a well-defined idle Lindblad evolution have
$[H(t),\Pi]=0$ and jumps $\Pi L_j(t)\Pi=s_jL_j(t)$,
$s_j\in\{+1,-1\}$. Then
$H_{\rm eff}=H-i\sum_jL_j^\dagger L_j/2$ is even. Each no-jump
propagator commutes with $\Pi$. For every complete trajectory, including
times and all purifying records, its Kraus operator therefore satisfies

$$
\Pi K_h\Pi=s_hK_h,\qquad
s_h=\prod_{j\in h}s_j=(-1)^{m(h)}.
\tag{CAT2}
$$

In (CAT1), $m$ counts the total number of memory loss **and heating**
jumps; buffer jumps and even stabilizer jumps do not contribute. The
identity holds on the full memory-buffer system, with identity on
unaffected registers. It does not require access to the trajectory.
Use one independent helper initially plus and the two known gates
$C_\Pi=P_0\otimes I+P_1\otimes\Pi$ before and after the entire
ordinary exposure. Since $C_\Pi^2=I$, each full Kraus becomes

$$
C_\Pi(I\otimes K_h)C_\Pi
 =(P_0+s_hP_1)\otimes K_h,\qquad
\mathcal E_\pm(\rho)=\sum_{h:s_h=\pm1}K_h\rho K_h^\dagger.
\tag{CAT3}
$$

An $X$ measurement reads jump parity without measuring the unknown
**initial** logical parity. The identity is before measurement and
therefore extends to arbitrary helper/data/reference inputs. Every
record, including the rejected parity if a task rejects it, is retained.
After summing flags, the data channel is exactly the original idle
channel. Consecutive parity-symmetric stages and simultaneous even
stabilization obey the same result, without ideal code states or
infinitesimal time steps.

There is also a bounded-operator proof that does not exchange an
unbounded jump expansion with a limit. If a normal CPTP map
$\mathcal E$ is parity covariant, take any Kraus representation and
put $K_j^\pm=(K_j\pm\Pi K_j\Pi)/2$. Direct expansion gives
$\sum_{j,\pm}K_j^\pm\rho K_j^{\pm\dagger}
=[\mathcal E(\rho)+\Pi\mathcal E(\Pi\rho\Pi)\Pi]/2
=\mathcal E(\rho)$. The wrapper's two flag Kraus operators are exactly
$K_j^\pm$. This proves (CAT3) on trace-class inputs for any such
well-defined channel. A noncovariant channel is instead parity twirled
by discarding this helper; it is not covered by the no-change statement.

The two $C_\Pi$ gates, helper coherence for the full exposure and its
readout are actual resources. Buffer homodyne tomography or a destructive
final parity measurement is not evidence that these coherent gates
exist. Conversely, if a switch proposal adds a qubit/coupler capable of
them, they belong in its ordinary comparator. Transferring the logical
state into a cleaner helper is a further baseline only when a physical
transfer, helper lifetime and gates are supplied and priced.

**What the small-time switch flag detects.** For a separate ideal
two-slot screen, let $\mathcal A_{t_A}$ have jumps
$L_-=\sqrt{\gamma_-}a$, $L_+=\sqrt{\gamma_+}a^\dagger$ and let
$\mathcal B_{t_B}$ have $L_B=\sqrt{\kappa_2}F$.
Keep their independent reservoir records. Write the no-jump generators
$R_A=iH_A+\sum_\sigma L_\sigma^\dagger L_\sigma/2$ and
$R_B=iH_B+L_B^\dagger L_B/2$, with $\hbar=1$.
The exact ideal switch-flag Kraus operators are
$M^\pm_{ij}=(B_jA_i\pm A_iB_j)/2$.
Summing both flags gives
$(\mathcal B\circ\mathcal A+\mathcal A\circ\mathcal B)/2$,
so this is a complete instrument, not a success-only channel.
Expand its **minus** operators on a common analytic/core domain:

$$
\begin{aligned}
M^-_{00}&=\tfrac12t_At_B[R_B,R_A]+\text{higher mixed orders},\\
M^-_{\sigma0}&=-\tfrac12t_B\sqrt{t_A}[R_B,L_\sigma]
                         +\text{higher mixed orders},\\
M^-_{0B}&=-\tfrac12t_A\sqrt{t_B}[L_B,R_A]
                         +\text{higher mixed orders},\\
M^-_{\sigma B}&=\tfrac12\sqrt{t_At_B}[L_B,L_\sigma]
                         +\text{higher mixed orders}.
\end{aligned}
\tag{CAT4}
$$

These follow by multiplying $A_0=I-t_AR_A+O(t_A^2)$,
$B_0=I-t_BR_B+O(t_B^2)$ and the leading jump amplitudes.
The first three lines explicitly keep the no-jump commutators; they
are not silently set to zero when the dissipative jumps commute.
Multiple-jump trajectories and corrections to the one-jump trajectories
enter higher orders. This is not an exact finite-time Kraus truncation
or a remainder bound uniform over all finite-energy states.

The CCR give

$$
[F,a]=-\lambda a,\qquad [F,a^\dagger]=2a+\lambda a^\dagger,
\quad
\mathcal F_-(\rho)=\frac{\kappa_2t_At_B}{4}
\left[\gamma_-|\lambda|^2a\rho a^\dagger
 +\gamma_+Q\rho Q^\dagger\right]+O(\epsilon^3),
\quad Q=2a+\lambda a^\dagger,
\tag{CAT5}
$$

where $t_A,t_B=O(\epsilon)$ and the expansion has a valid domain as
above. At zero temperature the leading minus map is a photon-loss map
of order $t_At_B$. The ordinary odd-parity branch has leading map
$\gamma_-t_Aa\rho a^\dagger$. Random thinning with probability
$\kappa_2t_B|\lambda|^2/4$ reproduces the leading selected map when
this probability is at most one. This comparison charges the discarded
launches. It matches that leading map only; it neither compiles the
whole non-Gaussian switch nor dominates a finite-time heralded frontier.
For $\lambda=0$ the loss contribution in (CAT5) vanishes, but the thermal
heating contribution and higher no-jump terms need not vanish.

**The measured bath is not loss-only.** On any state of mean photon
number $N$, Cauchy--Schwarz gives
$|\langle a^2\rangle|\le\sqrt{N(N+1)}$ and hence

$$
\operatorname{Tr}(Q^\dagger Q\rho)
 =4N+|\lambda|^2(N+1)
 +2\lambda\langle a^{\dagger2}\rangle
 +2\lambda^*\langle a^2\rangle
 \ge(2\sqrt N-|\lambda|\sqrt{N+1})^2.
\tag{CAT6}
$$

At the displayed rounded moon-cat parameters $N=4.1$, $\lambda=1.04$,
$n_{\rm th}=0.93$, the elementary bound
$\sqrt{N(N+1)}\le4.6$ gives a lower bound 2.78016 for this expectation,
while $|\lambda|^2N=4.43456$. Thus in the *leading effective-model*
minus map the heating-record fraction is at least

$$
\frac{0.93(2.78016)}{1.93(4.43456)+0.93(2.78016)}
 =0.232007\ldots>0.23.
\tag{CAT7}
$$

This is a bound on contributions of the two orthogonal thermal bath
records in (CAT5), not a measured switch probability, logical error rate
or proof that every heating event is uncorrectable. It rules out
interpreting this nominal model's flag as a loss-only syndrome. The
primary paper also reports pump-dependent effective error rates; bare
thermometry does not fix every pump-on $\gamma_\pm$. This calculation
uses the declared thermal component, without fitting those extra errors.

**Physical decision.** Ordinary simultaneous stabilization, bias-tuned
encoding, echo, accessible reservoir records and repetition/syndrome
correction are material comparators. The natural loss bath acts during
both pulse windows; turning a pump on and off does not by itself supply
two independent channel slots. A real controlled-order proposal must
give the joint memory/buffer/helper/environment Hamiltonian and the
early/late emitted wavepackets. Identifying time-distinguishable bath
photons by a common abstract Kraus index is not a physical erasure of
their timing. Charge any route, capture, delay, bath reset and phase
matching needed to realize the ideal two-slot instrument.

No full finite-error memory or heralded-fidelity frontier is dominated
here. The exact baseline is the finite-time parity instrument (CAT3);
the small-time screen shows why its non-Gaussian commutator is not by
itself a new loss syndrome, and why thermal records matter. A positive
application would have to exceed that ordinary record/energy/time
frontier using a demonstrated compatible coherent interface. The next
finite test must derive that instrument from the physical source and
joint bath dilation, calibrate odd pump terms and thermal populations,
and bound the finite-time, temporal-tail and mode-truncation remainders
over the admitted code energies and gate durations. A leading-order
commutator or a selected trajectory is insufficient. Finite-
energy anisotropic GKP remains a separate unclosed approximate-memory
comparison; ideal-syndrome dominance is not its finite-envelope proof.

The [exact parity replay](checks/architecture/verify_cat_reservoir_parity.py)
checks complete finite memory-buffer maps, both ordinary parity flags,
the complete switch/mixed-order record law, formal normally ordered CCR
commutators and all four mixed no-jump/jump coefficient families. It also
checks the nominal thermal bound with rational arithmetic. The
trace-class symmetry proof, trajectory convergence, finite-time
remainders, actual coherent access and experimental utility are analytic
or measured inputs, not consequences of a finite replay.

<a id="nr-r06-readout-noise-floor"></a>

### Readout protection needs noise ports and the actual cavity response

A useful microwave task is to protect a dispersively coupled readout
cavity and its qubit from amplifier thermal backflow while transmitting
the outgoing pointer to a detector. Hold fixed the cavity response and
loading over the operational band, probe energy, elapsed time, useful
forward information and available pump resources. The
[interferometric Josephson readout experiment of Abdo et al., PRX
Quantum **2**, 040360 (2021), §IV.3](https://arxiv.org/html/2006.01918)
varies isolation and measures qubit dephasing from output-chain noise.
Its model includes the resonator's frequency response, residual noise
and pump depletion/dynamic range. A single-frequency isolation value
therefore does not specify protection. A mean returning photon flux
is a useful backaction proxy; a full qubit dephasing or excitation claim
also needs its coupling and relevant noise spectrum.

**Complete Gaussian inputs and outputs.** For photon-flux-normalized
annihilation inputs, a stable linear pumped circuit has Bogoliubov map

$$
b_{\rm out}=U b_{\rm in}+V b_{\rm in}^\dagger,\qquad
UU^\dagger-VV^\dagger=I,\quad UV^T-VU^T=0.
$$

All loss, idler and dump inputs are included; at Fourier frequency
$\omega$, the creation input has the conjugate frequency. For independent
thermal inputs with occupation matrix N and coherent means treated
separately, its normal noise covariance is
$N_{\rm out}=UNU^\dagger+V(N^T+I)V^\dagger$. In particular a protected
output q receives
$n_q=\sum_j|U_{qj}|^2n_j+|V_{qj}|^2(n_j+1)$: gain has spontaneous
noise even with a vacuum idler. The
[41-tone comb of Bock et al., Physical Review Applied **24**, 014027
(2025), §§II–III](https://arxiv.org/html/2501.09453)
uses annihilation and conjugate amplitudes, low- and high-frequency
pumps and a common phase reference. Its coherent-tone scattering does
not itself supply the quantum noise covariance. No fresh-oracle prior
or unknown-coupler query ceiling is used in this readout task.

For a known-direction weak coherent pointer, define the forward
efficiency e as homodyne Fisher information divided by ideal homodyne
information on that incoming pointer. A passive detected gain
$\eta=|S_{dq}|^2$ and excess thermal occupation $N_d$ give
$e=\eta/(1+2N_d)$, since the quadrature variance is $1/2+N_d$.
This is a stated local information metric, not automatically every
experimental definition of qubit measurement efficiency or a binary
coherent-state discrimination error.

**Multimode passive feedback floor.** A network reflection changes the
cavity loading, so external-source transmission/noise alone can give a
misleading comparison. At each frequency take passive return and
environment blocks R,F satisfying

$$
b_{\rm in}=R b_{\rm out}+F e_{\rm env},\qquad
RR^\dagger+FF^\dagger=I.
$$

The identity is a row of the complete unitary scattering matrix,
including all loss ports. Let the cavity equations be
$a=\chi_0(D b_{\rm in}+d)$ and $b_{\rm out}=b_{\rm in}-Da$, with D
positive diagonal square roots of the bare external coupling rates.
The vector d contains independent drives and other cavity baths.
Require $X=(I-R)^{-1}$ to exist and the closed loop to be stable.
Eliminating the return gives
$b_{\rm in}=-XRDa+XF e_{\rm env}$ and
$\chi_{\rm eff}^{-1}=\chi_0^{-1}+DXRD$.
Write $\chi_0^{-1}=\chi_{\rm other}^{-1}+D^2/2$, explicitly separating
the bare network-port damping. Since X commutes with R and $XR=X-I$,
put $Y=(I+R)(I-R)^{-1}=2X-I$ and $L=DXF$. Then

$$
\chi_{\rm eff}^{-1}=\chi_{\rm other}^{-1}+\tfrac12DYD,\qquad
a=\chi_{\rm eff}(L e_{\rm env}+d),\qquad
K_{\rm eff}:=D\operatorname{Re}Y D=LL^\dagger.
\tag{G1}
$$

Here $\operatorname{Re}Y=(Y+Y^\dagger)/2$. To prove its last equality,
use
$I-RR^\dagger=(I-R)+(I-R^\dagger)-(I-R)(I-R^\dagger)$.
Multiplying by X and $X^\dagger$ gives
$X(I-RR^\dagger)X^\dagger=X+X^\dagger-I=\operatorname{Re}Y$;
substitute $FF^\dagger=I-RR^\dagger$. This proves positivity of the
effective damping kernel without assuming R normal or diagonal.

If the independent thermal environmental inputs obey
$N_{\rm env}\succeq n_cI$, their effective drive covariance satisfies

$$
Q_{\rm eff}=LN_{\rm env}L^\dagger\succeq n_cK_{\rm eff}.
\tag{G2}
$$

Congruence by the full susceptibility gives their intracavity noise
contribution

$$
N_{a,\rm network}=\chi_{\rm eff}Q_{\rm eff}\chi_{\rm eff}^\dagger
\succeq n_c\chi_{\rm eff}K_{\rm eff}\chi_{\rm eff}^\dagger.
\tag{G3}
$$

These are frequency-resolved matrix inequalities; integration against
positive mode/filter weights preserves them. At fixed full susceptibility
and coupling/damping kernel, passive routing cannot lower its effective
photon occupation below the smallest supplied thermal occupation. For
frequency conversion this compares occupations, not thermodynamic
temperatures at different frequencies; pump work still counts. Colored
noise and mode mixing are included in this spectral statement, but a
white-noise qubit dephasing formula is not thereby established. Active
gain, squeezed or correlated inputs, conditional measurement, changed
couplings or a changed cavity response require their actual instruments.

For one return r, (G1)–(G3) reduce to
$n_{\rm eff}=n_f/(1-|r|^2)\ge n_c$ and
$\kappa_{r,\rm eff}=\kappa_r(1-|r|^2)/|1-r|^2$.
At $r=4/5$ the external linewidth is nine times its bare value; at
$r=-4/5$ it is one ninth, although $n_{\rm eff}=n_c$ for a cold input in
both cases. A changed spectral density with changed linewidth is not a
fixed-bandwidth protection gain. A fully closed port with zero damping
does not evade a task requiring finite readout coupling.

**A finite-band ordinary reservoir benchmark.**
[Metelmann and Clerk, PRX **5**, 021025 (2015), §§II.A and
III.A](https://arxiv.org/html/1502.07274)
construct directionality by balancing coherent and dissipative
couplings. Retain their auxiliary reservoir mode rather than assuming
an infinitely broad Markov bath. In a passive three-mode realization,
let external linewidths be $\Gamma=\operatorname{diag}(\kappa,\kappa,
\kappa')$ and Hermitian hopping matrix h have
$h_{12}=i\kappa/2$, $h_{13}=h_{23}=g=\sqrt{\kappa\kappa'}/2$,
with zero diagonal. With no hidden loss bath,

$$
S(\omega)=I-\sqrt\Gamma
(\Gamma/2-i\omega I+ih)^{-1}\sqrt\Gamma.
$$

The defining damped input/output equations preserve the commutator,
and direct multiplication gives $S^\dagger S=I$ at real frequency.
At $\omega=0$, its power matrix is the cycle
$|S|^2=(\begin{smallmatrix}0&0&1\\1&0&0\\0&1&0\end{smallmatrix})$:
the pointer reaches port 2, hot port-2 noise goes to the dump, and
port 1 receives the reservoir input. Thus the matched carrier has
$B=n_c$ returning photons and $e=1$. For the explicit finite choice
$\kappa=1$, $\kappa'=4$, $g=1$, $\omega=1/2$, exact inversion gives

$$
|S|^2=\frac1{389}
\begin{pmatrix}65&4&320\\260&65&64\\64&320&5\end{pmatrix},\quad
B=\frac{4n_A+320n_c}{389},\quad
e=\frac{260}{389+2(65n_A+64n_c)}.
$$

For illustrative, unmeasured occupations $n_A=10$, $n_c=1/100$, these
are $B=216/1945$ and $e=6500/42257$. The reverse/forward power ratio is
$1/65$, consistent with
$|S_{12}|^2/|S_{21}|^2=\omega^2/(\kappa'^2+\omega^2)$ in this model.
These finite-frequency e,B are external-port metrics; when attached
to a cavity with $S_{11}\ne0$, (G1) must first update its response and
the correlations of its readout noise. Matching over a wider band
requires greater auxiliary coupling. The transparent ledger
$|h_{12}|^2+2g^2=\kappa^2/4+\kappa\kappa'/2$ is a squared-coupling
budget, **not calibrated pump watts**. Per-tone calibration, heating,
depletion, stability and pump reuse remain device constraints. This
construction is a concrete ordinary benchmark, not a proof of a global
finite-band, finite-pump optimum.

**A controlled-order router defeated by the same two ordinary pulses.**
In a favorable ideal limit, let A swap traveling modes q,d and B swap
d,c, with mode order (q,d,c). The source pointer enters q; detector
thermal backflow enters d and the cold dump input enters c. Then

$$
BA=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix},\qquad
AB=\begin{pmatrix}0&0&1\\1&0&0\\0&1&0\end{pmatrix}.
$$

Use their number-preserving second quantizations on the full Fock
space, not their one-photon matrices alone. Grant an ideal independent
helper controlling these orders, initially +, including the required
coherence of bath and timing records. The ordinary fixed order AB is
a matched circulator: it sends the source intact to d, hot detector
noise to c and the cold input to q. BA instead sends hot noise to q
and the source to the dump. Both have zero q-to-q reflection and use
the same one A and one B pulse. Tracing the helper gives

$$
B_{\rm switch}=\frac{n_A+n_c}{2},\qquad B_{\rm ordinary}=n_c.
\tag{G4}
$$

For the specified continuous, known-quadrature weak coherent pointer,
any joint helper/detector measurement after the switch is
parameter-independent processing of that pointer and independent
thermal ancillas. Its Fisher information is bounded by the incoming
pointer's quantum Fisher information. Ideal aligned homodyne after
AB attains that information. Thus a better helper measurement cannot
rescue this router's forward-information comparison. This metric is
essential: aligned homodyne does not generally attain the binary
coherent-state Helstrom optimum. Nor is this a converse for arbitrary
active or noisy order-dependent devices.

The helper nevertheless has a real order-sensitive thermal statistic.
At zero source signal put
$\rho=|0\rangle\langle0|_q\otimes\tau(n_A)_d\otimes\tau(n_c)_c$.
The helper's off-diagonal overlap is the trace of a three-cycle against
this product. A diagonal thermal term contributes only when all three
occupations are equal; the source vacuum forces them all to zero.
Hence $h=\langle X_O\rangle=[(1+n_A)(1+n_c)]^{-1}$ and
$p_\pm=(1\pm h)/2$. Inserting the protected number operator into
the same interference trace gives zero. Its conditional occupations
therefore satisfy

$$
B_\pm=\frac{n_A+n_c}{2(1\pm h)},\qquad
p_+B_++p_-B_-=\frac{n_A+n_c}{2}.
\tag{G5}
$$

This is a full-Fock thermal generating-function argument without a
cutoff. For $n_A=10$, $n_c=1/100$,
$h=100/1111$, $p_+=1211/2222$ and
$B_+=158873/34600\simeq4.592$. Even the selected plus output is
worse than the ordinary $1/100$; the unconditional switch gives
$1001/200=5.005$. The statistic measures thermal/order information,
not a protection gain. No experimental qubit-controlled global order
router is claimed by this ideal component calculation.

**Terminal helper measurements and the open task.** For arbitrary
physical Stinespring histories $U_0,U_1$, including all reservoirs and
the cavity, tracing a controlled-order helper leaves exactly
$pU_0\rho U_0^\dagger+(1-p)U_1\rho U_1^\dagger$. Ordinary randomized
histories reproduce this complete reduced process, with the same mean
waveform and primitive-resource ledger, when those histories are
available under the same interface. Keeping the ordinary branch record
can add information. Summing any complete terminal helper measurement
also leaves this mixture, so it cannot change the unconditional noise
energy already delivered to a qubit. Selecting a quiet subensemble
does not remove rejected trials' earlier exposure. Joint helper
readout, a conditional quantum output, early noise routing, or active
outcome-dependent qubit recovery are not excluded; they need a full
instrument and ordinary controlled-Gaussian/reservoir-monitoring
comparators with the same latency and costs.

The
[exact readout guards](checks/architecture/gaussian_readout_guards.py)
check a nonnormal two-mode return, the noise/damping and finite-cavity
inequalities, the finite three-mode reservoir scattering, and (G4)–(G5)
at rational occupations. General matrix/Fock and information arguments
are analytic. Finite-band, finite-pump active conditional readout remains
open; calibration, pump depletion and effective cavity loading cannot
be omitted from that comparison.

<a id="nr-r06-conditional-microwave-readout"></a>

### Conditional microwave readout needs the full signal–idler instrument

The [readout noise-floor comparison](#nr-r06-readout-noise-floor) concerns
the noise delivered to a cavity and its actual response. A complementary
task is to improve a retained conditional readout or quantum output.
Here the relevant object includes the measurement likelihood, qubit
coherence and every helper flag. A small selected output variance does
not alone establish a useful error–time–disturbance improvement.

**Measured controls and their limits.**
[Liu et al., Physical Review Applied **18**, 064092 (2022), including
the supplement](https://arxiv.org/pdf/2007.15460), measure a transmon
with a two-JPC SU(1,1) interferometer. They report 31% improvement in
power SNR at fixed coherent cavity drive. Fitted weak-readout efficiencies
at matched SNR are 0.58 and 0.29 at two pump settings, versus 0.46 for
coherent readout (0.52 after a $T_2$ correction); the variation lacks a
detailed theory. Analyzer pump-power variation from entangler leakage
reaches $\pm50\%$ without cancellation; active pump-copy cancellation
leaves residual leakage amplitude about 0.01. Inferred arm loss assumes a
quantum-limited analyzer. Both signal and idler connect the two JPCs;
the coherent drive enters a separate weak cavity port.
The retained correlated idler enables ordinary destructive noise
interference. These facts identify loss, pump crossfeed and backaction
as bottlenecks; the measured power-SNR change is not a fidelity change.

[Rosenthal et al., Physical Review Letters **126**, 090503
(2021)](https://doi.org/10.1103/PhysRevLett.126.090503),
[full primary text](https://arxiv.org/html/2008.03805), demonstrate SIMBA:
a dc-switched parametric cavity receives a readout pulse in 20 ns,
disconnects the qubit, latches by nonunitary bistable amplification,
then connects the output chain. Simultaneous reported metrics are
efficiency $70.4\pm0.9\%$, measurement time 265 ns and excess backaction
$0.66\pm0.01$ effective photons. Its fitted $F_0=95.5\pm0.3\%$ is
contrast $1-P(e|0)-P(g|\pi)$, not average assignment accuracy. A switch
tested in isolation exceeds 50 dB on/off; operating reflect-state
transmission is about $-26$ dB. This provides an ordinary readout
comparator with time-gated isolation, not a state-preserving quantum
transmission channel or a demonstrated qubit-coherent order controller.

[Descamps et al., arXiv:2602.16889
(2026)](https://arxiv.org/html/2602.16889), demonstrate an on-chip
attenuator for gain/noise calibration over 4–8 GHz. About 1 nW produces a
257 mK equivalent thermal field; the authors argue this avoids
undesirable baseplate heating. Fitted heating/cooling time constants
are 0.25/1.57 ms, and unintentional local heating is observed without
applied drive. These are calibration and settling costs, not a measured
parametric-amplifier drift spectrum or total calibration time. No source
here justifies independent unknown squeeze parameters on every trial.

The following equations are an independent specified-dilation baseline;
they do not fit the unexplained measured efficiency variation. In
particular, retaining a correlated idler is a different physical
instrument from cascading two reduced single-mode amplifier channels
with fresh traced idlers. A proposed coherent-order implementation must
declare which of these ports it routes.

**A complete ordinary SU(1,1) dilation.** The following specified model
retains the correlated idler and every loss output. It is an analytic
baseline, rather than a fit to a measured efficiency. Let the independent
incident modes be $a,b,f_{\rm pre},f_{\rm post},g$, with centered thermal
occupations $n_a,n_b,n_{\rm pre},n_{\rm post},n_g$ and coherent means
$\alpha,\beta,0,0,0$. Keep a purification of each thermal input when
computing qubit coherence. The entangler acts as

$$
a_1=u_1a+v_1b^\dagger,\qquad
b_1=u_1b+v_1a^\dagger,\qquad
u_j=\cosh r_j,\quad v_j=e^{i\phi_j}\sinh r_j.
\tag{CM1}
$$

The convention is $a_{\rm out}=U^\dagger a_{\rm in}U$, with the
standard continuous-to-identity squeezer
$U_j=\exp[r_j(e^{i\phi_j}a^\dagger b^\dagger
-e^{-i\phi_j}ab)]$ and beam splitters
$\exp[\vartheta(a^\dagger f-af^\dagger)]$.
The phase-only cavity block is explicitly
$U_z=\exp(i\theta_zN_c)$ for qubit state $z\in\{g,e\}$, with no
extra $z$-dependent scalar. Common qubit-independent global phases are
fixed identically. Additional controlled scalar phases of an apparatus
are calibration inputs. Undepleted pumps are declared classical coherent
controls; this approximation does not supply a finite quantum-pump
dilation or free coherent qubit control of a pump.

Let $p,q,\eta$ be the pre-cavity, post-cavity and idler power
transmissions, and $\theta_i$ the idler phase. Put
$c=\sqrt p\,a_1+\sqrt{1-p}\,f_{\rm pre}$,
$a_2=\sqrt q\,e^{i\theta_z}c+\sqrt{1-q}\,f_{\rm post}$ and
$b_2=\sqrt\eta\,e^{i\theta_i}b_1+\sqrt{1-\eta}\,g$.
After the analyzer the **five complete output rows** are

$$
\begin{aligned}
a_{\rm out}&=u_2a_2+v_2b_2^\dagger
 =A_za+B_zb^\dagger
   +L_{{\rm pre},z}f_{\rm pre}+L_{\rm post}f_{\rm post}+Mg^\dagger,\\
b_{\rm out}&=u_2b_2+v_2a_2^\dagger
 =C_zb+D_za^\dagger
   +\widetilde L_{{\rm pre},z}f_{\rm pre}^\dagger
   +\widetilde L_{\rm post}f_{\rm post}^\dagger+\widetilde M g,\\
\ell_{\rm pre}&=-\sqrt{1-p}\,a_1+\sqrt p\,f_{\rm pre},\\
\ell_{\rm post}&=-\sqrt{1-q}\,e^{i\theta_z}
 (\sqrt p\,a_1+\sqrt{1-p}\,f_{\rm pre})
                       +\sqrt q\,f_{\rm post},\\
\ell_i&=-\sqrt{1-\eta}\,e^{i\theta_i}b_1+\sqrt\eta\,g,
\end{aligned}
\tag{CM2}
$$

where direct expansion gives

$$
\begin{aligned}
A_z&=u_2\sqrt{pq}\,e^{i\theta_z}u_1
                    +v_2\sqrt\eta\,e^{-i\theta_i}v_1^*,\\
B_z&=u_2\sqrt{pq}\,e^{i\theta_z}v_1
                    +v_2\sqrt\eta\,e^{-i\theta_i}u_1,\\
C_z&=u_2\sqrt\eta\,e^{i\theta_i}u_1
                    +v_2\sqrt{pq}\,e^{-i\theta_z}v_1^*,\\
D_z&=u_2\sqrt\eta\,e^{i\theta_i}v_1
                    +v_2\sqrt{pq}\,e^{-i\theta_z}u_1,\\
L_{{\rm pre},z}&=u_2\sqrt{q(1-p)}\,e^{i\theta_z},\qquad
L_{\rm post}=u_2\sqrt{1-q},\qquad M=v_2\sqrt{1-\eta},\\
\widetilde L_{{\rm pre},z}&=v_2\sqrt{q(1-p)}\,e^{-i\theta_z},\qquad
\widetilde L_{\rm post}=v_2\sqrt{1-q},\qquad
\widetilde M=u_2\sqrt{1-\eta}.
\end{aligned}
$$

The cavity lies between the two upper losses. Moving one loss across
that interaction changes qubit backaction even if the measured total
transmission is unchanged. An actual dissipative cavity replaces the
phase-only block by its full measured conditional scattering matrix,
including internal loss ports. An independent weak-port cavity drive
requires its additional input/output column; the displayed source means
do not identify every experimental drive port.

**Canonical commutators and independent baths.** Write all five rows
as $\boldsymbol a_{\rm out}=X_z\boldsymbol a_{\rm in}
+Y_z\boldsymbol a_{\rm in}^\dagger$. Each beam splitter is unitary
and each squeezer has $u_j^2-|v_j|^2=1$. Composition therefore gives

$$
X_zX_z^\dagger-Y_zY_z^\dagger=I,\qquad
X_zY_z^{\mathsf T}-Y_zX_z^{\mathsf T}=0,
\qquad
|A_z|^2-|B_z|^2+|L_{{\rm pre},z}|^2
                  +|L_{\rm post}|^2-|M|^2=1.
\tag{CM3}
$$

For a direct first-row proof,
$|A_z|^2-|B_z|^2=u_2^2pq-|v_2|^2\eta$;
the remaining two annihilation coefficients contribute
$u_2^2[q(1-p)+(1-q)]=u_2^2(1-pq)$, and the last creation
coefficient contributes $-|v_2|^2(1-\eta)$. Their sum is one.
Replacing the independent upper baths by
$(L_{{\rm pre},z}+L_{\rm post})f$ adds the spurious commutator term
$2u_2^2\sqrt{q(1-p)(1-q)}\cos\theta_z$.
A normalized effective bath can represent one fixed-$z$ output
marginal, but its $z$-dependent definition cannot identify the same
environment in two initially coherent qubit branches. Keep the
orthogonal bath mode and shared physical input labels in that comparison.

**Warm moments and ordinary homodyne.** The entangler's signal marginal
and inter-arm correlation are
$\mu_1=u_1\alpha+v_1\beta^*$,
$n_1=u_1^2n_a+|v_1|^2(n_b+1)$ and
$M_1=\langle\delta a_1\delta b_1\rangle
=u_1v_1(n_a+n_b+1)$. Thus a warm idler changes both the signal
noise and its accessible correlation. For the independent inputs above,

$$
\begin{aligned}
\mu_{{\rm out},z}&=A_z\alpha+B_z\beta^*,\\
n_{{\rm out},z}&=|A_z|^2n_a+|B_z|^2(n_b+1)
 +|L_{{\rm pre},z}|^2n_{\rm pre}
 +|L_{\rm post}|^2n_{\rm post}+|M|^2(n_g+1),\\
\langle\delta a_{\rm out}\delta a_{\rm out}\rangle&=0.
\end{aligned}
\tag{CM4}
$$

Consequently $X_\vartheta=(e^{-i\vartheta}a_{\rm out}
+e^{i\vartheta}a_{\rm out}^\dagger)/\sqrt2$ has a Gaussian
distribution with mean
$\sqrt2\operatorname{Re}(e^{-i\vartheta}\mu_{{\rm out},z})$ and
variance $n_{{\rm out},z}+1/2$. Detector transmission $d$ with an
independent thermal input of occupation $n_d$ multiplies the mean by
$\sqrt d$ and gives variance
$d(n_{{\rm out},z}+1/2)+(1-d)(n_d+1/2)$.
Additional receiver noise uses its actual measured covariance.
The general full-mode rule is $V_{\rm out}=S_zV_{\rm in}S_z^{\mathsf T}$,
with the full source, loss and purification modes included. Correlated
baths, phase-sensitive inputs or reverse-propagating noise require that
larger model instead of (CM4)'s independent-input specialization.

Let the centered pre-analyzer arms have occupations $N_s,N_i$ and
$M_{si}=\langle\delta a_2\delta b_2\rangle$, with other anomalous
moments zero. Here
$N_s=pqn_1+q(1-p)n_{\rm pre}+(1-q)n_{\rm post}$,
$N_i=\eta[u_1^2n_b+|v_1|^2(n_a+1)]+(1-\eta)n_g$, and
$M_{si}=\sqrt{pq\eta}\,e^{i(\theta_z+\theta_i)}M_1$.
The ordinary analyzer has

$$
\begin{aligned}
V(r,\phi)&=\cosh^2r\,N_s+\sinh^2r\,(N_i+1)
 +2\cosh r\sinh r\operatorname{Re}(e^{-i\phi}M_{si})+\tfrac12,\\
\tanh(2r_*)&=\frac{2|M_{si}|}{N_s+N_i+1},\qquad
V_{\min}=\frac{\sqrt{(N_s+N_i+1)^2-4|M_{si}|^2}+N_s-N_i}{2}.
\end{aligned}
\tag{CM5}
$$

To obtain the minimum, set $\phi=\arg M_{si}+\pi$, express the
variance in $\cosh2r,\sinh2r$ and differentiate. Physical covariance
positivity gives a real square root; limiting cases are continuous.
This is a **noise** optimum. The unknown qubit requires one common
analyzer setting; it cannot choose the phase after learning $z$.
Means, covariance contrast, detector noise and pump costs change with
gain, so optimize the full stated readout likelihood rather than this
variance alone. The same analyzer obeys the operator identity

$$
X_{{\rm out},\vartheta}
 =\cosh r\,X_{a_2,\vartheta}
              +\sinh r\,X_{b_2,\phi-\vartheta}.
\tag{CM6}
$$

Its two arm quadratures commute, so ideal joint homodynes and electronic weighting
reproduce the entire scalar distribution. Finite detector noise can
favor physical pre-detection gain, with its actual ports and resources.
For a common covariance in a local linear-response model, the best
electronic linear discriminant is proportional to
$\Sigma^{-1}\Delta\mu$; qubit-dependent covariance requires the full
likelihood.

As a consistency check, vacuum inputs, lossless arms and inverse pumps
$u_2=u_1$, $v_2=-v_1$, $\theta_i=0$ give
$n_{{\rm out},z}=4n(n+1)\sin^2(\theta_z/2)$ for $n=|v_1|^2$.
With equal arm power transmissions $pq=\eta=\tau$ and vacuum loss
inputs this becomes
$n(1-\tau)+4\tau n(n+1)\sin^2(\theta_z/2)$.

**Total backaction and the lost columns.** Let $|\Psi_z\rangle$ be
the complete conditional output, including every source/bath
purification. Its unobserved qubit coherence multiplier is
$\Gamma=\langle\Psi_e|\Psi_g\rangle$.
For $\delta=\theta_g-\theta_e$, the cavity's incident marginal is a
displaced thermal state with
$n_c=pn_1+(1-p)n_{\rm pre}$ and $\mu_c=\sqrt p\,\mu_1$. Exactly,

$$
\Gamma=\operatorname{Tr}(\rho_c e^{i\delta N_c})
 =\frac{\displaystyle
 \exp\!\left[-\frac{|\mu_c|^2(1-e^{i\delta})}
                         {1+n_c(1-e^{i\delta})}\right]}
       {1+n_c(1-e^{i\delta})}.
\tag{CM7}
$$

For a proof, use the positive Gaussian coherent-state representation
of a displaced thermal state and
$\langle\gamma|e^{i\delta N}|\gamma\rangle
=\exp[-|\gamma|^2(1-e^{i\delta})]$.
Completing the complex Gaussian integral gives (CM7), with the
$n_c=0$ coherent-state limit understood continuously. It retains a
warm idler through $n_1$ and a warm pre-loss input through $n_c$.
Every later qubit-independent trace-preserving operation, including
the post-loss and analyzer, leaves the nonselective qubit state
unchanged. It can redistribute accessible information or amplify it
before a noisy receiver. A real network with back-propagation or
feedback needs the enlarged causal dilation; the one-way premise
cannot be assumed there.

For a passive cavity with vacuum loss inputs, let $h_z$ be its complete
signal-input output column, including all loss ports. For an incident
displaced thermal signal of parameters $n,\mu$, define

$$
\begin{aligned}
\kappa&=h_e^\dagger h_g,
\qquad
\Gamma=\frac{\displaystyle
 \exp\!\left[-\frac{|\mu|^2(1-\kappa)}{1+n(1-\kappa)}\right]}
 {1+n(1-\kappa)},\\
h_z\big|_{\{a_2,\ell_{\rm pre},\ell_{\rm post}\}}
 &=\left(\sqrt{pq}\,e^{i\theta_z},
          -\sqrt{1-p},
          -\sqrt{p(1-q)}\,e^{i\theta_z}\right)^{\mathsf T},\\
\kappa\text{ for (CM2)}&=(1-p)+pe^{i\delta}.
\end{aligned}
\tag{CM8}
$$

For a coherent incident amplitude $\gamma$, the complete outgoing
coherent vectors have overlap
$\exp[-|\gamma|^2(1-\kappa)]$. Its Gaussian thermal average proves
the first line. The last two lines follow by reading the signal-input
coefficients in (CM2); post-loss information in
$\ell_{\rm post}$ is essential. They agree with (CM7) for vacuum
pre-loss input. Transmissions alone do not determine $\kappa$:
the lost-port phases are required. Non-vacuum cavity loss inputs require
the full joint Gaussian purification instead of this column reduction.

**The complete qubit measurement kernel.** Let $x$ be the observed
homodyne record and $u$ all unobserved output and purifying coordinates.
Put $\Psi_z(x,u)=\langle x,u|\Psi_z\rangle$. The instrument density is

$$
\begin{aligned}
\mathcal J_x(\rho_Q)
 &=\begin{pmatrix}
 p_g(x)\rho_{gg}&k(x)\rho_{ge}\\
 k(x)^*\rho_{eg}&p_e(x)\rho_{ee}
 \end{pmatrix},\\
p_z(x)&=\int du\,|\Psi_z(x,u)|^2,\qquad
k(x)=\int du\,\Psi_g(x,u)\Psi_e(x,u)^*,\\
\int k(x)dx&=\Gamma,\qquad
|k(x)|\le\sqrt{p_g(x)p_e(x)},\qquad
|\Gamma|\le\int dx\sqrt{p_g(x)p_e(x)}.
\end{aligned}
\tag{CM9}
$$

The inequalities are Cauchy--Schwarz followed by the triangle inequality.
Unobserved idler/loss outputs, thermal purifications and detector-noise
dilations all belong to $u$. Record-dependent feedback can use the
phase of $k(x)$, while an inaccessible record cannot be corrected away.
This distinguishes better accessible readout from reduced total
backaction, without inferring qubit coherence from an output variance.

For a pure Gaussian branch write
$\Psi_z(q)=C_z\exp[-q^{\mathsf T}A_zq/2+b_z^{\mathsf T}q]$,
$q=(x,u)$, with $A_z$ symmetric and $\operatorname{Re}A_z>0$.
Partition $A_z,b_z$ into observed and unobserved blocks, and set

$$
\begin{aligned}
M_{ge}&=A_{g,uu}+A_{e,uu}^*,\\
j_{ge}(x)&=b_{g,u}+b_{e,u}^*
                    -(A_{g,ux}+A_{e,ux}^*)x,\\
k(x)&=\frac{C_gC_e^*(2\pi)^{\dim(u)/2}}{\sqrt{\det M_{ge}}}
 \exp\!\left[
 -\tfrac12x^{\mathsf T}(A_{g,xx}+A_{e,xx}^*)x
 +(b_{g,x}+b_{e,x}^*)^{\mathsf T}x
 +\tfrac12j_{ge}(x)^{\mathsf T}M_{ge}^{-1}j_{ge}(x)\right].
\end{aligned}
\tag{CM10}
$$

Multiplying the two wavefunctions isolates
$-u^{\mathsf T}M_{ge}u/2+j_{ge}^{\mathsf T}u$.
Completing its square and integrating gives the determinant factor
and final quadratic term in (CM10). Positive real part fixes the
convergent complex-Gaussian integral; choose the determinant branch
continuously from positive real matrices. Setting $g=e$ gives $p_z(x)$.
The complete symplectic matrix, mean and source purification determine
$A_z,b_z,|C_z|$, but do **not** determine the physical relative phase
of $C_z$. The declared conditional Hamiltonians/unitaries and their
vacuum extension fix that phase, including the metaplectic phase.
A coherent-amplitude scattering matrix alone therefore cannot fix a
controlled-history interference term. Finite-bandwidth models replace
these matrices by the actual temporal kernels, with a controlled mode
truncation or error bound when a finite replay is used.

**What an independent quantum helper adds.** Suppose a physically
specified qubit $H$ controls histories $r=0,1$, each a complete Gaussian
dilation with branch wavefunction $\Psi_{z,r}$. For $H$ initially plus,
an $X$ flag $\epsilon$ with declared helper phase $\phi_H$ gives

$$
\begin{aligned}
\Psi_{z,\epsilon}
 &=\frac{\Psi_{z,0}+\epsilon e^{i\phi_H}\Psi_{z,1}}2,\\
k_\epsilon(x)
 &=\frac14\sum_{r,s=0}^1
 \epsilon^{r+s}e^{i(r-s)\phi_H}
 \int du\,\Psi_{g,r}(x,u)\Psi_{e,s}(x,u)^*.
\end{aligned}
\tag{CM11}
$$

The diagonal densities have the analogous four terms. Each integral
is (CM10) with its corresponding pair of branch matrices and physical
phases. Covariance averaging drops the cross-history operator
interference; discarding idler/loss labels overestimates it. The flag
can create a non-Gaussian state, but the independent coherent helper,
its couplings and its complete outcome instrument are additional
physical resources.

A fixed Gaussian network with Gaussian ancillas maps Gaussian inputs
to Gaussian outputs. Exact Gaussian-measurement outcomes have Gaussian
conditional states. Grouping or classically postselecting records can
produce non-Gaussian mixtures, but supplies neither these coherent
cross-history terms nor Wigner negativity from positive-Wigner Gaussian
resources and Gaussian measurements. In particular a beam splitter
takes a coherent probe to a product of coherent amplitudes. Splitting
a nonclassical Gaussian probe may correlate arms but still supplies
one global Gaussian network, rather than an independent qubit selecting
operator order. Classical pump programmability also does not establish
a coherent qubit-controlled pump. The ordinary comparator must retain
its accessible idler correlations and any physically available qubit
controls with their actual source, detector, loss and timing costs.

**An ordinary conditional-noise likelihood.** The same experiment's
no-displacement readout uses different qubit-dependent noise widths
despite equal mean voltages. For the ideal circular Gaussian comparator,
let $y=I+iQ$, $p_z(y)=e^{-|y|^2/N_z}/(\pi N_z)$, equal priors and
$N_e>N_g$. The complete-record likelihood chooses $e$ when

$$
|y|^2>R_*^2=\frac{N_gN_e\log(N_e/N_g)}{N_e-N_g},\qquad
P_{\rm err}=\frac12\left[e^{-R_*^2/N_g}+1-e^{-R_*^2/N_e}\right].
\tag{CM12}
$$

Compare log densities to obtain the threshold; integrating in polar
coordinates gives $P_z(|y|^2>R^2)=e^{-R^2/N_z}$ and proves the error.
For $N_e=2N_g$, the optimum error is $3/8$ even though mean-separation
SNR is zero. An ordinary classical confidence flag accepting
$|y|^2>2N_g\log m$, $m>1$, has the complete accepted probabilities
$P(g,\mathrm{keep})=m^{-2}/2$ and
$P(e,\mathrm{keep})=m^{-1}/2$, with their complementary rejected
probabilities. Consequently

$$
p_{\rm keep}=\frac{m^{-1}+m^{-2}}2,\qquad
P(e\mid\mathrm{keep})=\frac{m}{m+1}.
\tag{CM13}
$$

Conditional confidence can approach one while yield vanishes without an
order helper. This ideal statistical example is consistent with ordinary
bullseye conditioning; it does not fit non-Gaussian tails, state errors,
finite bandwidth or the measured efficiency variation. Actual priors and
the complete time-voltage likelihood determine the experimental
comparator. The [full-record information and support
guards](obstructions.md#nr-r04-gaussian-displacement) apply to a
parameter-independent receiver after a fixed signal interaction. A
different order that changes the incident cavity probe requires a new
matched-exposure comparison rather than that downstream argument.

**Known squeezing/displacement preparation has an exact ordinary
compiler.** The primary
[Gaussian-order state-preparation proposal](https://arxiv.org/pdf/2108.13074)
and [Gaussian-probe metrology comparison](https://arxiv.org/pdf/2608.25870)
motivate conditional non-Gaussian outputs. For a known squeeze, fix
$S aS^\dagger=a\cosh r+e^{i\phi}a^\dagger\sinh r$ and define
$\beta=\alpha\cosh r-\alpha^*e^{i\phi}\sinh r$.
Conjugating the exponent of $D(\alpha)$ proves

$$
SD(\alpha)=D(\beta)S,\qquad
P_0\otimes SD(\alpha)+P_1\otimes D(\alpha)S
=[P_0\otimes D(\beta)+P_1\otimes D(\alpha)](I\otimes S).
\tag{CM14}
$$

Put $\mu=(\alpha+\beta)/2$, $d=(\alpha-\beta)/2$ and
$\vartheta=\operatorname{Im}(\mu d^*)$. The bracket is exactly

$$
\bigl(e^{i\vartheta}P_0+e^{-i\vartheta}P_1\bigr)\otimes I\;
(I\otimes D(\mu))
\bigl[P_0\otimes D(-d)+P_1\otimes D(d)\bigr].
\tag{CM15}
$$

Indeed the Weyl multiplication phases in $D(\mu)D(\mp d)$ are
$\mp\vartheta$, canceled by the displayed helper phase. One ordinary
known squeeze, one unconditional displacement and one sign-controlled
displacement therefore reproduce the complete controlled-order unitary
on arbitrary input and reference, before the same helper measurement.
Every helper-flagged conditional output is identical, including its
non-Gaussianity. The amplitude identity
$|\mu|^2+|d|^2=(|\alpha|^2+|\beta|^2)/2$ follows by expansion; it is not
the total energy or duration of a realistic pulse sequence.

[Eickbusch et al., Nature Physics **18**, 1464–1469
(2022)](https://doi.org/10.1038/s41567-022-01776-9),
[primary full paper](https://arxiv.org/pdf/2111.06414), demonstrate
ordinary echoed conditional-displacement control of a superconducting
oscillator. Strong temporary displacement enhances weak dispersive
coupling, with real pulse, peak-excitation, ancilla-noise and enhanced
dephasing costs. Their ECD primitive also flips the qubit; a known
qubit $X$ converts it to the diagonal sign-controlled form, at its own
control cost. This does not demonstrate (CM15) on a propagating
readout field; capture/release or coherent whole-mode routing is a
separate interface. If $r$ or $\alpha$ is an unknown sensed encoding,
the compiler cannot set $\beta$ from that unknown value: controls must
be held fixed under parameter derivatives. The identity is a known
probe-preparation baseline, not a general sensing no-go.

**Bounded device test and check scope.** Compare either assignment error
at fixed measurement time and permitted qubit disturbance, or
transmission fidelity at fixed latency. A latching detector is admitted
for the first task, not the second. Calibrate the complete causal
signal/idler/loss matrices, bath correlations, pump leakage and drift
over the repeat window. Compute both $p_z(\mathrm{record})$ and
$k(\mathrm{record})$, including every helper flag and rejected record.
A classical selectable pump matrix is not coherent control of its full
Gaussian dilation. A clean qubit selector or nonlinear predicate is an
extra resource. Compare its
ordinary conditional-displacement, parity, reservoir-monitoring or QEC
uses only where the same interface supplies them, and charge preparation,
capture/release, pump work, compression, storage, reset and all failures.
The measured devices supply strong ordinary controls, but no complete
cost separation for native coherent order has been established here.

The [five-mode exact replay](checks/architecture/verify_su11_ports.py)
checks canonical commutators, explicit Bogoliubov coefficients, warm
moments, independent-bath failure and downstream relative-network
cancellation. The [conditional
replay](checks/architecture/verify_conditional_readout.py) checks Weyl
phases, symplectic displacement products, amplitude identities,
accepted/rejected likelihoods and the (BOS6) isotropic variance law.
The Gaussian integrals, all-Fock operator identities, full physical
relative phases, continuous temporal bandwidth and measured costs remain
analytic or experimental inputs; finite replay is not their device
validation.

<a id="nr-r06-anisotropic-gkp"></a>

### Anisotropy defeats that compiler, but not an ideal logical comparator

The independent-random-displacement construction has a genuine limit.
Use complex displacement coordinates and independent centered Gaussian
vectors $\alpha,\beta$ with real covariances $aI$ and
$\operatorname{diag}(b_x,b_y)$, where $a>0$. Put
$\gamma=\alpha+\beta=(x,y)$, $v_j=a+b_j$ and $w_j=ab_j/v_j$.
Conditional Gaussian regression gives
$\mathbb E[\alpha_j\mid\gamma]=a\gamma_j/v_j$ and conditional
covariance $\operatorname{diag}(w_x,w_y)$. The switched order phase
$\chi=\operatorname{Im}(\beta\alpha^*)=y\alpha_x-x\alpha_y$ therefore has

$$
\mu(\gamma)=axy(v_x^{-1}-v_y^{-1}),\qquad
\operatorname{Var}(\chi\mid\gamma)=y^2w_x+x^2w_y,
$$

and its off-diagonal control multiplier is

$$
f(\gamma)=\mathbb E[e^{2i\chi}\mid\gamma]
=\exp\!\left[2iaxy(v_x^{-1}-v_y^{-1})-2(y^2w_x+x^2w_y)\right].
\tag{AG1}
$$

For $b_x\ne b_y$, this is even and generically complex. In contrast any
independent classical displacement sample $z$ in the preceding pre/post
compiler gives $g(\gamma)=\mathbb E e^{2i\operatorname{Im}(\gamma z^*)}$,
which necessarily satisfies $g(-\gamma)=g(\gamma)^*$. These kernels
cannot agree. This excludes equality of the full channels, not just one
chosen input: the adjoint of
$\int p(\gamma)f(\gamma)\operatorname{Ad}_{D(\gamma)}\,d^2\gamma$
on Weyl operators gives the Fourier transform of the integrable function
$pf$. Fourier injectivity, with strictly positive Gaussian $p$, would
force $f=g$ almost everywhere, hence everywhere by continuity. This is an
obstruction to that compiler class only; it is not an ordinary-protocol
converse or a logical-memory advantage.

**Deterministic fidelity in the ideal GKP Pauli-and-syndrome model.**
Use quadratures $[q,p]=i$, lattice length $\ell=\sqrt\pi$, translations
$X(x)=e^{-ixp}$, $Z(y)=e^{iyq}$ and logical normalizers
$X_L=X(\ell)$, $Z_L=Z(\ell)$. Here
$D(x,y)=e^{i(yq-xp)}$ uses real quadrature shifts, a fixed $\sqrt2$
rescaling of the preceding complex-amplitude coordinates.
Assume perfect modular syndrome access:
$u=x\bmod\ell$, $v=y\bmod\ell$ in the centered cell. Write
$x=u+k\ell$, $y=v+l\ell$. In this ideal model, correcting the analog
syndrome leaves logical Pauli $X_L^kZ_L^l$ up to global phase, and the
syndrome distribution is independent of the stored logical input.
The statement below is an exact channel statement in that logical model;
it does not regard infinite-energy GKP combs as physical states.

Suppose the centered net shift has diagonal Gaussian covariance in the
chosen lattice axes. Conditioned on $(u,v)$, the logical parity priors
factor as $p_{kl}=A_k(u)B_l(v)$, $k,l\in\{0,1\}$, where for example

$$
A_e(u)=\frac{\sum_{j\equiv e\ (\mathrm{mod}\ 2)}
 e^{-(u+j\ell)^2/(2\sigma_q^2)}}
 {\sum_{j\in\mathbb Z}e^{-(u+j\ell)^2/(2\sigma_q^2)}}.
\tag{AG2}
$$

Here $A_0\ge A_1$ throughout the centered cell, and similarly
$B_0\ge B_1$. To see this, their difference numerator is
$\sum_j(-1)^j e^{-(u+j\ell)^2/(2\sigma_q^2)}$. Including the positive
Gaussian normalization, the image construction identifies this with the
Dirichlet heat kernel from zero on $(-\ell/2,\ell/2)$: it solves the
heat equation, vanishes at both endpoints by pairing reflected terms,
and has initial positive point mass. Positivity follows from the maximum
principle, first for positive smooth initial approximations and then by
their kernel limit. Boundary values follow by continuity. Thus $p_{00}$
is largest and $p_{11}$ smallest; the two largest probabilities sum to

$$
R(u,v)=p_{00}+\max\{p_{10},p_{01}\}.
\tag{AG3}
$$

For the bare standard switch of the two noise maps, with independent
initial plus control and no prior encoding of the logical input into
that control, retain the syndrome. Its conditional logical channel has
the form

$$
\rho\longmapsto\sum_e p_e\,\omega_e^C\otimes P_e\rho P_e,
\tag{AG4}
$$

where $\omega_e$ are arbitrary states of one control qubit. Their actual
anisotropic order-phase kernel will not be needed. The best logical
entanglement fidelity after any joint control/logical recovery equals
the optimum guessing probability for the ensemble $\{p_e,\omega_e\}$.
Indeed expand each recovery Kraus as
$K_r=\sum_e\langle v_{re}|_C\otimes P_e$. Pauli trace orthogonality
in the Bell-fidelity formula gives
$\sum_e p_e\operatorname{Tr}(M_e\omega_e)$, where
$M_e=\sum_r|v_{re}\rangle\langle v_{re}|\ge0$.
Taking the identity-Pauli component of trace preservation gives
$\sum_eM_e=I_C$. Conversely any such POVM followed by the guessed Pauli
correction realizes this value. Since $\dim C=2$,

$$
\sum_e p_e\operatorname{Tr}(M_e\omega_e)
\le\sum_e p_e\min\{1,\operatorname{Tr}M_e\}
\le p_{\rm largest}+p_{\rm second\ largest}=R(u,v).
\tag{AG5}
$$

The last inequality allocates total weight at most two, with weight at
most one per label, to the ordered probabilities.

An ordinary end-only check attains (AG5). Take the known displacement
$Q=D(\ell,\ell)$, representing logical $Y$ up to phase. Apply
controlled-$Q$ before both serial noise calls and its inverse afterwards.
Weyl conjugation transfers phase $e^{i\ell(y-x)}$ to the helper.
After receiving the final syndrome, remove its known phase
$\ell(v-u)$. The remaining phase is $(-1)^{l-k}=(-1)^{k+l}$;
an $X$ measurement reads total logical parity. On even parity choose
error $00$; on odd parity choose the more likely of $10,01$ using the
analog record. Its fidelity is exactly (AG3), pointwise in the syndrome.
Averaging proves dominance over the specified switch's maximum
**unconditional logical entanglement fidelity**. No intermediate
noise-stage measurement or rejected branch is used. In particular this
applies to the diagonal net covariance in (AG1), even though its simple
full-channel compiler fails.

**The restrictions cannot be dropped.** This is not full raw-instrument
equality and does not dominate every heralded fidelity/yield frontier.
For example, independent fair logical $I/X$ and $I/Z$ channels give a
minus-switch branch that uniquely identifies their simultaneous $Y$
error, with probability $1/4$ and perfect correction. A fixed ordinary
$Y$-parity check has two errors in each flag, although both protocols'
optimal deterministic fidelity is $1/2$. This separates those specified
checks, not unrestricted ordinary coding. If a clean control can hold
the logical qubit, native logical SWAP/decoding is a further bypass
baseline; its gates and actual memory noise must be charged.

The echo control must remain coherent while the modular syndrome is
obtained. If the same physical ancilla is the only syndrome meter, it
cannot simply be read/reset while retaining that unknown phase. Count
a separate meter or prove a compatible coherent implementation; an
optimal switched-control decoder needs the same retained-control/record
interface. Finite-energy GKP states have a nonzero initial gauge width
and a nontrivial envelope. Their final syndrome is not the exact added
shift, so neither the Pauli model (AG4) nor perfect echo parity follows
automatically. No finite-energy error constant or lifetime is asserted.

The native distinction is real. In the trapped-ion
[finite-GKP stabilization experiment](https://arxiv.org/abs/2010.09681),
conditional displacements are available, but spin fluorescence recoil
would overwhelm the motional code; coherent feedback and repumping avoid
that measurement. A switched flag needs an equally explicit nondestructive
output interface. A [whole-mode cavity controlled-SWAP](https://doi.org/10.1103/PRXQuantum.4.020355)
has been demonstrated in $1.3\,\mu$s, but introduces a second cavity,
coupler/pumps and retained control, and is not a demonstrated switch of
two independent hidden-noise modules. Additive displacement noise excites
vacuum dummies, whose output/bath can retain path information; the complete
routing instrument and all physical opportunities must be counted.
If deliberately engineered displacement draws are recorded, ordinary
serial order plus the known phase
$\operatorname{diag}(1,e^{-2i\operatorname{Im}(\beta\alpha^*)})$
already reproduces the switch for every draw. Invisible bath noise is
not assumed to expose such a record. None of these scoped statements
establishes a native quantum-switch storage advantage.

<a id="nr-r06-terminal-noise"></a>

### Fixed terminal local noise limits raw full-register switch throughput

This bound concerns one standard two-slot channel switch on a full
$D$-dimensional payload, with an independent control initialized in
$|+\rangle$. The slots $\mathcal A,\mathcal B$ are independent CPTP maps
on that payload. The complete output control and data may undergo an
arbitrary trace-nonincreasing accepted decoder $\mathcal R$ into a
$D$-dimensional output. This includes both switch flags, coherent joint
decoding, clean postprocessing ancillas, discarded decoder registers and
heralded recovery. The inaccessible reference is passive. No copy or
encoding of the input has been retained in a noiseless side register
before the noisy slots, and the control initially carries no payload data.

Let $|\Phi_D\rangle=D^{-1/2}\sum_x|x\rangle_R|x\rangle_T$,
$\Phi_D=|\Phi_D\rangle\langle\Phi_D|$, and let $W$ be any target
unitary. For the complete accepted map $\mathcal L$, define

$$
p=\operatorname{Tr}[(\mathrm{id}_R\otimes\mathcal L)(\Phi_D)],
\qquad
q=\langle W|(\mathrm{id}_R\otimes\mathcal L)(\Phi_D)|W\rangle,
\qquad
|W\rangle=(I\otimes W)|\Phi_D\rangle.
\tag{T1}
$$

Thus $q/p$ is the fidelity of the normalized accepted Bell state, when
$p>0$. This definition remains valid for input-dependent success; it does
not assert that the conditioned operation is a linear channel on every
payload. Nor does $q$ assert a literal classical correct-gate component
in a Kraus decomposition.

**Depolarizing-slot bound.** Write
$\Omega_D(X)=\operatorname{Tr}(X)I/D$. For every CPTP $\mathcal B$ and
every accepted decoder as above,

$$
q\bigl(\operatorname{SWITCH}(\Omega_D,\mathcal B)\bigr)
\le \frac{2}{D^2}.
\tag{T2}
$$

To prove it, choose $K_{ab}=|a\rangle\langle b|/\sqrt D$ as Kraus
operators for $\Omega_D$, and let $B_j$ be Kraus operators for
$\mathcal B$. The raw switched Kraus operators are

$$
S_{abj}=\frac{|0\rangle\otimes B_jK_{ab}
                 +|1\rangle\otimes K_{ab}B_j}{\sqrt2}.
$$

Absorb $W^\dagger$ into each decoder Kraus operator and write that
operator as a row of two blocks, $R_\ell=(X_\ell,Y_\ell)$.
Trace nonincrease implies
$\sum_\ell X_\ell^\dagger X_\ell\le I$ and
$\sum_\ell Y_\ell^\dagger Y_\ell\le I$. Cyclicity of the trace and
$\sum_{ab}|\operatorname{Tr}(Z|a\rangle\langle b|)|^2
=\|Z\|_{\rm HS}^2$ give the exact expression

$$
q=\frac1{2D^3}\sum_{j,\ell}
       \|X_\ell B_j+B_jY_\ell\|_{\rm HS}^2.
\tag{T3}
$$

Put $s_X=\sum_{j,\ell}\|X_\ell B_j\|_{\rm HS}^2$ and
$s_Y=\sum_{j,\ell}\|B_jY_\ell\|_{\rm HS}^2$.
Using $\sum_j B_j^\dagger B_j=I$,

$$
\begin{aligned}
s_X&=\sum_j\operatorname{Tr}\!\left[
B_j^\dagger\Bigl(\sum_\ell X_\ell^\dagger X_\ell\Bigr)B_j\right]
\le D,\\
s_Y&=\sum_\ell\operatorname{Tr}\!\left[
Y_\ell^\dagger\Bigl(\sum_j B_j^\dagger B_j\Bigr)Y_\ell\right]
\le D.
\end{aligned}
$$

The squared-norm inequality then gives
$q\le(s_X+s_Y)/D^3\le2/D^2$. In particular, $\mathcal B$ need not be
unital or random unitary. The proof is pointwise in the target $W$ and
does not require the physical decoder to know its matrix.

Suppose a declared independent control-dephasing channel, applied before
decoding, multiplies the order off-diagonal blocks by real
$0\le\nu\le1$. Equation (T3) instead becomes

$$
q=\frac{s_X+s_Y+2\nu\operatorname{Re}
\sum_{j,\ell}\langle X_\ell B_j,B_jY_\ell\rangle_{\rm HS}}{2D^3}
\le\frac{1+\nu}{D^2},
\tag{T4}
$$

by global Cauchy--Schwarz and $s_X,s_Y\le D$. A measured interference
visibility alone does not establish this full control-noise model.

**Terminal-noise transfer.** Use normalized Choi states
$j_{\mathcal N}=(\mathrm{id}\otimes\mathcal N)(\Phi_D)$, so that
$j_{\Omega_D}=I/D^2$. If $\mu=\|j_{\mathcal N}\|_\infty$, then

$$
\mathcal N\le_{\rm CP}D^2\mu\,\Omega_D.
$$

For $\mathcal A=\mathcal N\circ\mathcal A_{\rm pre}$ with any CPTP
$\mathcal A_{\rm pre}$ on the same payload, precomposition preserves
this inequality and
$\Omega_D\circ\mathcal A_{\rm pre}=\Omega_D$. Positivity and linearity
of the standard switch in its $\mathcal A$ slot, followed by the
accepted decoder and positive Bell test, therefore imply

$$
q\le\min\{1,(1+\nu)\mu\}.
\tag{T5}
$$

The comparison map $D^2\mu\Omega_D$ need not be trace preserving;
complete positivity is sufficient for the inequality. Interchanging
the two slots gives the same bound from a terminal noise layer in
$\mathcal B$.

For $D=2^n$ and a terminal independent layer
$\mathcal N=\mathcal N_{\rm loc}^{\otimes n}$, normalized Choi states
tensor up to a wire permutation. Consequently

$$
q\le\min\{1,(1+\nu)\mu_{\rm loc}^{n}\},
\qquad
\mu_{\rm loc}=\|j_{\mathcal N_{\rm loc}}\|_\infty.
\tag{T6}
$$

For unequal site channels the product $\prod_i\mu_i$ replaces
$\mu_{\rm loc}^n$. Two useful fixed-rate examples are:

- A local Pauli channel has Choi eigenvalues equal to its Pauli
  probabilities, so $\mu_{\rm loc}=p_{\max}$. For identity-dominant
  total error probability $\epsilon$ this is $1-\epsilon$.
- A local amplitude-damping channel of damping probability $\gamma$
  has normalized Choi eigenvalues
  $1-\gamma/2,\gamma/2,0,0$, so $\mu_{\rm loc}=1-\gamma/2$.
  This includes a nonunital, off-diagonal fault model.

If Bell-input acceptance is at least $p_0>0$ and accepted Bell fidelity
is at least $F_0>0$, (T6) requires

$$
p_0F_0\le(1+\nu)\mu_{\rm loc}^{n}.
\tag{T7}
$$

Thus a raw two-slot switch with one independent order qubit cannot
maintain both positive yield and positive universal-gate Bell quality
at a fixed local rate with $\mu_{\rm loc}<1$ as the full register grows.
For amplitude damping, keeping $p_0,F_0$ constant requires
$\gamma=O(1/n)$ in the small-rate regime. Deterministic coherent unitary
faults have $\mu_{\rm loc}=1$ and give no such scaling conclusion.

This is a raw full-register obstruction, **not a fault-tolerance
threshold or a no-go theorem for encoded logical computation**. Earlier
compiled faults and gates may be arbitrary in
$\mathcal A_{\rm pre}$, but the finite terminal product layer is an
exact premise. Simultaneous interacting Hamiltonian evolution and local
Lindblad damping do not automatically factor this way. A proposed
Trotter replacement needs its complete-process error bound. The result
also does not cover an initially data-carrying control, retained input
paths, exposed reservoirs, correlated two-slot baths, or a smaller
logical payload encoded in a larger physical register. Clean ancillas
introduced only for postprocessing are already covered by the decoder.
The bound does not exclude a small finite-register benefit or useful
local-observable simulation despite poor global Bell fidelity.

Ideal commutation and knowledge of the common basis were never used in
(T2)–(T7). Thus hidden many-body eigenvectors alone cannot evade this
specified fixed-rate scaling bound. Conversely, a physical coherent
Hamiltonian controller is not automatically the independent-slot process
in its proof. [Vasilyev et al.](https://doi.org/10.1103/PRXQuantum.1.020302)
propose $H_{\rm spin}\otimes|0\rangle\langle0|$ using a Rydberg clock
atom, with explicit blockade and emission limitations;
[Morong et al.](https://doi.org/10.1103/PRXQuantum.4.010334) experimentally
protect interacting ion dynamics using ordinary synchronized dynamical
decoupling. The former does not demonstrate a noisy-channel switch, and
the latter does not correct arbitrary Markov relaxation. Their actual
controls, inactive branches, emitted records and helper noise belong in
the [native-device comparison](architecture.md).

<a id="nr-r06-local-output-noise"></a>

### Terminal replacement noise also limits local order coherence

The preceding Bell bound does not by itself settle a local observable or a smaller encoded output. A different argument bounds the **complete order-control and fixed local output**, even when the two native maps contain arbitrary global interactions. It requires terminal independent replacement noise in **both** slots. It does not assume commuting ideals, a common eigenbasis, unitary preprocessing or a factorization of the interacting dynamics into active sites and spectators.

Let the payload be $D=\bigotimes_{j=1}^n D_j$, with $d_j=\dim D_j$, and write

$$
\begin{aligned}
\mathcal A&=\left(\bigotimes_j\mathcal N_{A,j}\right)\circ\Lambda_A,
&\mathcal N_{A,j}&=(1-\eta_{A,j})\mathrm{id}+\eta_{A,j}\Omega_{d_j},\\
\mathcal B&=\left(\bigotimes_j\mathcal N_{B,j}\right)\circ\Lambda_B,
&\mathcal N_{B,j}&=(1-\eta_{B,j})\mathrm{id}+\eta_{B,j}\Omega_{d_j},
\end{aligned}
\qquad 0\le\eta_{A,j},\eta_{B,j}\le1.
\tag{T8}
$$

Here $\Lambda_A,\Lambda_B:D\to D$ are arbitrary CPTP maps. Their independent-slot channel model and the finite terminal product layers are exact premises. The replacement events are independent across sites and between slots. All inaccessible module/fault records are traced. Earlier noise in $\Lambda_A,\Lambda_B$ need not be local. The input may have arbitrary entanglement among payload sites, the order qubit $O$, and a passive reference.

For Kraus operators $A_\alpha,B_\beta$, define the controlled switch by
$W_{\alpha\beta}=|0\rangle\langle0|_O\otimes B_\beta A_\alpha+|1\rangle\langle1|_O\otimes A_\alpha B_\beta$.
Let $\mathcal S_\nu$ include a declared order-dephasing channel that multiplies its off-diagonal $O$ blocks by real $0\le\nu\le1$ before readout. Let $\mathcal S_{\rm cl}$ denote the channel with those blocks deleted. The latter is an ordinary protocol: measure the input $O$ in $Z$, run the corresponding ordinary module order, and retain its classical order label. For independent input $O=+$, this is a fair randomized order; no quantum-controlled call is needed.

For any fixed set $L$ of retained output sites, put

$$
K_L=\prod_{j\notin L}\left[1-\left(1-\frac1{d_j}\right)\eta_{A,j}\eta_{B,j}\right].
$$

Then the two **local-output channels**, including the full control, satisfy

$$
\frac12\left\|\operatorname{Tr}_{\bar L}\circ\mathcal S_\nu
             -\operatorname{Tr}_{\bar L}\circ\mathcal S_{\rm cl}\right\|_\diamond
\le\frac{\nu}{2}K_L.
\tag{T9}
$$

The diamond norm includes arbitrary input references. Thus this is more than a control-fringe or one-input statement. The sites outside $L$ must be discarded **before** a decoder can use them; a global decoder that reads those sites, their syndrome records or their environment is outside (T9). Arbitrary later processing on $O,L$ and clean ancillary memories preserves the bound. Input encodings are allowed in this channel comparison; it compares the switch with a matched ordinary process rather than imposing an absolute local-state fidelity ceiling.

**Common-replacement lemma.** Let $D=J\otimes R$, $\dim J=d$, and suppose
$\mathcal A=\Omega_J\circ\Lambda_A$, $\mathcal B=\Omega_J\circ\Lambda_B$, where $\Omega_J(X)=I_J\otimes\operatorname{Tr}_J X/d$ and both preprocessing maps are arbitrary global CPTP maps. For the order cross map

$$
\mathcal C(X)=\sum_{\alpha\beta}B_\beta A_\alpha X(A_\alpha B_\beta)^\dagger,
\qquad \mathcal T=\operatorname{Tr}_J\circ\mathcal C,
$$

one has

$$
\|\mathcal T\|_\diamond\le\frac1d,
\qquad
\left\|\sum_{\alpha\beta}(A_\alpha B_\beta)^\dagger(B_\beta A_\alpha)\right\|_\infty\le\frac1d.
\tag{T10}
$$

The second statement is the trace effect of the first, and bounds the control-only coherence after tracing the entire payload. The stronger first statement retains all of $R$.

To prove the lemma, every replacement-output channel has Kraus operators

$$
A_{x i}=\frac{|x\rangle_J\otimes a_i}{\sqrt d},\qquad
B_{y k}=\frac{|y\rangle_J\otimes b_k}{\sqrt d},\qquad
\sum_i a_i^\dagger a_i=\sum_k b_k^\dagger b_k=I_{JR},
\tag{T11}
$$

where $a_i,b_k:JR\to R$. For example, if $K_\mu$ are Kraus operators of $\Lambda_A$, take $a_i=(\langle z|_J\otimes I_R)K_\mu$ with $i=(z,\mu)$. Define $a_{i,x}=a_i(|x\rangle\otimes I_R)$ and $b_{k,x}$ similarly. Tracing the output $J$ enforces $x=y$ in the cross term, giving the exact map

$$
\mathcal T(X)=\frac1{d^2}\sum_{xik}
       (b_{k,x}a_i)X(a_{i,x}b_k)^\dagger.
\tag{T12}
$$

Write $L_{xik}=b_{k,x}a_i$, $R_{xik}=a_{i,x}b_k$. Trace preservation implies $\sum_k b_{k,x}^\dagger b_{k,x}=I_R$ for each $x$, so

$$
\begin{aligned}
\sum_{xik}L_{xik}^\dagger L_{xik}
 &=\sum_i a_i^\dagger\left(\sum_{xk}b_{k,x}^\dagger b_{k,x}\right)a_i=dI_{JR},\\
\sum_{xik}R_{xik}^\dagger R_{xik}&=dI_{JR}.
\end{aligned}
\tag{T13}
$$

For any elementary cross map, trace-norm duality and block row/column Cauchy–Schwarz at each reference dimension give
$\|\sum_iL_i(\cdot)R_i^\dagger\|_\diamond\le\|\sum_iL_i^\dagger L_i\|_\infty^{1/2}\|\sum_iR_i^\dagger R_i\|_\infty^{1/2}$.
Indeed, its dual acts on a norm-one test operator $Y$ as $\sum_i R_i^\dagger YL_i$, a product of the corresponding block row, block diagonal copies of $Y$, and block column. Equations (T12)–(T13) prove the first bound in (T10); operator Cauchy–Schwarz applied to $d^{-2}\sum R_{xik}^\dagger L_{xik}$ proves the second directly.

The constant is sharp. For $\dim R=d$ and $\Lambda_A=\Lambda_B=\operatorname{Ad}_{\mathrm{SWAP}_{JR}}$, the cross effect is $\mathrm{SWAP}_{JR}/d$, and
$\mathcal T(X)=I_R\operatorname{Tr}(\mathrm{SWAP}_{JR}X)/d^2$ has diamond norm $1/d$. Thus the stronger-looking $1/d^2$ bound is false for interacting preprocessing.

**Transfer to terminal local noise.** Expand each factor in (T8) into its identity or replacement branch. For branch sets $S_A,S_B$, let $J=(S_A\cap S_B)\setminus L$. Both branch channels end in the same $\Omega_J$, with arbitrary CPTP preprocessing. This factors only terminal replacements on disjoint sites: it does **not** move the first module's noise through the second module's global dynamics. Those earlier replacements remain in their actual chronological position inside the channel products.

The lemma bounds the cross map after tracing $J$ by $1/d_J$, $d_J=\prod_{j\in J}d_j$. Further tracing sites outside $L$ is contractive. For an arbitrary initial positive order-block matrix $(\rho_{ab})$, including its reference, $\|\rho_{01}\|_1\le\sqrt{\operatorname{Tr}\rho_{00}\operatorname{Tr}\rho_{11}}\le1/2$. The switch and ordinary comparator have identical diagonal blocks; their difference consists of an off-diagonal block $\nu\mathcal T(\rho_{01})$ and its adjoint. Its half trace norm is at most $\nu/(2d_J)$, uniformly over references. Convexity and independence of replacement events give

$$
\mathbb E\frac1{d_J}
=\prod_{j\notin L}\left[(1-\eta_{A,j}\eta_{B,j})
                   +\frac{\eta_{A,j}\eta_{B,j}}{d_j}\right]
=K_L,
\tag{T14}
$$

which proves (T9).

For qubits with equal terminal strengths $\eta_A,\eta_B$ and $|L|=\ell$,

$$
\epsilon_L:=\frac{\nu}{2}K_L
 =\frac{\nu}{2}\left(1-\frac{\eta_A\eta_B}{2}\right)^{n-\ell}
 \le\frac{\nu}{2}e^{-(n-\ell)\eta_A\eta_B/2}.
\tag{T15}
$$

Control-only readout is $L=\varnothing$. At equal rates the governing scale is $(n-\ell)\eta^2$, rather than $(n-\ell)\eta$. The finite bound also holds for size-dependent rates, but it need not vanish when $\eta=O(1/n)$, as in NR-R01. Small fixed rates and a modest register can leave substantial order coherence; the finite expression should be used for the device in question.

A common subsequent local instrument with payoff in $[-1,1]$ changes its all-launch expected payoff by at most $2\epsilon_L$; for a payoff in $[0,1]$ the bound is $\epsilon_L$. If the switch accepts with probability at least $p_0>\epsilon_L$, the ordinary comparator has positive acceptance, its probability differs by at most $\epsilon_L$, and their normalized accepted local outputs have half trace distance at most $\min\{1,2\epsilon_L/p_0\}$. To see this, contract through the accepted instrument, bound its unnormalized block difference by $2\epsilon_L$ and its probability difference by $\epsilon_L$, then normalize and use the triangle inequality. Hence fixed positive-yield local improvement cannot remain constant in the fixed-rate regime of (T15); rare postselection must be charged. No Fisher-information or parameter-derivative bound follows from pointwise channel closeness alone without additional regularity assumptions.

For at most $N$ independent paired uses of this same channel interface, with the discarded sites unavailable between uses, arbitrary adaptive processing of the retained outputs has half-diamond process distance at most $N\epsilon_L$ from replacing each use by its ordinary comparator. The usual hybrid proof replaces one use at a time; the per-use diamond bound is uniform over the adaptive input/reference, and the surrounding CPTP processing is contractive. This is a hard bound on the number of paired uses, with the same declared noise family; it does not infer a persistent-memory process bound from channel marginals or silently substitute an expected-use budget.

The theorem concerns the declared terminal noise and discarded systems. It does not cover simultaneous interacting Lindblad evolution without a process approximation bound, correlated slot baths/replacement events, exposed fault records, later access to discarded sites, or an encoded logical decoder that processes the full physical register **before** discarding it. A fixed local observable can be bounded by (T9); a global code must be analyzed with its actual decoding circuit. This extends the local-output screen beyond independent spectators while retaining those distinctions. The [known-basis checks](#distinct-commuting-layers-in-a-known-basis-admit-ordinary-fault-checks) also furnish ordinary pre/post syndrome comparators, while the [calibration-transfer screen](backaction.md#nr-r14) explains why a changed conditional statistic alone does not establish restoration. Such application mechanisms must be scored at their actual helper, time and acceptance costs, rather than inferred from a changed fringe or poor global Bell fidelity.

<a id="nr-r06-deterministic-pauli-weyl"></a>

### A single ordinary check closes deterministic Pauli-noise recovery

Consider two noise modules whose realized errors are known Pauli strings
$E_a,F_b$. Allow an arbitrary input-independent joint law $p_{ab}$, rather
than requiring independent errors, provided the same realized pair is used
in both coherent histories and the ordinary serial calls sample that same
law at matched settings and times. Pauli products in the two orders are
the same net Pauli up to phase. A bare switch with an initially independent
plus control therefore has a full channel of the form

$$
\rho\longmapsto\sum_e p_e\,\sigma_e^C\otimes W_e\rho W_e^\dagger,
\qquad p_e=\sum_{(a,b):\,F_bE_a\propto W_e}p_{ab},
\tag{DW1}
$$

where the distinct $W_e$ belong to an orthogonal unitary error basis and
$\sigma_e$ are normalized one-qubit states. Several histories with the
same net error may yield mixed $\sigma_e$. The same description applies
to finite-dimensional Weyl errors, whose products likewise differ only
by phases. It need not apply to noise around arbitrary ideal gates: if
the two histories yield different net operators rather than one $W_e$
times two scalars, (DW1) is not justified.

The utility here is **unconditional entanglement fidelity** for identity
storage after an arbitrary deterministic joint control/data recovery.
The initial control contains no data encoding. The priors and relevant
error labels are calibrated; learning them and selecting controls are
additional costs. This is not a parameter-independent simulator of an
unknown family or a heralded fidelity/yield comparison.

**The switch can identify at most two dominant errors.** Complete the
$W_e$ to a $d^2$-element orthogonal unitary error basis. Expand each recovery
Kraus operator as
$K_r=\sum_f\langle v_{rf}|_C\otimes W_f^\dagger$. The normalized Bell
fidelity formula and $\operatorname{Tr}(W_f^\dagger W_e)=d\delta_{fe}$
give

$$
F_e=\sum_e p_e\operatorname{Tr}(M_e\sigma_e),\qquad
M_e=\sum_r|v_{re}\rangle\langle v_{re}|\ge0.
$$

Taking the normalized partial data trace of
$\sum_rK_r^\dagger K_r=I_C\otimes I_d$ gives $\sum_fM_f=I_C$.
Conversely, any such POVM followed by the guessed $W_e^\dagger$ correction
realizes its label-guessing score. Zero-prior outcomes can be merged with
supported ones, so optimal recovery equals minimum-error discrimination
of $\{p_e,\sigma_e\}$. Since $\sigma_e\le I$ and $M_e\le I$,

$$
F_{e,\mathrm{switch}}\le
\sum_e p_e\min\{1,\operatorname{Tr}M_e\}
\le p_{(1)}+p_{(2)}.
\tag{DW2}
$$

The last step distributes total weight at most two, with at most one per
label, among descending priors.

For Pauli strings, let $W_1,W_2$ be two most likely distinct net errors.
They differ on some qubit $j$. Choose a known **single-qubit** Pauli $Q_j$
anticommuting with their relative Pauli at that qubit. Their conjugation
characters are opposite:
$Q_j^\dagger W_iQ_j=\chi_iW_i$, $\chi_1=-\chi_2\in\{1,-1\}$.
Apply controlled-$Q_j$, the same two actual noise calls in serial order,
then controlled-$Q_j^\dagger$. Error $e$ gives helper state
$(|0\rangle+\chi_e|1\rangle)/\sqrt2$ and the same data error $W_e$.
An $X$ measurement perfectly distinguishes the two chosen errors. Correct
$W_1$ or $W_2$ on its corresponding outcome. All outcomes return a quantum
output; contributions from the other orthogonal errors have zero Bell
fidelity. Thus

$$
F_{e,\mathrm{ordinary}}\ge p_{(1)}+p_{(2)}
\ge F_{e,\mathrm{switch}}.
\tag{DW3}
$$

Only one helper and two local controlled-Pauli gates are needed around
the serial calls, independently of the register size. The known final
Pauli correction is a product of single-qubit gates or an explicitly
permitted Pauli frame. No data-sized Bell reference, inverse unknown
query, controlled unknown module or mid-circuit data measurement is used.
This is a use of the ordinary coherent-check mechanism above, with both
outcomes corrected rather than postselected. It does not make the checks,
helper memory or calibration physically noiseless.

An exact correlated two-qubit example makes the comparison strict.
Enumerate $(I,X,Y,Z)^{\otimes2}$ lexicographically from zero and set

$$
p_{ab}=\frac{1+50\mathbf1_{a=b=0}+30\mathbf1_{a=1,\,b=3}}{336}.
$$

This has all 256 histories and is not a product law. The net-error
control states are $X_C$ diagonal, so their optimal discrimination value
is the sum of the largest masses in the plus and minus sectors:
$F_{e,\mathrm{switch}}=13/42$. The two dominant net errors are $I\otimes I$
and $I\otimes Y$; a single $I\otimes X$ check distinguishes them and gives
$F_{e,\mathrm{ordinary}}=1/3$. The finite replay checks the complete
switched/CQ channel identity on all 16 input matrix units, not just
this fidelity number.

**Cyclic qudit Weyl errors give an explicit near-dominance bound.** Let
$X|j\rangle=|j+1\bmod d\rangle$, $Z|j\rangle=\omega^j|j\rangle$,
$\omega=e^{2\pi i/d}$, and $W_{x,z}=X^xZ^z$. For $Q=X^uZ^v$,

$$
Q^\dagger W_{x,z}Q=\omega^{uz-vx}W_{x,z}.
$$

If the two dominant labels differ by $\Delta=(x,z)\ne(0,0)$, put
$g=\gcd(d,x,z)$ and $r=d/g\ge2$. Bezout's identity implies that the
available relative characters are exactly the $r$th roots of unity:
the residues $uz-vx\pmod d$ form precisely the subgroup generated by
$g$. Choose relative phase $2\pi\lfloor r/2\rfloor/r$. The two helper
states then have overlap zero for even $r$, or
$c=\sin(\pi/(2r))$ for odd $r$.

Write $a=p_{(1)}$, $b=p_{(2)}$. The Helstrom measurement of just those two
helper states, followed by their inverse-error corrections, is a valid
ordinary deterministic recovery with

$$
F_{e,\mathrm{ordinary}}\ge
\frac{a+b+\sqrt{(a+b)^2-4ab c^2}}2
\ge\alpha_r(a+b)\ge\alpha_r F_{e,\mathrm{switch}},
\quad
\alpha_r=\begin{cases}1&r\text{ even},\\
\cos^2(\pi/(4r))&r\text{ odd}.
\end{cases}
\tag{DW4}
$$

For the second inequality use $4ab\le(a+b)^2$; for odd $r$,
$(1+\sqrt{1-c^2})/2=\cos^2(\pi/(4r))$. The first expression follows by
diagonalizing $a|\psi_1\rangle\langle\psi_1|-b|\psi_2\rangle
\langle\psi_2|$: its trace is $a-b$ and determinant
$-ab(1-c^2)$. Other errors cannot contribute negatively to the delivered
Bell fidelity.

For odd prime $d$, every nonzero label difference has $r=d$, so the
multiplicative shortfall is $\pi^2/(16d^2)+O(d^{-4})$. For composite $d$,
an odd difference order may be a small divisor; a large ambient dimension
alone does not give that scaling. If $d$ is a power of two all nonzero
orders are even, giving exact dominance in (DW4). If $d$ has odd divisors,
the worst nontrivial odd order is its smallest odd prime divisor. In
particular all odd orders are at least three, giving the universal
factor $\cos^2(\pi/12)$, but this factor is not an exact no-advantage
theorem for arbitrary odd-order Weyl laws.

**Tensor-product qutrit Weyl errors admit exact dominance.** There is a
stronger statement for $n$ qutrits with local $ZX=\omega XZ$,
$\omega=e^{2\pi i/3}$. Their labels form $\mathbb F_3^{2n}$ and all
commutator phases are cube roots of unity. Write
$\rho_k=|\psi_k\rangle\langle\psi_k|$ with
$|\psi_k\rangle=(|0\rangle+\omega^k|1\rangle)/\sqrt2$.
Every conditional switched-control state in (DW1) lies in the convex hull
of $\rho_0,\rho_1,\rho_2$.

Fix an optimal switched-recovery POVM $M_e$. For each label choose a color
$k_e$ maximizing $\operatorname{Tr}(M_e\rho_k)$, breaking ties arbitrarily.
Let $G_k=\{e:k_e=k\}$, $N_k=\sum_{e\in G_k}M_e$, and for each nonempty
group choose $e_k\in G_k$ with largest prior $r_k=p_{e_k}$. Positivity
and convexity give

$$
F_{e,\mathrm{switch}}\le
\sum_e p_e\operatorname{Tr}(M_e\rho_{k_e})
\le\sum_k r_k\operatorname{Tr}(N_k\rho_k).
\tag{DW5}
$$

The $N_k$ form a POVM; empty groups have zero effect. Define the weighted
trine-guessing value
$G(a,b,c)=\max_{\{T_k\}}[a\operatorname{Tr}(T_0\rho_0)+
b\operatorname{Tr}(T_1\rho_1)+c\operatorname{Tr}(T_2\rho_2)]$, where
the maximum is over three-outcome qubit POVMs and weights need not sum
to one. This function is coordinatewise nondecreasing. It is also
symmetric: $\operatorname{diag}(1,\omega)$ cyclically permutes the trine
states and $X_C$ sends $k\mapsto-k$; these unitaries generate all six
permutations, and the POVM can be conjugated and relabeled accordingly.
The at most three selected labels $e_k$ are distinct, as they come from
disjoint groups. Their descending priors are therefore bounded termwise
by the global three largest priors, padding with zero if necessary. Thus
(DW5), symmetry and monotonicity imply

$$
F_{e,\mathrm{switch}}\le G(p_{(1)},p_{(2)},p_{(3)}).
\tag{DW6}
$$

Take the three global most likely distinct net-error labels, adding any
zero-prior labels if needed. There is an affine functional
$f(e)=\ell(e)+c$ on $\mathbb F_3^{2n}$ mapping them to the distinct
colors $0,1,2$. Subtract the first point. If the two difference vectors
are independent, solve the two color constraints using an invertible
$2\times2$ coordinate minor. If they are dependent, the three distinct
points exhaust an affine line over $\mathbb F_3$; the two differences
are opposites, as are the prescribed color increments $1,2$. One
nonzero coordinate then solves the constraint. The two-point and
one-point cases need only one coordinate or a constant. Equivalently,
every permutation of the three elements of $\mathbb F_3$ is affine.

In each case $\ell$ has at most two nonzero coordinates. The nondegenerate
Weyl commutator form identifies $\ell$ with a known Weyl $Q$ supported
on at most **two physical qutrits**. An ordinary controlled-$Q$ /
serial-call / controlled-$Q^\dagger$ echo gives helper state
$\rho_{\ell(e)}$. Absorb the known offset $c$ into its final POVM or
a known helper phase. Perform an optimal trine POVM for the three largest
priors and correct their corresponding errors. The selected labels
contribute exactly $G(p_{(1)},p_{(2)},p_{(3)})$; all other orthogonal
errors contribute zero Bell fidelity. This is a deterministic TP
recovery, proving ordinary dominance of (DW6).

In fact this is the **exact optimum among single controlled-Weyl echoes**
with arbitrary final helper POVM and inverse-error correction. For any
such echo, all labels in one character class have identical helper state,
so only the maximum prior in each of its three classes matters. Those
three maxima are bounded after sorting by the global three largest
priors, giving the same upper bound $G(p_{(1)},p_{(2)},p_{(3)})$. The
affine construction above attains it.

It needs one coherent helper through the noisy calls and at most four
local controlled-Weyl gates, independently of $n$, plus the final
three-outcome helper POVM and known error corrections. Implementing that
POVM can require postprocessing ancillas, which are additional resources.
Only the **three dominant net-error labels and priors** need to be
calibrated; the ordinary construction does not require $\sigma_e$, the
switch's optimal recovery, or a search through a full distribution.
Once those labels are known, finding the required coordinate minor
is elementary classical linear algebra, and the final discrimination
optimization is a three-state qubit problem. Obtaining reliable dominant
labels is nevertheless a real calibration task, with its actual probe,
memory, sample and classical-computation costs. No efficient general
learning guarantee follows from the interpolation proof. Calibration,
measurement and all rejected learning samples are not free. Cyclic
dimension $3^n$ Weyl operators
have higher-order central phases and are a different error group; this
ternary proof does not apply to them merely because their Hilbert-space
dimension is the same.

The four-error $I/X$ then $I/Z$ family is stronger still. Its switch has
three common plus-control labels and one phase-shifted $ZX$ label. With
$r_0=\max\{(1-p)(1-q),p(1-q),(1-p)q\}$ and $t=pq$, optimal switch fidelity
is $[r_0+t+\sqrt{(r_0-t)^2+4r_0t\sin^2(\pi/d)}]/2$. Each difference
between $ZX$ and a common label has a coordinate equal to one, so an
ordinary echo can replace $\sin^2(\pi/d)$ by
$\sin^2(\pi\lfloor d/2\rfloor/d)$. This dominates for every $d\ge2$
and is strictly better for $d\ge4$ when $r_0t>0$. No primality assumption
is needed for that special support.

For a fair independent $I/X$ then $I/Z$ pair on one qutrit, the switch
value is $(2+\sqrt3)/8\simeq0.4665$. The ordinary trine construction
attains $1/2$: the three selected priors are $1/4$ and the POVM is
$T_k=(2/3)\rho_k$. This also saturates its single-echo upper bound since
$\sum_k\operatorname{Tr}T_k=2$ and $\rho_k\le I_C$.

### Common preparation faults and final control noise preserve the comparison

The Pauli and tensor-qutrit deterministic comparison survives an arbitrary
**common final CPTP channel on the control alone**, with a precise ordering.
Let the control be prepared in the same fixed state $\rho_C$, independently
of the unknown payload and its reference. For $m=2$ (Pauli) or $m=3$
(tensor-qutrit Weyl), put

$$
D_k=\operatorname{diag}(1,e^{2\pi i k/m}),\qquad
\rho_k=D_k\rho_CD_k^\dagger,\qquad
\tau_k=\mathcal N_C(\rho_k).
\tag{DN1}
$$

The switch is the bare controlled-order operation. Its conditional control
states are convex combinations of the $m$ orbit vertices $\rho_k$;
after the stipulated final noise they are convex combinations of $\tau_k$.
The ordinary echo uses the same physical noise calls, control preparation
and final $\mathcal N_C$. The final noise acts after its controlled checks
and any chosen known helper phase, and **before** arbitrary joint recovery
or any retained measurement record. Data-correlated helper faults,
in-circuit noise, pre-noise decoding, or copying the helper into another
protected memory are different models. A fixed common final control frame
can be included in $\mathcal N_C$.

For nonnegative weights $a_1,\ldots,a_m$, define

$$
H_{\mathcal N,\rho_C}(a_1,\ldots,a_m)=
\max_{\pi\in S_m}\ \max_{\{T_k\}}
\sum_{k=0}^{m-1}a_{\pi(k+1)}\operatorname{Tr}(T_k\tau_k),
\qquad \sum_kT_k=I_C,\quad T_k\ge0,
\tag{DN2}
$$

where the weights need not sum to one. This value is symmetric in the
weights by its permutation maximum and coordinatewise nondecreasing by
positivity. No symmetry, covariance, unitality or purity of the noise
images $\tau_k$ is assumed.

The recovery-to-POVM argument applies unchanged after control-only noise.
Fix its optimal POVM $M_e$. For each net-error label choose a vertex $k_e$
maximizing $\operatorname{Tr}(M_e\tau_k)$. Group the effects as
$N_k=\sum_{e:k_e=k}M_e$ and retain in each group a maximum-prior label
with prior $r_k$. Convexity and nonnegative probabilities give

$$
F_{e,\mathrm{switch}}\le
\sum_ep_e\operatorname{Tr}(M_e\tau_{k_e})
\le\sum_kr_k\operatorname{Tr}(N_k\tau_k)
\le H_{\mathcal N,\rho_C}(p_{(1)},\ldots,p_{(m)}).
\tag{DN3}
$$

The last inequality uses the distinct selected labels, the termwise bound
of their sorted priors by the global largest $m$ priors, and the symmetry
and monotonicity of (DN2). Empty groups have zero effects and weights.

The ordinary construction attains the final bound. For Paulis, a local
separator maps the two dominant labels to the two orbit phases; an added
known $Z_C$ phase chooses either assignment. For tensor-qutrit Weyl
errors, the affine interpolation argument maps the three dominant labels
to any permutation of the three colors. It uses a known check supported
on at most two qutrits. Apply the constant phase offset **before**
$\mathcal N_C$, then the optimizing POVM in (DN2), and correct the
corresponding dominant errors. The selected labels contribute exactly
the bound in (DN3), and other orthogonal errors contribute zero Bell
fidelity. Conversely, any such echo yields identical noisy helper states
within each character class, whose largest priors are bounded by the
global largest $m$. Thus its best value is exactly (DN2), giving

$$
\max_{\mathrm{ordinary\ single\ echo}}F_e
=H_{\mathcal N,\rho_C}(p_{(1)},\ldots,p_{(m)})
\ge F_{e,\mathrm{switch}}.
\tag{DN4}
$$

The same two local controlled-Pauli gates, or at most four local
controlled-qutrit-Weyl gates, suffice during the noisy calls. The known
control phase, final POVM, postprocessing ancillas, actual error
corrections and their faults remain costs. Unlike a noiseless trine
orbit, $\tau_k$ need not possess permutation symmetry; optimizing the
assignment in (DN2) is essential. The offset cannot generally be moved
after the noisy channel or absorbed into its final POVM.

For example, take ideal plus preparation and
$\rho_\pm=|\pm\rangle\langle\pm|$. The legitimate measure-and-prepare channel
$\mathcal N(\rho)=\operatorname{Tr}(\rho_+\rho)I/2+
\operatorname{Tr}(\rho_-\rho)|0\rangle\langle0|$ sends $\rho_+$ to
$I/2$ and $\rho_-$ to a pure state. With priors $3/5,2/5$, assigning the
larger prior to the mixed image gives optimal guessing $7/10$; swapping
the orbit phases before the noise gives $4/5$. No post-noise unitary
or POVM relabeling can remove that statistical difference. Likewise,
replacement control noise makes every $\tau_k$ equal, so (DN2) reduces
to $p_{(1)}$, not the noiseless Pauli sum $p_{(1)}+p_{(2)}$.

This is a pointwise calibrated deterministic comparison. It requires the
dominant net-error labels and priors and the relevant control-state
images or final-decoder calibration. It does not differentiate through
unknown settings, provide a Fisher-information converse, suppress helper
noise for free, or reproduce the full switched instrument. Common fixed
preparation SPAM is permitted by $\rho_C$; preparation correlated with
the unknown payload, pre-noise classical records, and faults during
controlled gates require their own complete instrument.

All conclusions assume the complete same-net-error ensemble (DW1),
matched exogenous error law, calibrated labels/priors and ideal specified
checks. Unknown bases, a control initially carrying payload information,
coherent superpositions of error labels, quantum bath backaction,
unmodelled helper faults and time-dependent setting changes require their own instrument.
The comparison does not reproduce the full switched channel, every
accepted conditional output, a metrology likelihood or an adaptive future
utility. Source/reset/calibration effort, helper lifetime, connectivity,
readout and the actual controlled-Weyl implementation remain native costs.

<a id="nr-r06-encoded-pauli"></a>

### Encoded Pauli outputs admit an ordinary decoder and retained syndrome records

The fixed-control preparation in (DW1) excludes an order control that
already carries useful input information. A separate, exact comparison
applies to one such code. [Chen and Ma, *Commutator Geometry and
Information Preservation in the Quantum Switch*, §6](https://arxiv.org/html/2609.21310v1#S6)
consider the joint encoding $V|0\rangle=|00\rangle$,
$V|1\rangle=|11\rangle$. Their ordinary comparator is the specified map
$\mathrm{id}_C\otimes(\Phi\circ\Psi)$, rather than an optimization over
interleaved decoding, memory and measurements. The construction below
enlarges that comparator. It reproduces the full switched output on
this code without knowing the noise probabilities, and does not
contradict the paper's fixed-map inequalities.

**Error model and branch identity.** Let two target-only noise modules
apply $X^a$ and $Y^b$, where $a,b\in\{0,1\}$. Independent modules have
$\pi_{ab}=p^a(1-p)^{1-a}q^b(1-q)^{1-b}$ for unknown $p,q$. The proof
also allows any exogenous classical joint law $\pi_{ab}$ that is common
to both implementations and unaffected by the input, query order or
intermediate controls and reads. Reduced one-time channels alone do
not supply that promise for a correlated quantum memory process.
Using the source's order convention, put

$$
W_{ab}=|0\rangle\langle0|_C\otimes X^aY^b
       +|1\rangle\langle1|_C\otimes Y^bX^a,
\qquad
\mathcal S_\pi(\rho)=\sum_{ab}\pi_{ab}W_{ab}\rho W_{ab}^\dagger.
\tag{EP1}
$$

Let $V_c=(I_C\otimes X_T^c)V$, $c=a\mathbin\oplus b$, and
$f=b(1-a)$. Since $XY=iZ$, $YX=-iZ$, and $Z_CZ_TV=V$,

$$
W_{ab}V=i^b V_cZ_L^f.
\tag{EP2}
$$

In the order $ab=00,10,01,11$ these are $V,V_1,iV_1Z_L,iV$.
The single-error odd-parity output is part of the retained channel;
this is not just an equality after projection back onto the code.

**Ordinary chronology and proof.** The known gate
$E=\operatorname{CNOT}_{C\to T}=E^\dagger$ decodes any input on the code
to $\rho_C\otimes|0\rangle\langle0|_T$. The same statement holds for
an arbitrary mixed input correlated with a passive reference $R$.
Store the decoded logical state coherently in $C$ and perform:

1. Query the $X$ module and read $Z_T$ nondestructively, obtaining $s=a$.
2. Query the $Y$ module on the same target, **without resetting it**,
   and read $Z_T$ nondestructively again, obtaining $t=a\oplus b=c$.
3. Infer $b=s\oplus t$, apply $Z_C^{b(1-a)}$, and apply $E$ to reencode.
   The target is already $|c\rangle$, so this retains the appropriate
   even or odd output sector.

Indeed, after decoding the two target actions and read projectors give
$Y^bX^a|0\rangle=i^b(-1)^{ab}|c\rangle$. The projectors act on known
basis states of a tensor factor and reveal no logical or reference
information. The ordinary branch isometry is therefore

$$
M_{ab}=i^b(-1)^{ab}V_cZ_L^f=(-1)^{ab}W_{ab}V.
\tag{EP3}
$$

Only the double-error branch changes sign, from $iV$ to $-iV$. This is
a branch-global phase, not an uncorrected logical $Z$. Thus for every
logical operator $A$, $M_{ab}AM_{ab}^\dagger=(W_{ab}V)A(W_{ab}V)^\dagger$.
Each branch is an isometry. Summing with any $\pi_{ab}$ proves exact
trace-preserving equality of the full encoded-input, retained-output
channel. Tensoring this operator identity with $\mathrm{id}_R$ proves
the assertion for every mixed state and reference. All outcomes count;
no success normalization, learned $p,q$ or input-parameter-dependent
control is used. A signal written before decoding is included. A
signal acting later on the now-decoded target is a different task.

Retaining the two read records, and relabeling $(s,t)$ as $(a,b)$,
gives the ordinary instrument

$$
\Gamma_\pi(\rho)=\sum_{ab}\pi_{ab}|a,b\rangle\langle a,b|_F\otimes
       (W_{ab}V)\rho(W_{ab}V)^\dagger.
\tag{EP4}
$$

Discarding $F$ gives $\mathcal S_\pi(V\rho V^\dagger)$ through a
parameter-independent map. The refinement therefore includes every
later joint-output measurement, statistical decision and processing
that accesses only this output. It does not reproduce an inaccessible microscopic
environment or coherent superpositions of error labels.

**Perfect storage and noise information with the same access.** Instead
of the phase feedback in step 3, apply $X_T^c$ and then $E$. The decoded
logical state was untouched, and this restores $T=0$ before encoding.
The output is exactly

$$
V\rho_{RL}V^\dagger\otimes
       \sum_{ab}\pi_{ab}|a,b\rangle\langle a,b|_F.
\tag{EP5}
$$

Thus the same memory/readout ports allow perfect encoded storage while
retaining the complete error record. For independent interior $p,q$
the record Fisher matrix is
$\operatorname{diag}(1/[p(1-p)],1/[q(1-q)])$. With $p=q=\gamma$ its
single-parameter information is $2/[\gamma(1-\gamma)]$, the same optimal
noise information already established in the source's Appendix 9.3
for ordinary Bell probes and SWITCH. For any regular differentiable
classical law, the record matrix is
$\sum_{ab}(\partial_\mu\pi_{ab})(\partial_\nu\pi_{ab})/\pi_{ab}$.
For input-state parameters alone, (EP5) preserves the full input QFI
matrix. This does not assert simultaneous attainability of incompatible
parameter measurements or use interior Fisher formulas at a rank-changing
endpoint. The decoder and instrument are independent of every unknown
probability and signal parameter, so discarding records remains a valid
data-processing comparison when the probabilities vary.

**Deferred reads are a priced coherent variant.** When two clean record
qubits $R_1,R_2$ and their actual coherent gates are supplied, replace
the intermediate reads by $\operatorname{CNOT}_{T\to R_1}$ after the
$X$ query and $\operatorname{CNOT}_{T\to R_2}$ after the $Y$ query.
For each classical error branch they store $(a,c)$. Apply $Z_C$ if
$R_1=0,R_2=1$, then reencode. Since $f=b(1-a)=c(1-a)$, this is the same
isometry (EP3), with orthogonal retained records that may be read only
at the end. For (EP5), replace this controlled phase by
$\operatorname{CNOT}_{R_2\to T}$. This avoids an intermediate classical
readout deadline only by retaining coherent records and supplying the
additional couplings, conditional gate and memory. It is not free
controlled access to an arbitrary unknown module.

**Noise and physical boundary.** Identical parameter-independent
postprocessing of the simulated output can always be appended on both
sides. More specifically, diagonal control-noise Kraus operators
$f_j(Z_C)$ commute with $E$, the target operations, reads, phase feedback
and every $W_{ab}$. Under genuinely matched exposure and error law they
can be moved to the output, preserving the comparison, including ordinary
control phase noise. General in-loop helper noise does not have this
property. Already with noiseless queries, an $X_C$ during decoded storage
becomes $EX_CE=X_CX_T$, whereas an $X_C$ on the original encoded register
is $X_C$. They differ on $|00\rangle$. Helper relaxation, cross-talk,
leakage, wrong read records, noisy gates and measurement-reactive memory
need their complete timed instruments. Coherent non-Pauli rotations
cannot be replaced by the classical law in (EP1).

The ordinary ledger is two module calls, two known decode/encode CNOTs,
coherent $C$ storage over both calls and read latency, two sequential
nondemolition $Z_T$ reads, two classical bits and feedforward; or the
explicit coherent-record replacement above. A read must act as
$I_C\otimes|t\rangle\langle t|$ and retain the target carrier without
leaving a record of $C$. If $C$ is path and $T$ polarization of one
photon, path-resolving detection can destroy the logical coherence,
and destructive polarization detection destroys the retained photon.
Ancillas, failure events, buffer time, routing, coherent gates and
coupling loss enter the all-launch comparison. A postselected optical
QND demonstration does not supply a deterministic read for free; see
[Pryde et al., *Measuring a photonic qubit without destroying it*](https://doi.org/10.1103/PhysRevLett.92.190402).

The noiseless-control decoder is an established resource-model issue:
[Chiribella and Kristjánsson, §III.1.3](https://arxiv.org/html/1812.05292v3)
explicitly distinguish communication encoders that transfer information
to noiseless control from restricted non-signalling encoders. Ordinary
syndrome-based noise estimation is also established, for example
[Y. Fujiwara](https://arxiv.org/html/1405.6267v1). These are context, not
priority claims for this particular elementary circuit. Equations
(EP1)--(EP5) close this code-restricted candidate only when the stated
decode, memory and readout or coherent-record ports are allowed. They
do not simulate the switch on arbitrary $CT$ inputs or arbitrary channels,
and do not establish equal laboratory time. A native advantage must be
tested against the same actual storage, gates and retained-output ports.

<a id="nr-r06-fermionic-poisoning"></a>

### Fermionic collision flags require the even physical dilation

Quasiparticle poisoning is a real Majorana-memory bottleneck. The
[poisoning analysis of Karzig, Cole and Pikulin](https://doi.org/10.1103/PhysRevLett.126.057702)
distinguishes above-gap quasiparticles from localized subgap parity
reservoirs. The [local-detection construction](https://arxiv.org/html/2307.08896)
uses a four-Majorana tetron of fixed parity and explicitly includes its
parity measurement and additional quasiparticle detectors as ordinary
error-detection resources. These sources motivate the following screen;
they do not demonstrate a quantum switch of poisoning contacts or certify
the symmetric bath model below.

This application cannot be obtained merely by treating physical odd
Majoranas as commuting tensor factors with their fermionic reservoirs.
Let $\gamma_1,\ldots,\gamma_m$, $m=2n$, be system Majoranas, with
$\{\gamma_j,\gamma_k\}=2\delta_{jk}$. For each station $A,B$ and each
$j$, provide a **different reservoir fermion mode**, initially empty, and
use one of its Majoranas $\eta_{Aj},\eta_{Bj}$. All system and bath
Majoranas anticommute. One bath Majorana per independent fermion mode
ensures that distinct excited subsets have orthogonal vacuum records;
packing these Majoranas into fewer modes would not have that property.
The extra generator in a maximal $2n+1$ qubit Clifford alphabet is total
fermion parity, which is even and acts as a scalar on a fixed-parity code;
it is not another single-fermion poisoning error.
Consider the parity-preserving joint unitaries

$$
U_A=\prod_{j=1}^{m}(c+s\gamma_j\eta_{Aj}),\qquad
U_B=\prod_{j=1}^{m}(c+s\gamma_j\eta_{Bj}),\quad
c=\sqrt{1-r},\quad s=\sqrt r,\quad 0\le r\le1.
\tag{FP1}
$$

Each bilinear is anti-Hermitian and squares to $-I$, so its factor is
unitary and even. Terms at distinct $j$ within a station commute. This
is a declared joint system/bath process: stationary retained reservoir
modes are used in both order histories, with no additional timing record.
It is not inferred from the reduced memory channel. Grant a perfect
surviving order helper and ideal coherent routing to this process.

**The graded sign changes which flag detects a collision.** Put
$A_j=\gamma_j\eta_{Aj}$ and $B_k=\gamma_k\eta_{Bk}$. Direct CAR
reordering gives

$$
A_jB_k=B_kA_j\quad(j\ne k),\qquad A_jB_j=-B_jA_j.
\tag{FP2}
$$

For example, distinct $j,k$ require four odd exchanges, while a shared
system Majorana leaves one net minus sign. Consequently, if $J,K$ are
the excited system-index subsets in the two stations,
$A_JB_K=(-1)^{|J\cap K|}B_KA_J$. The order-minus flag selects
$|J\cap K|$ odd, and the net memory error is, up to a scalar phase,
$\gamma_{J\triangle K}$. Its branch probability before the flag is

$$
w(J,K)=r^{|J|+|K|}(1-r)^{2m-|J|-|K|}.
\tag{FP3}
$$

For a model that artificially allows at most one poisoning jump per
station, the minus branch selects exactly equal jump indices, leaving
identity on the memory and two bath excitations. Its yield is
$\sum_jp_{Aj}p_{Bj}$, or $p_Ap_B/m$ for uniform jump labels. Grading
therefore swaps the naive qubit collision flag; it does not by itself
eliminate that idealized filter. In the full product process (FP1),
additional unmatched jumps survive alongside an odd collision. There is
no exact identity filter at nonzero generic $r$.

**A useful tetron endpoint includes its ordinary parity check.** Set
$m=4$ and encode an arbitrary logical qubit, possibly entangled with a
passive reference, in the known $+1$ sector of
$P=-\gamma_1\gamma_2\gamma_3\gamma_4$. The final projective $P$
measurement rejects odd net errors. Every proper nonempty even Majorana
monomial restricts, up to phase, to one of the three logical Paulis;
complementary pairs have the same logical action. The empty and full
net subsets are both logical identity.

Write

$$
x=1-2r,\quad y=x^2,\quad
a=1-2r+2r^2=(1+x^2)/2,\quad q=2r(1-r)=(1-x^2)/2.
$$

Let $p_P$ be the unflagged probability of passing final parity, and
$g_P$ its unnormalized logical-identity/Bell-good weight. Let $p_S,g_S$
denote these quantities when also retaining the switched minus flag.
Summing (FP3) gives

$$
\begin{aligned}
p_P&=(1+x^8)/2,&g_P&=a^4+q^4=(x^8+6x^4+1)/8,\\
p_S&=\frac{1+x^8-(x+q)^4-(x-q)^4}{4}
 =\frac{(1-x^2)^2(7x^4-6x^2+7)}{32},\\
g_S&=(a^4-x^4)/2
 =\frac{(1-x^2)^2(x^4+6x^2+1)}{32}.
\end{aligned}
\tag{FP4}
$$

For $p_P$, each net bit is independently one with probability $q$.
For $p_S$, project simultaneously on even net cardinality and odd
intersection cardinality. Their per-index characters are respectively
$x^2$, $1-2r^2=x+q$, and $1-4r+2r^2=x-q$, giving the first expression.
For $g_S$, identity with empty net subset requires $J=K$ and odd $|J|$;
the generating function is $(a^4-x^4)/2$. The full net subset has
$J\cap K=\varnothing$ and never contributes to this flag. Permutation
symmetry makes the three nonidentity logical-Pauli weights equal to
$(p_S-g_S)/3$. These are complete CP maps on the code, rather than just
state fidelities.

**An ordinary one-helper comparator has higher yield and fidelity.**
Suppose the actual interface supplies known controlled applications of
the even bilinear $Q=i\gamma_1\gamma_2$, together with the same final
$P$ measurement. Prepare one helper in plus, apply controlled-$Q$, run
the two actual contacts in a fixed order, then controlled-$Q$ again.
Since $Q$ commutes with bath operators, its helper character on (FP3)
is $(-1)^{|(J\triangle K)\cap\{1,2\}|}$. Keep its plus outcome and
the final even-parity outcome. Both pair parities are now even, giving

$$
p_O=(1+x^4)^2/4,\qquad g_O=g_P=(x^8+6x^4+1)/8.
\tag{FP5}
$$

No oracle matrix or value of $r$ is needed for this fixed selection.
For all $0\le r\le1$,

$$
\begin{aligned}
32(p_O-p_S)
 &=y^4+1+20y(y-1)^2+30y^2>0,\\
256(g_Op_S-g_Sp_O)
 &=(1-y)^4\{5(y-1)^4+12y(y-1)^2+16y^2\}\ge0.
\end{aligned}
\tag{FP6}
$$

The polynomial identities prove both greater accepted yield and at least
as high conditional identity fidelity whenever $p_S>0$. At $r=0,1$
the switched minus branch never occurs. In fact this also defeats its
best deterministic final decoder: a Pauli channel with weights
$g_S,b,b,b$ has optimal corrected Bell-good weight $\max(g_S,b)$ by
the recovery-to-POVM argument. If $b$ is largest its conditional score
is at most $1/3$, whereas (FP5) obeys
$2g_O-p_O=y^2\ge0$. The comparison uses the physical parity-constrained
qubit; it does not encode arbitrary coherent even/odd superpositions.

**Symmetric final helper dephasing preserves this resource screen.**
Let both retained helpers suffer the same declared final $Z$-dephasing
visibility $\nu\in[0,1]$, after the order operation or echo and before
their $X$ readout. This flips the ideal flag with probability
$(1-\nu)/2$. The unnormalized selected weights become

$$
\begin{aligned}
p_{S,\nu}&=\nu p_S+(1-\nu)p_P/2,&
g_{S,\nu}&=\nu g_S+(1-\nu)g_P/2,\\
p_{O,\nu}&=\nu p_O+(1-\nu)p_P/2,&
g_{O,\nu}&=(1+\nu)g_P/2.
\end{aligned}
\tag{FP7}
$$

Their yield difference is $\nu(p_O-p_S)$. Their conditional-fidelity
cross numerator is $\nu^2C+\nu(1-\nu)D/2$, where
$C=g_Pp_S-g_Sp_O\ge0$ is given in (FP6), and

$$
\begin{aligned}
256D=(1-y)^2\{&4(y^6+1)+7(y-1)^2(y^4+1)\\
 &+94(y^4+y^2)+60y^3\}\ge0.
\end{aligned}
\tag{FP8}
$$

Here $D=(g_P-g_S)p_P-g_P(p_O-p_S)$. Thus fixed ordinary selection
also dominates the raw identity fidelity with this common final noise.
It does not model noisy controlled gates, bath-correlated helper errors
or arbitrary noncovariant final helper noise.

**Calibrated classical postprocessing simulates both accepted flags.**
There is a stronger complete-output comparison when the noise rate is
calibrated. Choose the echo check uniformly among
$i\gamma_1\gamma_2,i\gamma_1\gamma_3,i\gamma_1\gamma_4$.
Each choice uses the same two controlled-bilinear gates. In the fixed
code these are the three logical Pauli axes. Averaging their instruments
makes each ordinary flag depolarizing, with total weights $p_O,p_P-p_O$
and good weights $g_P,0$. No data-Clifford gates or extra quantum memory
are needed for this averaging; the classical random choice is discarded.

Keep the ordinary plus flag as a synthesized switched minus with
probability $\alpha=g_S/g_P$, and the ordinary minus flag with
$\beta=(p_S-\alpha p_O)/(p_P-p_O)$. At the endpoints choose both zero.
The numerator defining $\beta$ is nonnegative by (FP6). The complementary
constraint follows from

$$
\begin{aligned}
256\{g_P(p_P-p_S-p_O)+g_Sp_O\}
=(1-y)^2\{3y^6+34y^5+13y^4+156y^3+13y^2+34y+3\}\ge0.
\end{aligned}
\tag{FP9}
$$

Hence $0\le\alpha,\beta\le1$. By construction the synthesized flag
has both total weight $p_S$ and good weight $g_S$. Depolarizing logical
qubit CP maps are fixed by these two numbers, so this gives the complete
switched minus code map on every reference-entangled input. The
complement gives the switched plus code map because both sums equal
the same unflagged parity-accepted map. It also reproduces every later
decoder, flag-dependent herald and utility confined to that accepted code
instrument. It does not reproduce the rejected odd-parity quantum output
or the retained reservoir state. It simulates measured classical flags,
not a coherently unmeasured order register.

With the common dephasing in (FP7), replace the probabilities by

$$
\alpha_\nu=\nu\alpha+(1-\nu)(1+\alpha-\beta)/2,\qquad
\beta_\nu=\nu\beta+(1-\nu)(1-\alpha+\beta)/2.
\tag{FP10}
$$

These are convex combinations of numbers in $[0,1]$. Substitution in the
ordinary noisy flag weights gives exactly $p_{S,\nu},g_{S,\nu}$; its
complement again supplies the other switched code map. Thus the
calibrated simulation includes arbitrary downstream code recovery under
this declared helper-noise law. Calibration of $r,\nu$, classical
randomization and the actual three available controlled-parity settings
are real costs. No general efficient experimental learner is asserted.

The ordinary comparison has two occupied poisoning contacts, one coherent
helper, two known controlled-even-bilinear gates, and the same final code
parity readout. A switch additionally needs the actual coherent order
interface. These are resource inventories, not measured fault or latency
equalities. If controlled bilinears are unavailable, their compilation
cannot be imported for free; a native proposal must compare their actual
cost with its router. A stationary coherent selector has the ordinary
chronological comparator already described above. A clean helper that
can directly hold the encoded logical state supplies further ordinary
storage options.

This closes the specified symmetric tetron collision-filter candidate
under the stated ordinary ports. It is not an all-Majorana-noise no-go.
Unequal rates, correlated poisoning, accessible quasiparticle records,
nonvacuum reservoirs, additional Hamiltonian terms and physical timing
records change the model. In particular, emitted early/late reservoir
wavepackets cannot be treated as the same localized mode without their
actual overlap. The formulas favor the switch by retaining ideal bath
coherence; they do not establish that coherence in a device, a full
fermionic-channel SWITCH from reduced maps, or a native architecture gain.

The [microscopic tetron analysis of Bhattacharyya and van Heck](https://arxiv.org/html/2608.18042v1)
includes charging energy, Majorana overlap and thermal lead spectra.
Its transition operators are energy-projected Majoranas, rather than
the homogeneous bare-generator product (FP1). The declared contact model
cannot be silently substituted for that physical master equation. A
surviving application would have to identify its actual coherent bath
history and beat ordinary parity monitoring, accessible quasiparticle
records and production-schedule calibration at matched memory, gate,
reset, discarded-launch and routing costs.

<a id="nr-r06-jc-energy"></a>

### Finite-energy Jaynes--Cummings rotations have a stronger ordinary comparator

[Fellous-Asiani et al., *Phys. Rev. Research* **5**, 023111 (2023)](https://doi.org/10.1103/PhysRevResearch.5.023111)
([complete model and Appendices A, C, E](https://arxiv.org/html/2208.01952v2))
compare a quantum switch with a four-independent-box simulation at fixed
initial photon budget. A coherent-state Jaynes--Cummings interaction
approximates an equatorial atomic rotation; the other gate is ideal.
Their actual equatorial promise admits an ordinary perfect discriminator
in the infinite-energy limit (Appendix E.3), while the headline ordinary
comparison imposes isotropy. Appendix A proposes a four-level atom and
two-mode cavity with an intermediate control flip. It is a proposed
experiment, not an established architecture gain.

The following comparison uses their ordinary isometry and extends its
measurement on the ideal experiment's unused subspace. It proves an
exact finite-energy inequality for the stated prior, without an optimizer.
It preserves the distinct four-box and isotropic comparisons. There is
no priority claim for the published isometry, and no claim that this
diagnostic supplies a new useful gate or a total hardware-cost advantage.

**Promise, actual noise and photon budget.** Write
$\sigma_\phi=\cos\phi X+\sin\phi Y$ and
$\sigma_\perp=\sigma_{\phi+\pi/2}$. The commuting class has ideal
$A=R_\phi(\theta)$, $B=R_\phi(\vartheta)$, with
$\phi,\theta,\vartheta$ independent and uniform on $[-\pi,\pi]$.
The anticommuting class has $A=R_\phi(\pi)$ and
$B=-i(\cos\chi\,\sigma_\perp+\sin\chi\,Z)$, with $\phi,\chi$
uniform on $[-\pi,\pi]$. The two classes have equal prior. The laboratory
energy axis $Z$ is known; the gate parameters are unknown. This is the
physical equatorial prior, rather than a later Haar-twirled prior.

Let $N>0$ be the mean photon number in $A$'s one coherent field. Put
$w_m=e^{-N/2}N^{m/2}/\sqrt{m!}$, $w_{-1}=0$, and $u=\theta/2$.
The complete field-traced Kraus operators for the interaction time
$t=\theta/(\Omega_0\sqrt N)$ are

$$
\begin{aligned}
K_m(\theta,\phi)&=
\begin{pmatrix}
r_m&-i\beta_m e^{-i\phi}\\
-i\gamma_m e^{i\phi}&s_m
\end{pmatrix},\qquad m\ge0,\\
r_m&=w_m\cos\!\left(u\sqrt{m/N}\right),\quad
s_m=w_m\cos\!\left(u\sqrt{(m+1)/N}\right),\\
\beta_m&=w_{m-1}\sin\!\left(u\sqrt{m/N}\right),\quad
\gamma_m=w_{m+1}\sin\!\left(u\sqrt{(m+1)/N}\right).
\end{aligned}
\tag{J1}
$$

Negative angles use the stipulated sign or axis control. No optimized
interaction time is assumed. The field is traced over every $m$;
there is no photon-number postselection. Equivalently,

$$
\begin{aligned}
K_m&=a_mI+b_m\sigma_\phi+c_m\sigma_\perp+d_mZ,\\
a_m&=(r_m+s_m)/2,\quad d_m=(r_m-s_m)/2,\\
b_m&=-i(\beta_m+\gamma_m)/2,\quad
c_m=(\beta_m-\gamma_m)/2.
\end{aligned}
\tag{J2}
$$

Here $a_m,c_m,d_m$ are real and $b_m$ is imaginary. Define
$q_a(\theta)=\sum_m a_m^2$, $q_b(\theta)=\sum_m|b_m|^2$,
$q_c(\theta)=\sum_m c_m^2$, and $q_d(\theta)=\sum_m d_m^2$.
They are independent of $\phi$. Taking half the trace of Kraus
completeness gives $q_a+q_b+q_c+q_d=1$. Angular brackets below denote
the uniform $\theta$ average in the commuting class.

**An explicit ordinary circuit and complete measurement.** Prepare
$|\Phi^+\rangle_{Sb}$, call the one ideal unknown $B$ on $S$, then use
the following known isometry, independent of every unknown parameter:

$$
\begin{aligned}
V|00\rangle&=|\Phi^+\rangle_{Sa_1}|0\rangle_{a_2},&
V|11\rangle&=|\Phi^+\rangle_{Sa_1}|1\rangle_{a_2},\\
V|01\rangle&=|01\rangle_{Sa_1}|2\rangle_{a_2},&
V|10\rangle&=|10\rangle_{Sa_1}|2\rangle_{a_2}.
\end{aligned}
\tag{J3}
$$

Its four images are orthonormal, so it extends to a known unitary after
adjoining an initialized qutrit. Call the single noisy $A$ on $S$ and
measure the two-outcome projective measurement

$$
\begin{aligned}
P_-&=I_{Sa_1}\otimes|-\rangle\langle-|_{a_2}
 +|\Phi^-\rangle\langle\Phi^-|_{Sa_1}\otimes|2\rangle\langle2|_{a_2},\\
P_+&=I-P_-,\qquad |\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2.
\end{aligned}
\tag{J4}
$$

Guess anticommuting on $P_-$. Its summands have orthogonal $a_2$
support; $P_-$ has rank five and its complement rank seven. Assigning
the whole $a_2=-$ block to this guess extends the ideal experiment's
success-one effect onto two unused directions. No unknown query,
intermediate record or rejected attempt is added.

The protocol uses one $B$ and one $A$ call, the same one $A$ field with
mean $N$ photons, and no field readout, refill, inverse or controlled
unknown gate. It requires an initial Bell pair, a known isometry and
joint measurement, one memory qubit after $B$, and a qubit plus qutrit
of memory after $V$ through $A$. Their preparation, native compilation,
energy, storage and readout must be charged in a hardware comparison.
The photon budget concerns the field implementing $A$; it is not a
bound on the energy of all controls or the stipulated ideal $B$.

**Exact ordinary class errors.** Define
$|\Psi_\phi\rangle=(e^{-i\phi}|01\rangle+e^{i\phi}|10\rangle)/\sqrt2$.
Equation (J3) gives
$V|\Phi^+\rangle=|\Phi^+\rangle|+\rangle$,
$V|\Phi^-\rangle=|\Phi^+\rangle|-\rangle$, and
$V|\Psi_\phi\rangle=|\Psi_\phi\rangle|2\rangle$.
For the commuting class, averaging $\vartheta$ removes the sine--cosine
cross terms, giving the pre-$A$ state

$$
\frac12|\Phi^+\rangle\langle\Phi^+|\otimes|+\rangle\langle+|
+\frac12|\Psi_\phi\rangle\langle\Psi_\phi|\otimes|2\rangle\langle2|.
\tag{J5}
$$

The first term never triggers $P_-$, for any noise on $S$. For the
second,
$\langle\Phi^-|(K_m\otimes I)|\Psi_\phi\rangle=-ic_m$.
Consequently the commuting-class error at fixed $\theta$, after the
$B$-angle average, is

$$
e_{\rm com}^{\rm FCO}(\theta)=q_c(\theta)/2.
\tag{J6}
$$

For the anticommuting class, averaging $\chi$ gives the pre-$A$ state

$$
\frac12|\Phi^+\rangle\langle\Phi^+|\otimes|-\rangle\langle-|
+\frac12|\Psi_{\phi+\pi/2}\rangle\langle\Psi_{\phi+\pi/2}|
                 \otimes|2\rangle\langle2|.
\tag{J7}
$$

The first term is always classified correctly, regardless of the
$A$ noise. In the second term the $\Phi^-$ amplitude is $ib_m$,
so its success probability is $q_b(\pi)$. Thus

$$
e_{\rm anti}^{\rm FCO}
=\frac{1-q_b(\pi)}2
=\frac{q_a(\pi)+q_c(\pi)+q_d(\pi)}2.
\tag{J8}
$$

All $\phi$ dependence has canceled before its average. The ordinary
circuit does not require knowing $\phi$. Its complete equal-prior error is

$$
e_{\rm FCO}
=\frac{\langle q_c\rangle+q_a(\pi)+q_c(\pi)+q_d(\pi)}4.
\tag{J9}
$$

**Exact comparison with the specified switch readout.** The switch
prepares a plus control and maximally mixed data, then guesses using
the final control $X$ outcome. Its cross amplitude for Kraus $K_m$
and unitary $B$ is
$\operatorname{Tr}(K_m^\dagger B^\dagger K_mB)/2$.
In the commuting class, $a_mI+b_m\sigma_\phi$ commutes with
$\sigma_\phi$ and $c_m\sigma_\perp+d_mZ$ anticommutes with it.
The uniform $\vartheta$ average and Hilbert--Schmidt orthogonality
remove the cross terms, giving

$$
e_{\rm com}^{\rm QS}(\theta)
=\frac{q_c(\theta)+q_d(\theta)}2.
\tag{J10}
$$

For the anticommuting class, averaging $\chi$ gives equal weights to
the conjugation tests with $\sigma_\perp$ and $Z$. Their errors are
$q_a(\pi)+q_c(\pi)$ and $q_a(\pi)+q_d(\pi)$, respectively:

$$
e_{\rm anti}^{\rm QS}
=q_a(\pi)+\frac{q_c(\pi)+q_d(\pi)}2.
\tag{J11}
$$

Combining (J6)--(J11) proves

$$
p_{\rm FCO}-p_{\rm QS}
=e_{\rm QS}-e_{\rm FCO}
=\frac{\langle q_d\rangle+q_a(\pi)}4\ge0.
\tag{J12}
$$

This holds for every $N>0$ in the complete infinite-Fock-space model,
without numerical truncation or an asymptotic limit. It concerns this
prior and switch strategy, rather than arbitrary priors, both gates
being noisy, an unknown laboratory energy axis, or all possible switch
protocols. The inequality is strict at every finite positive $N$:
the $m=0$ term alone has
$d_0(\theta)^2=e^{-N}[1-\cos(\theta/(2\sqrt N))]^2/4$.
This continuous function is not identically zero on $[-\pi,\pi]$,
so its average is positive. An accidental zero at $\theta=\pi$ does
not affect this argument.

**High-energy behavior and its remainder.** Let $\epsilon=1/N$,
$x=m/N$, and $f_u(x)=\cos(u\sqrt x)$. Then
$d_m=(w_m/2)[f_u(x)-f_u(x+\epsilon)]$.
For $x\ge0$, $|f_u'(x)|\le u^2/2$, including its continuous value
at zero. Therefore $q_d(\theta)\le u^4/(16N^2)$ uniformly on
$|u|\le\pi/2$, and $\langle q_d\rangle=O(N^{-2})$.
At $\theta=\pi$, $f_{\pi/2}(1)=0$ and
$f_{\pi/2}'(1)=-\pi/4$. The Poisson variance gives

$$
q_a(\pi)=\frac{\pi^2}{16N}+O(N^{-2}).
\tag{J13}
$$

To justify the remainder, expand on $|m/N-1|\le1/2$. The centered
Poisson moments are
$\mathbb E(x-1)^2=N^{-1}$,
$\mathbb E(x-1)^3=N^{-2}$, and
$\mathbb E(x-1)^4=3N^{-2}+N^{-3}$.
The relevant derivatives are bounded on this interval, uniformly for
$|u|\le\pi/2$. Outside it the Poisson Chernoff tail is exponentially
small, while cosine is bounded. Taylor expansion through the required
orders therefore yields the stated $O(N^{-2})$ contribution.

The Poisson coefficient ratios also give
$c_m=(w_m/2)[\sqrt x\sin(u\sqrt x)
-\sin(u\sqrt{x+\epsilon})/\sqrt{x+\epsilon}]$.
At $\epsilon=0$ the bracket is
$g_u(x)=(\sqrt x-1/\sqrt x)\sin(u\sqrt x)$, with its continuous
value at zero. It obeys $g_u(1)=0$, $g_u'(1)=\sin u$.
The same central-moment expansion, with exponentially small tails
bounded using the at-most-polynomial growth of this bracket, gives

$$
q_c(\theta)=\frac{\sin^2(\theta/2)}{4N}+O(N^{-2}),\qquad
\langle q_c\rangle=\frac1{8N}+O(N^{-2}),\qquad
q_c(\pi)=\frac1{4N}+O(N^{-2}).
\tag{J14}
$$

Substitution into the exact errors yields

$$
\begin{aligned}
p_{\rm FCO}&=1-\frac{6+\pi^2}{64N}+O(N^{-2}),\\
p_{\rm QS}&=1-\frac{3+\pi^2}{32N}+O(N^{-2}),\\
p_{\rm FCO}-p_{\rm QS}&=\frac{\pi^2}{64N}+O(N^{-2}).
\end{aligned}
\tag{J15}
$$

The switch coefficient agrees with the source's expression (28).
The ordinary coefficient is achieved by the explicit circuit above;
it is not an asserted optimum over all finite-energy ordinary protocols.

**The native selector and the correct dummy interface.** The proposed
four-level-atom experiment supplies a chronological selector
$M=P_0^C\otimes U_{A,SF_A}+P_1^C\otimes U_{B,SF_B}$.
The same two prepared cavity modes persist across both interaction
intervals. A middle control flip and restoring output flip give

$$
X_CM X_CM
=P_0^C\otimes U_BU_A+P_1^C\otimes U_AU_B.
\tag{J16}
$$

This identity holds on both fields and every passive reference, before
field trace or control readout, at any photon budget. It uses the same
two intervals and one prepared field per mode, rather than two
half-energy copies of $A$. It specializes the
[native-selector comparison](backaction.md#nr-r14) to the actual
supplied interaction. It does not construct that selector from
classically selectable opaque channels or invalidate their query
separation. The actual selector, pulses and their faults must be
available and charged to both hardware strategies.

A separate three-window route is possible if a true no-atom sector is
supplied coherently: the cavity acts as $I_F$ on an unoccupied branch
and as $U_{A,SF}$ on an occupied branch. Route the payload through $A$
in the first window on control branch zero and in the third window on
branch one, through $B$ in the middle, and leave $A$ unoccupied in the
other window. Its full result is again the right side of (J16), with
the same one $A$ field and initial energy. Extra coherent delay,
transport, clock phases and free-field evolution are resources; this
extension is not supplied by an abstract qubit Jaynes--Cummings channel.

An atomic ground-state dummy is different. With $B=I$, payload $S=e$,
dummy $T=g$, field $F=0$, and resonant interaction time $\pi/\Omega_0$
(a complete swap on the one-excitation doublet),

$$
U_{A,TF}U_{A,SF}|e,g,0\rangle=-|g,e,0\rangle,\qquad
U_{A,SF}U_{A,TF}|e,g,0\rangle=-i|g,g,1\rangle.
\tag{J17}
$$

The unused $T,F$ outputs are orthogonal. Treating the retained field
as a memoryless unitary oracle in a dummy-based simulation would
therefore dephase its order control, although switching $A$ with $I$
does not. This vacuum-field example is an exact operator counterexample,
not the $N>0$ coherent-drive promise in (J12).

Equation (J16), the conditional no-atom route, and the interacting
atomic dummy are distinct access models. A positive energetic
architecture claim still needs a useful gate or calibration workload
and matched full energy, time, memory, control and readout costs against
the ordinary methods that the physical device actually admits.

<a id="nr-r07"></a>

## NR-R07 — The efficient finite-frame family admits polynomial-query reused calibration

This theorem concerns the local-noise family of NR-R01 with a **fixed
frame reused across outputs**, rather than its original fresh-frame game.
The ordinary baseline retains NR-R01's unrestricted known computation,
ideal known gates and quantum memory. It exposes a query-amortization
limit, not a practical learning-time bound.

### Training states and candidate measurements

A public word of $G=O(n^2)$ nearest-neighbour gates from an alphabet of
size $a$ has at most $M=[a(n-1)]^G$ possibilities. Every candidate $h$
specifies known $A_h,B_h,C_h=iB_hA_h$. Repetitions of the same description
do not matter. The finite-bit sampler may use more bits, but its support
is still contained in this word set.

One training pair uses two ordinary calls and accessible Bell references
to prepare

$$
\sigma=\rho_A\otimes\rho_B,\qquad
\rho_A=\sum_Pw_P\Phi_{PA},\quad
\rho_B=\sum_Qw_Q\Phi_{QB},
$$

where $\Phi_V$ is the normalized unitary Choi projector. Pauli process
vectors are orthonormal. The top eigenvector of $\sigma$ is
$|A\rangle|B\rangle$, with eigenvalue $r=81/100$; every other eigenvalue
is at most $\mu\le3/(100n)$, by the joint Pauli-weight bound in
[NR-R01](theorem.md). For $n\ge8$, its gap is

$$
g=r-\mu\ge129/160.
$$

For $H_h=\Phi_{A_h}\otimes\Phi_{B_h}$, put
$f_h=\operatorname{Tr}(\sigma H_h)$ and
$x_h=F(\Phi_A,\Phi_{A_h})F(\Phi_B,\Phi_{B_h})$.
Spectral domination gives

$$
f_h\le\mu+(r-\mu)x_h.
$$

The true word is included and has $f_h=r$.

Apply the quantum Threshold Search theorem of
[Bădescu and O'Donnell, fixed v4, Theorem 1.1](https://arxiv.org/html/2011.10908v4)
with threshold $r-\xi/2$ and accuracy $\xi/2$. The strict offset ensures
that the true word rules out the permitted “all below threshold” answer.
Except with probability $\delta$, an index with $f_h>r-\xi$ is returned.
The required number $m$ of independent joint copies satisfies

$$
m=O\!\left(
\frac{(\log^2M+\log(1/\delta))\log(1/\delta)}{\xi^2}
\right).
$$

These copies cost exactly $2m$ module calls. At fixed accuracy and
confidence this is polynomial in $n$, of order
$O(n^4\log^2n)$ up to the theorem's constant. The theorem is a sample
bound: enumerating and processing $M$ candidate projectors may take
exponential time. Storage of the copies uses $O(nm)$ qubits.

### From the selected candidate to recovered outputs

On the good event $x_h\ge1-\xi/g$, so each individual fidelity factor
is at least $1-\xi/g$. Pure-state Choi trace distance is
$\sqrt{1-F}$; its triangle inequality and invariance under known
unitary left/right multiplication give

$$
d_{\rm tr}(\Phi_{B_hA_h},\Phi_{BA})\le2\sqrt{\xi/g},
\qquad
F(\Phi_{C_h},\Phi_C)\ge1-4\xi/g.
$$

Known $C_h$ applied to a scrambled payload is a valid always-accepting
ordinary decoder with no further module calls. Including the learning
failure event at the worst possible score $-1$, its mean Bell score is
at least $1-8\xi/g-2\delta$.

Choose $\xi=1/400$, $\delta=1/100$. Then

$$
\mathsf S_{\rm learned}\ge\frac{6161}{6450}
 \approx0.9551938.
$$

For the specified switch, its score is at most its acceptance probability.
Its Haar acceptance is at most $0.905$, and the allowed approximate-source
loss for acceptance is at most $0.0005$. Thus its **actual** mean score
is at most $1811/2000=0.9055$, not just the previously proved lower bound.
The same safe upper bound holds with the specified control dephasing.

### Count training, rejections and repeated use

For $L$ outputs sharing one frame:

- If calibration can precede delivery, spend $2m$ calls once, then decode
  all outputs by known synthesis. For $L\ge m$ this fits the same total
  $2L$ query budget and has the score lower bound above.
- With strict two-call rounds and delivery before the next input, reject
  the first $m$ payloads while collecting one training pair per round.
  Then decode later payloads without module calls. At $L=20m$ the average
  score is at least
  $117059/129000\approx0.9074341>0.9055$.

The sacrificed training payloads and all their calls remain counted.
The learning event is shared by all outputs; linearity of expectation
does not require independent per-output failures. Neither crossover
gives a numerical laboratory call count because the cited theorem
contains asymptotic constants, and its known processing can be expensive.
An explicit fallback tests each candidate separately with Hoeffding
confidence, using
$m=M\lceil2\xi^{-2}\ln(2M/\delta)\rceil$ joint copies.
It has a finite but exponential cost; it does not replace the stronger
collective query baseline.

The current one-output prefix converse cannot be restarted after this
training: initial receiver memory is then correlated with the frame.
The fresh-frame theorem remains valid, including allocation of a total
budget across independent fresh frames. It supplies no persistent-frame
direct-product bound.

### Hardware and metric qualifications

A physical lifetime window must include acquisition time $2m/v$ at
call rate $v$, learning/compilation time, subsequent synthesis and all
desired outputs. Arbitrary drifting training states do not satisfy the
i.i.d. premise of Threshold Search. Drift also changes switch arms
visiting a module at different laboratory times; it cannot selectively
hurt only the ordinary learner by assumption.

This comparison uses the Bell metric of NR-R01. Two balanced target
reflections can differ on only two basis vectors: their Choi fidelity
is $(1-4/D)^2\to1$, while their half-diamond distance is one. Thus the
learning result is not an arbitrary-input error-per-location guarantee.
Nor does an average/Bell score alone make the switch composable for QEC.
Noisy known synthesis and routing need a joint physical cost model.

<a id="nr-r08"></a>

## NR-R08 — Measurement records and syndrome-sector count change the baseline

Let $E(\rho)=\sum_aP_a\rho P_a$ and $F(\rho)=\sum_bQ_b\rho Q_b$ be
repeatable Lüders measurements with outcomes discarded. Ranks may vary.
On $I/D$, the switched control measures

$$
v=\frac1D\sum_{ab}\operatorname{Tr}(P_aQ_bP_aQ_b),
\qquad p_-=\frac{1-v}{2}.
$$

Each summand equals $\operatorname{Tr}[(P_aQ_bP_a)^2]\ge0$.
This concerns measurement-projector compatibility; commuting averaged
channels alone do not imply $v=1$.

### One shared frequency does not automatically provide two unread meters

For elastic dispersive sections driven by the same photon, write their
spatial transformations at frequency $\omega$ as $A(\omega),B(\omega)$.
Tracing frequency after one visit gives, for example,
$E(\rho)=\int p(\omega)A(\omega)\rho A(\omega)^\dagger d\omega$.
The physical two-section channel instead contains the **same-frequency**
average

$$
\Phi(\rho)=\int p(\omega)B(\omega)A(\omega)\rho
 A(\omega)^\dagger B(\omega)^\dagger d\omega.
$$

Composing the individually reduced channels uses two independent frequency
averages. They need not agree. In particular, complete dephasing in each
section does not establish independent unread records or the standard
independent-channel switch of those two marginals.

There is an exact all-dimensional example. Let $E_i=|e_i\rangle\langle e_i|$
and $F_j=|f_j\rangle\langle f_j|$, $0\le i,j<D$, be mutually unbiased
rank-one PVMs, and set

$$
A_\phi=\sum_i e^{-\mathrm i i\phi}E_i,\qquad
B_\phi=\sum_j e^{-\mathrm i j\phi}F_j,\qquad
\phi\sim\operatorname{Unif}[0,2\pi].
$$

Each section separately is a perfect pinching channel. For the joint
process, histories $(i,j)$ and $(k,l)$ have overlap
$1_{i+j=k+l}$. Its joint Gram matrix therefore has $2D-1$ all-ones blocks
of sizes
$m_s=1,2,\ldots,D-1,D,D-1,\ldots,1$. The normalized composed Choi state
has eigenvalues $m_s/D^2$, with $D^2-(2D-1)$ additional zeros; the
independent MUB composition has Choi state $I_{D^2}/D^2$. Since every
$m_s\ge1$, their half trace distance is exactly

$$
\frac12\left\|j_\Phi-\frac{I_{D^2}}{D^2}\right\|_1
=1-\frac{2D-1}{D^2}.
\tag{M1}
$$

Even the control calibration can change. On data input $I/D$, and with
control zero assigned $B_\phi A_\phi$, its off-diagonal coherence factor is
$v=D^{-1}\int\operatorname{Tr}[(A_\phi B_\phi)^\dagger
B_\phi A_\phi]\,d\phi/(2\pi)$. Computational/Fourier bases give
$v=1/4$ at $D=2$, hence $p_{X,-}=3/8$ rather than the independent-channel
value $1/4$. At $D=4$, using Fourier entries $e^{2\pi irj/4}/2$, they give
$v=(24+20i)/64$ and $p_{X,-}=5/16$, rather than $v=1/4$ and $p_{X,-}=3/8$.
Exchanging the order or Fourier convention conjugates the complex value.
These quoted coherences use $I/D$; a general input can change their
imaginary part. The exact replay verifies the full marginal and composed
Choi matrices, not only this scalar diagnostic.

### A quantitative bandwidth--delay cost for independent delay records

The shared-frequency mechanism can also implement two independent meters
if its **joint** records have sufficient capacity. The following bound
specifies that cost for controlled delays; it is not a general fiber or
channel-implementation impossibility theorem.

Take a normalized source wavefunction $f(\omega)$ with spectral support in
$[\omega_c-B/2,\omega_c+B/2]$. Here $B$ is angular-frequency **hard support
width**, not a full width at half maximum or a reported $-20$ dB bandwidth.
Assume $D\ge2$ and $B>0$.
Let $\Omega|\omega\rangle=\omega|\omega\rangle$ be the frequency operator.
The delayed states and the two controlled interactions are

$$
|\eta_\tau\rangle=\int f(\omega)e^{-i\omega\tau}|\omega\rangle d\omega,
\quad
U_A=\sum_i E_i\otimes e^{-i\Omega a_i},\quad
U_B=\sum_j F_j\otimes e^{-i\Omega b_j}.
\tag{M2}
$$

The source is initially independent of data and its passive reference.
The same frequency register is retained between layers, with no extra
independent label record. Write $\tau_{ij}=a_i+b_j$ and let
$T=\max_{ij}\tau_{ij}-\min_{ij}\tau_{ij}$; shift all delays so they lie in
$[0,T]$. This shift is an environment unitary and changes no channel.
$T$ is a maximum relative controlled delay or record extent, not
automatically the single-shot wall time of a stationary stream.

Put $M=D^2$ and $K_{ji}=F_jE_i$. Mutual unbiasedness gives
$\operatorname{Tr}(K_{lk}^\dagger K_{ji})=
\delta_{ik}\delta_{jl}/D$. Thus the vectors
$|u_{ij}\rangle=\sqrt D\,\operatorname{vec}(K_{ji})$ form an orthonormal
basis, where $\operatorname{vec}$ is unnormalized. Acting on a normalized
maximally entangled input gives the exact purification

$$
|J\rangle=\frac1{\sqrt M}\sum_{ij}
 |u_{ij}\rangle|\eta_{\tau_{ij}}\rangle.
\tag{M3}
$$

Consequently the normalized data Choi spectrum is the joint Gram spectrum
divided by $M$, and equals the nonzero spectrum of
$\Xi=M^{-1}\sum_{ij}|\eta_{\tau_{ij}}\rangle
\langle\eta_{\tau_{ij}}|$. The independent MUB composition is completely
depolarizing, $\Omega_D(X)=\operatorname{Tr}(X)I/D$, with Choi state $I_M/M$.
It is realized **exactly if and only if the full $M$-state joint Gram
matrix is $I_M$**. Orthogonal $D$-state records for each layer separately
do not suffice, as (M1) illustrates.

For two delays separated by $h$, removing the central-frequency phase gives

$$
\operatorname{Re}\!\left[e^{i\omega_c h}
 \langle\eta_0|\eta_h\rangle\right]
\ge\cos(B|h|/2)>0\qquad(|h|<\pi/B).
$$

Exact orthogonal records must therefore be separated by at least $\pi/B$.
Sorting all $M$ delays proves

$$
BT\ge\pi(D^2-1).
\tag{M4}
$$

This is attainable within a factor two: a rectangular density
$|f(\omega)|^2=1/B$ on the band has overlap
$e^{-i\omega_c h}\operatorname{sinc}(Bh/2)$. With $\Delta=2\pi/B$, choose
$a_i=iD\Delta$ and $b_j=j\Delta$. Then all $D^2$ sums are distinct lattice
points and mutually orthogonal, with $BT=2\pi(D^2-1)$. This ideal spectral
rectangle does not also provide a finite temporal-support pulse or a lossless
delay line. In ordinary-frequency units $B=2\pi\Delta\nu$, (M4) reads
$\Delta\nu T\ge(D^2-1)/2$.

The scaling remains necessary for approximate composition. Let
$\delta=\tfrac12\|\Phi-\Omega_D\|_\diamond$. For every integer $R\ge1$,

$$
\boxed{\quad
\delta\ge1-\frac{R}{D^2}
 -\left[\frac{(BT/4)^R}{R!}\right]^2.
\quad}
\tag{M5}
$$

To prove it, center delay at $\tau_c=T/2$ and put $L=BT/4$. The subspace

$$
\mathcal S_R=\operatorname{span}\{
e^{-i\Omega\tau_c}(\Omega-\omega_c)^k|f\rangle:0\le k<R\}
$$

has dimension at most $R$. Up to a scalar phase, every delay state is
$e^{-i\Omega\tau_c}e^{-i(\Omega-\omega_c)(\tau-\tau_c)}|f\rangle$.
The real-axis integral Taylor remainder obeys
$|e^{-ix}-\sum_{k<R}(-ix)^k/k!|\le|x|^R/R!$, with no $e^{|x|}$ factor.
Since $|x|\le L$, its orthogonal projector $Q_R$ has uniform leakage
$\|(I-Q_R)\eta_\tau\|\le\epsilon_R=L^R/R!$. Therefore
$\operatorname{Tr}(Q_R\Xi)\ge1-\epsilon_R^2$.

The Ky Fan principle and (M3) put at least this much mass in the largest
$R$ eigenvalues of $j_\Phi$. Their projector has probability $R/M$ on
$I_M/M$, so
$\tfrac12\|j_\Phi-I_M/M\|_1\ge1-\epsilon_R^2-R/M$.
The Choi input is allowed in the diamond norm, proving (M5). For $R\ge M$
the displayed lower bound is merely trivial. This argument controls the
whole channel and does not assume entrywise small joint-record overlaps.

For $0<\epsilon\le1/2$, $R!\ge(R/e)^R$ shows that
$R=\lceil\max\{eBT/2,\log_2(1/\epsilon),1\}\rceil$ makes
$\epsilon_R\le\epsilon$. Thus

$$
BT\ge\frac2e\left[D^2(1-\delta-\epsilon^2)
             -\log_2(1/\epsilon)-1\right].
\tag{M6}
$$

For example, $\delta\le1/4$ and $D\ge2$ require
$BT>(D^2-2)/e$: set $\epsilon=1/2$; (M5) forces
$\lceil\max\{eBT/2,1\}\rceil\ge D^2/2$, hence $eBT/2>D^2/2-1$.
The sharper exact bound (M4) and the robust bounds are separate statements;
no optimal approximate time--bandwidth constant is claimed.

An initially mixed source is covered by purifying it once to
$|\Psi\rangle_{ER}$ and replacing $|\eta_\tau\rangle$ by
$(e^{-i\Omega\tau}\otimes I_R)|\Psi\rangle$ everywhere. The same
polynomial orbit has dimension at most $R$, regardless of inert purifier
dimension. If only spectral mass $1-\zeta$ lies in the selected width-$B$
interval, use its band-projected source in $\mathcal S_R$. Orthogonality
of the spectral complement yields the explicit replacement

$$
\delta\ge1-\frac R{D^2}-\zeta
 -(1-\zeta)\left[\frac{(BT/4)^R}{R!}\right]^2.
\tag{M7}
$$

Thus a measured spectral width without a tail-mass guarantee is not the
hard-support premise of (M4)--(M6). For ideal stationary illumination, or a
frequency-diagonal state in a finite frequency-bin model, the local states
$e^{-i\Omega\tau}\rho_Ee^{i\Omega\tau}$ can all
equal $\rho_E$ even though their **purified** overlaps differ. The proof
does not turn such a source into accessible arrival-time labels. A
triggered pure pulse with resolved delays is a different measurement
interface. Independent source resets, additional spatial or polarization
records, non-delay couplings and new per-slot baths require their actual
joint dilation; they are not excluded by this shared-clock theorem.

An input-specific output check is also weaker: every channel (M2) is
random unitary and fixes $I/D$, including at $T=0$. A $D^2$ requirement
cannot follow from that test. It needs the channel/Choi guarantee above.

Real multimode spectral averaging is therefore an instrument question.
[Li, Ryczkowski and Genty](https://doi.org/10.1364/OE.558061) study hundreds
of supported fiber modes using broadband ASE and an ordinary spatial
coherence interferometer. That does not establish hidden rank-one meters,
two independent discarded records or an inaccessible production encoder.
Frequency-resolved or narrowband pilots, native mode preparation and
ordinary coherence/survival tests remain matched comparators. The
[hardware assessment](architecture.md) retains their access, stability,
loss and downstream-task costs; no blanket multimode-fiber no-go or
measured switch advantage follows from (M1)--(M7).

### Stable accessible records give an exact three-call statistic

Prepare $I/D$, perform $E,F,E$, and compare only the first and last
$E$ labels, $I,K$. Direct Lüders probabilities give

$$
\Pr(I=K)=\frac1D\sum_{ab}
\operatorname{Tr}(P_aQ_bP_aQ_bP_a)=v.
$$

No $F$ record, hidden basis, encoder, inverse or quantum memory is needed.
If labels agree output plus; otherwise flip a fair coin. The resulting
minus probability is exactly $(1-v)/2$. Thus a three-call ordinary trial
reproduces the switched calibration bit. Estimating $v$ to additive
$\epsilon$ at confidence $1-\delta$ costs
$O(\epsilon^{-2}\log(1/\delta))$ trials, independent of $D$.
The record-return comparison is already present in the measurement
incompatibility literature, including
[Gao et al.](https://arxiv.org/abs/2208.06210).

Records must be stable and the instrument must be Lüders. Extra hidden
backaction or unreliable labels require their own model. These
qualifications also apply to interpreting the switch signal.

### Protected dimension is not the number of unread sectors

Suppose there are $S\ge2$ equal-rank projectors of rank $m$, $D=Sm$.
The normalized Choi purity is $1/S$ and cross overlap is

$$
\operatorname{Tr}(\rho_E\rho_F)
 =D^{-2}\sum_{ab}[\operatorname{Tr}(P_aQ_b)]^2.
$$

It is $1/S$ for the same PVM and $1/S^2$ if all
$\operatorname{Tr}(P_aQ_b)=D/S^2$.
Two sequential calls $E$ then $F$ on one half of a Bell pair have
exactly this Bell-return probability. Bernstein concentration therefore
distinguishes these two promised overlaps in
$O(S\log(1/\delta))$ trials, independent of the protected rank $m$:
the mean gap is at least $1/(2S)$, variance at most $1/S$, and a
midpoint threshold suffices.

Uniform trace overlap does **not** fix $v$ for degenerate PVMs.
Commuting coordinate measurements $Z_1,Z_2$ on two qubits have uniform
trace overlaps but $v=1$. The stronger condition
$P_aQ_bP_a=P_a/S$, for example MUB measurements on a syndrome factor,
gives $v=1/S$. Treating protected logical dimension as if it were the
rank-one outcome count imports the wrong C6 scaling.

### Even unread balanced binary measurements have a dimension-independent baseline

For traceless Hermitian involutions $P,Q$,
$E_P=(\mathrm{id}+\operatorname{Ad}_P)/2$ and
$E_Q=(\mathrm{id}+\operatorname{Ad}_Q)/2$. Expanding the four projector
terms gives

$$
v=(3+\tau)/4,\quad
\tau=\operatorname{Tr}(PQPQ)/D,\quad p_-=(1-\tau)/8.
$$

There is an ordinary one-call filter for $P$. Keep an input, a Bell pair
and a plus control; coherently swap the input with one Bell half before
and after the call. Project that Bell pair back onto its initial state
and the control onto minus. A Kraus operator $K$ induces

$$
K\longmapsto\frac{K-\operatorname{Tr}(K)I/D}{2}.
$$

For Kraus operators $I/\sqrt2,P/\sqrt2$, this kills the identity and
gives exactly the successful map $\operatorname{Ad}_P/8$.
It is valid on entangled inputs and has input-independent success.

Apply four such filters in the fixed sequence $P,Q,P,Q$. An outer
control routes all four through the payload in one branch, and the two
$P$ calls through one dummy and two $Q$ calls through another in the
other branch. The dummies return to their initial states because
$P^2=Q^2=I$. A Hadamard test on the outer control and maximally mixed
payload measures $\tau$. All four filter successes occur with
probability $1/4096$. Charging rejected trials gives at most $16384$
expected calls per retained scalar sample, or $4680$ with early abort.
Fixed-budget concentration is also possible. The constants are large,
but independent of $D$; there is no rank-one C6-style exponential
scaling for this binary scalar problem. This filter does not provide
free retries on a unique data payload or a high-yield recovery channel.

### A three-call heralded simulator reproduces the full balanced-binary switch

The same filter gives a stronger ordinary baseline than a scalar estimator.
For memoryless $E_P,E_Q$ with fixed traceless Hermitian involutions $P,Q$,
there is an ordinary instrument using at most **three total calls** whose
successful subchannel is exactly

$$
\mathcal S_{\rm success}=\frac4{529}\,\mathsf{Switch}(E_P,E_Q).
$$

This equality retains the input order control, arbitrary data and every
entangled reference. No commutation promise or knowledge of $P,Q$ is needed.
Put

$$
W_{P,Q}=|0\rangle\langle0|\otimes QP+
        |1\rangle\langle1|\otimes PQ.
$$

Kraus invariance permits using $\{I/\sqrt2,P/\sqrt2\}$ and
$\{I/\sqrt2,Q/\sqrt2\}$ for the unread Lüders channels, giving the full
channel identity

$$
\mathsf{Switch}(E_P,E_Q)=\frac14\left[
\operatorname{Ad}_I+\operatorname{Ad}_{I_C\otimes P}
+\operatorname{Ad}_{I_C\otimes Q}+\operatorname{Ad}_{W_{P,Q}}\right].
$$

The four components have ordinary heralded implementations with respective
success probabilities $1,1/8,1/8,1/512$. The middle two use the one-call
filter above. For the last, extract $P,Q,P$ in that fixed slot order and
use the three-call unitary routing described earlier: the first $P$ acts
on data in control branch zero and a dummy in branch one; the final $P$
uses the opposite routing, while $Q$ acts on data. The joint unitary is
$W_{P,Q}\otimes P_{\rm dummy}$. The dummy therefore factors identically
in both control branches and can be discarded. Each successful filter
has Choi rank one, so its environment also factors independently of the
entire query input; it leaves no hidden route record on success. This
justifies composition on control-data-reference entanglement, not merely
on classical control values.

Choose these four classical branches with probabilities
$(1,8,8,512)/529$ and discard the branch label. Each successful component
then has weight $1/529$, proving the claimed full-channel submap and its
input-independent success $p=4/529$. Known swaps are coherently controlled;
the unknown module identity is never selected coherently. Abort the
three-filter branch at its first failed filter. With $t=1/8$, the exact
expected module-call count is

$$
c=\frac{8+8+512(1+t+t^2)}{529}=\frac{600}{529},
\qquad \frac cp=150.
$$

The ratio is a cost per retained output across fresh supplied inputs.
Failures can destroy an irreplaceable payload, so they cannot be retried
freely on that same state. The failure instrument is not a simulation
of the switch. The proof requires fresh memoryless calls to the same
$P,Q$, clean known routing and Bell ancillas; equal one-call marginals of
a shared or drifting bath do not suffice.

For comparison, the known universal teleportation-based postselected
simulator uses one call per arbitrary channel with success $1/D^2$
([Chiribella et al.](https://doi.org/10.1103/PhysRevA.88.022318);
[later explicit comparison](https://www.nature.com/articles/s41467-025-64996-6)).
The structured three-call bound above is dimension independent, but it
does not settle deterministic, two-call or high-yield performance, or
establish a hardware-runtime advantage.

### Recorded parity measurements already give a deterministic elementary braid

The binary baseline also matters for measurement-only Majorana computation.
Consider ideal repeatable parity measurements of known Hermitian involutions
$P,Q$ with $PQ=-QP$. Write
$\Pi_s=(I+sP)/2$, $\Theta_t=(I+tQ)/2$, $s,t\in\{\pm1\}$, and
$R=QP$, so $R^\dagger=-R$ and $R^2=-I$. Prepare the order control in
plus and measure it in the $X$ basis. If both native parity records are
retained, the complete instrument has Kraus operators

$$
N_{st,-}=\frac{\Theta_t\Pi_s-\Pi_s\Theta_t}{2}
          =\frac{stR}{4},\qquad
N_{st,+}=\frac{\Theta_t\Pi_s+\Pi_s\Theta_t}{2}
          =\frac{I+sP+tQ}{4}.
$$

Thus minus has total probability $1/4$ and applies the known Pauli/parity
$R$. It is not the elementary braid $U_+=(I+R)/\sqrt2$.
For example, $P=i\gamma_a\gamma_b$ and $Q=i\gamma_b\gamma_c$ give
$R=\gamma_a\gamma_c=U_+^2$, up to the convention for braid orientation.
On unrestricted inputs the plus records are not harmless retries:
$N_{st,+}^\dagger N_{st,+}=(3I+2sP+2tQ)/16$ depends on the input.
If both native records are discarded, the full switch instead has the
particularly simple channel identity

$$
\mathsf{Switch}(E_P,E_Q)=\frac14\left[
\operatorname{Ad}_{I}+\operatorname{Ad}_{I_C\otimes P}
+\operatorname{Ad}_{I_C\otimes Q}+\operatorname{Ad}_{Z_C\otimes R}
\right].
$$

This is an identity on the entire control-data-reference input. With a
fresh independent control and control-only postselection, it yields a
mixture of the known parity operations, not a coherent $I\pm R$ braid.
Retaining native outcomes is a different instrument and is covered by
the explicit $N_{st,\pm}$ above.

A standard initialized measurement ancilla can change the conditional
logical action, but supplies a stronger ordinary comparator at the same
time. Let a known ancilla parity $S$ anticommute with both $P,Q$, and
start in $S_+=(I+S)/2$. Then $[S,R]=0$; assume $R$ is non-scalar on
this code when asking for a nontrivial logical braid. Measure $S$ after the switch,
writing $S_-=(I-S)/2$. The four types of record branch, restricted to
the initial code, are

$$
\begin{array}{c|c|c|c}
\text{control}&\text{final }S& S_uN_{st,m}S_+&
 \text{probability summed over }s,t\\\hline
+&+&S_+/4&1/4\\
-&+&stR S_+/4&1/4\\
+&-&sP(I-stR)S_+/4&1/2\\
-&-&0&0.
\end{array}
$$

The last nonzero row is an elementary braid
$U_{-st}=(I-stR)/\sqrt2$ after accounting for the known syndrome-transfer
frame $P$. Opposite orientations differ by the Pauli $R$, since
$R U_-=U_+$. Every probability in this table is input independent,
including for inputs entangled with a reference. The first two rows
leave the data unchanged up to a known Pauli and return the ancilla to
$S_+$. Consequently this particular scheme admits valid retries: its
braid success probability is $1/2$ per attempt, with mean two attempts.
If every attempt uses the two switched parity measurements, one final $S$
measurement, and one order-control readout, its mean cost is
**six parity measurements and two control readouts**, with the ancilla
initialization charged separately to both schemes. Reading the control
first allows skipping $S$ on the minus branch, which is already known to
remain in $S_+$. This reduces the per-attempt parity count to
$2+3/4=11/4$, hence the mean to $11/2$ per successful braid; the mean
two control readouts is unchanged. Both switch versions also require
mean two order-control preparations/resets, which the ordinary sequence
does not use.

An ordinary sequence $P,Q,S$ already implements the braid deterministically
up to the same Pauli/syndrome bookkeeping. Its eight outcome branches are

$$
S_+\Theta_t\Pi_s S_+=\frac{(I+stR)S_+}{4},\qquad
S_-\Theta_t\Pi_s S_+=\frac{sP(I-stR)S_+}{4}.
$$

Each has probability $1/8$. After the known final syndrome frame, each
is $U_+$ or $U_-$, and their difference is tracked by $R$. This costs
**three parity measurements**, with no retry or order-control readout.
The fixed three-measurement, software-corrected baseline is established
by [Zheng, Dua and Jiang](https://doi.org/10.1088/1367-2630/aa50bb)
([explicit protocol and software corrections, Sections II--III](https://arxiv.org/html/1607.07475v2));
it supersedes a comparison solely with the earlier forced-measurement
repeat-until-success scheme. Geometry-dependent measurement costs and
Majorana-Pauli tracking must also be included in a hardware comparison;
see [Tran et al.](https://doi.org/10.21468/SciPostPhys.8.6.091).

The comparison accepts a classically known Pauli and syndrome frame as
the output convention for both protocols. If a fixed physical frame is
required, its correction or reset must be charged to both; software
tracking is not a physical recovery operation. Neither count includes
unmodelled detector faults, loss or readout latency. Every failed switch
attempt is included in both retry expectations above. A native
coherent-order interface must also be supplied: stationary Majorana data
need coherently ordered parity-measurement couplings with device-labelled
records and no surviving environmental order/timing record. Merely routing
a readout probe through two stations does not establish that interface
for overlapping parity measurements on the same data. Ordinary coherent
probe/ancilla operations available at that interface belong in the
matched comparator as well. These identities exclude an ideal gate-count
advantage for the specified balanced $X$-readout construction; they are
not an optimization over every coherent-control protocol or a hardware
runtime/noise no-go theorem.

### Compatibility is not logical correctness

An unwanted measurement of a logical $Z$ commutes with all stabilizer
projectors while destroying a logical plus state. Relabelling a correct
syndrome PVM also leaves its channel and switch signal unchanged while
potentially changing a decoder's action. Consequently zero switch
incompatibility alone cannot certify logical information preservation
or agreement of syndrome dictionaries.

<a id="nr-r08-material-pointer-clock"></a>

### Material-pointer mode dephasing needs a joint clock and ordinary controls

**A primitive-backed array, rather than a demonstrated high-dimensional box.**
[Reiserer, Ritter and Rempe, Science **342**, 1349 (2013)](https://doi.org/10.1126/science.1246164)
([primary full text](https://arxiv.org/pdf/1311.3625)) demonstrate the binary
write primitive: cavity reflection conditionally changes an atom's
superposition phase, followed by an atomic rotation and fluorescence
readout. Their faint-pulse characterization reports $74\%$ detection
efficiency and $66\%$ photon survival. These are detector figures, not a
complete arbitrary-input instrument for an array. The microwave
[Kono et al. experiment](https://doi.org/10.1038/s41567-018-0066-3)
([full text](https://arxiv.org/pdf/1711.05479)) implements the corresponding
photon/transmon conditional phase, reporting detection efficiency $0.84$
and survival $0.87$. Its phase condition requires the pulse spectrum to
fit inside the cavity bandwidth. Neither experiment demonstrates two
independently routed rank-$d$ unread meters with hidden bases.

Here is an explicit ideal extension to test. Let $D$ contain one photon
in $d$ orthogonal paths, with one cavity/atom cell per path. Prepare the
atoms in $|+\rangle^{\otimes d}$. An occupied cell applies $Z_j$ to its
atom; vacuum cells act as identity. For an actual input $U^\dagger$/output
$U$ mode encoder, the joint unitary on the one-photon code is

$$
W_U=\sum_{j=1}^d P_j^U\otimes Z_j,
\qquad P_j^U=U|j\rangle\langle j|U^\dagger,
\qquad
W_U|\psi\rangle|+\rangle^{\otimes d}
 =\sum_j P_j^U|\psi\rangle|e_j\rangle.
\tag{MC1}
$$

Orthogonality of the $P_j^U$ and $Z_j^2=I$ give $W_U^\dagger W_U=I$.
The state $e_j$ has $| -\rangle$ in cell $j$ and $|+\rangle$ elsewhere.
For $i\ne j$ a differing cell has zero inner product, so
$\langle e_i|e_j\rangle=\delta_{ij}$. Tracing the atoms therefore gives
the rank-$d$ Lüders channel $\Delta_U$. This is a material record, not
a frozen classical phase setting or a trace over the photon's one shared
frequency. The ideal extension obeys
$W_U(|\mathrm{vac}\rangle\otimes|a\rangle)
=|\mathrm{vac}\rangle\otimes|a\rangle$ for every pointer state $a$.
Whether the real empty apparatus has that action is a separate test.

With distinct arrays $E_A,E_B$ and projectors $P_i,Q_j$, the joint
pointer family $\{e_i\otimes f_j\}_{i,j}$ is orthonormal with $d^2$
labels. In the common ideal pointer frame the switched write is

$$
|\psi\rangle\longmapsto\frac1{\sqrt2}\sum_{ij}
\left(|0\rangle Q_jP_i|\psi\rangle
     +|1\rangle P_iQ_j|\psi\rangle\right)
       |e_i\rangle_{E_A}|f_j\rangle_{E_B}.
\tag{MC2}
$$

This establishes the required *record capacity*, not the rank of every
particular output state: SAME inputs can occupy fewer joint labels.
The direct two-module construction uses $2d$ material pointers and $d$
cavity cells per module. A photon occupies one cell in each module,
while array preparation, pumps, calibration and reset remain charged.
An abstract record needs only $\log_2d$ bits per module; compressing this
physical construction needs its actual additional gates and interactions.
The encoders, their inverses and matrix knowledge are also access. Known
mesh settings already supply ordinary pointer preparation/decoding.
Unknown drift needs a physical joint law; mode count gives neither a
Haar prior nor a SAME/MUB promise.

**Which-mode records do not determine the order-history records.** Let
$e_i^r,f_j^r$ be the complete final records when the respective write
occurs in window $r$, including emitted and reset fields. Assuming the
same projectors in both windows, the control off-diagonal cross map is

$$
\mathcal X(\rho)=\sum_{ijkl}
\langle e_k^{\rm late}|e_i^{\rm early}\rangle
\langle f_l^{\rm early}|f_j^{\rm late}\rangle
 Q_jP_i\rho Q_lP_k.
\tag{MC3}
$$

This follows by multiplying the two branch isometries in (MC2) and
tracing the actual records. Orthogonality of different labels *within*
each window does not fix these cross-window inner products. For example,
fresh pointer arrays in the two windows have states
$e_i\otimes e_0$ versus $e_0\otimes e_i$, with $e_0=|+\rangle^{\otimes d}$.
Since $\langle e_0|e_i\rangle=0$, the histories are orthogonal although
each isolated reduced channel is the exact desired dephaser. Disjoint
early/late fluorescence can do the same. Delaying a classical timestamp
does not erase an emitted record. Holding the same atoms until a common
readout can avoid this example only with the appropriate full spin,
apparatus and field dynamics.

**An exact three-window ordinary compiler at a common finish.** The
following is a sufficient native-access model. Let $F(t,0)$ be the
route-independent idle evolution of the complete target, apparatus and
field system. Keep the order control in a fixed or coherently compensated
path frame. A vacuum/bypass opportunity contributes only that idle
evolution: it triggers no separate preparation, read/reset or slot
record. Let $G_A(t),G_B(t)$ be the actual occupied pulses in this
interaction picture. Finite pulses are allowed by defining each $G$ as
its full propagator relative to the matching idle propagator. These are
physical joint unitaries with every private pointer and reservoir
retained, rather than chosen Kraus representations.

At a common final time $T$, the two-window switch and the ordinary
$A$--$B$--$A$ construction respectively have joint operators

$$
\begin{aligned}
V_S&=F(T,0)\left[
 P_0^C G_B(\tau)G_A(0)+P_1^C G_A(\tau)G_B(0)\right],\\
V_O&=F(T,0)\left[
 P_0^C G_B(\tau)G_A(0)+P_1^C G_A(2\tau)G_B(\tau)\right].
\end{aligned}
\tag{MC4}
$$

To implement the second line, use fixed named windows $A$ at $0$, $B$
at $\tau$, and $A$ at $2\tau$. Route the photon through early $A$ on
$C=0$ and late $A$ on $C=1$, bypassing the other $A$ opportunity as
vacuum. Both histories occupy $B$ in the middle. Thus each history
has two occupied encounters, with one additional global window and
coherent delay. The bypass and surviving order helper are physical
resources beyond channel-only opaque-query access.

If $G_A(2\tau)=G_A(\tau)$ and $G_B(\tau)=G_B(0)$, the two lines of
(MC4) are identical. Time-independent interaction-picture writes are
sufficient; no commutation between $A,B$, basis knowledge, environment
readout or inverse is used. Equality holds on every input/reference
and all private records at that common finish. Appending any common
measurement or future instrument therefore preserves it. This is a
direct full-joint identity, not an inference from equal reduced channels.

The common finish matters: the earlier switch is padded by its actual
idle evolution in (MC4). Earlier readout/reset or extra target/control
storage noise changes the cycle comparison. Spontaneous emission,
window-dependent loss fields, route-dependent idle dynamics and mandatory
fresh resets can violate the premises. Their complete instruments must
be used. A bare single-detector survival number cannot supply this
joint equality or a routing-rate estimate.

There is a conservative robustness version. Set
$\epsilon_A=\|G_A(2\tau)-G_A(\tau)\|$ and
$\epsilon_B=\|G_B(\tau)-G_B(0)\|$ in physical operator norm. Subtracting
the $P_1$ blocks and inserting $G_A(\tau)G_B(\tau)$ gives

$$
\|V_O-V_S\|\le\epsilon_A+\epsilon_B,
\qquad
\frac12\|\mathcal V_O-\mathcal V_S\|_\diamond
 \le\epsilon_A+\epsilon_B.
\tag{MC5}
$$

For the first inequality use the triangle inequality, unitary norms
and the norm of a block-diagonal operator. For the second, purify a
common initial apparatus state. On every pure input/reference the two
output vectors differ by at most the first bound, and their trace
distance is at most that vector norm. Convexity and partial trace give
the channel bound, including any common retained classical instrument.
One-time process tomography and a scalar $T_2$ do not establish the
physical joint-operator mismatch premise.

**The actual noise axis and ordinary pointer echo matter.** For (MC1),
an idle dilation acting only on the pointers/baths and commuting with
every $Z_j$ factors as the common $F$. More generally it must commute
with the full $W_U$, including its data projectors. Atomic energy-basis
$Z$ dephasing can reduce final $X$-readout contrast while leaving this
early/late joint-record relation unchanged. A quoted Ramsey $T_2$ is
therefore not automatically an order-visibility decay constant.

A separate homogeneous example illustrates possible timing costs.
Suppose every label at station $j$ has the same cross-history overlap
$\kappa_j(\Delta)$. The switch samples
$\kappa_A(\tau)\kappa_B(\tau)$, while repeating $A$ or $B$ samples
$\kappa_A(2\tau)$ or $\kappa_B(2\tau)$. For independent Markov records
$\kappa_j(\Delta)=e^{-\gamma_j|\Delta|/2}$, put
$x_j=\kappa_j(\tau)$. Then

$$
\max\{\kappa_A(2\tau),\kappa_B(2\tau)\}
 =\max\{x_A^2,x_B^2\}\ge x_Ax_B.
\tag{MC6}
$$

Indeed the larger of $x_A,x_B$ has square at least their product.
The better repeated station is therefore at least as coherent in this
example; doubling one pointer span alone is not a Markov advantage.
Mode-dependent kernels or correlated noise require the full (MC3).
Identical Gaussian quasistatic kernels
$\kappa(\Delta)=e^{-\sigma^2\Delta^2/2}$ instead give
$e^{-\sigma^2\tau^2}$ for the switch and $e^{-2\sigma^2\tau^2}$ for
either bare repeat. This is a possible raw-coherence margin, not a
useful-task advantage or an empirically justified noise law.

It must also survive ordinary control. If a Hadamard-equivalent write
uses controlled $X_j$ on energy-basis pointers, and idle uncertainty is
$H=\sum_j\xi_jZ_j$ with static unknown real $\xi_j$, the global pointer
pulse $R=\prod_jX_j$ satisfies
$[R,X_j]=0$ and $RHR=-H$. Hence

$$
R e^{-iH\tau}R e^{-iH\tau}=I.
\tag{MC7}
$$

A midpoint pulse and a restored or tracked final pointer frame refocus
the repeated station's interval without learning the photon basis or
label. Moving an endpoint write past $R$ is valid by the displayed
commutator. Exactness uses separated ideal writes/control pulses, or
actual complete pulse propagators satisfying those relations. Finite
simultaneous noisy write dynamics, pulse errors, duration and
state-dependent survival need their own bounds. This is a serious
ordinary comparator, not a claim that laboratory echo is free or perfect.

**A bounded physical next test.** Actual many-mode count and actual
measurement backaction are distinct evidence.
[Chakram et al.](https://doi.org/10.1038/s41567-022-01630-y)
([full text](https://arxiv.org/pdf/2010.15292)) demonstrate nine stored
cavity modes, dispersive number-dependent transmon shifts and two/three-mode
single-photon superpositions, rather than a complete which-mode instrument.
[Essig et al.](https://doi.org/10.1103/PhysRevX.11.031045)
([full text](https://arxiv.org/pdf/2001.03217)) measure fluorescence
backaction for Fock labels $0$ through $8$ of one oscillator. Their
proof-of-principle experiment did not achieve single-shot number
discrimination; those nine labels are not one photon in nine modes.
Neither source supplies the complete two-module interface above.

Start with $d\ge3$ on a declared one-photon code. Measure within-history
record Gram matrices, survival/leakage, accessible outcomes and the
early/late cross maps at $\tau$ and $2\tau$, including actual vacuum
action. Compare a held-out modal-retention/alignment decision with
native pointer encoding/decoding, the stable-record three-call estimator
above, bright or weak pilots in their valid photon-number regime,
amortized calibration, both three-window orders and available pointer
echo. Freeze controls after a fixed training budget and charge source
and control energy, pointer preparation/reset, memory, routing loss,
every rejected attempt and mean completion time. Excluding readable
material records needs a physical reason. A remaining finite benefit
must arise from a measured task/noise/cost regime, not an imposed reset
deadline or a Haar assumption inferred from mode count.

The [material-pointer clock replay](checks/architecture/material_pointer_clock.py)
checks finite exact array isometries, record orthogonality, a fresh-clock
counterexample and formal echo/timing identities. The universal clock,
norm and physical-interface arguments remain the proofs above. No
native advantage, general measurement-switch simulator or new priority
claim follows from the construction.

<a id="nr-r08-mechanical-record-strength"></a>

### Mechanical record rank and useful meter strength

A harmonic material pointer gives a concrete way to test the strength
premise in (MC1), independently of the clock premise in (MC3). At one
station take $d$ independent oscillators initially in identical thermal
states $\theta_{\bar n}$ and the declared occupied write

$$
W_U=\sum_{j=1}^d P_j^U\otimes D_j(\alpha),\qquad
A=|\alpha|^2,\qquad
\operatorname{tr}[\theta_{\bar n}D(z)]
 =e^{-(\bar n+1/2)|z|^2}.
\tag{MW1}
$$

Vacuum triggers no force. This is an explicit controlled-displacement
model, rather than a deduction from a driven polariton's coupling rate.
For $i\ne j$, the two displacement factors act on different cells.
Tracing the pointers therefore gives the exact channel

$$
\mathcal E_U=r\,\mathrm{Id}+(1-r)\Delta_U,
\qquad r=e^{-(2\bar n+1)A}.
\tag{MW2}
$$

For a purification of the initial thermal state, the $d$ final record
vectors have Gram matrix $(1-r)I+rJ$. Its eigenvalues are
$1+(d-1)r$ and $1-r$ with multiplicity $d-1$. Thus any $A>0$ gives
rank $d$, even when the channel is arbitrarily close to identity.
The dimension of a nonzero record span does not certify strong pinching.

There is an exact error certificate, independent of basis knowledge:

$$
\frac12\|\mathcal E_U-\Delta_U\|_\diamond
 =r(1-1/d),\qquad
\frac12\|\mathcal E_U-\mathrm{Id}\|_\diamond
 =(1-r)(1-1/d).
\tag{MW3}
$$

For the lower bound, apply $\mathrm{Id}-\Delta_U$ to half a maximally
entangled state. Its nonzero eigenvalues are $1-1/d$ and $-1/d$ with
multiplicity $d-1$. For the upper bound, let $Z_U$ have the distinct
$d$th-root phases in the unknown basis. The mathematical identity
$\Delta_U=d^{-1}\sum_{k=0}^{d-1}\operatorname{Ad}(Z_U^k)$ gives

$$
\mathrm{Id}-\Delta_U
 =(1-1/d)\left[\mathrm{Id}
 -\frac1{d-1}\sum_{k=1}^{d-1}\operatorname{Ad}(Z_U^k)\right].
$$

The diamond norm of the difference of two channels is at most two.
Scaling by $r$ or $1-r$ proves (MW3). This proof does not grant an
executable unknown $Z_U$. In particular, half-diamond accuracy
$\epsilon<1-1/d$ to a complete dephaser requires
$A\ge\log[(1-1/d)/\epsilon]/(2\bar n+1)$.

**A complete serial benchmark at weak strength.** Suppose both slots
really supply the independent, common-frame standard channel-switch
interface, with $\mathcal E_j=r_j\mathrm{Id}+p_j\Delta_j$ and
$p_j=1-r_j$. This additional interface is tested by the
[cross-history clock calculation below](#nr-r08-mechanical-clock);
it does not follow from (MW2). Retain an arbitrary input order helper
$C$, target and reference. Multilinearity of the switch gives

$$
\mathfrak S(\mathcal E_A,\mathcal E_B)
 -\mathrm{Id}_C\otimes(\mathcal E_B\circ\mathcal E_A)
 =p_Ap_B\left[
 \mathfrak S(\Delta_A,\Delta_B)
 -\mathrm{Id}_C\otimes(\Delta_B\circ\Delta_A)\right].
\tag{MW4}
$$

Indeed, in the other three terms of the expansion at least one slot is
identity. Both causal words then agree, including every control
off-diagonal, so that term equals the corresponding serial channel
with the helper unchanged. Both maps in the final bracket are channels;
hence the half-diamond distance in (MW4) is at most $p_Ap_B$.
Any fixed bounded linear task reward changes by at most $p_Ap_B$ per
launch compared with this achievable two-call ordinary experiment.
Optimizing its receiver only strengthens the ordinary baseline.
The statement includes subsequent herald records and charges their
probability; conditioning on rare events cannot remove their yield.
It is an absolute reward bound, not a relative rate, adaptive-stopping,
capacity or unrestricted optimality theorem. Additional routing and
control errors need their actual instruments.

For input $I/d$ and an independent helper $|+\rangle$, write
$v=d^{-1}\sum_{ij}|\langle u_i|v_j\rangle|^4$. Then

$$
q_- =\frac{p_Ap_B}{2}(1-v).
\tag{MW5}
$$

The SAME promise gives zero, while MUB gives
$p_Ap_B(1-1/d)/2$. For exactly independent launches with no dark counts,
the explicit receiver declaring MUB on the first minus has miss
probability $(1-q_-)^N$ and zero SAME error. Its required launch count
is $\lceil\log\delta/\log(1-q_-)\rceil$ for miss at most $\delta$,
when $0<q_-<1$. This is an achievable receiver's cost, not a lower bound
on every strategy. If a separately established control-dephasing model
multiplies all cross blocks by real $\nu\in[0,1]$, the two probabilities
become $(1-\nu)/2$ and
$(1-\nu)/2+\nu p_Ap_B(1-1/d)/2$. Background calibration and drift then
matter as well as raw minus counts. Physical clock kernels generally
need more than this single scalar.

**A bounded passive one-photon force example.** For a photon held
uninterrupted under $H/\hbar=\Omega b^\dagger b+
g n_{\mathrm{ph}}(b+b^\dagger)$, exact forced-oscillator evolution gives
$\alpha(t)=(g/\Omega)(1-e^{-i\Omega t})$ up to sign convention,
common rotation and the known one-photon phase. Thus
$A\le4(g/\Omega)^2$. At zero temperature and nominal $g/\Omega=1/25$,

$$
p\le1-e^{-4/625}<4/625,\qquad
p_Ap_B<16/390625=0.00004096.
\tag{MW6}
$$

Even granting a perfect switch interface, the infinite-$d$ MUB-minus
probability is then below $8/390625$ per launch. This fixed-sign,
single uninterrupted-force guard excludes resonant modulation, repeated
passages, bright displacement and nonlinear amplification. Hot pointers
change $(2\bar n+1)A$ and cannot inherit the zero-temperature numbers.
Photon escape, pulse shape and collection also require a complete
input-output model; a loaded cavity linewidth is not by itself a
travelling-photon loss probability.

[Bera et al., Nature Communications **15**, 7115 (2024)](https://doi.org/10.1038/s41467-024-51499-z)
([primary model and supplement](https://arxiv.org/html/2309.06765v2))
report a polariton coupling ratio near $0.04$ and driven instabilities.
They do not demonstrate the preserved-photon array (MW1).
The number in (MW6) only illustrates the passive ground-state model at
that nominal ratio. The actual operating point's temperature, loading,
ports and drive must be measured together.
[Sekatski, Aspelmeyer and Sangouard, PRL **112**, 080502 (2014)](https://arxiv.org/abs/1401.2357)
propose bright displaced-light enhancement of weak single-photon
optomechanics; that state, optical energy and control interface require
a different instrument. Partial monitoring maps and their switched
control-noise behavior are already studied by
[Molitor et al., Communications Physics **7**, 373 (2024)](https://arxiv.org/abs/2405.09631).
These identities do not establish new priority or a native application.

The [exact partial-meter replay](checks/architecture/mechanical_pointer_strength.py)
tests complete finite control-matrix blocks, Gram/Choi witnesses and
SAME/MUB laws. The thermal oscillator, all-dimensional norm, statistical
and physical-interface arguments are the proofs above.

<a id="nr-r08-mechanical-clock"></a>

### Mechanical material pointers: complete clock records and ordinary controls

The preceding partial-dephaser calculation assumes a standard switch of two
independent common-frame channel slots. A mechanical material pointer needs
its actual two-history instrument. The following conditional model supplies
that calculation and concrete ordinary controls; it establishes no native
advantage.

**Closed harmonic pointers at a common finish.** Let $P_i$ be station $A$'s
photon basis projectors, with one independent oscillator per label, and define

$$
W_A=\sum_i P_i\otimes D_i(\alpha),\qquad
D(v)=e^{v b^\dagger-v^*b},\qquad a=|\alpha|^2.
\tag{MP1}
$$

Vacuum triggers no force. Station $B$ has projectors $Q_j$ and an independent
pointer array. Each oscillator initially has thermal state $\theta_n$, with
$\operatorname{tr}[\theta_nD(v)]=e^{-(n+1/2)|v|^2}$. Its purification remains
part of the private record. For idle evolution $R(t)=e^{-i\Omega tN}$ and a
common finish $T$,

$$
R(T-t)D_i(\alpha)R(t)
 =R(T)D_i(\alpha e^{i\Omega t}).
\tag{MP2}
$$

Thus a kick at $t$ writes the interaction-picture displacement
$v_i(t)=\alpha e^{i\Omega t}e_i$. The common $R(T)$ cancels from record inner
products; the early/late rotation does not. For purified records $r_i(t)$,
the Weyl law $D(-w)D(v)=e^{i\operatorname{Im}(w^\dagger v)}D(v-w)$ gives

$$
\begin{aligned}
K_{ik}(t,s)&=\langle r_k(s)|r_i(t)\rangle\\
 &=e^{i\operatorname{Im}[v_k(s)^\dagger v_i(t)]}
   e^{-(n+1/2)\|v_i(t)-v_k(s)\|^2}\\
 &=q+[\kappa(t-s)-q]\delta_{ik},\\
q&=e^{-(2n+1)a},\\
\kappa(\Delta)&=
 e^{ia\sin(\Omega\Delta)-(2n+1)a[1-\cos(\Omega\Delta)]}.
\end{aligned}
\tag{MP3}
$$

Different labels use different material cells, so their overlap is $q$ even
across times in this isotropic closed model. The same-label clock contains
both distinguishability and a Weyl phase. At finite $q$ the complete
instrument is consequently not an orthogonal-record dephaser times one
scalar visibility.

Writing the two order isometries and tracing their actual records gives the
switch's control off-diagonal map and the three-window ordinary route's map:

$$
\begin{aligned}
\mathcal X_S(\rho)
 &=\sum_{ijkl}K^A_{ik}(0,\tau)K^B_{jl}(\tau,0)
                  Q_jP_i\rho Q_lP_k,\\
\mathcal X_O(\rho)
 &=\sum_{ijkl}K^A_{ik}(0,2\tau)K^B_{jl}(\tau,\tau)
                  Q_jP_i\rho Q_lP_k.
\end{aligned}
\tag{MP4}
$$

The ordinary route occupies early $A$ on one helper branch and late $A$ on
the other, with $B$ occupied in the middle on both branches. Both diagonal
control blocks have the same respective one-use channels in this closed
stationary thermal model. Together with those blocks, (MP4) specifies the
full target/helper channel on arbitrary reference inputs and hence every
later common measurement. For negligible $q$, the equal-label factors reduce
to $\kappa_A(-\tau)\kappa_B(\tau)$ versus $\kappa_A(-2\tau)$. This limit
neither removes finite-$q$ terms nor optimizes an ordinary processor.

**Readable mechanics and thermal purification are distinct records.** For
two displaced thermal states the root fidelity is

$$
F_{\rm root}\bigl(D(v)\theta_nD(v)^\dagger,
                  D(w)\theta_nD(w)^\dagger\bigr)
 =e^{-\|v-w\|^2/[2(2n+1)]}.
\tag{MP5}
$$

This is the equal-covariance displacement specialization of the Gaussian
fidelity formula of [Banchi, Braunstein and Pirandola, Eq. (9)](https://arxiv.org/html/1507.01941).
Here $F_{\rm root}=\operatorname{tr}\sqrt{\sqrt\rho\sigma\sqrt\rho}$, so the
coherent-state limit has the ordinary overlap rather than its square.
For distinct labels the squared displacement difference is $2a$; hence
$F_{\rm root}=e^{-a/(2n+1)}$ and the mechanical trace distance is at most
$\sqrt{1-e^{-2a/(2n+1)}}$. A hot pointer can strongly dephase the photon
while these accessible mechanical states are close. The remaining record
can reside in the thermal purification or initially unknown phase
fluctuations. The channel trace alone does not certify a readable label.

**Damping retains a clock in emitted fields.** Now couple each oscillator
passively to an independent Markov field, with energy damping rate $\Gamma$
and frequency $\Omega$, retaining the entire field at the same finish. A
kick at $t$ displaces a normalized vector $f_t$ of the initial oscillator
and incident field modes. The passive Langevin dilation gives, for $t\ge s$,

$$
f_s^\dagger f_t=e^{-\Gamma(t-s)/2+i\Omega(t-s)}=:h(t-s).
\tag{MP6}
$$

Indeed its initial-oscillator coefficient is
$e^{-(\Gamma/2-i\Omega)t}$ and its causal field coefficients are
$\sqrt\Gamma e^{-(\Gamma/2-i\Omega)(t-u)}$ for $0\le u\le t$.
Their squared norms sum to one, and integrating their cross product gives
(MP6). This is an identity of this passive Markov dilation, not a claim
that every mechanical reservoir is Markovian.

If oscillator and incident modes all initially have thermal occupation $n$,
the covariance is invariant under passive mixing. The Weyl calculation now
uses $v_i(t)=\alpha f_t$ in the independent label subspace and gives

$$
\kappa_{\rm damp}(\Delta)
 =e^{ia\operatorname{Im}h(\Delta)
       -(2n+1)a[1-\operatorname{Re}h(\Delta)]},\qquad
\kappa_{\rm damp}(-\Delta)=\kappa_{\rm damp}(\Delta)^*.
\tag{MP7}
$$

The different-label coefficient remains $q$. The complete squared
displacement difference is
$2a[1-e^{-\Gamma|\Delta|/2}\cos(\Omega\Delta)]$, including both final
mechanics and emitted fields. After a full mechanical period the magnitude
is $e^{-(2n+1)a(1-e^{-\Gamma|\Delta|/2})}<1$ when $a,\Gamma,|\Delta|>0$.
An oscillator revival does not recover its leaked early/late record.

A freshly prepared oscillator need not be in equilibrium with the field.
For initial mechanical occupation $n_m$, incident-field occupation $n_b$
and $t=s+\Delta\ge s$, set

$$
\begin{aligned}
L_m&=ae^{-\Gamma s}
 [1+e^{-\Gamma\Delta}-2e^{-\Gamma\Delta/2}\cos(\Omega\Delta)],\\
L_{\rm tot}&=2a[1-e^{-\Gamma\Delta/2}\cos(\Omega\Delta)].
\end{aligned}
\tag{MP8}
$$

The same-label Weyl phase remains that of (MP7), while the real exponent is
$-(n_b+1/2)L_{\rm tot}-(n_m-n_b)L_m$. To see this, split the displacement
difference into its initial mechanical component of squared norm $L_m$
and field components of total squared norm $L_{\rm tot}-L_m$, then apply
their independent thermal characteristic functions. For different labels,
the real exponent is
$-(2n_b+1)a-(n_m-n_b)a(e^{-\Gamma t}+e^{-\Gamma s})$.
These expressions retain absolute preparation time as well as separation.
A non-Markov bath instead needs its actual response and covariance kernels;
a scalar fitted $T_2$ does not specify them.

**Ordinary waiting, forces and phase control.** In the closed
single-frequency model, a full period makes the corresponding $f_t$ equal
and removes that separation's clock record. Several frequencies require
their actual common recurrence or an approximation bound. Storage, delay,
launch rate and reset are charged. Retiming the original switch by whole
periods defines a different timed experiment unless its complete instrument
is preserved. With damping, (MP7) forbids an exact positive-time recurrence.

An unconditional known force adds the same displacement vector to both
histories of a linear oscillator. Their difference, and therefore the
magnitude of their complete Gram overlap, is unchanged; Weyl phases can
change. Independently addressed classical cell forces still add one common
vector. Photon-label-conditioned or helper-controlled forces are additional
access. Moreover, mechanical parity $R_\pi=e^{i\pi N}$ commutes with the
harmonic Hamiltonian, so

$$
R_\pi e^{-i\Omega\tau N}R_\pi e^{-i\Omega\tau N}
 =e^{-2i\Omega\tau N}.
\tag{MP9}
$$

It is not the static-qubit echo (MC7). Parity changes a later displacement's
sign but does not generally reverse harmonic clock evolution. Optical phase
alone also commutes with photon number and does not reverse a radiation
pressure number-force interaction. Any claimed force echo needs its actual
actuator, sign change, rotation or further passage.

If native controls can instead set each occupied force phase to
$\alpha(t)=\alpha e^{-i\Omega t}$, its closed interaction-picture write is
static. The vacuum three-window compiler then realizes the corresponding
static two-slot switch without knowing the projectors. This is a sufficient
control premise, not a consequence of classical pump adjustability or of
equal one-use reduced channels. It does not by itself simulate the original
unprogrammed (MP4), and a local phase update cannot retrieve emitted fields.

A stronger exact comparator is available with coherent helper-to-pointer
rotations. Define

$$
\begin{aligned}
R_A&=e^{-i\Omega_A\tau N_A},&R_B&=e^{-i\Omega_B\tau N_B},\\
S_0&=P_0^CW_BW_A+P_1^CW_AW_B,\\
K_{\rm pre}&=P_0^CR_B+P_1^CR_A,&K_{\rm post}&=K_{\rm pre}^\dagger.
\end{aligned}
$$

After removing the common idle factor, the original closed timed operator is

$$
S_\tau=K_{\rm post}S_0K_{\rm pre}.
\tag{MP10}
$$

For example its $P_0^C$ block is
$R_B^\dagger W_BW_AR_B=W_B(\tau)W_A(0)$ because $R_B$ commutes with $W_A$;
the $P_1^C$ block is $R_A^\dagger W_AW_BR_A=W_A(\tau)W_B(0)$.
Compile $S_0$ with phase-referenced ordinary writes, then apply these coherent
pre/post rotations. Equality holds on every target, pointer and reference
input, including thermal purifications and unknown bases. The required
coherent helper-to-pointer control is stronger than classical forces or two
opaque channel slots. Thermal invariance of a pointer marginal does not
permit dropping $K_{\rm pre}$, which can correlate helper and pointers.
Inaccessible mechanics or emitted fields can obstruct this comparator.

**A closed displacement loop extracts ordinary basis control.** Suppose the
actual joint $W$, its phase-referenced inverse and independently addressed
classical pointer forces are native. For $V=\prod_jD_j(\beta_j)$,

$$
W^\dagger VWV^\dagger
 =\sum_j e^{\beta_j\alpha^*-\beta_j^*\alpha}P_j\otimes I_E.
\tag{MP11}
$$

On label $j$, only $D_j(\alpha)$ fails to commute with $V$; all other cell
factors cancel. The remaining displacement commutator is the scalar shown.
With $a>0$ and $\beta_j=i\theta_j\alpha/(2a)$ this implements the unknown-basis
unitary $\sum_je^{i\theta_j}P_j$ and restores every pointer exactly, on all
inputs including its thermal purification. No learning of the basis occurs.
Global pointer parity supplies $W^\dagger=R_\pi WR_\pi$ for the actual
instantaneous joint displacement model. Parity commutes with harmonic idle
but inverts the kick; finite writes and intervening dynamics must still
implement the claimed inverse.

Set $\theta_j=2\pi kj/d$ with $k$ uniform in $\{0,\ldots,d-1\}$. Averaging
the extracted unitary channel gives exactly $\Delta_P$, by the finite
root-of-unity sum. At $B$ use an independent seed. Hold each seed fixed across
the helper's two histories and the repeated ordinary opportunity. The
three-window compiler then realizes each unitary switch, and averaging
realizes the standard channel switch of the two complete dephasers. With
identity probability $r_j$ and this random-root choice with probability
$1-r_j$, the same construction realizes the standard switch of
$\mathcal E_j=r_jI+(1-r_j)\Delta_j$. This follows from the random-unitary
representation and switch multilinearity on the complete target/helper/
reference channel, not merely on its control statistics.

Each extracted unitary uses two occupied native $W/W^\dagger$ couplings.
The worst case has six scheduled coupling opportunities and four occupied
couplings per order history, versus two occupied weak-meter encounters in
the proposed switch, plus forces, coherent delays and inverses. In vacuum
$W=W^\dagger=I$, so the loop is $VV^\dagger=I$; it introduces no slot record
under this declared closed model. Identity choices can be bypassed, while
their physical timing and training costs remain in the attempt ledger.
At weak $a$, the force scale is
$\sum_j|\beta_j|^2=\sum_j\theta_j^2/(4a)$, with phases chosen modulo $2\pi$.
Force precision, array energy, extra encounters, idle/bath leakage and reset
must be charged. Leaked fields need not be restored by a mechanical loop.
This is neither a two-physical-query simulator nor a simulator of the
original timed kernels without the stated full phase-frame premises.

**Continuity scope.** Distinct nonzero bosonic displacements have
operator-norm distance two, however small the displacement difference:
their relative displacement has the full unit-circle spectrum. Thus the
unrestricted operator-norm bound (MC5) is generally vacuous here. With a
fixed untouched thermal preparation, one equal-label purified write instead
has vector mismatch $\eta=\sqrt{2-2\operatorname{Re}\kappa}$, or
$\sqrt{2-2|\kappa|}$ after an allowed common phase alignment. Orthogonal
photon projectors make this uniform over data/reference inputs in the
isotropic model; station mismatches add by the triangle inequality. This is
a preparation-restricted channel bound, not unrestricted diamond continuity
over arbitrary pointer inputs. Its preparation and diagonal helper-control
conditions must be checked after earlier pointer processing. In particular,
arbitrary correlated preparations do not inherit the scalar $\eta$ bound.

**Bounded primary evidence and the next test.**
[Bera et al.](https://doi.org/10.1038/s41467-024-51499-z) measure driven
electromechanical polaritons and instabilities below unit mean occupation.
Their near-resonant maximum coupling is about $g/\Omega=0.04$; a separate
device-2 point reports $g/(2\pi)=45.0\pm1.9$ kHz and
$\kappa/(2\pi)=9$ MHz. These operating points cannot be combined. The latter
loaded energy-decay time is about $17.7$ ns, rather than an absorption-only
or travelling-photon loss estimate. The work demonstrates neither a
surviving one-photon conditional displacement nor a mode-resolving array.
[Sekatski, Aspelmeyer and Sangouard](https://arxiv.org/pdf/1401.2357) propose
enhancement with displaced single-photon entanglement: their illustrative
$\beta=40000$ costs about $1.6$ billion displacement photons, with about
$4$ billion in the separate readout pulse and bare $g\tau\simeq3.8\times10^{-5}$.
Their bright-state, feedback and re-displacement resources are ordinary
access too; this is a proposal rather than a measured two-order array.

The next useful candidate must preserve a declared photon code with at
least three independently addressable material cells and measured response.
Measure the complex complete cross-history kernels at $\tau,2\tau$,
different-label coherences, survival/leakage and outgoing-field records.
Compare both repeated-station orders, waiting, physical force/phase controls,
the closed-loop comparator when available, direct material readout and
pilots. Freeze controls after a fixed training budget and assess a held-out
modal-retention/alignment task, charging all source/control energy, storage,
reset, losses and mean completion time. The unresolved candidate is a
strong, photon-preserving material record with a measured non-Markov response
whose useful-task benefit survives these controls and costs. A bare
two-history visibility margin is insufficient.

The [mechanical-clock replay](checks/architecture/mechanical_pointer_clock.py)
checks finite exact passive-dilation Gram and covariance identities, force
translation/loop identities, parity and leaked-field counterexamples. Scalar
exponentials are additional numerical transcription guards. Infinite-mode
Weyl/thermal, all-input instrument and physical-control claims remain the
analytic arguments above.

## Shared quantum baths require more than two channel marginals

A shared hidden bath illustrates the access issue sharply. Suppose one
module acts as $I_S\otimes X_B$ and another as $I_S\otimes Z_B$.
Every ordinary definite-order experiment on $S$ is identity, including
all its accessible ancillas and records. A stipulated coherent order of
these **joint dilations**, however, flips the order control because
$X_BZ_B=-Z_BX_B$. Commuting bath-only operations leave it unchanged.

This does not make the standard independent-channel switch of two
identity channels implementation dependent: that switch is fixed and
leaves its control unchanged. It shows that a coherent-order extension
with a shared bath is additional data. A fixed-order process description
or two reduced CPTP maps alone do not specify it. The bath-only example
also has no harmful data error to mitigate. A positive memory-based
application must supply a microscopic collision and routing model,
matched ordinary interventions, timing and vacuum behaviour, and a
useful accessible-output decision.

## Verification scope

The proofs above are analytic deductions under their explicit models.
The architecture checks linked in [the replay map](checks/README.md)
verify small exact measurement examples, scalar calibration crossovers,
orthogonality/filter identities and shared-frequency Choi/control
counterexamples; the all-dimensional bandwidth--delay argument remains
the analytic proof (M2)--(M7). The bosonic compiler replay checks finite
full-control Fock/phase coefficients and Gaussian quadratic/Weyl
identities; infinite-Fock extension, Fourier and Gaussian integration
remain analytic. The native-check replay verifies finite rectangular
cross-map identities, norm factors, sharp SWAP witnesses and replacement
weights for (T8)--(T15); the universal diamond, postselection and repeated-use
arguments remain analytic. The same native-check replay verifies the
complete fixed-plus two-qubit correlated-Pauli channel on all input
matrix units, local separators, cyclic Weyl character images, ternary
affine assignments and noisy-control grouped-POVM examples for
(DW1)--(DW6) and (DN1)--(DN4). It also checks every encoded Pauli
error/readout branch, logical/reference matrix units, correlated laws,
retained records, the deferred coherent-record circuit and helper-noise
boundary for (EP1)--(EP5). It verifies the even fermionic CAR branches
and exact probability/positivity polynomial identities for (FP1)--(FP10);
the rational rate/visibility grid is only an additional scope and
transcription guard. For (J1)--(J17), it verifies the finite isometry,
complete projective measurement, ordinary and switched CP-weight
identities, nonnegative gap and full invariant-sector atomic-dummy
counterexample. The all-Fock sums, strict finite-energy inequality,
Poisson remainders and native-selector access remain analytic.
Recovery-to-POVM reduction,
all-dimensional dominance and sparse interpolation remain analytic;
finite examples do not certify a general noise model or native
performance. It also checks transported-Pauli calibration branch and
cross-effect identities and the helper/temporal counterexamples above.
The passive-reordering replay checks finite
seed symmetrizer, dimension/weight, qutrit second-design and CP-overlap
identities; representation decomposition, Haar integration and all-mode
variance bounds (PR2)--(PR5) remain analytic. The anisotropic compiler
obstruction and ideal-GKP comparison (AG1)--(AG5) are also analytic, with no finite-energy
or heralded-frontier certificate. The checks are not a proof of hardware
costs or a new optimal-strategy SDP. The ordinary learning algorithm is
a cited mathematical input. None of these results is a new
Lean-formalized theorem or a claim of priority for Bell learning,
measurement-return tests or trace filtering.
