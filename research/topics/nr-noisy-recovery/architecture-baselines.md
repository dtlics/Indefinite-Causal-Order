# Ordinary baselines for architecture applications

[Application audit and next tests](architecture.md) · [Recovery theorem](theorem.md) · [Topic](README.md)

These scoped results screen candidate applications against ordinary
methods with quantum memory, accessible records, calibration reuse and
known processing. They do not contradict the fresh-frame recovery game.
They also do not establish a hardware-runtime winner: ideal known
operations in a query model must be replaced by an explicit native cost
and noise model before making that comparison.

<a id="nr-r06"></a>

## NR-R06 — Calibrated orthogonal-unitary faults admit exact ordinary simulation

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

<a id="nr-r07"></a>

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
and orthogonality/filter identities; they are not a proof of hardware
costs or a new optimal-strategy SDP. The ordinary learning algorithm is
a cited mathematical input. None of these results is a new
Lean-formalized theorem or a claim of priority for Bell learning,
measurement-return tests or trace filtering.
