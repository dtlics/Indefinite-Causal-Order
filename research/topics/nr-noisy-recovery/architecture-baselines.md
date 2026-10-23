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
arguments remain analytic. The passive-reordering replay checks finite
seed symmetrizer, dimension/weight, qutrit second-design and CP-overlap
identities; representation decomposition, Haar integration and all-mode
variance bounds (PR2)--(PR5) remain analytic. The anisotropic compiler
obstruction and ideal-GKP comparison (AG1)--(AG5) are also analytic, with no finite-energy
or heralded-frontier certificate. The checks are not a proof of hardware
costs or a new optimal-strategy SDP. The ordinary learning algorithm is
a cited mathematical input. None of these results is a new
Lean-formalized theorem or a claim of priority for Bell learning,
measurement-return tests or trace filtering.
