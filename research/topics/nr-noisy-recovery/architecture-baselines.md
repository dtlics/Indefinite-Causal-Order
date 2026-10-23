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
