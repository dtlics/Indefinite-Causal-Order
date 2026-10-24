# Fault-parity flags: ordinary controller memory

[NR-R06 owner](../architecture-baselines.md#nr-r06) · [Pauli-check memory](../architecture-baselines.md#nr-r06-pauli-statistic-memory) · [Exact replay](../checks/architecture/verify_binary_fault_controller.py)

This proof component separates fault flags from ordinary data protection
and calibration when the complete unknown payload is supplied before
the first charged device call. For two known anticommuting Pauli fault families,
a closed ordinary two-query circuit needs at least three clean helper
levels; a qutrit reproduces the complete measured SWITCH instrument.
For $k$-bit CSS fault labels, the minimum is $k$ protected helper qubits
even with arbitrary subsequent CPTP processing, resets and classical
records, and $k+1$ in the closed model. Exact preservation of the full
input when no fault occurs is essential to the former lower bound.
These are controller-resource comparisons, not practical native
advantages or priority claims.

## Instrument and response-uniform promise

Let $D=2^n$, $n\ge1$, and let the full $D$-dimensional payload be
arbitrary, including entanglement with an inaccessible passive reference
$R$. The known Hermitian Pauli strings satisfy
$P^2=Q^2=I$ and $PQ=-QP$. The slots are

$$
 \mathcal A_p=(1-p)\operatorname{Id}+p\operatorname{Ad}_P,
 \qquad
 \mathcal B_q=(1-q)\operatorname{Id}+q\operatorname{Ad}_Q,
 \qquad 0\le p,q\le1.
 \tag{BFC1}
$$

Faults are independent, fresh and input-independent. In a Kraus
unraveling, write their bits as $a,b\in\{0,1\}$. Initialize the standard
SWITCH control in $|+\rangle$ and measure it in $X$. The data Kraus
operators before their probability weights are
$(Q^bP^a\pm P^aQ^b)/2$. Thus minus occurs exactly for $a=b=1$.
Writing $\operatorname{Ad}_U(X)=UXU^\dagger$ and leaving $I_R$
implicit, the complete unnormalized measured instrument is

$$
\begin{aligned}
 \mathcal M_-(X)&=pq\operatorname{Ad}_{QP}(X),\\
 \mathcal M_+(X)&=(1-p)(1-q)X
  +p(1-q)\operatorname{Ad}_P(X)
  +(1-p)q\operatorname{Ad}_Q(X).
\end{aligned}
\tag{BFC2}
$$

Every flag and its output state count. The task is to return this
binary classical flag and the entire unknown payload, rather than to
simulate the channel for an arbitrary incoming quantum order control.

The ordinary compiler must be one fixed protocol, independent of the
unknown $p,q$, correct throughout an open parameter rectangle. With
exactly one query to each slot, its output is bilinear in $p,q$.
Polynomial identity therefore gives the four deterministic corner maps:
words $00,10,01$ always flag plus and word $11$ always flags minus,
on every input. One can equivalently impose this wordwise requirement
directly. Equality for a single supplied interior pair $(p,q)$ does
not imply these corner demands.

The bits are a proof unraveling, not assumed accessible physical bath
records. Equality of the reduced instrument does not imply a coupling
to an inaccessible actual fault label. A matched exogenous correlated
law can replace the independent weights in the construction below,
but only if the same joint process is supplied to both circuits;
channel marginals alone do not specify that promise.

## Closed ordinary controls and a flag-only lower bound

An initially pure helper has dimension $h$. Before, between and after
the two fixed-order queries, allow arbitrary known unitaries on the
$hD$-dimensional helper/payload space. There is no other initialized
workspace, intermediate measurement transcript, reset or discarded
environment. The terminal joint instrument is unrestricted: it may
measure data and helper together, use fine classical outcomes, apply
conditional corrections and discard systems. A terminal dilation is
therefore allowed; it does not add memory during the two-query interval.

All known controls have a common normal form. Let
$J:\mathbb C^D\to\mathbb C^{hD}$ append the initial pure helper, and
let $U_0,U_1,U_2$ be the known pre-, intermediate- and endpoint
unitaries. Put $\widetilde P=I_h\otimes P$,
$\widetilde Q=I_h\otimes Q$, and define

$$
\begin{aligned}
 V&=U_2U_1U_0J,\\
 E&=U_2U_1\widetilde P U_1^\dagger U_2^\dagger,\\
 F&=U_2\widetilde Q U_2^\dagger.
\end{aligned}
\qquad
 W_{ab}=F^bE^aV.
\tag{BFC3}
$$

Here $V$ is an isometry and $E,F$ are unitaries. This includes arbitrary
encoding, data-as-workspace, helper swaps and decoding. The reverse
fixed order has the same form after relabeling the slots.

**Dimension theorem.** Exact response-uniform reproduction of even the
flag alone requires $h\ge3$.

**Proof.** Let $0\le T\le I$ be the terminal plus effect. Deterministic
corner flags imply

$$
 TV=V,\qquad TEV=EV,\qquad TFV=FV,\qquad TFEV=0.
 \tag{BFC4}
$$

For example, $V^\dagger(I-T)V=0$ and positivity give $(I-T)V=0$.
The one- and zero-eigenspaces of $T$ are orthogonal. Hence
$\operatorname{ran}(FEV)$ is orthogonal to the ranges of $V,EV,FV$.
In particular,

$$
 0=(FV)^\dagger(FEV)=V^\dagger EV.
$$

Thus $\operatorname{ran}(V)$ and $\operatorname{ran}(EV)$ are also
orthogonal. The three ranges of $V,EV,FEV$ are pairwise orthogonal,
each of dimension $D$, inside dimension $hD$. Therefore $hD\ge3D$.
No assumption about the returned data state was needed. Anticommutation
identifies the requested flag as AND; the dimension step uses only
(BFC3)–(BFC4). $\square$

Independent classical randomization, including a random choice of
fixed order, does not help: zero corner error forces almost every
randomized component to satisfy the same perfect flag demands.
An arbitrary unknown gauge register is part of the full input
dimension, not free initialized space. An additional full-rank dirty
register of dimension $r$ multiplies both the initial support and
physical dimension by $r$, giving the same $3Dr$ versus $2Dr$
obstruction for a qubit helper. Restricting inputs to a proper code
or supplying a lower-rank initialized workspace changes this premise.

There is a limited extension to a multi-Kraus **source** encoder into
the same declared space, if the full instrument (BFC2) is exact and
the inter-query interval remains unitary. At word $00$ the returned
data channel is the identity. If $K_s$ are source Kraus operators and
$L_t$ are terminal decoder Kraus operators, Choi rank one gives
$L_tU_2U_1K_s=c_{ts}I$ for the plus flag, and zero for the other flag.
Terminal completeness ensures that for every nonzero $K_s$ some
$c_{ts}\ne0$; otherwise its entire output trace would vanish.
Consequently each nonzero $K_s$ has rank $D$, and the same three-range
proof applies to it. This extension needs the exact full-input
recovery premise. It does not allow arbitrary intermediate CPTP
controls: their discarded environments need not preserve (BFC3).

## No unambiguous double-fault herald on every input with two levels

The qubit obstruction also has a one-sided form. Let an accepted
effect $0\le H\le I$ have zero probability on words $00,10,01$ for
every input. Their rank-$D$ ranges $V,EV,FV$ lie in $\ker H$.
Suppose the $11$ acceptance effect
$(FEV)^\dagger H(FEV)$ were positive definite. This means strictly
positive success on every nonzero input; it holds, in particular, if
an accepted Kraus operator has full column rank, as for a nonzero
exact unitary-success map.

Positive definiteness forces $\operatorname{rank}H\ge D$. In total
dimension $2D$, $\dim\ker H\le D$, so

$$
 \ker H=S=\operatorname{ran}V=\operatorname{ran}(EV)
               =\operatorname{ran}(FV).
 \tag{BFC5}
$$

Both $E$ and $F$ preserve $S$, so $\operatorname{ran}(FEV)\subset S$,
contradicting its positive acceptance. Thus every zero-false-positive
$11$ herald in this closed qubit-helper model has a dark input
direction. Rank-deficient/data-consuming heralds, selected-input
averages and nonzero false positives are not excluded. No conclusion
about arbitrary interval-CPTP strategies follows from this proof.

## A qutrit reproduces the complete data/reference instrument

Take helper basis $|0\rangle,|1\rangle,|2\rangle$, initially
$|0\rangle$. Let $S$ swap $0\leftrightarrow1$ and fix $2$; let $R$
swap $1\leftrightarrow2$ and fix $0$. Both are Hermitian involutions.
For $J=S,R$, put $\Pi_\pm^J=(I\pm J)/2$. The known echo controls

$$
 C_Q^S=\Pi_+^S\otimes I+\Pi_-^S\otimes Q,
 \qquad
 C_P^R=\Pi_+^R\otimes I+\Pi_-^R\otimes P
 \tag{BFC6}
$$

are Hermitian unitaries. Orthogonal helper projectors and $QPQ=-P$
give

$$
 C_Q^S(I\otimes P^a)C_Q^S=S^a\otimes P^a,
 \qquad
 C_P^R(I\otimes Q^b)C_P^R=R^b\otimes Q^b.
 \tag{BFC7}
$$

Wrap the ordinary $\mathcal A_p$ query by $C_Q^S$ and the subsequent
$\mathcal B_q$ query by $C_P^R$. The complete branch operator is
$(R^bS^a)\otimes Q^bP^a$. The helper labels are

$$
 00\mapsto0,\qquad10\mapsto1,\qquad01\mapsto0,
 \qquad11\mapsto2.
 \tag{BFC8}
$$

One terminal coarse PVM
$\{I-|2\rangle\langle2|,\ |2\rangle\langle2|\}$ therefore flags
AND. Forgetting the residual qutrit gives weighted flagged Kraus
operators

$$
 K_{ab}=\sqrt{\pi_{ab}}\,|ab\rangle_{\mathrm{flag}}
                      \otimes Q^bP^a,
 \qquad
 \pi_{ab}=p^a(1-p)^{1-a}q^b(1-q)^{1-b},
 \tag{BFC9}
$$

where $ab$ in the flag ket is the Boolean product, not the two-bit
string. Their adjoint products sum to $I$. Tensoring each $K_{ab}$
with $I_R$ proves equality with (BFC2) on every unknown payload and
reference operator, including all unnormalized flag branches.
No rate estimate, bath-label readout, postselection or reset is used.

The qutrit's plus subspace retains extra information: word $10$ has
helper state $1$, while $00,01$ have state $0$. This record must be
discarded to match the binary instrument. There is no claimed unitary
compression of these two states to one, or full-channel simulation
for an arbitrary incoming quantum order control. The lower bound and
construction together make helper dimension three tight for the
declared task and controls.

The ordinary resource ledger is two actual noisy queries, four known
controlled-Pauli-string echoes, qutrit basis rotations, one clean
coherent qutrit and one terminal coarse readout. String weight,
connectivity, gate synthesis, helper leakage/dephasing and readout
time/error all count. Using a three-level subspace of two physical
qubits is not a one-physical-qubit implementation. A transmon's third
level is a possible comparator only with those real costs included.

## Many labels: exact memory with arbitrary later CPTP processing

Let $k\ge1$, $n\ge k$, $M=2^k$ and $D=2^n$. On the first $k$ data
qubits define $X^a=\prod_iX_i^{a_i}$ and
$Z^b=\prod_iZ_i^{b_i}$ for $a,b\in\mathbb F_2^k$. The remaining
data are arbitrary. Consider the known CSS fault families

$$
 \mathcal A_p=\sum_a p_a\operatorname{Ad}_{X^a},\qquad
 \mathcal B_q=\sum_b q_b\operatorname{Ad}_{Z^b}.
 \tag{BFC10}
$$

The fresh labels are independent and input-independent. With fixed
initial order control $|+\rangle$ and $X$ readout, the complete SWITCH
instrument is

$$
 \mathcal M_f(X)=\sum_{a\cdot b=f}p_aq_b
                   \operatorname{Ad}_{Z^bX^a}(X),\qquad f=0,1.
 \tag{BFC11}
$$

All maps act as identity on passive $R$. The compiler is fixed,
independent of $p,q$, and exact on an open set of their probability
simplices. Bilinearity gives the deterministic word demands, just
as for (BFC2). Independent per-bit Bernoulli rates varying on an open
$2k$-dimensional box also suffice by polynomial identity. A single
calibrated weighted law does not give this promise.

At the first query cut, the ordinary device has the queried register
of dimension $D$ and protected quantum memory of dimension $h$.
Count every retained quantum ancilla, program, purifier or held
output that can subsequently assist it. The complete unknown payload
is supplied before the first charged call. Any original input held
at the source, remotely bypassed and later returned also counts in
this first-cut space; there is no later input-bearing quantum delivery
from outside the counted systems. The source may be an
arbitrary CPTP encoder, and a truly classical pre-query transcript
may be conditioned on. There is no fault-label side channel,
fault-correlated advice or additional device query. After the first
query, allow arbitrary CPTP controls, fresh independent ancillas,
resets, discarded environments, classical records and terminal
instruments. Thus the following bound does not assume a closed
inter-query interval. It does require the full input to return
exactly at word $(0,0)$; destructive pilots do not satisfy it.

**Open-controller theorem.** Exact simulation of (BFC11), with one
query per slot, requires $h\ge M$, and $k$ clean helper qubits with
an intermediate read/reset attain it.

**Proof of the lower bound.** First fix the query order. At word
$(0,0)$ both slots are identity. The subsequent ordinary processing,
with the flag forgotten, is a CPTP left inverse $\mathcal R$ of
the source encoder $\mathcal E$. If $K_s,L_t$ are their respective
Kraus operators, the identity channel's rank-one Choi matrix gives

$$
 L_tK_s=c_{ts}I.
 \tag{BFC12}
$$

For every nonzero $K_s$, some $c_{ts}\ne0$: otherwise completeness
of $\mathcal R$ would imply
$K_s^\dagger K_s=\sum_tK_s^\dagger L_t^\dagger L_tK_s=0$.
Hence every nonzero $K_s$ has column rank $D$, and
$\rho=\mathcal E(I/D)$ has rank at least $D$.

Suppose $\mathcal A_p$ is queried first. At deterministic label $a$,
the state just after that query is

$$
 \rho_a=(I_h\otimes X^a)\rho(I_h\otimes X^a)^\dagger,
 \qquad\operatorname{rank}\rho_a\ge D.
 \tag{BFC13}
$$

Grant a hypothetical decoder the second label $b=e_i$. It can simulate
the entire remaining ordinary protocol, replacing the second query
by the known $Z^{e_i}$. This is a CPTP measurement of $\rho_a$ and
returns $a_i$ exactly, regardless of the intermediate resets or
records. For distinct $a,a'$, choose a differing bit $i$. Perfect
decoding forces their state supports into orthogonal zero- and
one-eigenspaces of a measurement effect. Thus the $M$ supports in
(BFC13) are pairwise orthogonal, each of rank at least $D$.
Consequently $hD\ge MD$. The opposite first order interchanges
$a,b$ and gives the same bound.

Public classical preprocessing and random order do not evade it.
Let $r$ include the complete classical record before the first query,
including its order, and let $\mathcal E_r$ be that source branch.
At word $(0,0)$, the decoded branch maps are CP summands of the
identity channel. Rank-one Choi implies
$\mathcal R_r\mathcal E_r=p_r\operatorname{Id}$.
Since the suffix is TP, $p_r$ is independent of the input, and the
normalized encoder $\mathcal E_r/p_r$ is reversible whenever $p_r>0$.
Zero total error at each of the finitely many words forces zero
conditional error for almost every such record simultaneously.
Apply the rank argument to any such fixed-order branch. Arbitrarily
large later classical memory cannot make nonorthogonal first-cut
states perfectly distinguishable. $\square$

**Attaining $h=M$ with read/reset.** Prepare $k$ meter qubits in
$|+\rangle^{\otimes k}$. The controlled-$Z_i$ check bank around the
first slot gives

$$
 C_Z(I\otimes X^a)C_Z=Z_H^a\otimes X^a.
 \tag{BFC14}
$$

Read the meters in $X$, retain $a$ classically and reset them to
$|+\rangle^{\otimes k}$. A controlled-$X_i$ bank around the second
slot similarly records $b$, while applying $Z^b$ to the data. Return
$a\cdot b$ and forget the finer records. Every word has exactly the
data operation $Z^bX^a$, so this is the full (BFC11), including unknown
reference correlations. It uses the same two noisy queries, four
known check banks, a middle $k$-bit read/reset and transcript, and
one terminal readout. Every control, reset and classical latency is
paid. No optimum for the number of reset rounds or arbitrary
time-dependent space tradeoffs is asserted.

If protected SWAP storage is available, another $k$-helper upper
avoids check banks. Store the $k$ active unknown input qubits in the
helpers, query $\mathcal A_p$ on the replacement $|0\rangle^{\otimes k}$
and read $a$ in $Z$; reset those queried qubits to
$|+\rangle^{\otimes k}$, query $\mathcal B_q$ and read $b$ in $X$.
Reset the queried active register to zero, restore the stored input
and apply the known $X^a$ followed by $Z^b$. Every word gives exactly
$\operatorname{Ad}_{Z^bX^a}$ on the original full data/reference;
coarse-graining the transcript returns $a\cdot b$. Unaffected gauge
qubits are untouched. This pays protected storage, SWAPs, two active-
register read/reset rounds, records, latency and Pauli replay. It
does not need knowledge of $p,q$ or a controlled unknown slot.

## Closed many-label controllers: bounds in levels and exact qubit count

In the closed model of (BFC3), write the word isometries as
$F_bE_aV$, with $E_0=F_0=I$. If $a\ne a'$, choose $b$ with
$(a+a')\cdot b=1$. Opposite flags make $F_bE_aV$ and $F_bE_{a'}V$
orthogonal; unitarity of $F_b$ cancels. The $M$ ranges of $E_aV$
are therefore mutually orthogonal. At $b=0$ they all lie in the
plus eigenspace, contributing dimension $MD$. At any fixed nonzero
$b$, the $M/2$ minus-word ranges remain mutually orthogonal and add
$MD/2$ dimensions in the orthogonal minus eigenspace. Hence

$$
 h\ge\frac{3M}{2}.
 \tag{BFC15}
$$

This is a flag-only closed-space bound. It is stronger than the
open-controller bound, under its stricter interval assumptions.

An explicit closed construction uses helper basis $|a,0\rangle$ for
all $a$ and $|a,1\rangle$ for nonzero $a$, initially $|0,0\rangle$.
Its dimension is $2M-1$. Let $E_x$ translate the plus layer,
$E_x|a,0\rangle=|a+x,0\rangle$, and fix the minus layer. Let $F_y$
swap the pair $|a,0\rangle,|a,1\rangle$ iff $a\cdot y=1$, and fix
$|0,0\rangle$. Each family is a commuting representation of
$\mathbb F_2^k$ by Hermitian involutions. Their separate character
projectors are

$$
 \Pi_c^E=\frac1M\sum_x(-1)^{c\cdot x}E_x,
 \qquad
 \Pi_c^F=\frac1M\sum_y(-1)^{c\cdot y}F_y.
 \tag{BFC16}
$$

Character orthogonality gives orthogonal resolutions of identity
and $E_x=\sum_c(-1)^{c\cdot x}\Pi_c^E$, with the same formula for
$F_y$. The regular plus layer of $E$ supplies each character once,
and its $M-1$ minus levels are trivial. For $F$, every nonzero pair
has a symmetric trivial-character vector and an antisymmetric
character-$a$ vector; $|0,0\rangle$ is trivial. Thus both trivial
projectors have rank $M$ and every nonzero-character projector has
rank one. Their eigenbases need not coincide.

The known Hermitian unitaries

$$
 C_E=\sum_c\Pi_c^E\otimes Z^c,
 \qquad C_F=\sum_c\Pi_c^F\otimes X^c
 \tag{BFC17}
$$

satisfy $C_E(I\otimes X^a)C_E=E_a\otimes X^a$ and
$C_F(I\otimes Z^b)C_F=F_b\otimes Z^b$, by the Pauli commutation
characters. Four wrappers around the two ordinary queries give

$$
 F_bE_a|0,0\rangle\otimes Z^bX^a
       =|a,a\cdot b\rangle\otimes Z^bX^a.
 \tag{BFC18}
$$

Coarse readout of the second helper coordinate, followed by disposal
of the finer $a$ record, proves the full (BFC11). No rate estimate
or middle reset is used. The construction is for these CSS groups;
it is not an upper construction for arbitrary non-isotropic Pauli
supports.

For $k\ge1$, (BFC15) exceeds $2^k$, while $2M-1<2^{k+1}$.
The minimum integer number of clean controller qubits in the closed
model is therefore exactly $k+1$. Literal helper dimension is only
bounded by $3M/2\le h\le2M-1$ for $k>1$; no equality is claimed
there. For $k=1$, the construction is precisely the qutrit above.

An efficient full-register implementation uses $k$ helper label
qubits $A$ and a flag qubit $f$, padding with $|0,1\rangle$.
Extend the composite representations to fix that unused level.
Writing $H_A$ for Hadamards on every label qubit and $H_f$ for a
flag Hadamard gives

$$
\begin{aligned}
 C_E&=H_A\left[\prod_i\operatorname{CCZ}_{f=0,A_i,D_i}\right]H_A,\\
 C_F&=H_f\left[\prod_i\operatorname{CCX}_{f=1,A_i;D_i}\right]H_f.
\end{aligned}
\tag{BFC19}
$$

In the first line the character is the label $A$ when $f=0$ and
zero otherwise. In the second it is $fA$. These are (BFC17) on the
padded register, using $O(k)$ known three-body controlled-Pauli
gates and Hadamards per wrapper; their gate-set decomposition,
non-Clifford cost, connectivity, error and duration all count.
The individual Hadamards can transiently occupy the padded level.
Thus (BFC19) is an efficient $k+1$-qubit realization, not the same
cost certificate for a literal $(2M-1)$-level device constrained to
that subspace at every intermediate instant.

## Robust flags when the no-fault data channel remains exact

A dimension bound survives imperfect flags if the complete unflagged
data channel at word $(0,0)$ remains exactly identity. Suppose the
flag error is at most $\epsilon<1/2$ for every word and payload,
with arbitrary source and later CPTP processing as above. For fixed
first order,

$$
 \log_2h\ge k[1-H_2(\epsilon)],
 \tag{BFC20}
$$

where $H_2$ is binary entropy. This is a random-access-code bound;
see [Nayak, Theorem 2.3](https://arxiv.org/html/quant-ph/9904093v3).

Here is the source-entropy and decoding argument. From (BFC12) and
decoder completeness,
$K_s^\dagger K_{s'}=\alpha_{ss'}I$, where
$\alpha_{ss'}=\sum_tc_{ts}^*c_{ts'}$. Diagonalize this positive
Kraus Gram matrix. The resulting source Kraus operators are
$\sqrt{\lambda_j}V_j$ with
$V_j^\dagger V_\ell=\delta_{j\ell}I$ and $\sum_j\lambda_j=1$.
Therefore $\mathcal E(I/D)$ has eigenvalues $\lambda_j/D$, each
repeated $D$ times, and entropy
$\log_2D+H(\lambda)\ge\log_2D$.

Choose the first label uniformly. Its conditional states are unitary
rotations of this source state, so their Holevo information in a
$Dh$-dimensional cut is at most $\log_2h$. Keep any public
pre-query record as decoder side information: it is independent of
the first label, and each normalized conditional encoder is reversible.
For $b=e_i$, the suffix decodes bit $a_i$ with error at most
$\epsilon$, averaged over that record. Binary Fano, data processing
and conditional-entropy subadditivity give information at least
$k[1-H_2(\epsilon)]$. This proves (BFC20); fresh later ancillas,
resets and transcripts cannot increase the information at the cut.
One must retain the public seed in this argument, rather than
select a seed with an unproved uniform error bound.

If the initial order is also randomized, choose an order of
probability $\alpha\ge1/2$. Nonnegative errors give conditional
word error at most $\epsilon/\alpha\le2\epsilon$. Thus the safe
order-independent consequence, for $\epsilon<1/4$, is

$$
 \log_2h\ge k[1-H_2(2\epsilon)].
 \tag{BFC21}
$$

For example, order-control $Z$ dephasing of visibility $0\le v\le1$
before native $X$ readout flips the ideal bit with probability
$\epsilon=(1-v)/2$, on every deterministic word, while leaving
the data operation exactly $\operatorname{Ad}_{Z^bX^a}$. An exact
ordinary simulator of this specified noisy CQ instrument has an
exact no-fault unflagged data identity, so (BFC20) applies, and
(BFC21) applies for $v>1/2$. This is not a bound for a generic
approximate ideal simulator whose no-fault data recovery is also
imperfect. No approximate-reversibility estimate or unrestricted
repeated-query bound is asserted.

## When a uniform mean-two budget forces one query per slot

For an exact full-instrument simulator, a uniform expected-cost
condition can imply the one-each query interface rather than assume
it. Consider one law-independent, almost-surely terminating ordinary
program, allowing adaptive queries and rare long branches. Charge
every opaque device call, including any calibration calls. Query
choices and stopping are classical events, and each invocation has
unit cost; this is not a coherent variable-query-count or occupied-
amplitude convention. Require
exact full-instrument correctness for **all laws, including point
masses**, with unflagged output exactly
$\operatorname{Ad}_{Z^bX^a}$ at every deterministic corner $(a,b)$,
and require

$$
 \mathbb E_{p,q,\,I/D}N\le2
 \quad\text{for every law }p,q\text{, including all point masses}.
 \tag{BFC22}
$$

Then the program makes exactly one call to each slot almost surely
for every law, so the applicable memory bound above applies with
its own source and interval assumptions.

To prove this, fix a corner $(a,b)$. Aggregate the terminating
branches that never call $\mathcal B$ into a CP map $\mathcal T_a$,
forgetting all flags. It is independent of $b$, but is a CP summand
of $\operatorname{Ad}_{Z^bX^a}$ for every $b$. Its Choi matrix must
therefore lie on every one of these distinct rank-one unitary rays;
their intersection is zero. Thus $\mathcal T_a=0$. The same argument
excludes branches omitting $\mathcal A$. Almost-sure termination
then gives $N\ge2$ at every corner; (BFC22) forces $N=2$, one call
each, there. Zero event probability on the full-rank $I/D$ implies
that event's CP effect is zero on every input.

This also eliminates hidden interior-law long branches. Before a
second call, the decision to stop or repeat the first slot has seen
only its first fault label. Its probability is affine in that
slot's law; all possible first labels occur at point-mass corners,
where those decisions have zero probability. They therefore vanish
for every mixed law. The first two calls are consequently distinct.
Any decision to make a third call then depends on a prefix with one
label from each slot; its probability is bilinear in their fresh
stationary laws. The point-mass corners again exhaust those prefixes
and force zero third-call probability for every law. No finite
query cutoff is needed for the assumed program.

The uniformity in (BFC22) is essential. A prior-averaged mean budget,
a budget known only on an interior subset, supplied law-dependent
advice, temporal/reactive faults, or a cost counting only occupied
branches does not establish this reduction. One must not apply a
two-query polynomial argument to an arbitrary unbounded-query
program before proving the reduction. Exact simulation of the
specified noisy-control instrument above has the required unitary
unflagged data maps at every corner, so it is covered. The general
imperfect-flag bounds (BFC20)–(BFC21), assuming only the no-fault
data identity, do not by themselves supply this extra hypothesis.
The payload is retained on both flags. Discarding it on a reject
branch or requesting only an accepted subchannel does not give the
unitary unflagged corner and needs a separate argument.

## Ordinary alternatives and the application boundary

**Data protection.** A public Clifford maps the known anticommuting
pair to $X_1,Z_1$ on one virtual qubit and identity on the remaining
$n-1$ qubits. Swap that virtual qubit into the clean helper around
both slots, then swap back. If these known controls and a noiseless
helper bypass are available, the original full payload/reference is
preserved exactly. The faults act on the initialized replacement.
This does not recover their AND flag, so it is consistent with the
dimension theorem; it closes a data-protection application in that
stronger interface.
For (BFC10), the same construction stores all $k$ active input qubits
in $k$ protected helpers. Preserving the payload is a different task
from returning its complete fault-parity instrument.

**Calibrated probabilities.** Given $p,q$ and optional queries,
classically sample $a,b$, apply the known $Q^bP^a$, and return $ab$.
This reproduces (BFC2) without the slots. If two encounters are
mandatory, the logical-qubit bypass above followed by resampling
also works when its ports are granted. This matches the reduced
CQ law, rather than correlations with an inaccessible actual bath
record. Calibration, precision and reuse must be charged in a
learning task. The theorem requires a response-uniform unknown-rate
protocol, not a calibrated numerical pair.
For the many-label families, supplied $p,q$ similarly permit direct
classical sampling of $a,b$ and synthesis of (BFC11).

**Queries before payload arrival.** Even unknown $p,q$ do not create
a memory lower bound if the same-law calls may precede input delivery.
Query $\mathcal A_p$ on a pure zero pilot and read $a$, prepare a plus
pilot for $\mathcal B_q$ and read $b$, then cache these classical
labels. When the unknown payload arrives, synthesize $Z^bX^a$ and
return $a\cdot b$. This reproduces the reduced (BFC11) for all unknown
laws with the same two actual calls and no input-bearing quantum
memory, without learning the probabilities. A specified noisy-control
flag coin can also be cached. This timing is outside the already-
received-input source map used in the lower bound. Physical drift,
job timing and the validity of earlier same-law samples need an
actual access model; pipeline warmup must not be excluded merely to
claim a memory advantage. Correlations with an inaccessible actual
bath record require a separately declared joint-process endpoint.

**Destructive diagnosis.** For $n\ge2$ and available pure calibration
probes, prepare a Bell pair between the active virtual qubit and an
unaffected gauge qubit. After ordinary $\mathcal A_p,\mathcal B_q$
the four faults $I,P,Q,QP$ produce four orthogonal Bell states.
A single terminal destructive readout learns both bits without an
extra helper. Probe preparation, purity and consumption are genuine
resources; this does not preserve an arbitrary unknown payload.
It defeats a simple fault-correlation diagnostic when such probes
are allowed.
For the known CSS families, even product pilots suffice: query
$\mathcal A_p$ on $|0\rangle^{\otimes k}$ and measure $Z$ to sample
$a$, then prepare $|+\rangle^{\otimes k}$ for $\mathcal B_q$ and
measure $X$ to sample $b$. Their independent labels give an exact
parity sample with two calls and no extra coherent helper. These
preparations/readouts consume the input. Alternatively $k$ Bell
references expose the combined word; an initialized unaffected
payload gauge supplies those references only when $n\ge2k$.

**Reset or extra records.** A reusable qubit can check the first
slot, read/reset, check the second slot and classically AND the
records. Two qubit helpers can instead store both syndromes
coherently until terminal readout. The retained classical transcript
is additional memory even if only one quantum helper exists at a
time. Reset, entropy disposal, latency and extra coherent levels are
the resources that the closed-space theorem distinguishes.

These comparisons also delimit the existing
[deterministic Pauli recovery bound](../architecture-baselines.md#nr-r06-deterministic-pauli-weyl)
and [encoded Pauli decoder](../architecture-baselines.md#nr-r06-encoded-pauli).
They ask a different recovery utility or use a smaller logical input
and additional records; neither is contradicted here.

A physical standard SWITCH additionally needs coherent order routing
for the whole payload and compatible environmental timing. Known
controlled dilations or setting selectors can admit ordinary
chronological implementations, as in the
[shared-bath comparison](../backaction.md#nr-r14). Noise indivisibly
embedded in an unknown ideal gate presents a different check-transport
problem. The present result establishes no such native access or
favorable cost ratio against a qutrit, reset or bypass. It excludes
neither richer ordinary architectures nor their actual workloads.
The abstract order-control factor $\mathbb C^2$ does not price
whole-payload buffers, parallel modules, propagation storage, routing
loss or timing coherence. Those resources must be compared with
ordinary helpers and records. The full instrument endpoint is
stronger than scalar calibration and is not itself useful recovery.
Known pure gauge qubits or a smaller promised code change the full
rank-$D$ input premise.

Each opaque query here applies the stated channel to its entire
declared $D$-dimensional register. Controlled evaluations, setting
selectors and vacuum/idle ports are extra access, not implicit
ordinary queries. For example, a chronological $A\to B\to A$
route can use only one occupied $A$ visit in each history but two
nominal $A$ windows. If those controlled idle ports are physically
available, its two occupied visits need not fit this two-opaque-query
interface. Its real windows, routing and payload storage must be
priced against the native schedule; the memory theorem does not
exclude that compiler.

## Attribution and verification

The controlled-commutation mechanism is established prior work; see
[van den Berg et al., *Single-shot error mitigation by coherent Pauli checks*](https://arxiv.org/abs/2212.03937)
and [Gonzales et al., *Quantum Error Mitigation by Pauli Check Sandwiching*](https://doi.org/10.1038/s41598-023-28109-x).
Measure-once versus repeated-measurement quantum memory also has a
finite-automata literature, for example
[Moore and Crutchfield, *Quantum Automata and Quantum Grammars*](https://arxiv.org/abs/quant-ph/9707031).
The specific dimension proof and compiler are given in full here;
no novelty priority or hardware advantage is inferred from those
references.

The [standard-library exact replay](../checks/architecture/verify_binary_fault_controller.py)
checks the wrapped operators, all realized branch isometries,
coarse flags, many-label CSS constructions and the read/reset upper,
including weighted reference-inclusive instrument examples.
Its finite examples guard normalization, order and signs. The
all-dimensional flag lower bound, all-input herald obstruction and
all-reference identities remain the analytic arguments above;
they have not been formalized in Lean by this component.
