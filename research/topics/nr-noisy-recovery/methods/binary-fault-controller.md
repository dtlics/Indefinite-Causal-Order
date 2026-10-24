# Binary-fault flags: a tight closed-controller dimension

[NR-R06 owner](../architecture-baselines.md#nr-r06) · [Pauli-check memory](../architecture-baselines.md#nr-r06-pauli-statistic-memory) · [Exact replay](../checks/architecture/verify_binary_fault_controller.py)

This proof component separates a nonlinear fault flag from ordinary
data protection and calibration. A standard SWITCH of two known
anticommuting Pauli fault families flags their simultaneous faults.
An ordinary two-query circuit needs at least three clean helper levels
to reproduce that flag exactly in the closed-controller model below.
A qutrit attains the bound and reproduces the complete measured
data/reference instrument. The statement is a controller-resource
comparison, not a practical native advantage or a priority claim.

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

**Calibrated probabilities.** Given $p,q$ and optional queries,
classically sample $a,b$, apply the known $Q^bP^a$, and return $ab$.
This reproduces (BFC2) without the slots. If two encounters are
mandatory, the logical-qubit bypass above followed by resampling
also works when its ports are granted. This matches the reduced
CQ law, rather than correlations with an inaccessible actual bath
record. Calibration, precision and reuse must be charged in a
learning task. The theorem requires a response-uniform unknown-rate
protocol, not a calibrated numerical pair.

**Destructive diagnosis.** For $n\ge2$ and available pure calibration
probes, prepare a Bell pair between the active virtual qubit and an
unaffected gauge qubit. After ordinary $\mathcal A_p,\mathcal B_q$
the four faults $I,P,Q,QP$ produce four orthogonal Bell states.
A single terminal destructive readout learns both bits without an
extra helper. Probe preparation, purity and consumption are genuine
resources; this does not preserve an arbitrary unknown payload.
It defeats a simple fault-correlation diagnostic when such probes
are allowed.

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
coarse flags and weighted reference-inclusive instrument examples.
Its finite examples guard normalization, order and signs. The
all-dimensional flag lower bound, all-input herald obstruction and
all-reference identities remain the analytic arguments above;
they have not been formalized in Lean by this component.
