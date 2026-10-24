# Communication links: exact reductions and resource bounds

[Architecture assessment](architecture.md) · [Local baselines](architecture-baselines.md) · [References](references.md) · [Checks](checks/README.md)

These results distinguish an abstract switch placement from a physical network cut. Local operations, classical communication (LOCC), encoding, quantum memory, distillation and rejected attempts belong in the comparator. A usable control wire across a cut is an additional communication resource; an abstract provider-owned order control does not automatically supply that wire. The proofs below are analytic, with finite identities replayed by the linked checks. The continuum scattering and reservoir-support arguments use the specified dilations and are not finite replays. They have not been formalized in Lean, and no priority claim is made.

<a id="nr-r09"></a>

## NR-R09 — Optical loss: calibrated reductions and native record constraints

### Specified channel and exact output

Let the carrier space be $S\oplus\operatorname{span}\{|v\rangle\}$, with $\dim S=D$. A loss channel with survival $a\in[0,1]$ has the **square absorbing-vacuum extension**

$$
A_0=\sqrt a\,I_S+|v\rangle\langle v|,
\qquad A_i=\sqrt{1-a}\,|v\rangle\langle i|\quad(i=1,\ldots,D).
$$

The second independent channel has the analogous Kraus operators $B_j$ and survival $b$. The input is supported on $S$; the order control is fixed to $|+\rangle$. Neither channel contains a hidden payload gate or returns a lost quantum state.

For any reference-entangled $\rho_{RS}$, the entire switched output is

$$
ab\,\rho_{RS}\otimes|+\rangle\langle+|_C
 +\rho_R\otimes|v\rangle\langle v|\otimes\tau_{ab},
\tag{1}
$$

where

$$
\tau_{ab}=\frac{1-a}{2}
 \begin{pmatrix}1&\sqrt b\\\sqrt b&b\end{pmatrix}
 +\frac{1-b}{2}
 \begin{pmatrix}a&\sqrt a\\\sqrt a&1\end{pmatrix}.
\tag{2}
$$

Both summands are positive rank-one matrices. Its trace is $1-ab$, its diagonal entries are $(1-ab)/2$, and its off-diagonal entry is

$$
\frac{(1-a)\sqrt b+(1-b)\sqrt a}{2}.
$$

To prove (1), the no-jump product is $B_0A_0=A_0B_0=\sqrt{ab}\,I_S+|v\rangle\langle v|$, giving the first term. An $A_i$ jump gives control amplitudes $(1,\sqrt b)\sqrt{1-a}/\sqrt2$; a $B_j$ jump gives $(\sqrt a,1)\sqrt{1-b}/\sqrt2$. Summing their input basis indices leaves exactly $\rho_R$, producing (2). Every two-jump product vanishes on the input subspace. This proves the full output identity, including loss, rather than a selected control outcome.

### Ordinary equivalence and scope

Ordinary serial transmission is the flagged erasure channel with survival $ab$. A receiver reproduces (1) by preparing $|+\rangle$ on survival and $\tau_{ab}/(1-ab)$ on loss. Conversely, tracing out $C$ recovers that serial erasure channel. At $ab=1$ the loss branch is absent; the endpoint cases otherwise follow from the displayed formulas.

Thus the two channels are related by receiver-local postprocessing in both directions. They have identical performance for communication and entanglement-distribution tasks with arbitrary data encodings, memories, parallel uses, LOCC and postselection, when calibrated $a,b$ are available for that postprocessing. Both use the same two module slots; switch routing supplies no improvement in this model. Conditional fidelity on a surviving or selected branch cannot replace the all-attempt comparison.

The conclusion concerns this vacuum extension and fixed input control. It is not a statement about every rectangular erasure-switch definition, quantum-correlated losses, unknown-parameter estimation, or arbitrary encoding into the control. In particular, preparing the forward simulation's flag depends on $a,b$; it is not a parameter-independent simulator of an unknown loss family. Other erasure conventions must be checked from their complete channel, as illustrated by the distinct flag formulas in [Caleffi, Simonov and Cacciapuoti](https://arxiv.org/abs/1912.08575).

<a id="nr-r09-passive-qubit-transfer"></a>

### Passive qubit transfer needs the vacuum coherence and delayed field

[Diekmann et al., PRX Quantum **7**, 043013 (2026), primary v3](https://arxiv.org/html/2605.12018v3)
give a theory/design and numerical-optimization study of passive transfer
between giant atoms. Their spatial coupling profiles shape emission for
matched capture. Equation (16) optimizes peak receiver excitation
$P=|c_2(T)|^2$, with about 87% for two coupling legs per atom and
over 99% around ten or more per atom under ideal chirality; realizing
directionality can require extra legs.
These are model predictions. Footnote 1 notes receiver reemission and an
additional fast $\Lambda$-system storage pulse. The source supplies no
coherent order port. Its own matched passive geometry is the first
ordinary comparator, including chirality, propagation and storage costs.

The complete unknown-qubit endpoint follows directly from its
number-conserving rotating-wave Hamiltonian. Prepare receiver D in its
ground state and field E in vacuum; S carries an arbitrary input,
possibly entangled with a passive R. The zero-excitation state is fixed,
and the one-excitation solution gives, with D written first,

$$
|0\rangle_S\mapsto|0\rangle_D|v\rangle_{SE},\qquad
|1\rangle_S\mapsto h|1\rangle_D|v\rangle_{SE}
 +\sqrt{1-|h|^2}|0\rangle_D|j_T\rangle_{SE},
\quad h=e^{-i\omega_qT}c_2(T),\quad\langle v|j_T\rangle=0.
\tag{ST1}
$$

Here $|j_T\rangle$ contains every leftover sender/field excitation.
Tracing SE produces amplitude damping with
$K_0=\operatorname{diag}(1,h)$ and
$K_1=\sqrt{1-|h|^2}|0\rangle\langle1|$. This is an equality on every
S/R input. Relative to identity transfer its entanglement fidelity is
$F_e=|1+h|^2/4$ and uniform pure-qubit average fidelity is
$F_{\rm av}=(3+|h|^2+2\operatorname{Re}h)/6$.
An available calibrated phase correction gives
$F_e=(1+\sqrt P)^2/4$ and $F_{\rm av}=(3+P+2\sqrt P)/6$.
Thus excitation probability is neither of those fidelities nor an
input-independent exact-unitary success weight. At $P=1$, the corrected
ordinary channel is already perfect on all references in this ideal model.

Receiver excitation readout has Kraus $h|1\rangle\langle1|$ and deletes
the logical zero. Even resolved no-jump output gives
$\operatorname{diag}(1,h)$, not a scalar unitary for $0<|h|<1$.
For $|h|<1$ with the jump unobserved, no receiver-only postfilter has a
nonzero exact qubit-isometry branch: rank-one Choi support would force every accepted
filter F to annihilate the rank-one jump, hence $F|0\rangle=0$, also
killing the no-jump ground input. Monitoring other outputs, encoding and
entanglement-first delivery are different ports and protocols whose
preparation, records, attempts and storage must be priced.

Eliminating the field from the source Hamiltonian also retains its memory:

$$
\dot c_\alpha(t)=-\sum_\beta\int_0^t
 \mathcal K_{\alpha\beta}(t-s)c_\beta(s)\,ds,\qquad
\mathcal K_{\alpha\beta}(u)=\int dk\,
 g_\alpha(k)g_\beta(k)^*e^{-i[\omega(k)-\omega_q]u}.
\tag{ST2}
$$

Use the actual waveguide cutoff/envelope convention. The spatial phases
in $g_\alpha(k)=\sum_jg_j^{(\alpha)}e^{ikx_j^{(\alpha)}}$ carry the
leg delays; the shared field persists between contacts. A complete
transfer marginal (ST1) does not supply independently reset channels
for separate legs, atoms or time windows. With $g_1$ engineered to emit a
time-reversal-symmetric pulse, the matched receiver $g_2(k)=e^{ikd}g_1(k)^*$ already
enables the source's ideal direct transfer. A new order proposal needs
an actual controlled Hamiltonian,
field/record ports and common capture/storage time before comparison
with the same passive design and any available ordinary pulse controls.

**A separate fresh-channel repair also fails for the plain switch.**
This next model is not the delayed network (ST2). To avoid confusing
notation with the survival probabilities in (1), use amplitudes
$0<x,y<1$. Let two independent amplitude-damping channels have
$A_0=\operatorname{diag}(1,x)$,
$A_1=\sqrt{1-x^2}L$, $B_0=\operatorname{diag}(1,y)$,
$B_1=\sqrt{1-y^2}L$, $L=|0\rangle\langle1|$.
Use one call each with an independent fixed $|+\rangle_C$, no input
encoding or intermediate target operation, and inaccessible fresh baths.
The complete pre-readout Kraus operators are

$$
N_0=|+\rangle\otimes D_{xy},\quad
N_A=\frac{\sqrt{1-x^2}}{\sqrt2}(|0\rangle+y|1\rangle)\otimes L,
\quad
N_B=\frac{\sqrt{1-y^2}}{\sqrt2}(x|0\rangle+|1\rangle)\otimes L,
\quad D_{xy}=\operatorname{diag}(1,xy).
\tag{ST3}
$$

The double jump vanishes. Helper X readout gives
$\Phi_+(\rho)=D_{xy}\rho D_{xy}^\dagger+\gamma_+\rho_{11}|0\rangle\langle0|$
and $\Phi_-(\rho)=\gamma_-\rho_{11}|0\rangle\langle0|$, with
$\gamma_\pm=(1\pm x)(1\pm y)(1-xy)/2$.
Their sum is ordinary serial amplitude damping with amplitude xy.
The minus flag is a reset whose probability depends on the input;
plus retains unobserved jumps. On all references replace $\rho_{11}$
by $\langle1|\rho_{SR}|1\rangle$ and tensor D with $I_R$.

The obstruction covers every terminal SC filter, beyond this readout.
For an accepted exact rank-two isometry J, Choi rank one forces each
terminal Kraus F to satisfy $FN_\mu\propto J$.
The rank-one $N_A,N_B$ must therefore be killed. Their helper vectors
$(1,y)$ and $(x,1)$ span C since $1-xy>0$; hence F kills
$C\otimes|0\rangle$, including $N_0|0\rangle$.
No accepted full-rank branch can remain. Independent output ancillas,
multiple accepted outcomes and passive references do not change this
argument. Input encoding, bath monitoring, extra calls, approximate
recovery and the lossless boundary are outside this statement.

The existing [ordinary parity-check mechanism](architecture-baselines.md#nr-r06)
provides a different conditional interface: controlled Z before and
after ordinary A then B isolates $D_{xy}$ because it commutes with Z
and every nonzero jump anticommutes. If the calibrated physical filter
$\operatorname{diag}(xy,1)$ is also supplied, their product is $xyI$,
an exact unknown-qubit branch of weight $x^2y^2$. This uses input
encoding and needs actual coherent helper transport, controlled gates,
filtering, readout and storage; those ports do not follow from a passive
link or order router. It is a baseline application, not a demonstrated
giant-atom protocol or a converse for all encoded switch strategies.

### Unknown loss calibration differs from calibrated storage

The [calibrated bosonic compilers](architecture-baselines.md#nr-r06-bosonic-compilers)
reproduce the full switched channel, including a reference and every control
outcome, when their loss-dependent helper settings are supplied. This does
not imply a parameter-independent simulation of an unknown loss family.
For two single-mode pure-loss channels, write

$$
\tau=\eta_1\eta_2,\qquad
\zeta=\frac{\sqrt{\eta_1}+\sqrt{\eta_2}}{1+\sqrt\tau}.
$$

On a one-photon input and an independent $|+\rangle_C$ control, the
abstract same-port switch has probabilities

$$
p(1)=\tau,\qquad
p(0,\pm)=\frac{(1-\tau)(1\pm\zeta)}2.                 \tag{L1}
$$

The serial channel depends only on $\tau$, whereas (L1) can also reveal
$\zeta$. Together they determine the **unordered** pair of efficiencies:
the roots $a,b$ obey $ab=\sqrt\tau$ and
$a+b=\zeta(1+\sqrt\tau)$, with $\eta_1=a^2,\eta_2=b^2$.
They do not identify which labeled node is worse. If either efficiency is
already known, serial transmission determines the other. The calibrated
compiler samples helper phases from a law depending on $\zeta$; it cannot
be differentiated as though that unknown law were freely provided to a
sensing experiment. No Fisher-information converse follows from that
pointwise storage simulation.

### A fixed passive vacuum network is determined by its field matrix

There is a separate family-level obstruction for a common proposed
photonic realization. Let $a$ collect all accessible optical input
annihilation operators, $b$ all accessible outputs, and $e$ the initially
uncorrelated vacuum environment inputs of a **fixed passive,
number-preserving linear network**. Include accessible reflection,
polarization, spatial, frequency and temporal modes. Its dilation has

$$
b=Ta+Re,\qquad TT^\dagger+RR^\dagger=I.                 \tag{P1}
$$

The second identity follows from preservation of the output commutators;
$T$ may be rectangular. With the complex Weyl convention
$D_a(\alpha)=\exp(a^\dagger\alpha-\alpha^\dagger a)$,
substitution in $D_b(\xi)$ gives

$$
D_b(\xi)=D_a(T^\dagger\xi)D_e(R^\dagger\xi).
$$

The two factors commute. Taking the vacuum expectation of the second
factor gives the complete channel's characteristic function

$$
\chi_{\Phi_T(\rho)}(\xi)
=\chi_\rho(T^\dagger\xi)
 \exp\!\left[-\frac12\xi^\dagger(I-TT^\dagger)\xi\right]. \tag{P2}
$$

Characteristic functions determine arbitrary trace-class operators, so
(P2) identifies the entire channel, including non-Gaussian inputs and
inputs entangled with retained references. This is the passive-vacuum
specialization of the Gaussian-channel Weyl action and dilation in
[Caruso, Eisert, Giovannetti and Holevo, New J. Phys. **10**, 083030
(2008), Eqs. (16), (18) and Section 2](https://arxiv.org/html/0804.0511v3).

Consequently, if $T_\theta$ depends on unknown internal parameters only
through $\tau(\theta)$, no parameter-independent endpoint protocol

$$
\Lambda_{\rm out}\circ
 (\Phi_{T_\theta}\otimes\operatorname{id}_M)
 \circ\Lambda_{\rm in}                                  \tag{P3}
$$

can distinguish internal parameter values having the same $\tau$.
The endpoint maps may use an independent
stored control, controlled path demultiplexing and recombination,
nonlinear helpers, memories and arbitrary measurements. Equality of
channels includes the complete outcome instrument and its postselected
statistics. Repeated-use extension requires fresh baths, or the same
premise on the **full joint temporal transfer matrix**; isolated one-use
matrices do not characterize a device with reservoir memory.

In particular, $T=\sqrt\tau V$ with known $V$ gives only $\tau$ access.
If a different loss split changes accessible reflections or cross-coupling,
that change belongs in $T$ and is also identifiable in principle with
coherent probes: $|\alpha\rangle\mapsto|T\alpha\rangle$.
This observation is not a claim that bright pilots have optimal precision
or negligible dose, latency or detector cost.

### Opposite-direction loss records need not be the same environment

The simple counterpropagating ring shows the missing physical record.
For one reciprocal two-port attenuator in matched power-normalized
orthogonal propagating modes, write its one-photon isometry as

$$
\begin{aligned}
|L\rangle&\longmapsto r_L|L_{\rm out}\rangle
 +t|R_{\rm out}\rangle+|\ell_L\rangle,\\
|R\rangle&\longmapsto t|L_{\rm out}\rangle
 +r_R|R_{\rm out}\rangle+|\ell_R\rangle.
\end{aligned}
$$

Here the $\ell$ vectors contain every inaccessible loss mode.
Preserving the zero inner product of the input columns gives

$$
\langle\ell_L|\ell_R\rangle
=-(r_L^*t+t^*r_R).                                      \tag{R1}
$$

For the reciprocity convention see [Svendsen, Haakestad and Skaar,
Phys. Rev. A **87**, 013838 (2013)](https://arxiv.org/abs/1301.2458).
Equation (R1) is the elementary isometry consequence used here. A
reflectionless attenuator has orthogonal opposite-direction loss
records. Equal reduced transmitted channels therefore do not establish
the environment identification required by the abstract switch.

For two such reflectionless elements with independent vacuum baths,
opposite-direction $AB$ and $BA$ routes have orthogonal records for
every lost one-photon history: loss at the same node has the direction
tag in (R1), and loss at different nodes occupies independent baths.
After endpoint recombination the output for arbitrary stored $\rho_C$ is

$$
\tau\rho_C\otimes|1\rangle\langle1|
 +(1-\tau)\Delta_Z(\rho_C)\otimes|0\rangle\langle0|.       \tag{R2}
$$

It contains no $\zeta$ signal. This does not rely on distinct pulse
arrival times: long wavepackets can overlap, but the direction records
already suffice. If the control is carried only by the lost photon's
path or polarization, there is also no independent control qubit left
to measure in the vacuum sector.

These are scoped implementation statements. Controller-conditioned
**internal** interactions, active or nonlinear networks, initially
non-vacuum or correlated baths, and access to emitted fields fall
outside (P1)-(P3). A retained endpoint control alone does not supply
those resources. An actual same-port quantum router could fall outside
the proof and requires its complete ports, records and cost model.

### Network tomography supplies the ordinary access test

[Zheng, Gong, Guha and Towsley, arXiv:2604.25194v1 (2026), Sections 2.1
and 4.1](https://arxiv.org/html/2604.25194v1), study loss inference from
end-to-end optical probes when only some nodes have transceivers.
Their ordinary routes are walks, including repeated edges; a route
has transmissivity $\prod_{e\in P}\eta_e$, and identifiability requires
the edge-count matrix to have full column rank. Additional native routes
or returns can therefore remove an apparent two-link ambiguity.
These network routing switches are distinct from a causal-order switch.
If individual elements are interrogable, [Nair, Phys. Rev. Lett.
**121**, 230801 (2018)](https://arxiv.org/html/1804.02211v2) gives the
energy-constrained diagonal QFI $N_j/[\eta_j(1-\eta_j)]$, attained by
number-diagonal-signal probes without observing the loss baths. That
benchmark does not grant local access to a genuinely composite-only
interface.

The theoretical [Li, Li and Dahlsten, EPJ Quantum Technology **13**,
78 (2026)](https://link.springer.com/article/10.1140/epjqt/s40507-026-00523-w)
uses effective erasure/fading loss and proposes quantum-controlled MZI
routing in Appendix A; it supplies no measured loss-localization
interface or full bosonic pure-loss analysis. The models should be
distinguished: with a vacuum bath, a pure-loss beamsplitter maps
$|1\rangle\langle0|$ to $\sqrt\eta|1\rangle\langle0|$, whereas a
transmitted-or-vacuum-replaced interpolation scales it by $\eta$.
Its illumination error bounds are not needed for the reductions above.

A useful next experiment would hold $\tau$ fixed while changing the
loss split, measure the complete accessible $T$, and test an independent
control conditioned on probe vacuum. Any split-dependent signal at
unchanged $T$ must identify which premise of (P1) fails. A network claim
must additionally explain physically why local probes, alternate walks,
bright pilots, reflected fields and reflectometry are unavailable while
the required coherent two-order interaction remains available. No
deployed loss-localization advantage is established by the abstract
parameter distinction alone.

<a id="nr-r10"></a>

## NR-R10 — An entanglement-breaking slot bounds the switched quantum resource

### Product-channel model and a rank bound

Let $\mathcal A,\mathcal B$ be finite-dimensional channels on $S$, with independent slot environments in the standard channel switch. Suppose $\mathcal A$ is entanglement breaking (EB). It admits rank-one Kraus operators

$$
A_i=|a_i\rangle\langle\alpha_i|.
$$

The other channel's Kraus operators $B_j$ need not be rank one. The full controlled switch, including an arbitrary input control, has Kraus operators

$$
W_{ij}=|0\rangle\langle0|_C\otimes B_jA_i
       +|1\rangle\langle1|_C\otimes A_iB_j.
\tag{3}
$$

Each diagonal block has rank at most one, so $\operatorname{rank}W_{ij}\le2$. An arbitrary sender encoding into $C\otimes S$, receiver instrument or conditioned control measurement cannot increase that Kraus rank. Hence every reference-output state has Schmidt number at most two. More generally, if one slot has a Kraus representation of rank at most $r$, the corresponding bound is $2r$. This uses the established [partially entanglement-breaking channel framework](https://arxiv.org/abs/quant-ph/0511244).

Starting with no shared entanglement, $n$ such channel uses interleaved with arbitrary LOCC give Schmidt number at most $2^n$. Indeed, a rank-two rectangular Kraus map transferring a subsystem from Alice to Bob is a sum of two rank-one maps. Applied to a pure state of Schmidt rank $R$ across their cut, it produces at most $2R$ product terms. Local Kraus maps, classical adaptation and postselection do not increase this number. Refining all hidden outcomes gives the same bound for mixed states.

Consequently every fixed-$n$ accepted output obeys

$$
\langle\Phi_K|\rho_{\rm acc}|\Phi_K\rangle
 \le\min\{1,2^n/K\}.
\tag{4}
$$

For a pure Schmidt-rank-$s$ vector this follows from Cauchy–Schwarz, $|\langle\Phi_K|\psi\rangle|^2\le s/K$; convexity proves the mixed-state claim. Equation (4) is a strong converse for rates above one qubit per switched use, including LOCC distillation. High payload dimension does not remove this ceiling.

For recorded random stopping, let $p_n$ be the accepted probability at $N=n$ and $q_K$ the unnormalized Bell-pass probability. The valid bound is

$$
q_K\le\sum_n p_n\min\{1,2^n/K\}.
\tag{5}
$$

One cannot substitute $\mathbb E N$ into $2^n$. Exact accepted $\Phi_K$ requires $n\ge\lceil\log_2K\rceil$ on every successful count sector, so $p\lceil\log_2K\rceil\le\mathbb E N$. Rare long branches are fully charged.

### Exact known-channel simulation by a control-quality qubit wire

Define the dephasing wire

$$
\mathcal Q_\kappa(T)=\frac{1+\kappa}{2}T+
 \frac{1-\kappa}{2}ZTZ,\qquad0\le\kappa\le1.
$$

Consider (3) followed by mandatory $\mathcal Q_\kappa$ on its output control. For every $i,j$, its range lies in the two orthogonal sectors spanned by

$$
|0\rangle B_j|a_i\rangle,
\qquad |1\rangle|a_i\rangle.
$$

Choose an isometry $V_{ij}:\mathbb C^2\to C\otimes S$ taking qubit basis vectors to the normalized vectors in these sectors. If a vector is zero, choose any unit vector in its control sector. Set $L_{ij}=V_{ij}^\dagger W_{ij}$. Then

$$
V_{ij}L_{ij}=W_{ij},\qquad
\sum_{ij}L_{ij}^\dagger L_{ij}=I_{C\otimes S}.
\tag{6}
$$

Sector preservation gives $(Z_C\otimes I)V_{ij}=V_{ij}Z$, and therefore

$$
(\mathcal Q_\kappa^C\otimes\operatorname{id})
 \circ\mathcal S(\mathcal A,\mathcal B)
 =\sum_{ij}\operatorname{Ad}_{V_{ij}}
       \circ\mathcal Q_\kappa\circ\operatorname{Ad}_{L_{ij}}.
\tag{7}
$$

This is an exact LOCC-assisted communication construction. Alice applies the instrument $\{L_{ij}\}$, transmits its qubit output once through $\mathcal Q_\kappa$, and sends $i,j$ classically. Bob applies $V_{ij}$. Equality includes every reference correlation and later success flag. At $\kappa=1$, a single noiseless qubit wire simulates the whole known switched channel, not merely its entanglement yield.

For a provider-fixed control $\omega_\kappa=(I+\kappa X)/2$, with only $S$ supplied by the sender, the switch equals output-control dephasing of the $|+\rangle$ switch: (3) commutes with $Z_C$. Equation (7) applies after replacing $L_{ij}$ by $L_{ij}(|+\rangle\otimes I_S)$.

This construction requires known Kraus descriptions and unrestricted known local instruments; their gate cost may be large. It is not a universal simulator of unknown oracles. The qubit wire must be independently usable across the relevant cut, with its classical label, latency and loss costs included. Such a wire is not inferred merely from a drawn control line or from calling a physical path “noise free.”

The same construction extends to rank-$r$ slot Kraus operators, for
$1\le r\le D$. In each control sector, choose an $r$-dimensional isometry
whose range contains the corresponding block's range, padding if its
rank is smaller. Their direct sum is an isometry from
$\mathbb C^2\otimes\mathbb C^r$ satisfying
$(Z_C\otimes I_S)V=V(Z\otimes I_r)$. Equations (6)–(7) then hold with
a $2r$-dimensional instrument output and simulating wire
$\mathcal Q_\kappa\otimes\mathrm{id}_r$. This is a protected
$r$-dimensional channel plus one control-quality qubit, rather than a
dimension-free simulator of general channels.

### A coherence budget including finite-mean stopping

For fixed independent provider controls $\omega_\kappa$ on successive uses, define in bits

$$
C_\kappa=D(\omega_\kappa\|I/2)
 =1-h_2\!\left(\frac{1+\kappa}{2}\right).
$$

Assume no initial shared entanglement or other quantum link. An opaque provider supplies a fresh $\omega_\kappa$ only upon each counted launch, independent conditioned on all previous accessible records. No party can encode into, filter, reset or replace that control before routing; no purification or phase-error record is supplied. Post-use control measurements and feedback are allowed. Decisions to launch another invocation or stop are classically recorded. With arbitrary LOCC, memory, distillation and rejected histories, if $c=\mathbb E N<\infty$, the delivered state and accept flag satisfy

$$
E_R(\rho_{\rm out})\le cC_\kappa,
\qquad pE_R(\rho_{\rm acc})\le cC_\kappa,
\tag{8}
$$

where $E_R$ is relative entropy of entanglement. Here $N$ counts launched
switched invocations; each uses one call to each module. Their expected
primitive-module cost is $2c$, in addition to routing and control costs.
Rejected invocations remain included.

Here is the complete accounting argument. Compare the actual protocol with the identical one supplied $I/2$ at every launched control. Each reference invocation is a classical mixture of the two serial compositions, each EB. Its full output, including the classical order flag, is EB. The reference protocol therefore remains separable across Alice–Bob throughout.

For a hard limit $m$, retain launch/stop flags before each invocation. Applying the same instrument to actual and reference states cannot increase their relative entropy. On a launch branch, append $\omega_\kappa$ to the actual state and $I/2$ to the reference; on a stopped branch append the same dummy. The direct-sum chain rule and tensor additivity increase relative entropy by exactly

$$
\Pr_{\rm actual}(N\ge j)\,C_\kappa
$$

at invocation $j$. Reference branch probabilities may differ: the weight in this identity is the **actual** probability. The same switch and all later instruments are CPTP, so data processing cannot increase the ledger. Since initial actual and reference states coincide, truncating on a request for call $m+1$ and rejecting unresolved runs yields

$$
D(\rho_m\|\sigma_m)
 \le C_\kappa\sum_{j=1}^m\Pr(N\ge j)
 =C_\kappa\mathbb E[\min\{N,m\}],
$$

with separable $\sigma_m$. Discard private work registers, keeping the fixed finite-dimensional delivered registers and flag. Finite mean implies $\Pr(N>m)\to0$, so $\rho_m\to\rho_{\rm out}$. A subsequence of the separable $\sigma_m$ converges by compactness; joint lower semicontinuity of relative entropy and monotone convergence of the cost prove the first inequality in (8). LOCC readout and copying of the success flag give the second by the flags property of $E_R$. This charges rare long paths without assuming that their distribution matches the reference protocol.

For accepted Bell fidelity $F$, comparison with the Bell projector and its complement gives $E_R(\rho_{\rm acc})\ge F\log_2K-h_2(F)$: every separable state's Bell overlap is at most $1/K$, and relative entropy contracts under that two-outcome measurement. Thus (8) also bounds approximate, probabilistic entanglement yield.

For **mandatory output-control dephasing**, the wire reduction gives a
stronger port scope: arbitrary sender control encodings are allowed.
It also gives the rank-$r$ finite-mean extension

$$
pE_R(\rho_{\rm acc})\le
c\,[C_\kappa+\log_2r].
\tag{8a}
$$

To see this without assuming an additivity theorem, simulate each wire
by teleportation using
$\tau_\kappa\otimes\Phi_r$, where
$\tau_\kappa=((1+\kappa)/2)\Phi_++((1-\kappa)/2)\Phi_-$.
Pauli teleportation through this Bell-diagonal state implements
$\mathcal Q_\kappa$, and $\Phi_r$ implements the identity channel.
Compare it with the separable resource
$\sigma_2\otimes\sigma_r$, where
$\sigma_2=(|00\rangle\langle00|+|11\rangle\langle11|)/2$
and $\sigma_r=r^{-1}\sum_{t=1}^r|tt\rangle\langle tt|$.
Direct entropy evaluation gives
$D(\tau_\kappa\otimes\Phi_r\|\sigma_2\otimes\sigma_r)
=C_\kappa+\log_2r$. Supply one resource pair only on each counted
launch and perform the same known LOCC instrument, teleportation and
decoding. The reference remains separable. The actual-launch ledger,
truncation and lower-semicontinuity argument above now prove (8a).
This is the standard
[Bell-diagonal teleportation](https://arxiv.org/abs/quant-ph/9604024) and
[relative-entropy channel-simulation methodology](https://arxiv.org/abs/1510.08863)
applied to the explicit sector reduction. Independent fresh resources,
the product-channel model and absence of other quantum links remain
essential. Here too primitive-module cost is $2c$.

The rate ceiling is sharp. The established channel $\mathcal N(\rho)=(X\rho X+Y\rho Y)/2$ is EB, yet switching two independent uses with $|+\rangle$ gives correctable $I/Z$ flags. With $\omega_\kappa$, control readout and correction give exactly $\mathcal Q_\kappa$. Its phase-error coding rate is $C_\kappa$; hence the general bound cannot be reduced. Taking both slots to be $\mathcal N\otimes\mathrm{id}_r$ attains $\mathcal Q_\kappa\otimes\mathrm{id}_r$ and $C_\kappa+\log_2r$. The dephasing rate follows from the matching hashing and relative-entropy bounds in the linked capacity source. This is the known [perfect-activation mechanism](https://arxiv.org/abs/1810.10457), with its stated noisy-control/protected-factor specialization, not a new activation protocol.

The fixed-port premise matters: at $\kappa=0$, an allowed pre-use $X$ measurement and conditional $Z$ reset $I/2$ to $|+\rangle$, invalidating the initial-state budget. Encoding or free control filtering can also replenish/select coherence. Mandatory dephasing **after** arbitrary encoding is different: (7) still applies, so a physically available $\mathcal Q_\kappa$ wire exactly simulates that known full channel.

### Placed channels, memory and architectural interpretation

EB reduced marginals alone are insufficient. Draw one uniformly random Pauli string $P$ and apply that same $P$ in both slots. Each isolated marginal is completely depolarizing and EB, but $P^2=I$: ordinary serial transmission already preserves a full $D$-dimensional payload. This correlated two-time resource lacks the product Kraus factorization used in (3). Hidden quantum baths and reused environmental memories likewise need their joint process specified.

Across a network cut, the full accessible instrument matters. An EB Pauli channel with its error label discarded can become perfectly correctable when that label is exposed. Also, [NR-R06](architecture-baselines.md#nr-r06)'s local Bell-label decoder is not automatically LOCC: a transmitted Bell probe leaves its halves at different sites, and compiling a known unitary on an Alice-stored payload does not move it to Bob.

Known switch activation genuinely beats ordinary EB-channel networks with no additional quantum resource, even allowing coding and distillation. It is not generally a trivial side channel: [Kristjánsson et al.](https://arxiv.org/abs/1910.08197) explicitly distinguish provider-fixed switch placement from control encodings that independently bypass the channels. Equations (7)–(8) instead screen a **specified physical architecture** where an equally usable control-quality wire really exists. They do not establish that every implementation has one, nor settle multi-receiver locality constraints such as [random-receiver communication](https://arxiv.org/abs/2012.15459).

Control coherence as a communication resource has prior thermodynamic treatment, including [Liu, Ebler and Dahlsten](https://arxiv.org/abs/2205.07406); the current bounds use the explicit EB/product-channel and cut assumptions above. A practical gain still requires a named wiring graph, allowed mode encoders, actual control transport, loss, reset and memory costs. No new deployed-link advantage follows solely from the channel activation or these reductions.

<a id="nr-r10-random-receiver"></a>

### Random receivers require a physical controller graph

The bipartite simulator (7) does not settle a distributed locality task.
[Bhattacharya et al., PRX Quantum **2**, 020350 (2021)](https://doi.org/10.1103/PRXQuantum.2.020350)
([full protocol and Appendices D--E](https://arxiv.org/html/2012.15459v1))
give a prior positive example: a sender encodes an unknown qubit across
$n$ receivers before knowing which receiver will later be chosen. The
receivers then localize it using LOCC. A global switch of two products of
$\mathcal N_{XY}(\rho)=(X\rho X+Y\rho Y)/2$ permits this through EB
slots, whereas adding noiseless side channels to only a proper subset
does not. Their arbitrary-controlled-operation ordinary construction and
their odd-$n$ obstruction for the specified controlled permutations are
different resource comparisons. Their proposed one-photon realization
simulates receiver sites with different degrees of freedom; it is not
a spatial network demonstration.

The following conditional constructions identify ordinary comparators
for concrete controller interfaces. They preserve that prior separation
and do not infer free quantum wires from control lines.

**Distributed controls implementing one global flag.** Let local switches
have Kraus operators

$$
S_i=P_0^{C_i}\otimes F_{b_i}E_{a_i}
       +P_1^{C_i}\otimes E_{a_i}F_{b_i}.
$$

If the controls start in
$|G_n\rangle_C=(|0^n\rangle+|1^n\rangle)/\sqrt2$, their joint action on
an arbitrary payload is

$$
\frac{|0^n\rangle\otimes K_0+|1^n\rangle\otimes K_1}{\sqrt2},
\qquad K_0=\bigotimes_iF_{b_i}E_{a_i},\quad
K_1=\bigotimes_iE_{a_i}F_{b_i}.
\tag{RR1}
$$

For local $X$-measurement outcomes $\mathbf x$, the payload Kraus is
$2^{-(n+1)/2}[K_0+(-1)^{|\mathbf x|}K_1]$. There are $2^{n-1}$
patterns of each parity. Summing each parity therefore gives exactly
the corresponding global-switch flag map, on every input/reference.
This supplies an explicit implementation using $n$ local order registers
and their coherent repetition state. Its generation, distribution,
memory, route loss and readout are physical resources. The identity does
not prove independently usable noiseless control transport: the complete
switched noise may act on order coherence. If independently declared
local $Z$-dephasing visibilities are $\nu_i$, the repetition coherence is
$\kappa=\prod_i\nu_i$. In the specified ideal $\mathcal N_{XY}$/GHZ code,
the imperfect parity flag then leaves logical $Z$ error $(1-\kappa)/2$
and entanglement fidelity $(1+\kappa)/2$. This assumes that full noise
model; a measured fringe alone does not establish it.

**An ordinary parity sandwich for the known noise alphabet.** Suppose the
actual interface also supplies known controlled operations before and
after the two serial product channels, with the same controller retained
coherently. For the $X/Y$ Kraus alphabets, put $e_i=a_i\oplus b_i$.
Each $F_{b_i}E_{a_i}$ is a scalar times $Z^{e_i}$, and reversing that
pair multiplies it by $(-1)^{e_i}$. With $Q=X^{\otimes n}$, consequently

$$
K_1=(-1)^{|\mathbf e|}K_0=QK_0Q.
\tag{RR2}
$$

Let $C_Q=P_0^C\otimes I+P_1^C\otimes Q$. Apply $C_Q$, the two actual
channels in a fixed order on the payload, then $C_Q$ again. The resulting
ordinary Kraus operator is

$$
C_Q(I_C\otimes K_0)C_Q
 =P_0^C\otimes K_0+P_1^C\otimes QK_0Q
 =P_0^C\otimes K_0+P_1^C\otimes K_1.
\tag{RR3}
$$

This is the full switched channel, before encoding, flags or decoding;
it does not estimate the individual errors. Known, possibly nonuniform
exogenous probabilities on the same Kraus alphabet do not change this
branchwise identity. With a distributed repetition control, controlled-$Q$
on its code is implemented by the local controlled-$X_i$ gates from
$C_i$ to $D_i$. The comparator uses the same $2n$ noisy elementary slots,
two such known checks per payload and the actual control distribution and
storage. It is not free LOCC when the control exists only centrally.
Its premise includes a serial channel on the payload while that control
is retained: a path switch alone does not grant a common fixed-order
rail, a bypass, or an environment-independent control extension. Those
ports and records must be checked in the native graph. This is a
specified-noise check construction, not a universal ordinary simulation
of spatially distributed unknown channels.

**A travelling Fredkin bus has a separate ordinary fanout protocol.**
Consider a physical bus qubit $C$ that can carry the input from the source
and visit every receiver before the recipient is chosen. At each receiver
it can control a SWAP of two configurable local target qubits; local
preparation and $X$ readout are available. This is a stronger stated
interface, not a consequence of the abstract global switch.

At receiver $i$ prepare $T_i=0,A_i=1$. Fredkin sends

$$
(\alpha|0\rangle+\beta|1\rangle)_C|0,1\rangle_{T_iA_i}
 \longmapsto
 \alpha|0,0,1\rangle+\beta|1,1,0\rangle.
\tag{RR4}
$$

An $X$ measurement of $A_i$ with outcome $m_i\in\{0,1\}$ leaves,
up to its constant $1/\sqrt2$ factor and a global sign,
$Z_C^{m_i}(\alpha|0,0\rangle+\beta|1,1\rangle)_{CT_i}$.
The $Z_C$ frames commute with subsequent bus-controlled swaps, so their
correction can be deferred. After all $n$ visits measure $C$ in $X$ with
outcome $b$. If $V_n|c\rangle=|c^n\rangle$, the complete branch map is

$$
K_{\mathbf m,b}
 =2^{-(n+1)/2}(-1)^{|\mathbf m|}
       V_n Z^{b\oplus (|\mathbf m|\bmod2)}.
\tag{RR5}
$$

Thus all $2^{n+1}$ branches have input-independent probability
$2^{-(n+1)}$, and a known local $Z$ removes their logical frame.
Linearity gives the same isometry for any reference-entangled input.
The parties retain the GHZ encoding until the later receiver choice,
then use the other receivers' local $X$ outcomes and their classical
parity to recover the message. No recipient was needed when the bus
travelled, and no branch is rejected.

The cost is one coherent bus visit and one Fredkin per receiver, two
initialized local target qubits and one auxiliary measurement per visit,
a final bus measurement, classical messages and retained receiver memory.
The bus transport, errors and source loading must be supplied and charged.
If the same configurable Fredkin and known single-qubit gates are available
at the source, loading has an explicit constant construction. Write
$F=\operatorname{Fredkin}_{C;T,A}$. Then

$$
FZ_TFZ_T=P_0^C\otimes I+P_1^C\otimes Z_TZ_A.
\tag{RR6}
$$

On $A=0$ this is $\mathrm{CZ}_{CT}$ and returns $A$ unchanged.
Hadamards give CNOT, Hadamards on both systems reverse its direction,
and three CNOTs give source SWAP, costing six Fredkins and known rotations.
This optional loading circuit assumes those actual source ports.
The extra local targets and intermediate measurements in (RR4)--(RR6)
are absent from the fixed-payload controlled-permutation comparison;
they do not contradict it. Nor is this an assertion that every optical
order router can be reconfigured as a receiver-local Fredkin bus.

**Pre-existing entanglement and complete cut maps.** If Alice actually
shares an $(n+1)$-party GHZ state with the candidate receivers, she can
teleport her input into its repetition-code block by a local Bell
measurement and broadcast the Pauli frame, allowing the same late choice.
Its preparation, heralding, distribution and memory are charged. A GHZ
state only among the receivers is a different resource: without an
Alice share it cannot move an input across an otherwise entirely EB
Alice-versus-receivers cut. A provider-fixed control also need not expose
Alice's required encoding or Bell-measurement port.

One elementary graph test is useful. If a receiver cut is initially
separable, every actual transmitted quantum system crossing it undergoes
an EB map on its complete degrees of freedom, and all remaining
operations are local or classical across it, the final reference/receiver
state remains separable. Refine each crossing map into measure-and-prepare
terms; every term and every later local operation preserves separability,
including adaptive branches and local memories. Perfect communication
to that receiver would instead deliver an EPR pair. Therefore a native
random-receiver implementation must identify, at every relevant cut,
the non-EB complete map, initial entanglement, coherent nonlocal operation
or channel memory that invalidates that premise. This test does not
identify a separately usable noiseless wire: complete path/vacuum/time
extensions and provider-fixed placement must still be analyzed.

There are real ordinary network baselines. [Pompili et al.](https://doi.org/10.1126/science.abg1919)
demonstrate three-node solid-state multipartite entanglement using remote
links, memory, local logic and real-time feedforward. A more recent
[three-atom network](https://arxiv.org/html/2606.32006v1) sequentially
uses photonic entanglement swapping and heralded storage; it reports
$77(1)\%$ GHZ fidelity, lifetime above $200\,\mu$s and $0.16\%$
generation efficiency. Its nominal generation rate excludes technical
duty limitations. These experiments expose light--matter and memory
costs; neither implements the global switch or validates an ideal
$\mathcal N_{XY}$ spoke. In the bare one-share-per-receiver GHZ code,
tracing out any lost share removes the logical off-diagonal, so all-share
survival under independent loss is the product of the transmissions.
Other loss-tolerant codes need a separate matched ordinary comparison.

The next native test is a complete spatial graph with source ports,
controller locations, all quantum paths and records, followed by a
late-choice delivered-fidelity/rate comparison with the applicable
check sandwich, bus fanout or pre-entanglement method. The conditional
identities above supply no general hardware no-go, no new priority claim,
and no demonstrated native random-receiver advantage. Their universal
proofs are analytic; the communication replay checks finite phase,
code, branch and Fredkin identities, not the physical controller graph.

### Complete replacement channels have an exact ordinary realization

There is a stronger ordinary reduction for the special case of two independent, memoryless replacement channels,

$$
\mathcal A(X)=\tau\operatorname{Tr}X,
\qquad \mathcal B(X)=\omega\operatorname{Tr}X.
$$

The states $\tau,\omega$ may be different, unknown and noncommuting. With the switch convention in (3), write an arbitrary control–target input as $\sum_{c,d}|c\rangle\langle d|\otimes X_{cd}$. The complete output blocks are

$$
Y_{00}=\omega\operatorname{Tr}X_{00},\qquad
Y_{11}=\tau\operatorname{Tr}X_{11},\qquad
Y_{01}=\omega X_{01}\tau,\qquad
Y_{10}=\tau X_{10}\omega.
$$

For example, replacement Kraus operators $A_{ab}=F|a\rangle\langle b|$ and $B_{cd}=G|c\rangle\langle d|$, with $FF^\dagger=\tau$ and $GG^\dagger=\omega$, give these blocks by direct summation. The formula extends to an arbitrary inaccessible reference $R$: replace each trace by $\operatorname{Tr}_S$ and each multiplication by $\tau\otimes I_R$ or $\omega\otimes I_R$ on the retained copy of $S$.

An ordinary circuit reproduces this whole quantum channel with one call to each replacement map. Store the actual input $S$ and query $\mathcal A,\mathcal B$ in a fixed order on two auxiliary registers $A,B$, producing $\tau_A,\omega_B$. Their initial states may be arbitrary. In register order $A,S,B$, define

$$
V|a,s,b\rangle=|b,a,s\rangle,\qquad
U=|0\rangle\langle0|_C\otimes V
  +|1\rangle\langle1|_C\otimes I.
$$

Apply $U$ and retain $A$. For $Z=\tau\otimes X\otimes\omega$,

$$
\begin{aligned}
\operatorname{Tr}_{SB}(VZV^\dagger)&=\omega\operatorname{Tr}X,&
\operatorname{Tr}_{SB}Z&=\tau\operatorname{Tr}X,\\
\operatorname{Tr}_{SB}(VZ)&=\omega X\tau,&
\operatorname{Tr}_{SB}(ZV^\dagger)&=\tau X\omega.
\end{aligned}
$$

For example, the last expression's $(a,a')$ entry is $\sum_{s,b}\tau_{a,s}X_{s,b}\omega_{b,a'}$. The same contraction holds when the entries of $X$ are operators on $R$. Applying it to the four control blocks proves equality for arbitrary control–input–reference correlations, all later flags, and coherent downstream use. This does not require learning either replacement state.

The cycle is two controlled register SWAPs: first exchange $S,B$, then $A,S$, on control zero. The resource account is two replacement calls, the same supplied control, two additional $D$-level registers, input retention, those two Fredkin gates, and any exchanges needed to restore a prescribed output port. There is no extra pure $D$-level initial state. For equal register Hamiltonians and a control Hamiltonian diagonal in its control basis, the displayed $U$ commutes with the total bare Hamiltonian; this does not make its physical implementation or storage free. A single fixed bath-contact port requires the corresponding real routing and memory.

The identical-bath thermalization identity and a controlled-SWAP bath circuit appear already in [Felce and Vedral, PRL **125**, 070603 (2020)](https://arxiv.org/html/2003.00794v3). The full constant-channel unfolded ordinary circuit is explicitly established by [Xue et al., PRL **137**, 030404 (2026)](https://arxiv.org/html/2511.04028v2), who distinguish that equality from the convenience of their free-space photonic implementation. [Capela et al., PRA **107**, 062208 (2023)](https://arxiv.org/html/2208.03205v2) likewise compare thermodynamic claims with stronger ordinary replacement and environment-memory processes. These are prior mechanisms, not new priority claims here.

Equality concerns the retained control and working substance. An abstract channel does not specify a reservoir's final heat record, correlations or restoration cost, so it does not by itself prove equal refrigerator heat or coefficient of performance. Partial thermalization, correlated bath uses and inaccessible input storage are distinct models. If the independent actual channels lie within half-diamond distances $\epsilon_A,\epsilon_B$ of the promised replacement maps, each two-call implementation is within $\epsilon_A+\epsilon_B$ of its ideal channel. Their discrepancy is at most $2(\epsilon_A+\epsilon_B)$ before including helper errors. This bound is on unnormalized outputs; rare conditioning can amplify the conditional error.

### Thermal sources, the clean control and ordinary population filters

For identical reset states, a separately prepared plus control and an initially thermal source $\rho=\tau$ give the two physical unnormalized outputs

$$
\sigma_\pm=\frac{\tau\pm\tau^3}{2},\qquad
p_\pm=\frac{1\pm\operatorname{Tr}\tau^3}{2}.
$$

Their nonselective source is $\tau$. When $\tau=\operatorname{diag}(t_i)$ is known, the same pure degenerate flag qubit implements this source-specific instrument without another bath contact:

$$
|i\rangle|0\rangle\longmapsto
|i\rangle\left[
\sqrt{\frac{1+t_i^2}{2}}\,|{+}\mathrm{flag}\rangle+
\sqrt{\frac{1-t_i^2}{2}}\,|{-}\mathrm{flag}\rangle\right].
$$

Measure the flag. Each energy-conditioned rotation extends to a unitary; it commutes with the source Hamiltonian for a degenerate flag. The required spectral knowledge and conditional gates are real resources, especially for a large unknown system. One reset suffices if a fresh $\tau$ must first be prepared. The arbitrary-input cycle above removes this source restriction with different storage and gate costs. Simpler definite-order controlled-phase purification is also explicit in [Goldberg and Heshami, J. Phys. Commun. **7**, 015003 (2023), Section VI](https://arxiv.org/html/2108.08853v3).

A no-work qubit example exposes the same purity budget. Let $S,B_1,B_2$ each start in $\operatorname{diag}(g,e)$, $g=1-e$, $0<e\le1/2$, with identical gap $\Delta$. Give the ordinary circuit the same pure **degenerate** control bit, rotated from plus to zero. On bits ordered $C,S,B_1,B_2$, exchange only

$$
|0,1,0,0\rangle\leftrightarrow|1,0,0,1\rangle,
\qquad
|0,1,0,1\rangle\leftrightarrow|1,0,1,1\rangle.
$$

Both transpositions conserve total $S,B_1,B_2$ excitation. Their control-one destinations initially have zero weight. The only remaining source-excited weights are $ge^2$ and $e^3$, giving unconditional excited population $e^2$, without postselection or temperature estimation. The two bath copies require the same two reset calls. The switched-plus source instead has

$$
p_S=1-\frac32ge,\qquad
e_S=\frac{e+e^3}{2-3ge},\qquad
e_S-e^2=\frac{e(1-e)(1-e+3e^2)}{2-3ge}>0.
$$

The known four-register permutation and restoration of its consumed clean bit must be charged. A nondegenerate control needs its appropriate drive/work account. This is a retained-source population comparison with the plus branch, not an optimum over both switch outcomes or a full refrigerator cycle.

### Thermal bosonic inputs and native number checks

A retained-mode state-preparation comparison can be made without temperature learning. Let

$$
\tau_r=(1-r)\sum_{n\ge0}r^n|n\rangle\langle n|,
\quad 0<r<1,\qquad z=1+r+r^2.
$$

For the switched-plus output of two identical complete resets on this thermal input, define acceptance $p_S$, joint accepted-vacuum probability $q_S$, conditional vacuum fidelity $F_S=q_S/p_S$, and conditional mean occupation $\bar n_S$. Exact infinite sums give

$$
\begin{aligned}
\operatorname{Tr}\tau_r^3&=\frac{(1-r)^2}{z},&
p_S&=\frac{2-r+2r^2}{2z},&
q_S&=\frac{(1-r)+(1-r)^3}{2},\\
\bar n_S&=
\frac{r/(1-r)+(1-r)^3r^3/(1-r^3)^2}{2p_S}.
\end{aligned}
$$

An ordinary QND parity check uses the same clean plus qubit, controlled $e^{i\pi N}$ and an $X$ measurement. Its retained-mode Kraus operators are $\Pi_{\rm even},\Pi_{\rm odd}$, so accepting even gives

$$
p_P=\frac1{1+r},\quad q_P=1-r,\quad
F_P=1-r^2,\quad \bar n_P=\frac{2r^2}{1-r^2}.
$$

All four comparisons are strict for $0<r<1$:

$$
\begin{aligned}
p_P-p_S&=\frac{r(1-r)(1+2r)}{2(1+r)z}>0,\\
q_P-q_S&=\frac{(1-r)-(1-r)^3}{2}>0,\\
F_P-F_S&=\frac{r(1-r)(1+3r^2-r^3)}{2-r+2r^2}>0,\\
\bar n_S-\bar n_P&=
\frac{r(1+4r^2+2r^3+2r^4)}{(1+r)z(2-r+2r^2)}>0.
\end{aligned}
$$

These are nonthermal conditional states; “cooler” here refers to the displayed occupation and vacuum criteria. The comparison also holds for the explicitly all-attempt signed vacuum reward $R=2q-p$:

$$
R_P-R_S=
\frac{r(1-r)(3+4r+4r^2-2r^4)}{2(1+r)z}>0.
$$

No reset contact is needed on the already thermal source, and the check does not resolve its exact initial photon number. An ideal binary vacuum predicate is another ordinary option: $p_V=q_V=1-r$, with exact vacuum on success. More generally, a QND filter with initial vacuum mass $t_0$ obeys $q\le\min\{t_0,p\}$. This bound is attainable by accepting vacuum first and then a chosen fraction of nonvacuum records, giving the frontier $q_{\rm ord}(p)=\min\{t_0,p\}$. Thus it can match $p_S$ with $q_{\rm ord}(p_S)\ge q_S$. The desired acceptance mixing requires the corresponding calibration; the parity inequalities themselves do not.

These controls have real retained-cavity implementations. [Sun et al., Nature **511**, 444–448 (2014)](https://arxiv.org/abs/1311.2534) demonstrate repeated ancilla-assisted QND photon parity. [Hutin et al., PRX Quantum **6**, 010321 (2025), Appendix F.3](https://arxiv.org/html/2409.05557v1) implement vacuum heralding using a 20-microsecond selective qubit pulse and readout, with residual initialization error. They establish relevant native access, not free ideal gates. A finite device comparison must include parity/selective-control duration, readout and reset, cavity loss, rejected outputs, all attempts and any source replenishment. It must also compare available ordinary active cooling, rather than only unassisted equilibrium contacts. No native throughput, heat/COP or general-channel dominance is asserted by these ideal retained-state formulas.

The [communication checker](checks/architecture/verify_communication.py) compares normalized full Choi matrices of the two-reset controlled-cycle circuit and the standard switch for identical and distinct complex states in dimensions two and three. It verifies arbitrary quantum input control, noncommuting reset states and trace preservation using exact Gaussian fractions. The arbitrary-dimensional identities, thermal inequalities and thermodynamic access/heat qualifications above remain analytic; this is not a new Lean audit or a measured hardware advantage.

<a id="nr-r11"></a>

## NR-R11 — Accepted cavity, Raman and nonlinear-scattering instruments

Let a photon bus have a common set of orthogonal mode projectors $T_h$.
Two stations with independent slot environments act on disjoint matter
memories $A,B$ in the standard product-channel switch. Suppose every
**accepted** Kraus operator preserves that same complete bus label:

$$
K_s=\sum_h T_h\otimes A_{s,h}\otimes I_B,\qquad
L_t=\sum_h T_h\otimes I_A\otimes B_{t,h}.
\tag{9}
$$

The local operators may be nonunitary, lossy, noisy, and noncommuting
within a station. Orthogonality gives

$$
L_tK_s=K_sL_t=\sum_h T_h\otimes A_{s,h}\otimes B_{t,h}.
$$

Thus the accepted full-switch Kraus operator is
$I_C\otimes L_tK_s$. Its entire accepted quantum instrument equals
the identity channel on the order control tensored with ordinary serial
processing. For an initially independent plus control, there is no extra
minus flag or conditional matter-state purification.
This statement includes reference systems and arbitrary later photon or
memory measurements; it is stronger than a vanishing average statistic.
It assumes the same station instruments in both routes and common
outcome definitions. It does not identify the rejected/lost instruments.

The separate [remote spin-phase comparison](methods/remote-spin-phase.md)
treats a noncommuting controlled-$X$/controlled-$Z$ photon-bus pair.
It gives ordinary implementations of its detected spin gates on arbitrary
unknown input, with local phase controls and modal-access requirements
charged. A stronger ordinary compiler reproduces the complete observed
detected/no-click spin instrument under calibrated state-independent
erasure, reciprocal propagation and unresolved loss locations. The
proof retains explicit counterexamples to inferring that completion
from a detected-map identity alone. Its spin-dependent cavity extension
retains spectral loss amplitudes and proves that a nonzero rank-deficient
loss Kraus operator prevents exact heralded restoration of an unresolved,
unencoded full-space input. An ordinary entanglement-first construction
protects unknown data from factory losses when extra communication qubits
and local gates are available; their storage, feedback and reset costs
are explicit, including a two-local-CZ online construction. For the
scalar reflected sector, ordinary polarization control attains the
universal average-concurrence bound. A certified ordinary Bell factory
leaves less than 0.104% relative room for a switch improvement at the
specified resonant scalar point. This is not a finite-pulse rate result:
coherent spectral readout can invalidate a pointwise frequency bound.
For a pure reflected state, a fixed-marginal rank reduction and the
credited rank-two assistance theorem give the exact Bell yield from an
arbitrary fully accessible photon purifier. At most eight effective
helper outcomes suffice, followed by priced local filters. A separate
interval certificate gives an ordinary full-Gaussian witness with
Bell probability greater than $0.36675027$ per launch in the stated
elastic model. It requires coherent polarization/temporal-mode analysis;
unresolved inaccessible records do not satisfy that premise.
Within its factorized-pulse, constant-optics bus model, four coherent
photon modes attain the same Bell-yield optimum as any larger path
register. The fixed-spin optimization has five real variables; a single
optical compression must apply across the whole pulse spectrum.
A separate reverse-order compiler matches all survivor vectors for the
stated eigen-polarization source, with coefficients independent of the
cavity response. These are scoped optical comparisons, not complete
loss-record or adaptive-control simulations.
Actual router records, encoded recovery and matched physical clocks
remain open comparisons.

A separate [finite-gain bosonic gate screen](methods/bosonic-order-gates.md)
treats a retained unknown Fock-mode qutrit and a nonlinear sign gate.
It keeps all physical addition/subtraction number records, optimizes the
declared two-order family, and includes the ordinary KLM gate's complete
failure instrument. Independent control, auxiliary photons, detector
resolution and recovery remain explicit resources; the comparison does
not optimize arbitrary optical gadgets or all failed-output utilities.

The accepted-label screen (9) applies to the elastic two-time-bin model of
[Knaut et al.](https://doi.org/10.1038/s41586-024-07252-z). Its local
successful-reflection operator has the form

$$
K_j=|e\rangle\langle e|\otimes X_jR_j
   +|l\rangle\langle l|\otimes R_jX_j,
\qquad
R_j=r_{\downarrow,j}P_{\downarrow,j}
    +r_{\uparrow,j}P_{\uparrow,j}.
$$

Complex reflection contrast and extra local spin operations that
preserve the bus bins retain (9). Relabelling this elastic imperfection
as a generic depolarizer would introduce order sensitivity absent from
the microscopic model. The demonstrated architecture already uses
photon/time-delay-interferometer heralds; those records belong in the
ordinary comparison.

<a id="nr-r11-retained-spin-parity"></a>

### Retaining spin memories requires the ordinary parity and photon-bus comparison

Spin entanglement is a useful architecture endpoint beyond an outgoing
photon correlation. It already has an ordinary chiral-waveguide comparator:
[Mahmoodian, Lodahl and Sørensen](https://doi.org/10.1103/PhysRevLett.117.240501)
([complete one/two-click instrument](https://arxiv.org/html/1602.07054v2))
place one spin-bearing emitter in each Mach--Zehnder arm and use photon
detection to measure parity. Their gate figures are theoretical estimates,
with coupling, detuning, finite-pulse and incoherent-scattering assumptions;
they are not a demonstrated gate between the present two dots. That
separate-arm layout is also different from the inline waveguide pair.

The elementary operator comparison is explicit. In the elastic,
spin-conserving narrowband model, let spin $0$ be optically dark and
spin $1$ have monitored transmission $t_j$. Put
$D_0=\operatorname{diag}(1,t_0)\otimes I$ and
$D_1=I\otimes\operatorname{diag}(1,t_1)$. A balanced MZI gives the
unnormalized detector Kraus operators

$$
K_+=(D_0+D_1)/2,\qquad K_-=(D_0-D_1)/2.
\tag{SP1}
$$

These act on every spin/reference input. Their total effect is
$(D_0^\dagger D_0+D_1^\dagger D_1)/2$. For independent arm-local
spin-preserving loss, Kraus operators
$\ell_j|1\rangle\langle1|_j/\sqrt2$, with
$|\ell_j|^2=1-|t_j|^2$, complete this effect to identity. Accessible
reflected ports should instead be kept as additional outcomes. A no-click
event can disturb an unknown spin state; heralded failure is not a free
nondestructive retry. Preparing and resetting known spins after failed
Bell-pair generation has its actual cost.

Let $P_e=(I+Z_0Z_1)/2$, $P_o=(I-Z_0Z_1)/2$. At $t_0=t_1=-1$,
$K_+=Z_0P_e$ and $K_-=Z_0P_o$. A known local $Z_0$ therefore gives
the complete parity instrument. On $|++\rangle$ either click supplies a
Bell state, with known local frame and probability $1/2$.

There is a stronger ordinary filter for unequal transmissions. Write
$F=X_0X_1$, retain equal-detector two-click events, and restore the spin
frame after the second click. Direct multiplication gives

$$
\begin{aligned}
L_s&=FK_sFK_s,\\
L_+&=tP_e+aP_o,\qquad L_-=-bP_o,\\
t&=(t_0+t_1)/2,\quad
a=(1+t_0)(1+t_1)/4,\quad b=(1-t_0)(1-t_1)/4.
\end{aligned}
\tag{SP2}
$$

For example, the even diagonal entries of $K_+$ are $1$ and
$(t_0+t_1)/2$, while its odd entries are $(1+t_1)/2$ and
$(1+t_0)/2$. Conjugation by $F$ exchanges complementary entries,
giving (SP2). The minus entries on $|00\rangle,|11\rangle$ multiply
to zero; the two odd products are the same $-b$. Thus the retained minus
branch is an exact odd-parity projector up to a scalar, even for unknown
unequal **stationary** $t_j$. The plus branch's incorrect-parity weight
is proportional to $|a|^2$, fourth order in small $1+t_j$ amplitudes.
No estimate of the two matrices is needed for this algebraic cancellation.

This comparator uses two photon launches and successful detections, two
local spin flips between them, and either two final flips or an explicitly
permitted Pauli frame. Each photon occupies one interferometer arm and
one emitter interaction; it does not traverse both emitters in series.
Different-detector events and loss are charged failures. Sources, detector
efficiency/dark counts, readout, spin initialization, waiting time and reset
enter a delivered-pair rate. They cannot be replaced by conditional
fidelity alone.

The stationarity and narrowband premises matter. For finite pulses the
actual Kraus operator is $FK_s(\omega_2)FK_s(\omega_1)$, with the photon
spectra and any bath records retained until their stated measurement.
The two odd amplitudes in the minus branch become
$-(1-t_0(\omega_2))(1-t_1(\omega_1))/4$ and
$-(1-t_1(\omega_2))(1-t_0(\omega_1))/4$. They need not agree.
Pure dephasing, Raman transitions and unfiltered inelastic photons need
their complete environment-labelled instrument. The cited proposal
already examines such imperfections; fitting one complex transmission
does not prove they are absent.

**A counterpropagating quarter-phase pair is the known photon-spin bus.**
There is a nontrivial retained-spin state even when the transmitted photon
alone is a poor endpoint. Assume, as an additional native model, that a
single frequency supplies complementary directional spin phases
$D_j^R=\operatorname{diag}(t_j,1)$ and
$D_j^L=\operatorname{diag}(1,t_j)$, with no reflected or inelastic field.
After matching the two paths, the clockwise and counterclockwise spin
operators are

$$
D_R=\operatorname{diag}(t_1t_2,t_1,t_2,1),\qquad
D_L=\operatorname{diag}(1,t_2,t_1,t_1t_2).
\tag{SP3}
$$

Their measured path Kraus operators $(D_R\pm D_L)/2$ are

$$
K_+=uP_e+vP_o,\qquad K_-=wZ_0P_e+zZ_0P_o,
\quad
(u,v,w,z)=\tfrac12(1+t_1t_2,t_1+t_2,t_1t_2-1,t_1-t_2).
\tag{SP4}
$$

For identical lossless $t=e^{i\theta}$, the minus click on $|++\rangle$
is a Bell state with probability $\sin^2\theta/2$. At $t=i$, the two
Kraus operators are $iP_o$ and $-Z_0P_e$: both clicks give Bell states
with known corrections. At $t=-1$ the minus branch vanishes and the
common product $Z_0Z_1$ does not entangle $|++\rangle$. The quarter-phase
example therefore cannot be dismissed by the resonant $\pi$-phase case.

Its mechanism, however, is already a fixed-order photon-spin protocol.
For lossless $t_j=e^{i\theta_j}$ and a photon logical basis $R,L$,
a single station's full operation is
$V_j=P_R\otimes D_j^R+P_L\otimes D_j^L$. It is, up to basis relabeling,

$$
V_j=\exp\!\left[i\theta_j
 (P_R\otimes|0\rangle\langle0|_j+
  P_L\otimes|1\rangle\langle1|_j)\right].
\tag{SP5}
$$

The $V_j$ commute because they are diagonal in the same photon basis
and act on distinct spins. A separate order register controlling their
permutation therefore factors out; the useful direction register is the
photon bus, not an order flag for these full operators. Their fixed-order product is
$P_R\otimes D_R+P_L\otimes D_L$, exactly the complete path/spin operator
behind (SP3)--(SP4). A photon in $|+\rangle$, two such interactions in
ordinary chronological order and final $X$ readout thus realize the same
flagged instrument. This is an operator identity, not a comparison of
selected state fidelities. The ordinary quarter-phase entangler appears
explicitly in [Hu et al., PRB **78**, 085307 (2008)](https://doi.org/10.1103/PhysRevB.78.085307),
§III, equations (6)--(10),
([published full text](https://api.research-repository.uwa.edu.au/ws/portalfiles/portal/89223500/Final_version_Giant_optical_Faraday.pdf));
its two sequential cavity reflections have the same ideal spin-photon
phase operator and both detector outcomes create spin entanglement.

The fixed-order circuit requires the **actual full logical-photon port**
of each station, such as its two polarization components or a locally
routed pair of directions. An inline device with only outside access does
not automatically permit two independent local direction loops or a
same-order rail. Their extra connections, delays, mode matching and loss
must be compared with the whole-loop Sagnac route. Likewise the two
separate-arm MZI is not a free reconfiguration of the inline pair.
These identities establish neither a universal hardware no-go nor a
new spin-entanglement mechanism. Any remaining benefit would be a
quantified native routing/noise advantage over these existing ordinary
instruments.

There is also a comparator on the **same forward inline rail**, provided
coherent spin flips and time-bin access are actually available. Let
$F=X_1X_2$, so $FD_RF=D_L$ in (SP3). Prepare one photon in coherent early
and late bins. Both bins traverse the same physical order $1\to2$.
Apply each local spin $X_j$ after the early bin has scattered and before
the late bin reaches that spin, then apply it again after the late bin
has scattered. In the ideal separated-window model the complete operator
is

$$
\begin{aligned}
E&=P_e^{C}\otimes D_R+P_l^{C}\otimes I,\qquad
L=P_e^{C}\otimes I+P_l^{C}\otimes D_R,\\
(I_C\otimes F)L(I_C\otimes F)E
 &=P_e^{C}\otimes D_R+P_l^{C}\otimes FD_RF
  =P_e^{C}\otimes D_R+P_l^{C}\otimes D_L.
\end{aligned}
\tag{SP6}
$$

The early history is $FFD_R=D_R$; the late one is $FD_RF=D_L$.
Thus no photon-controlled spin flip or separately addressable local loop
is required. Relabeling the time-bin qubit as the direction qubit and
performing its $X$ measurement reproduces (SP4) on every spin/reference
input. The same identity holds for arbitrary frequency superpositions
when $FD_R(\omega)F=D_L(\omega)$ throughout their support and complete
elastic wavepackets lie in the stipulated windows. Actual single-dot
[time-bin scattering with intermediate spin echo](https://doi.org/10.1038/s41534-023-00717-5)
is an ordinary implementation precedent; it does not demonstrate the
required two-dot complementary instrument.

The comparator pays two local $\pi$ pulses per spin, time-bin separation,
spin/helper coherence, and the actual time-bin readout. A passive balanced
unbalanced-path analyzer retains the desired interference only in its
central time window, with probability $1/2$; its side windows are charged
outcomes in the ideal lossless case (loss further reduces delivered yield).
Complete deterministic time-bin $X$ readout requires additional
active routing or mode conversion with its own loss and latency. There
are four nominal module-window opportunities but only two occupied
interactions in each photon history. This uses the native vacuum/idle
extension and is not an opaque two-query simulator.

Nor does (SP6) identify every noisy bath history. In the Sagnac route,
the two order histories swap which spin is visited earlier; the ordinary
early/late construction shifts both visits in the same temporal direction.
Spin precession, finite scattering tails, pulse disturbance, inelastic
records and a persistent bath therefore need their complete actual
instrument and a matching or error bound. The ideal operator identity
does not silently translate those records into the same state. Any useful
Sagnac advantage must survive this priced same-rail comparator as well
as the available MZI and fixed-order photon-bus alternatives.

A second strong ordinary comparison needs only an external coherent
bypass of the entire inline pair. If native Stark tuning and coupling
permit the resonant elastic $t_1=t_2=-1$ endpoint, its forward operator
is $D_R=Z_1Z_2$. Interference of that same-order rail with the bypass
then gives $(I\pm Z_1Z_2)/2$, the exact all-outcome parity measurement
and both Bell outputs from $|++\rangle$ with one photon. This needs
the actual reference path, beam splitters, phase stabilization, matching
delays and their losses, but no access between the two dots. Stark
tunability alone does not guarantee unitary $\pi$ transmission: finite
coupling efficiency, linewidth and inelastic output must be included.
Neither this conditional graph nor the time-bin method grants the
ordinary comparator a free bypass or noiseless spin pulses.

The complementary phases in (SP3) are themselves a device hypothesis.
Opposite Zeeman transitions can be split, so one incident frequency need
not have the same $t_j$ for both spin-direction choices. The Hallacy PL/HBT
data do not establish arbitrary resident-spin preparation, preservation
and readout with those matched coherent ports. Relative path phase,
drift and finite-pulse spectral overlap must also be calibrated. A path
phase that leaves an output maximally entangled can still leave its
unknown local frame unusable as a calibrated Bell pair. Retained spins
therefore do not remove the need for a complete, measured instrument.

At the ideal quarter-phase endpoint a simple finite comparison can be
stated without optimizing all native protocols. If the only path fault
is dephasing with visibility $v$, and $\eta$ is the valid-photon
preparation/transport/detection probability independent of the spins,
the all-outcome acceptance and joint Bell-good weight are
$p=\eta$, $q=\eta(1+v)/2$. Dephasing is a path phase flip with probability
$(1-v)/2$; it exchanges the two ideal flags, and their usual local
corrections then give an orthogonal Bell state. A passive time-bin
analyzer's factor $1/2$ belongs in its $\eta$. Extra spin-pulse errors,
drift and initialization faults are not contained in this formula.
These parameters and the full preparation/reset duration, rather than
the occupied scattering count, determine a finite delivered-fidelity
and rate comparison. The inline dimer data do not currently provide
all of them for either implementation.

There is relevant measured spin-control hardware, but it must not be
silently combined with the dimer. [Koong et al.](https://doi.org/10.1038/s41467-026-74590-z)
demonstrate Raman control with cyclic Faraday transitions in separate
GaAs/InGaAs devices. A GaAs sequence has $2.195(2)$ ns $\pi$ time, while
its fitted $96.8(1)\%$ contrast is explicitly an **upper bound** on
$\pi$-pulse fidelity. The same experiments use nuclear cooling and
microsecond initialization/readout; their end-to-end efficiency below
$1\%$ prevents single-shot spin readout in that device. These establish
ordinary controls and substantive overheads, not the matched two-dot
quarter-phase gate or its delivered-pair rate.

<a id="nr-r11-raman-swap"></a>

### Raman scattering: useful Bell outputs and stronger ordinary SWAP baselines

The common-label closure (9) does not cover a photon that changes a
retained ground-state spin. A concrete replacement is the single-photon
Raman interaction (SPRINT), rather than an arbitrary depolarizing map.
[Koshino, Ishizaka and Nakamura](https://arxiv.org/html/0909.4762v2),
equations (6)--(19), derive the complete wavepacket map of a degenerate
three-level Lambda system. Its equal-leg, long-pulse limit supplies both
a resonant photon--atom SWAP, up to local phases, and a detuned partial
SWAP. [Bechler et al.](https://doi.org/10.1038/s41567-018-0241-6)
([primary preprint](https://arxiv.org/pdf/1711.10974)) demonstrate passive
state transfer using a single Rb atom and counterpropagating nanofiber
modes. Their attenuated coherent-pulse experiment infers the
single-photon transfer fidelity; it does not demonstrate the two-node
protocols below. [Rosenblum, Borne and Dayan](https://doi.org/10.1103/PhysRevA.95.033814)
([primary analysis](https://arxiv.org/html/1412.0604v3)) include cavity
loss, unguided emission, polarization imperfections and additional levels.
The following flat symmetric model is a declared reduction, not a fit to
that full experiment or the inline quantum-dot dimer.

In particular, [Hallacy et al., published Fig. 3](https://www.nature.com/articles/s44310-026-00148-y.pdf)
identify the selected dimer lines as negatively charged excitons $X^-$
in a $0.5$ T Faraday field. A resident-electron ground manifold is
compatible with that assignment. It does not establish a coherent
common-excited-state Lambda transition or arbitrary ground-spin control.
Ideal Faraday cycling legs are disconnected; a mixing or control
mechanism must supply the Raman cross leg. PL/HBT interference and
Stark alignment do not by themselves measure its amplitude or phase.

**Monitored Raman operator and excluded records.** Label the photon
qubit $P$ by $0=H,1=V$, and the ground-state memory by $0,1$.
The active states are $|H1\rangle,|V0\rangle$; $|H0\rangle,|V1\rangle$
are spectators. Each guided leg has population decay rate $\Gamma$;
all excluded radiative channels together have rate $\gamma\ge0$. Write

$$
a=\Gamma+\gamma/2,\quad \beta=\Gamma/a,\qquad
r(\delta)=-\frac{\Gamma}{a-i\delta},\quad t(\delta)=1+r(\delta).
\tag{RS1}
$$

The accepted one-photon operator $T(\delta)$ is identity on the
spectators and has block $tI+rX$ on the active states. Its active dark
state has eigenvalue $1$, while the bright state
$|b\rangle=(|H1\rangle+|V0\rangle)/\sqrt2$ has eigenvalue
$1-2\Gamma/(a-i\delta)$. Consequently

$$
I-T^\dagger T=
\frac{2\Gamma\gamma}{a^2+\delta^2}|b\rangle\langle b|.
\tag{RS2}
$$

This is a contraction with an explicit positive loss defect. A complete
physical dilation must assign that defect to the actual lost-photon
modes and final memory states. A valid photon herald excludes these
events; tracing them into an accepted ideal SWAP would change the task.
On resonance the defect is $4\beta(1-\beta)|b\rangle\langle b|$.
At $\beta=1$, $T=(Z_P\otimes Z_S)\operatorname{SWAP}_{PS}$.
Known local $Z$ operations convert this to literal SWAP, with their
actual access and faults charged. For $0<\beta<1$ there is coherent
elastic leakage $t=1-\beta$, not a scalar successful SWAP.

The frequency bookkeeping follows from the full one-excitation
resolvent. For ground energies $\epsilon_\mu$, one excited energy
$\epsilon_e$ and optical legs
$v_\mu=\sqrt{\Gamma_\mu}e^{i\phi_\mu}$, include all radiative output
legs in $v$ and put $\Gamma_{\rm tot}=v^\dagger v$. On the correlated
channels $|\mu,E-\epsilon_\mu;g_\mu\rangle$ the flat Markov operator is

$$
S_{\nu\mu}(E)=\delta_{\nu\mu}
-\frac{i v_\nu v_\mu^*}{E-\epsilon_e+i\Gamma_{\rm tot}/2}.
\tag{RS2a}
$$

Its bright eigenvalue is
$(E-\epsilon_e-i\Gamma_{\rm tot}/2)/
(E-\epsilon_e+i\Gamma_{\rm tot}/2)$; every dark eigenvalue is one.
It is therefore unitary on the full optical channel space. Restricting
to monitored rows gives the contraction and the other rows give loss
records with their final ground states. Mismatched mode/ground pairs
are spectators under the ideal selection rules. This derives (RS1)
for equal guided legs and excluded total rate $\gamma$, and identifies
what the scalar reduction omits. A real cavity with extra levels,
intrinsic loss or polarization crosstalk needs its enlarged resolvent.

For nondegenerate ground energies $\epsilon_s$, a transition
$s\to s'$ sends a photon of frequency $\omega$ to
$\omega+\epsilon_s-\epsilon_{s'}$. Thus frequency is part of the
quantum record. In the task below either useful history flips exactly
one memory from $0$ to $1$. Matching the two ground-state gaps and
transfer functions makes their final Raman bands identical; unequal
gaps or frequency-dependent path phases require the actual overlap
kernel or a priced eraser. Detection of $H$ alone does not erase a
frequency record. Reversed propagation must also return the same
logical $H,V$ ports and couplings to each node: chirality does not
automatically supply the same $T$ in opposite routes.

**Complete surviving switch output.** Initialize $PAB$ in $|V00\rangle$.
The ordinary product $T_BT_A$ gives

$$
t_At_B|V00\rangle+t_Ar_B|H01\rangle+r_A|H10\rangle.
\tag{RS3}
$$

For identical $t_A=t_B=t$, $r_A=r_B=r$, a plus-prepared independent
order helper and its $X$ measurement give the unnormalized vectors

$$
\begin{aligned}
|\psi_+\rangle&=t^2|V00\rangle+
 \frac{r(1+t)}2(|H10\rangle+|H01\rangle),\\
|\psi_-\rangle&=\frac{r(1-t)}2(|H10\rangle-|H01\rangle).
\end{aligned}
\tag{RS4}
$$

Both $H$ flags are useful Bell pairs after a recorded local phase
correction. Their total probability is

$$
p_S=|r|^2(1+|t|^2)
=\beta^2[1+(1-\beta)^2]\quad(\delta=0).
\tag{RS5}
$$

The surviving non-Bell outcome has probability $|t|^4$, and lost
photons have probability $1-p_S-|t|^4$. These are all charged outcomes.
Failed attempts change the spin state and require the actual
reinitialization before a retry.

If the spectral density $w(\nu)$ is normalized, both nodes have the
same functions $t(\nu),r(\nu)$ and the routes have matched delays and
Raman bands, (RS4) holds at every frequency. Each useful flag then
factors into one photon wavepacket and a fixed Bell state. In this
model, without narrowband truncation,

$$
p_S=\int d\nu\,w(\nu)|r(\nu)|^2[1+|t(\nu)|^2],
\qquad F_S=1.
\tag{RS6}
$$

This spectral symmetry is an assumption about the full transfer
functions, rather than a consequence of equal carrier transmissions.
Unequal nodes, pure dephasing, unmonitored photon-preserving records,
port mismatch and finite helper coherence need their enlarged instrument.

**Ordinary detuned serial benchmark, with its precise restriction.**
For a monochromatic photon, the ordinary (RS3) output conditioned on $H$
is $r_A|10\rangle+t_Ar_B|01\rangle$. A local phase corrects their
relative argument. It is a Bell pair exactly when
$|r_A|=|t_Ar_B|$. With common $\Gamma,\gamma$ and independently
adjustable real node detunings this is

$$
\delta_A^2=2a\Gamma-\Gamma^2+\delta_B^2.
\tag{RS7}
$$

The success probability is $2\Gamma^2/(a^2+\delta_A^2)$.
It is maximized by $\delta_B=0$,
$\delta_A^2=\Gamma^2+\Gamma\gamma$, yielding

$$
p_D=\frac{2\beta^2}{1+2\beta-\beta^2}.
\tag{RS8}
$$

Indeed, putting $h=1-\beta$, $x=\delta_A/a$, $y=\delta_B/a$
reduces (RS7) to $x^2-y^2=1-h^2$. The denominator $1+x^2$ is
smallest at $y=0$, proving the stated continuous optimum. At
$\beta=1$, A is the source's detuned partial SWAP and B its resonant
SWAP: one photon and two ordinary interactions create a Bell pair
deterministically without an order helper. Independent resonance tuning
or actual frequency conversion must supply the different detunings;
neither is free access inferred from a formula.
This is a pointwise calibrated optimum: choosing the detunings and
correcting the phase needs stable $\Gamma,\gamma$ and relative phase
information. Training and reuse across its measured drift window belong
in a cost comparison.

The positive difference under loss is real but restricted:

$$
p_S-p_D=\frac{\beta^2h^2(1-h^2)}{2-h^2}>0
\quad(0<\beta<1).
\tag{RS9}
$$

For example $\beta=0.9$ gives $p_S=0.8181$ and
$p_D\simeq0.81407035$. This optimizes only a fixed $V00$ input,
one serial traversal of each node, two detunings, final $H$ herald and
unitary phase correction. It is not an ordinary-helper optimum or a
native rate comparison.

For finite bandwidth define $A(\nu)=r_A(\nu)$,
$B(\nu)=t_A(\nu)r_B(\nu)$ and
$z=\int w(\nu)A(\nu)B(\nu)^*d\nu$. Tracing the photon frequency gives

$$
p_{D,H}=\int w(|A|^2+|B|^2)d\nu,\qquad
F_{D,H}=\tfrac12+|z|/p_{D,H}.
\tag{RS10}
$$

Here $F_{D,H}$ is Bell-state overlap (squared fidelity); when
$p_{D,H}>0$, it optimizes one frequency-independent local phase.
Frequency-resolved detection permits a frequency-dependent phase, but
cannot unitarily balance unequal magnitudes. If resolved frequency and
ideal local probabilistic spin filters are additionally granted, their
pure two-term branch gives exact-Bell yield
$2\int w\min(|A|^2,|B|^2)d\nu$. This follows by equalizing the two
Schmidt weights in each resolved branch. The filter, resolution and
latency are additional physical primitives.

**Ordinary helper and source schedules must also be included.** A
balanced coherent path can scatter at A only or B only. Its $H$ output
is $r(|\mathrm{path\ A},10\rangle+
|\mathrm{path\ B},01\rangle)/\sqrt2$. Erasing the path in $X$ and
correcting the recorded sign gives an exact Bell pair with probability
$p_1=|r|^2$, using one occupied scattering per attempt. If two independent
source photons, failure reset and two attempt slots are available, its
success by the second attempt is

$$
p_2=2\beta^2-\beta^4,\qquad
p_2-p_S=2\beta^3(1-\beta)\ge0.
\tag{RS11}
$$

Stopping after success uses at most two occupied scatterings. This
comparison charges the additional photon and preparation, readout and
reset slot, along with the actual separate-node connections. It does
not settle a single-photon or source-limited clock budget. Equation (RS11)
supplies an occupied-scattering yield comparison only after the two
photons and herald/reset slots are granted. Unequal cycle durations
require a complete clock budget; neither (RS9) nor (RS11) is a rate theorem.

There is also an ordinary two-interaction, one-photon protocol using an
independent helper degree $O$ preserved by both nodes. In the ideal
literal-SWAP frame, prepare $(|O0,P0\rangle+|O1,P1\rangle)/\sqrt2$,
with $AB=00$. Apply SWAP$(P,A)$, the known photonic CNOT$(O\to P)$,
and SWAP$(P,B)$. The result is
$|P0\rangle(|O0,00\rangle+|O1,11\rangle)/\sqrt2$.
Both $O$-$X$ outcomes give a Bell pair. No second photon is needed.
This requires real helper-preserving ports and the intermediate
two-degree photonic operation. The switch's path or direction encoding
does not automatically give their product extension.

The ideal protocol must not be silently used for lossy $T$. For input
$\sqrt{p_0}|O0,P0\rangle+\sqrt{p_1}|O1,P1\rangle$, the same raw
scattering circuit gives instead

$$
\sqrt{p_0}|O0,P0,00\rangle+\sqrt{p_1}\bigl[
t_A|O1,P0,00\rangle+r_At_B|O1,P1,10\rangle+
r_Ar_B|O1,P0,11\rangle\bigr].
\tag{RS12}
$$

The elastic $t_A$ term is accepted leakage, rather than a scalar
efficiency. Optimizing actual photon/helper operations, readout and
spin filtering with (RS1) remains necessary before assigning an advantage.

<a id="nr-r11-bare-swap-gate"></a>

**A bare two-SWAP switch cannot deliver a full unknown-memory unitary.**
Known-input Bell preparation in (RS4) is different from a gate on
arbitrary unknown $ABR$. Let $A,B,S$ each have dimension $d\ge2$,
$D=d^2$, and let binary $C$ remain the actual order label in

$$
W=|0\rangle\langle0|_C\otimes
  \operatorname{SWAP}_{SB}\operatorname{SWAP}_{SA}
 +|1\rangle\langle1|_C\otimes
  \operatorname{SWAP}_{SA}\operatorname{SWAP}_{SB}.
\tag{SG1}
$$

The initial state $\rho_{CS}$ may be arbitrary, including entanglement,
but is independent of the input $ABR$. There is no additional accessible
correlated program or purification. After (SG1), allow arbitrary joint
$CS$ measurement, postselection on available classical records, and any
conditional CPTP/TNI decoder on $AB$ with fresh independent ancillas.
The Kraus refinement below includes accessible and unobserved outcomes
for the proof; it does not grant access to hidden records or purification.
The target output is the two memories, not a reassigned $S$-inclusive
payload. Extra coherent bus–memory gates, intermediate processors or
input encoding into protected registers define different protocols.

For a pure source write
$|\Psi\rangle_{CS}=|0\rangle|\chi_0\rangle+|1\rangle|\chi_1\rangle$,
with unnormalized $\chi_i$. On basis input $|a,b\rangle$ the output is
$|0\rangle_C|b\rangle_S|\chi_0,a\rangle_{AB}
 +|1\rangle_C|a\rangle_S|b,\chi_1\rangle_{AB}$.
Thus its $AB$ support lies in

$$
\mathcal L=\chi_0\otimes\mathcal H_d+
           \mathcal H_d\otimes\chi_1,\qquad
\dim\mathcal L\le r=2d-1<D .
\tag{SG2}
$$

When both vectors are nonzero the two summands intersect only on
$\operatorname{span}\{\chi_0\otimes\chi_1\}$; if one is zero the dimension
is $d$. Contracting any fine $CS$ measurement row gives an $AB$ operator
with range in $\mathcal L$. Composing a decoder Kraus operator cannot
increase its rank. For mixed $\rho_{CS}$, refine its pure-state
decomposition in an inaccessible preparation record: each fine Kraus
$K_\mu$ still has rank at most $r$, though there need not be one common
$\mathcal L$ for the mixture. This is a full-input isometry argument and
therefore includes every passive reference.

For target unitary $U$ define the mean accepted yield and unnormalized
target Bell overlap

$$
p=\frac1D\sum_\mu\operatorname{Tr}K_\mu^\dagger K_\mu,\qquad
g=\frac1{D^2}\sum_\mu|\operatorname{Tr}(U^\dagger K_\mu)|^2.
$$

These use a normalized maximally entangled $D$-dimensional input; a
general accepted yield need not be input independent. The trace-norm
inequality gives
$|\operatorname{Tr}(U^\dagger K_\mu)|^2
 \le r\|K_\mu\|_{\rm HS}^2$, hence

$$
g\le\frac rD p\le\frac{2d-1}{d^2}.
\tag{SG3}
$$

For a complete protocol this is an all-attempt entanglement-fidelity
ceiling; rejected erasures have zero good overlap. For $p>0$ its accepted
normalized Choi overlap also obeys $g/p\le r/D$. An exact accepted map
$q\operatorname{Ad}_U$ has rank-one Choi support, so every fine Kraus
must be $c_\mu U$. Since those have full rank unless zero, (SG2) forces
$q=0$. Coarsening or rare postselection cannot remove the obstruction.
For qubit memories the ceiling is $3/4$; it concerns a full unknown gate,
not a known Bell output or a promised lower-dimensional code.

There is also a quantitative exact-yield boundary near this ideal.
Suppose the actual and ideal **whole-circuit**, normalized Stinespring
isometries from the $D$-dimensional input $AB$ into the same
output/dilation space satisfy
$\|W_{\rm actual}-W_0\|_{\rm op}\le\epsilon$, with aligned source,
relative order phase and inaccessible-environment labels. Apply the
same allowed terminal instrument, decoder and acceptance to both.
Its common dilation and acceptance projection give
$\sum_\mu\|K_\mu-K^0_\mu\|_{\rm HS}^2\le D\epsilon^2$.
If the actual accepted map is exactly $q\operatorname{Ad}_U$, then
$K_\mu=c_\mu U$, whereas $\operatorname{rank}K^0_\mu\le r$.
The best rank-$r$ approximation misses $D-r$ equal singular values, so

$$
(D-r)q\le D\epsilon^2,\qquad
q\le\min\!\left\{1,\frac{d^2}{(d-1)^2}\epsilon^2\right\}.
\tag{SG4}
$$

For $d=2$ this is $\min\{1,4\epsilon^2\}$, not a strict noisy no-herald
claim. Per-slot errors must first be composed: two aligned slot bounds
$\epsilon_A,\epsilon_B$ give whole error at most
$\epsilon_A+\epsilon_B$, hence $16\epsilon_{\rm slot}^2$ for equal
qubit-slot bounds. Reduced-channel fidelity or a selected reflected
process does not certify that full coherent distance. The Raman model
above supplies literal SWAP only in its equal-leg resonant long-pulse
limit, with both local phase frames handled; finite-pulse delays,
partial exchange, loss and additional modes require their actual
complete instrument. The measured transfer experiment is not a
certificate of (SG1) or of $\epsilon$.

The source restriction is substantive. An extra preserved Bell-correlated
$Q$ can escape it even when consumed at terminal readout. More strongly,
if the route can be fixed and preserves the same physical $C$, an
ordinary circuit may repurpose it as that Bell helper rather than as the
order label, implementing (RS13) below. Initial Bell entanglement of
$C,S$ does not itself escape (SG2) while $C$ still controls the two orders.
All helper-preserving ports, readout, feedforward, storage and extra
visits remain charged. This consolidates the singular-branch boundary
for the restricted source and adds its quantitative consequences; it is
not an obstruction to every two-contact Raman program.

The existing [Raman replay](checks/architecture/raman_baselines.py) adds
literal $d=2,3$ word/support, complex joint-readout, normalization and
rank/overlap ingredients. Arbitrary-decoder, all-dimension and
whole-isometry perturbation statements (SG2)–(SG4) are analytic proofs,
not conclusions inferred from those finite examples.

**Unknown-memory SWAP has an ordinary teleportation comparator.**
With the same ideal SWAP ports, prepare a Bell pair of flying $P$ and
clean helper $Q$, perform SWAP$(P,A)$ then SWAP$(P,B)$, and jointly
Bell-measure $P,Q$. For arbitrary input $|x\rangle_A|y\rangle_B$, the
premeasurement state is
$|\Phi^+\rangle_{AQ}|x\rangle_B|y\rangle_P$.
For Bell states
$|B_{mn}\rangle_{PQ}=2^{-1/2}\sum_{p=0}^1(-1)^{np}
|p,p\mathbin\oplus m\rangle$, the branch operator on $AB$ is
$\tfrac12(X^mZ^n)_A\operatorname{SWAP}_{AB}$.
Applying $(Z^nX^m)_A$ gives

$$
K_{mn}=\tfrac12\operatorname{SWAP}_{AB},\qquad
\sum_{m,n}K_{mn}(\cdot)K_{mn}^\dagger
=\operatorname{Ad}_{\operatorname{SWAP}_{AB}}.
\tag{RS13}
$$

The product-input calculation extends linearly to every entangled
input and reference; all four outcomes have probability $1/4$.
$Q$ may be a second degree of the same photon if the actual node
preserves it. Complete joint readout of two degrees of one photon,
local phase frames, feedforward, storage, route matching and losses
must be supplied and charged. This is the standard entanglement-transfer
and teleportation construction; no novelty or full noisy simulation
claim is made. Replacing its two SWAPs by actual $T$ changes the
instrument, just as in (RS12).
Complete polarization/path Bell readout on one photon has an
[experimental linear-optics precedent](https://arxiv.org/abs/quant-ph/0303125).
That validates the operation class, while its compatibility with the
actual SPRINT port encoding remains an additional implementation task.

**Known flying programs also give ordinary gates on unknown memories.**
Keep the same ideal, known-frame contacts and write $D=P$ for their
flying qubit. All additional helper factors below are accessible to the
known source, intermediate processor and terminal readout, and are
preserved by the node contacts. These are sufficient constructions,
not minimum-mode or minimum-control theorems.

With one helper qubit $E$, prepare $|\Phi^+\rangle_{DE}$ and place the
known accepted contraction

$$
V_{\rm even}=\frac{
 |00\rangle\langle00|+|00\rangle\langle11|
+|11\rangle\langle00|-|11\rangle\langle11|}{\sqrt2},
\qquad
V_{\rm even}^\dagger V_{\rm even}=P_{\rm even}
\tag{RS14}
$$

between $\mathrm{SWAP}_{AD}$ and $\mathrm{SWAP}_{BD}$.
It annihilates the odd sector and maps $|a,a\rangle$ to
$\sum_x(-1)^{ax}|x,x\rangle/\sqrt2$.
After the second contact the Bell convention of (RS13) gives

$$
K_{mn}=\frac{X_B^m\,\mathrm{CZ}_{AB}Z_A^m Z_B^n}{2\sqrt2},
\qquad
(Z_A^m Z_B^nX_B^m)K_{mn}
=\frac{\mathrm{CZ}_{AB}}{2\sqrt2}.
\tag{RS15}
$$

Indeed the first contact leaves $A=d,D=a,E=d$ in the Bell-source
sum; the filter enforces $d=a$, and the Bell bra enforces
$x=b\oplus m$ with phase $(-1)^{ax+nb}$.
Each of the four useful flags has effect $I/8$ on arbitrary $AB$.
Thus the complete accepted map is
$\tfrac12\operatorname{Ad}_{\rm CZ}$, including arbitrary references.
The complementary probability is $1/2$.
The filter is not a closed four-mode unitary: $P_{\rm odd}$ is a
positive reject completion, since
$V_{\rm even}^\dagger V_{\rm even}+P_{\rm odd}=I$.
Rejected light must exit failed ports before the B contact and cannot
be counted as CZ-success readout. Simply tracing those ports can damage
the unknown input.

There is a stronger completion if the rejected odd optical modes are
retained coherently and read **before B** in the basis
$2^{-1/2}(|01\rangle+(-1)^n|10\rangle)$.
The odd constraint is $d=a\oplus1$, so its two branch operators are

$$
J_n=\tfrac12(X_A Z_A^n\otimes I_B),\qquad
(Z_A^nX_A\otimes I_B)J_n=\tfrac12 I_{AB}.
\tag{RS15a}
$$

Both have effect $I/4$. Together with the four CZ flags (RS15), these
give a complete six-flag trace-preserving instrument: corrected success
is $\tfrac12\operatorname{Ad}_{\rm CZ}$ and corrected early failure is
$\tfrac12\operatorname{Id}$, on every $ABR$.
This needs coherent odd-sector erasure, its detectors and local
feedback; a lost photon is not such a flag. With fresh Bell helpers
and the exact ideal contacts, these identity failures permit the
standard [repeat-until-success mechanism](https://arxiv.org/pdf/quant-ph/0408043).
Stopping at the first CZ flag takes a mean of two attempts, two A
contacts and one B contact, hence three occupied contacts.
There is no hard three-contact cap.
With at most $M$ attempts, the final recorded maps are
$(1-2^{-M})\operatorname{Ad}_{\rm CZ}$ and
$2^{-M}\operatorname{Id}$, and the expected occupied-contact count is
$3(1-2^{-M})$.
Source/readout/calibration, correction, storage and complete failure
clocks are charged. Actual Raman loss, partial exchange or unresolved
records do not inherit this ideal identity-failure completion.

A deterministic CZ uses two preserved helper qubits $E_0,E_1$.
Prepare $|\Phi^+\rangle_{D E_0}|0\rangle_{E_1}$. After the A contact,
apply, in chronological order,

$$
\mathrm{CNOT}_{D\to E_1},\quad
\mathrm{CNOT}_{E_0\to E_1},\quad
\mathrm{CNOT}_{D\to E_0},\quad
H_D,\quad
\mathrm{CNOT}_{D\to E_0}.
\tag{RS16}
$$

This is a unitary on all eight flying modes. On its occupied input
$|a,d,0\rangle$ it acts as
$\sum_x(-1)^{ax}|x,x\oplus p,p\rangle/\sqrt2$,
where $p=a\oplus d$.
Then contact B, read $E_1=p$ and Bell-measure $D,E_0$ with label
$(m,n)$. The physical outputs are
$A=a\oplus p$, $B=b\oplus m\oplus p$.
Putting $k=m\oplus p$, their phase is $(-1)^{ab+ak+nb}$, so

$$
K_{pmn}
=\frac{X_A^pX_B^k\,\mathrm{CZ}_{AB}Z_A^kZ_B^n}{2\sqrt2},
\qquad
(Z_A^kX_A^p\otimes Z_B^nX_B^k)K_{pmn}
=\frac{\mathrm{CZ}_{AB}}{2\sqrt2}.
\tag{RS17}
$$

All eight effects are $I/8$ and all outcomes are retained. The
corrected channel is exactly $\operatorname{Ad}_{\rm CZ}$ on every
unknown $ABR$. The basis calculation is an operator equality, so it
also preserves coherences between distinct inputs.

For any prescribed known two-qubit unitary $U$, three preserved helper
qubits suffice. Prepare
$|\Phi^+\rangle_{D E_0}|00\rangle_{E_1 E_2}$.
After $\mathrm{SWAP}_{AD}$, a known $\mathrm{SWAP}_{D E_1}$ stores A's
unknown input in $E_1$ and leaves $D=0$. Prepare
$|\Phi^+\rangle_{D E_2}$ with known $H_D$ and
$\mathrm{CNOT}_{D\to E_2}$, then contact B. For every input
$|\psi\rangle_{ABR}$ the state is now
$|\Phi^+\rangle_{A E_0}|\Phi^+\rangle_{B E_2}
|\psi\rangle_{E_1DR}$.
Apply the known $U$ to $E_1,D$, then Bell-measure $E_1,E_0$ and
$D,E_2$. If their Pauli labels are $(m_A,n_A),(m_B,n_B)$,
the full branch is

$$
K=\tfrac14
(X_A^{m_A}Z_A^{n_A}\otimes X_B^{m_B}Z_B^{n_B})U_{AB}.
\tag{RS18}
$$

The inverse local Paulis give $U/4$. All sixteen effects are $I/16$,
and their sum gives $\operatorname{Ad}_U$ on the prescribed A,B ports
and every reference. No Clifford property of $U$ is assumed:
it is applied before both output teleportations. The known helper
processor must actually implement $U$ on the held inputs; the two
contacts alone do not synthesize it. This uses the standard
[gate-teleportation primitive](https://arxiv.org/pdf/quant-ph/9908010).
It supplies no unknown oracle $U$, or compilation of an arbitrary
switch supermap, for free.

The smaller four-mode Bell program has another distinct corollary:
inserting a known $\mathrm{CZ}_{DE}$ between the two contacts in
(RS13) gives raw branches
$\tfrac12(X_A^mZ_A^n\otimes Z_B^m)
\mathrm{SWAP}_{AB}\mathrm{CZ}_{AB}$.
Local inverse-Pauli feedback gives deterministic
$\mathrm{SWAP}\,\mathrm{CZ}$, whose exchange of the physical outputs
must not be called fixed-port CZ.

The eight-mode CZ admits a qualified serialization on the same
four-mode station port. At A, $E_1=0$, so only $D,E_0$ occupy that
port. After (RS16), the key $p$ has effect $I/2$ on the input.
It is unchanged by the subsequent gates and is eventually measured.
For each fixed $p$, the four corrected Bell flags sum to
$\tfrac12\operatorname{Ad}_{\rm CZ}$.
Consequently dephasing only $p$, or recording only its arrival bin,
does not change the final recorded instrument. The coherent initial
Bell source is essential; it cannot be replaced by a classical
$00/11$ lottery. For example, that fully dephased source gives the
corrected map $\operatorname{Ad}_{\rm CZ}\circ\Delta_A$ instead,
even though all eight flag probabilities remain $1/8$.

A separately supplied coherent mode-to-time router can encode $p$
in two disjoint B arrival windows while $D,E_0$ use the same
four-mode port. In an identity-idle/vacuum frame their actions are

$$
W_0=\Pi_0\otimes F_{DB}+\Pi_1\otimes I,\qquad
W_1=\Pi_0\otimes I+\Pi_1\otimes F_{DB},\qquad
W_1W_0=I_{E_1}\otimes F_{DB},
\quad \Pi_p=|p\rangle\langle p|.
\tag{RS19}
$$

Thus the schedule A,B0,B1 has three potential contact windows and one
occupied A and B contact per history. It needs real mode conversion,
holds and the processor (RS16), but no early measurement of $p$.
An actual nondestructive key readout followed by classical routing is
another sufficient interface with its own latency; final photon
detection does not supply that intermediate readout. Neither
serialization follows from merely counting helper labels. The actual
slot-conditioned scattering, vacuum and idle/bath evolution must
give the displayed common-frame instrument at one finish, with
finite-pulse guards and all extra loss and storage charged.

Their flying computational spaces contain four, eight or sixteen
coherent one-photon modes, respectively; the heralded filter has
additional rejected ports. These are not multiple-photon Bell
measurements. Known mode unitaries and complete single-photon mode
readout are substantive supplied controls, with their synthesis,
calibration and latency charged. Real two-mode SPRINT access does
not automatically extend as identity on the extra helper factors;
the [port and time-bin tests](#nr-r11-raman-route) still apply.
External helper memories instead need their actual coherent transfer
and gates. The resources include Bell preparation, pure helper
registers, internal processing, retained input storage, readout,
classical messages and local Pauli feedback. Losing D can destroy an
unknown supplied input; it is not the coherent early rejection in
(RS15a).
Replacing a SWAP by the actual partial/lossy Raman operator changes
every branch, including coherent elastic leakage. No noisy dominance,
minimum-resource, delivered-rate or hardware-advantage
claim follows from these ideal ordinary programs.

The [communication replay](checks/architecture/verify_communication.py)
checks the full finite gate instruments, traced and coherent early
rejection, helper unitarity, uniform key and complementary B windows.
Its arbitrary-U
coefficient identities support the all-unitary proof (RS18); they
do not certify physical helper-preserving ports or clock costs.

<a id="nr-r11-raman-partial-gate"></a>

**Opposite partial contacts admit a full-input CZ flag, with an ordinary match.**
The bare-SWAP obstruction does not extend to every detuning. In the
lossless equal-leg long-pulse family of the same
[source, equations (15)--(18)](https://arxiv.org/html/0909.4762v2), a known
bus-$Z$ conjugation gives $Z_ST(\delta)Z_S=tI-rF_{Sj}$, where $F$ is
literal SWAP and $r,t$ are (RS1). At $\delta_A=+\Gamma/2$ and
$\delta_B=-\Gamma/2$, put $\theta=\arctan(2)$. The contacts are
$e^{-i\theta}U_A,e^{i\theta}U_B$, with

$$
U_A=\frac{I+2iF_{SA}}{\sqrt5},\qquad
U_B=\frac{I-2iF_{SB}}{\sqrt5}.
\tag{RS19a}
$$

Their scalar phases cancel in either word; the shared conjugating
bus-$Z$ factors cancel internally. Actual independent resonance tuning
or coherent frequency conversion must supply the opposite detunings.
This source-derived ideal family does not certify a two-node order
router, helper-preserving ports or a finite-pulse/loss instrument.

Prepare $|\Phi^+\rangle_{CS}$ independently of arbitrary unknown $ABR$,
where $C$ controls $U_BU_A$ for $0$ and $U_AU_B$ for $1$.
Use the terminal joint basis
$|B_{mn}\rangle_{CS}=2^{-1/2}(|0,m\rangle+(-1)^n|1,1\oplus m\rangle)$.
The $01=\Phi^-$ flag has the full-input Kraus operator

$$
K_{01}=\frac25G,\qquad
G=\operatorname{diag}(1,i,-i,-1)
=(\mathsf S_A^\dagger\otimes\mathsf S_B)\mathrm{CZ},
\qquad \mathsf S=\operatorname{diag}(1,i).
\tag{RS19b}
$$

Thus local correction $\mathsf S_A\otimes\mathsf S_B^\dagger$ gives
$\tfrac4{25}\operatorname{Ad}_{\rm CZ}$ on every $ABR$, with physical
outputs at A,B. This is an operator identity, not a Bell-input score.
For completeness, the other native records are

$$
\begin{aligned}
K_{00}&=\tfrac15\begin{pmatrix}3&0&0&0\\0&1&4&0\\0&0&1&0\\0&0&0&3\end{pmatrix},\\
K_{10}&=\tfrac15\begin{pmatrix}0&2-i&i&0\\2-i&0&0&2+i\\i&0&0&-i\\0&2+i&-i&0\end{pmatrix},\\
K_{11}&=\tfrac15\begin{pmatrix}0&2-i&i&0\\-2+i&0&0&2+i\\-i&0&0&-i\\0&-2-i&i&0\end{pmatrix}.
\end{aligned}
\tag{RS19c}
$$

Together $\sum_{mn}K_{mn}^\dagger K_{mn}=I$; the other three effects
are nonconstant, so output-unitary feedback does not turn these flags
into unitary gates. Further filtering or another terminal POVM is not
excluded.

An ordinary A-then-B traversal matches the displayed useful flag at the
same helper dimension. Repurpose $C$ as a preserved helper, use the same
$\Phi^+_{CS}$ source, and between $U_A,U_B$ place the known accepted
four-mode filter
$V=|00\rangle\langle00|-|11\rangle\langle11|$ on $CS$.
This is an even-mode phase operation in the control class already used
by (RS14), with $V^\dagger V=P_{\rm even}$. Its terminal branches are

$$
\begin{aligned}
L_{00}&=\tfrac25G,&
L_{01}&=\tfrac15\operatorname{diag}(3,1,1,3),\\
L_{10}&=\tfrac15X_B\operatorname{diag}(i,2-i,-2+i,-i),&
L_{11}&=\tfrac15X_B\operatorname{diag}(-i,2-i,2-i,-i).
\end{aligned}
\tag{RS19d}
$$

Their effects are $4I/25$, $\operatorname{diag}(9,1,1,9)/25$ and,
for each of $10,11$, $\operatorname{diag}(1,5,5,1)/25$, summing to
$3I/5$. The $00$ flag therefore gives exactly the same corrected CZ
mass $4/25$. The other terminal flags are nonunitary and are not safe
identity failures. Complete the filter by coherently collecting
$P_{\rm odd}$ and reading $B_{1n}$ **before B**. The early maps are

$$
J_n=\frac{i(-1)^n}{\sqrt5}(X_AZ_A^n\otimes I_B),\qquad
J_n^\dagger J_n=I/5.
\tag{RS19e}
$$

After local correction these give identity mass $2/5$; the four terminal
and two early flags form a trace-preserving instrument. The filter
needs explicit rejected ports and coherent odd-mode erasure, not a
closed four-mode unitary or an unresolved lost photon. Retrying only
these corrected early identity flags with fresh Bell sources gives,
at most $M$ launches, CZ mass
$\tfrac4{15}(1-(2/5)^M)$ and remaining corrected-identity mass $(2/5)^M$.
Other terminal flags stop without a claimed usable gate. With unlimited
early retries the CZ mass is $4/15$, with mean $5/3$ A contacts and one
B contact, hence $8/3$ occupied contacts. This is an ideal stopping
policy, not a hard cap or a measured rate. When early rejects are
actually read before B, one ordinary launch has mean occupied-contact
count $1+3/5=8/5$, versus two for the displayed native circuit. The
filter, readout and feedback times remain paid; this count is not an
optimized-rate comparison.

The selected-branch equality has wider scope than this calibrated point.
For arbitrary scalar contacts $U_A=aI+bF_{SA}$ and $U_B=cI+dF_{SB}$,
the same Bell source, native $\Phi^-$ flag and ordinary $V$/$\Phi^+$
flag give exactly

$$
K=L=\left(\frac{bc}{2}+\frac{bd}{4}\right)Z_A
     +\left(\frac{ad}{2}+\frac{bd}{4}\right)Z_B.
\tag{RS19f}
$$

Indeed the native expansion is
$bcZ_A/2+adZ_B/2+bd(P_{0A}-P_{1B})F_{AB}/2$, and
$(P_{0A}-P_{1B})F_{AB}=(Z_A+Z_B)/2$ on all four basis states.
For ordinary order the zero-, A-only, B-only and two-exchange terms
are respectively $0$, $bcZ_A/2$, $adZ_B/2$ and
$bd(P_{00}-P_{11})/2=bd(Z_A+Z_B)/4$. No unitarity or reality of the
scalar coefficients was used.

This also proves equality of the **full selected retained-frequency
map** when $a,b,c,d$ are common frequency-diagonal elastic
multipliers. They commute, so the identity holds as an operator on
$L^2(d\omega)\otimes AB$, including frequency coherences and passive
references. The Bell source/filter/readout must act on $CS$ with the
same frequency-independent amplitudes, and both routes must have the
same finish and propagation/history-phase frame. Fourier transformation
of the source's stationary equation (14), together with (10)--(13),
gives this multiplier form for its degenerate equal-leg asymptotic
elastic model; replacing an actual routed apparatus by that model
still requires those interface conditions.

For example, in units $\Gamma=1$, let the incident offset be $\xi$,
so $\delta_A=\xi+1/2$, $\delta_B=\xi-1/2$. Then (RS19f) is

$$
K(\xi)=L(\xi)=
\frac{(1+i-2i\xi)Z_A+(1-i-2i\xi)Z_B}{4D(\xi)},
\qquad D(\xi)=(1-i\xi)^2+\tfrac14.
\tag{RS19g}
$$

Its $00,11$ magnitudes are
$\sqrt{1+4\xi^2}/(2|D|)$, versus $1/(2|D|)$ for $01,10$.
Thus proportional CZ is the carrier-point limit; ordinary order matches
the entire selected finite-bandwidth distortion, including a coherent
pulse's off-diagonal frequencies. This is not equality of the other
flags, radiative rejects or full lossy/bath instrument. Different
history delays/phases, frequency-changing processes and noncommuting
retained-bath kernels are outside this commuting-multiplier identity.

Both routes pay for a coherent Bell source and joint readout of two
degrees of one photon, preserved helper coherence, local feedback,
calibrated detunings/phases, drift and reuse, rejected launches, storage
and the complete clock. The ordinary route additionally supplies the
midpoint filter, reject collection and early feedback when retries are
used; the native route supplies coherent order and matched time/mode
records. Finite wavepackets, unequal legs, emission loss or leaked
history records require their actual complete instrument. Matching
the selected flag proves neither equality of the remaining instruments
nor an optimum over filters/POVMs or a physical advantage. The
[same Raman replay](checks/architecture/raman_baselines.py) checks all
ten finite branch maps, source/contact normalization, both complete
instruments and all gate matrix-unit coefficients. Complex scalar
fixtures and two coherently retained frequency bins check the selected
identity and cross-frequency coefficients; the continuum multiplier
extension is the analytic operator argument above.

<a id="nr-r11-two-port-gate"></a>

**The selected-map compiler needs two flying ports, not a SWAP sector.**
Let the flying photon have exactly two retained channels $S$, with arbitrary
local memory spaces $A$ and $B$. Write the callable contractions as

$$
T_A=\sum_{s,t=0}^1|s\rangle\langle t|_S\otimes A_{st},\qquad
T_B=\sum_{s,t=0}^1|s\rangle\langle t|_S\otimes B_{st}.
$$

The blocks are arbitrary local operators, not scalar amplitudes or
excitation-preserving matrices. The interface must actually compose these
contractions: excluded outputs are selected away per contact, enter
absorbing orthogonal failure records, or are proved unable to leave and
return through omitted flying modes. A final surviving-photon or code
projection alone does not justify multiplying projected sub-blocks.

Use the normalized $\Phi^+_{CS}$ source, native histories $T_BT_A$ and
$T_AT_B$, and terminal $\Phi^-_{CS}$. Direct expansion gives

$$
K_N=\frac{B_{00}A_{00}+B_{01}A_{10}
                 -A_{10}B_{01}-A_{11}B_{11}}2
   =\frac{B_{00}A_{00}-B_{11}A_{11}}2=L_F.
\tag{RS19h}
$$

The cancellation uses only that every $A$ block commutes with every $B$
block on disjoint memories. $L_F$ is the ordinary sequence $T_A$, then
the photon-only contraction
$V=|00\rangle\langle00|_{CS}-|11\rangle\langle11|_{CS}$, then $T_B$,
and terminal $\Phi^+_{CS}$. $V$ removes the off-diagonal intermediate
photon paths. Both normalized Bell factors are included, so this is exact
equality of selected trace-nonincreasing maps for every unknown $ABR$
input and arbitrary local dimensions, with output labels unchanged.
For a supplied local instrument the identity holds per fine Kraus pair,
including its records, if the actual common-clock dilation pairs those
history labels. Equality of separately measured channel marginals alone
does not establish that physical pairing.

Common commuting frequency multipliers preserve the cancellation and
every coherent cross-frequency/reference block in the same final frame.
This does not identify other flags or a full lost-photon instrument.
Bell preparation/readout, preserved $C/S$ tensor-product ports, $V$ and
its rejected output, routes, phases and clocks remain paid requirements;
a native route alone does not supply the ordinary midpoint processor.

[Rosenblum, Borne and Dayan, arXiv:1412.0604v3, Secs. IV–V](https://arxiv.org/html/1412.0604v3)
provide a concrete extension beyond the one-bright model: an opposite-sign
excited pathway gives two bright responses. Their larger Eq. (12) retains
cavity modes $a,b$ and local ground states $G_0,G_1,G_2$; unwanted
polarization components are within those two modes. Thus a declared
stationary elastic, degenerate-ground, two-mode guided scattering model
with a common frequency offset fits (RS19h) on the full local qutrit
outputs, when its loss is absorbing and its contacts compose. Two cavity
modes alone do not certify this complete traveling-field interface.
Local code exits do not defeat equality; a common
later code filter preserves it. This is not a fitted timed two-node
instrument, a code-herald apparatus or a demonstrated order router.
Motion during a pulse, frequency-changing ground transitions, additional
flying modes, coherent loss returns and shared bath records need their
actual full interface.

If the blocks instead share a noncommuting field/bath $H$, the exact
remainder is

$$
K_N-L_F=\tfrac12\bigl([B_{01},A_{10}]+[B_{11},A_{11}]\bigr).
$$

Only their sum must vanish; separate locality or common scalar frequency
multipliers suffice. A nonzero remainder alone is not a useful gate.
The concrete remaining test is a useful retained output of an actual
noncommuting or larger-flying-space instrument, with its physical erasure,
loss and ordinary-control ports supplied. The
[same exact Raman replay](checks/architecture/raman_baselines.py) checks
literal Bell/filter/readout contractions for dense excitation-changing
local qubit and qutrit contacts, populated local code exits, full reference
coefficients, and coherent frequency blocks of declared passive two-bright
fixtures. The universal local-block and multiplier arguments, physical
dilation and costs remain analytic or supplied assumptions; these finite
checks certify no device fit or rate advantage.

<a id="nr-r11-raman-operator-gate"></a>

**Noncommuting field coefficients have a measurable selected-map boundary.**
Retain a common field/bath space $H$, and let its coefficients commute
with the displayed logical swaps but not necessarily with each other:
$U_A=A_0I+A_1F_{SA}$, $U_B=B_0I+B_1F_{SB}$.
Use the same Bell source and flags as (RS19f). Suppress tensor identities
on $H$ and $AB$, and write $P_{kA}=|k\rangle\langle k|_A$.
The forward ordinary selected operator and the native remainder are

$$
\begin{aligned}
L_F&=\left(\frac{B_0A_1}{2}+\frac{B_1A_1}{4}\right)Z_A
    +\left(\frac{B_1A_0}{2}+\frac{B_1A_1}{4}\right)Z_B,\\
N-L_F&=\frac12\left([B_0,A_0]I+[B_0,A_1]P_{1A}
              +[B_1,A_0]P_{1B}+[B_1,A_1]P_{1B}F_{AB}\right).
\end{aligned}
\tag{OG1}
$$

These are full $HAB$ operator identities, so retain arbitrary passive
references and correlations before a bath trace. Indeed the native
contraction is
$\tfrac12(\langle0|U_BU_A|0\rangle-\langle1|U_AU_B|1\rangle)$.
Use $\langle k|F_{Sj}|k\rangle=P_{kj}$ and
$\langle0|F_{SB}F_{SA}|0\rangle=P_{0A}F_{AB}$,
$\langle1|F_{SA}F_{SB}|1\rangle=P_{1B}F_{AB}$.
The forward midpoint contraction expands as
$\tfrac12[(B_0+B_1P_{0B})(A_0+A_1P_{0A})
-(B_0+B_1P_{1B})(A_0+A_1P_{1A})]$; subtracting gives (OG1).
An arbitrary CS-only forward midpoint/readout still has the ordered
field words $B_jA_i$, so the commuting proof does not manufacture the
reverse words. A field commutator alone is not a useful gate.

The source-like **one bright sector** has the stronger constraint
$A_0+A_1=B_0+B_1=I_H$. Put $X=A_1$, $Y=B_1$,
$J=[Y,X]$, $D=(X-Y)/2$, and
$u=(X+Y-XY)/2$, $v=-(X+Y-YX)/2$. Then

$$
\begin{gathered}
N=\begin{pmatrix}
u&0&0&0\\0&D&J/2&0\\0&0&-D&0\\0&0&0&v
\end{pmatrix}_{AB},\qquad
L_F=\operatorname{diag}(-v,D,-D,v),\\
L_R=\operatorname{diag}(u,D,-D,-u),\qquad
N-L_F=\tfrac12J P_{0A}F_{AB}.
\end{gathered}
\tag{OG2}
$$

$L_R$ uses ordinary B-then-A visits with the same $V$, Bell source and
Bell-plus flag; it does not swap the physical memory labels.

For a channel statement, fix a common specified initial field/bath state
$\tau_H$, including any purification, independent of logical $ABR$ and
the CS Bell source. The theorem permits a joint field/bath state; a
photon--bath product is not its general premise. Apply the same H-only
accepted CP filter with Kraus $M_r$ after the flag, and let $\Gamma_N$,
$\Gamma_F$ retain $H$, $AB$ and the stated available records. Kraus
refinement includes unobserved outcomes only for the proof; acceptance
cannot use hidden records. A physical filter acts only on available
ports, as identity on inaccessible baths; formally retaining $H$ does
not grant access to those baths or their purification. Directly from
the odd block of (OG2),

$$
\Delta p:=p_N(10)-p_N(01)=\frac{q_M}{4}\ge0,\qquad
q_M=\sum_r\operatorname{Tr}(M_rJ\tau J^\dagger M_r^\dagger).
\tag{OG3}
$$

Thus equal acceptance on these **two** logical basis inputs suffices:
$q_M=0$ forces every $M_rJ\sqrt\tau=0$, and (OG2) proves equality of
the complete selected outputs $\Gamma_N=\Gamma_F$, including all
unknown $ABR$ coherences and retained field records. Any common later
TP decoder preserves equality. In particular, an input-independent
heralded gate/recovery component cannot gain a new selected output here.

There is also a robust unnormalized bound. Choose one fixed purification
$|\psi\rangle_{HE}$ of $\tau$ and identical fine record labels for the
two accepted Stinesprings $V_N,V_F$. Their difference is the tensor
product of $\tfrac12\sum_r|r,\mathrm{records}\rangle
(M_rJ\otimes I_E)|\psi\rangle$ with $P_{0A}F_{AB}$.
Since $\|P_{0A}F_{AB}\|_{\rm op}=1$,
$\|V_N-V_F\|_{\rm op}=\sqrt{q_M}/2=\sqrt{\Delta p}$.
Physical accepted contacts and filters make both Stinesprings
contractions. Expanding their two left/right multiplication maps gives

$$
\frac12\|\Gamma_N-\Gamma_F\|_\diamond
\le\min\{1,\sqrt{\Delta p}\}.
\tag{OG4}
$$

Discarding inaccessible purification systems or applying common
downstream channels only contracts this bound. It controls the selected
map **before normalization**; conditioning on a rare event still needs
its success-probability account. Two measured populations do not by
themselves certify the one-bright model, the matched physical dilation
or its stationarity.

The displayed CZ benchmark has a second ordinary comparison even when
acceptance depends on the input. Use the raw target
$G=\operatorname{diag}(1,i,-i,-1)$ from (RS19b), with its same known
local output correction. For a selected operator $K$ define
$p=\operatorname{Tr}[K(\tau\otimes I_4)K^\dagger]/4$ and
$g=\operatorname{Tr}(T\tau T^\dagger)/16$,
$T=\operatorname{Tr}_{AB}(G^\dagger K)$.
These are accepted Choi mass and unnormalized target Bell weight.
First take no extra H filter, so $q=\operatorname{Tr}(J\tau J^\dagger)$.
The three traces are

$$
\begin{aligned}
T_F&=X+Y-YX-i(X-Y),\\
T_R&=X+Y-XY-i(X-Y),\qquad T_N=(T_F+T_R)/2.
\end{aligned}
\tag{OG5}
$$

A recorded fair coin chooses the ordinary forward or reverse route
before launch. Let $p_O=(p_F+p_R)/2$, $g_O=(g_F+g_R)/2$. Then

$$
g_O-g_N=\frac q{64},\qquad
p_N-p_O=\frac q{16},\qquad
(p_N-g_N)-(p_O-g_O)=\frac{5q}{64}.
\tag{OG6}
$$

The first identity is the parallelogram identity applied to (OG5).
For the second, the native input-column norms sum to
$u^\dagger u+2D^\dagger D+v^\dagger v+J^\dagger J/4$;
the fair-coin sum is the same expression without its last term.
The third identity follows. The argument holds after a common H-only
filter as well, replacing $q$ by $q_M$ and summing the filtered traces.
If $p_N>0$, then $p_O>0$ and the ordinary conditional target Bell
fidelity $F_O=g_O/p_O$ is at least $F_N=g_N/p_N$. Ordinary accepts
**less** mass, so this is not domination of every yield--fidelity
frontier or equality of the two selected maps.

There is a useful high-fidelity constraint. The native off-diagonal
block $J/2$ is Hilbert--Schmidt orthogonal to the diagonal target $G$,
so $p_N-g_N\ge q_M/16$. Consequently

$$
p_O\ge g_N=p_NF_N,\qquad
F_N\ge1-\epsilon\ \Longrightarrow\
p_O\ge(1-\epsilon)p_N,\quad F_O\ge F_N.
\tag{OG7}
$$

This is the declared Choi-average selected-G benchmark, not a
worst-input gate certificate, a clock comparison or an optimized
statement over other CS measurements and data-dependent/joint TNI
acceptance filters.

A declared microscopic connection combines the quantized equal-leg
Lambda model above with the trion-conditioned linear phonon term in
[Koong et al., SI S14--S22](https://arxiv.org/abs/1904.05103).
With selective matched optical legs and identical ground orbital
potentials, only the bright sector scatters through $S_b$ on common
photon frequency and local phonons. Thus
$T=I+P_b\otimes(S_b-I)$; the known bus-$Z$ frame gives
$a=(I+S_b)/2$, $b=(I-S_b)/2$ and $a+b=I$.
Independent local baths need not make these coefficients commute,
because they share the flying frequency. This is a declared Hamiltonian
extension: Koong's Zeeman-split free-space driven Raman experiment
certifies neither an incoming unknown-spin two-channel port nor a
two-node order router. The microscopic thermal scattering extension
may additionally assume product input preparation; it is not needed
for the operator theorem's common joint $\tau_H$.

Both comparisons still pay for their actual routes, helper-preserving
ports, Bell source/readout, midpoint filter/reject collection, carriers,
local phase frames, record access and complete clocks. In particular,
the fair coin needs BOTH ordinary classical visit orders with a
preserved CS helper and the supplied midpoint operation; those ports
are not inferred merely from a native order-selector drawing. The
same initial preparation and physical reset/reuse rule must apply per
launch. This is not a simulation of a reused bath's entire conditional
trajectory. Other flags, general symmetric-sector operators, unmatched
time kernels, preencoding, and joint/data-dependent acceptance are
outside the stated comparisons. A remaining application must specify
a useful required output and a complete costed instrument beyond
these premises; a nonzero phonon or field commutator alone does not
provide one.

The [existing Raman checker](checks/architecture/raman_baselines.py)
replays literal one-bright contacts on finite field spaces, Bell
source/flag contractions, common-filter contrast and retained-output
matrix ingredients, and the accepted/good/bad weight identities.
The all-input positivity, diamond bound, continuum and physical-model
claims are the analytic arguments and assumptions above.

<a id="nr-r11-raman-inelastic-gate"></a>

**A Raman frequency record can add accepted error without adding a gate.**
Consider the following declared stationary selection-rule extension of
(RS19h), keeping the complete frequency/bath space $H$:

$$
T_j=\sum_{s,a}u_j(s,a)|s,a\rangle\langle s,a|
       +p_j|10\rangle\langle01|+q_j|01\rangle\langle10|.
$$

The elastic diagonal blocks are commuting frequency multipliers across
nodes, while $p_j,q_j$ may be nonnormal weighted frequency translations.
More generally only $[D_{B,1},D_{A,1}]=0$ is needed. This allows a
nonzero exchange commutator beyond the two-port local-block hypothesis.
All intermediate frequencies remain part of the callable interface;
final collection of two bands cannot replace the composability/no-return
conditions above. Prepare $\Phi^+_{CS}$ tensor a common $\tau_H$, both
independent of the full unknown $ABR$ input. Match the physical history
records, final frame and clock; these are not inferred from marginal
channel measurements or an input-independent bath rate.

With the same native minus flag and ordinary two-contact midpoint-$V$
plus flag as (RS19h), literal paths give

$$
K_N=L_F+\frac J2E,\qquad J=[q_B,p_A],\quad
E=|01\rangle\langle10|_{AB},\qquad
L_F=\frac{D_{B,0}D_{A,0}-D_{B,1}D_{A,1}}2.
\tag{IG1}
$$

Here $L_F$ is diagonal on $AB$. For
$T_\delta|\omega\rangle=|\omega+\delta\rangle$,
$p_A=T_{\Delta_A}M_a$ and $q_B=T_{-\Delta_B}M_b$ give
$J|\omega\rangle=[a(\omega)b(\omega+\Delta_A)
-b(\omega)a(\omega-\Delta_B)]
|\omega+\Delta_A-\Delta_B\rangle$.
Unequal constant-amplitude shifts still cancel; dispersive weights
produce the new one-way logical exchange.

Allow the same field-only CP trace-nonincreasing filter with Kraus
$M_r$ in both circuits. It acts as identity on inaccessible baths and
purifiers; retaining them in the proof grants no access. Acceptance uses
available records, although hidden outcomes may refine the proof.
Set $q_M=\sum_r\operatorname{Tr}(\tau J^\dagger M_r^\dagger M_rJ)$
and $e=q_M/16$. Let $p_N,p_F$ be acceptance on the maximally mixed
two-qubit input, and $g_N,g_F$ the **unnormalized** Bell overlaps with a
fixed diagonal unitary target $G$, using the normalized four-dimensional
Choi input and tracing $H$. A fine memory Kraus $K_\mu$ contributes
$\operatorname{Tr}K_\mu^\dagger K_\mu/4$ to $p$ and
$|\operatorname{Tr}G^\dagger K_\mu|^2/16$ to $g$. Diagonal/$E$
Hilbert--Schmidt orthogonality therefore gives

$$
p_N=p_F+e,\qquad g_N=g_F=g,\qquad
(p_N-g_N)-(p_F-g_F)=e\ge0.
\tag{IG2}
$$

These are Choi averages: $L_F^\dagger JE$ can change acceptance on a
coherent data input. There is no pointwise acceptance or CP ordering.
If $p_F>0$, the ordinary conditional target fidelity is no lower, and
$p_F\ge g=p_NF_N$. Thus a native diagonal-target fidelity at least
$1-\eta$ has an ordinary flag with at least $(1-\eta)p_N$ acceptance
and no lower conditional fidelity. If $p_F=0$, then $g=0$; native may
still accept pure error. This is not equal yield or an optimized
yield--fidelity frontier.

There is also an all-input selected-map bound. Purify $\tau$ by
$|\chi\rangle$ and stack common filter/environment records. The
Stinespring difference is
$A_N-A_F=\tfrac12\sum_r|r\rangle M_rJ|\chi\rangle\otimes E$,
of operator norm $2\sqrt e$. Both accepted Stinesprings are contractions,
so their two-term channel difference gives

$$
\frac12\|\Gamma_N-\Gamma_F\|_\diamond
 \le\min\{1,2\sqrt e\},\qquad
e\le p_N(1-F_N)\quad\text{for diagonal }G.
\tag{IG3}
$$

This retains the common spectral/filter outputs and all references,
before normalization. It does not equate rejects, normalized rare-event
channels or arbitrary all-launch payoff discrepancies.

For **any** raw unitary target $U$ there is a separate near-unitary
constraint. The accepted Choi support is the four diagonal matrix units
$\mathcal D$ plus $\mathcal J=\operatorname{span}\{|01,10\rangle\}$,
whose population is $e/p_N$. For $|u\rangle=\operatorname{vec}(U)/2$,
put $d_U=\sum_i|U_{ii}|^2/4$, $q_U=|U_{01,10}|^2/4$.
Unitarity equates squared-entry flow across the cut
$\{00,01\}\mid\{10,11\}$ in both directions, so $d_U+2q_U\le1$.
Weighted rank-one Cauchy gives
$P_{\mathcal D+\mathcal J}|u\rangle\langle u|P_{\mathcal D+\mathcal J}
\le P_{\mathcal D}+P_{\mathcal J}/2$. Consequently

$$
F_N(U)\le1-\frac e{2p_N},\qquad
F_N(U)\ge1-\eta\Longrightarrow
p_F\ge(1-2\eta)p_N,\quad
\tfrac12\|\Gamma_N-\Gamma_F\|_\diamond
\le\min\{1,2\sqrt{2p_N\eta}\}.
\tag{IG4}
$$

This does not order conditional fidelities for a nondiagonal $U$.
Known record-dependent output unitaries pull back the target branchwise
and remain paid controls; arbitrary AB--field CP recovery is outside
this support argument. For an **exact** full-input accepted unitary,
rank-one Choi forces every fine memory Kraus to be proportional to $U$.
Its diagonal-plus-one-way support is triangular, and a triangular square
unitary is diagonal. Every filtered $J$ action therefore vanishes on
the actual source, giving full selected-map equality with the ordinary
flag, including retained field output. No lower-dimensional code or
preencoding is implicit.

<a id="nr-r11-inelastic-parity"></a>

**The same selected support limits a raw parity outcome.** This is a
separate endpoint from a full-input unitary gate. Put
$P_e=(I+Z_AZ_B)/2$, $P_o=(I-Z_AZ_B)/2$, and allow any fixed known
unitary output frame $V$. The normalized Choi target for one ideal
parity outcome is
$|\pi_s(V)\rangle=\operatorname{vec}(VP_s)/\sqrt2$, $s=e,o$.
Keep the source, common field filter and selected readout of (IG1)--(IG3).
Let $p_{D,e},p_{D,o}$ be the Choi masses on the even and odd diagonal
matrix-unit subspaces. The same $\Phi_4$ normalization as (IG2) gives
$p_N=p_{D,e}+p_{D,o}+e$ and $p_F=p_{D,e}+p_{D,o}$; $e$ is unchanged.
For $p_N>0$, the selected normalized target overlaps obey

$$
F_N^{(e)}(V)\le\frac{p_{D,e}}{p_N},\qquad
F_N^{(o)}(V)\le\frac{p_{D,o}+e/2}{p_N}.
\tag{IG4p}
$$

For the even target, projection onto the native Choi support lies only
in the even diagonal subspace, with squared norm at most one. For the
odd target, that projection has components
$(a,b,c)/\sqrt2$ on the two odd diagonal units and $E$, where
$a=V_{01,01}$, $b=V_{10,10}$, $c=V_{01,10}$.
The norm of row $01$ and column $10$ gives
$|a|^2+|c|^2\le1$ and $|b|^2+|c|^2\le1$.
Thus $(|a|^2+|b|^2+2|c|^2)/2\le1$, without assuming that $V$
preserves either parity subspace. Weighted rank-one Cauchy consequently
dominates the projected target projector by
$P_{\mathcal D_o}+P_{\mathcal J}/2$.
Tensoring this operator inequality with identity on retained field and
filter outputs and evaluating the positive Choi operator proves (IG4p),
including its possible coherent diagonal/exchange cross terms. The even
bound loses all odd-diagonal and exchange mass; the odd bound loses all
even-diagonal and half the exchange mass.

Set $\kappa_e=1$, $\kappa_o=2$. Combining (IG4p) with (IG3) gives

$$
F_N^{(s)}(V)\ge1-\eta\ \Longrightarrow\quad
e\le\kappa_s p_N\eta,\qquad
p_F\ge(1-\kappa_s\eta)p_N,\qquad
\tfrac12\|\Gamma_N-\Gamma_F\|_\diamond
\le\min\{1,2\sqrt{\kappa_s p_N\eta}\}.
\tag{IG4q}
$$

In particular, an exact raw parity outcome up to $V$ has $e=0$ and the
same full selected map as the ordinary flag, including retained field
output. These are maximally mixed-input Choi weights and unnormalized
map bounds. They do not order the ordinary and native conditional
fidelities for arbitrary $V$, equate yields or rejects, or imply a
worst-input normalized guarantee after rare acceptance. Both parity
records and every failed herald still require their actual instruments.
The statement excludes different source/readout choices, joint AB--field
recovery, preencoding and general logical codes; it does not extend a
full-space recovery obstruction to every encoded parity protocol.

The [same Raman checker](checks/architecture/raman_baselines.py) adds
Gaussian-rational projected-target and retained-dilation guards for this
argument. Its independently chosen support coefficients are not claimed
to be realizable by the complete Raman contacts; the universal weighted
inequality and parity consequences are the analytic proof above.


A real frequency-changing example is
[Inomata et al., PRL 113, 063604 (2014)](https://arxiv.org/abs/1405.5592).
Their driven circuit-QED device has nondegenerate dressed lower states,
two upper states, a waveguide and a separate qubit-loss bath. Its
initialized continuous-probe conversion establishes Raman shifts, not
an unknown joint-memory gate, a two-node router, or the independent
polarization-$S$ tensor offset-frequency interface assumed here.
Lower-state relaxation, off-resonant frequencies and full loss records
require a finite-window model. It motivates weighted translations;
these equations are not a fit to its conversion spectra.

Known photon-only conditional frequency adapters can restore commuting
local blocks in a matched stationary model. For
$R_j=\sum_s|s\rangle\langle s|\otimes T_{\kappa_js}$, the wrapped
contact is $R_j^\dagger T_jR_j$. The ordinary physical sequence is
pre-$R_A$, $T_A$, midpoint $R_BVR_A^\dagger$, $T_B$, post-$R_B^\dagger$.
This is a comparison of wrapped contacts, not the unmodified native
circuit without those frames. Converter work, coherence, loss, helper
ports, failed launches, preparation, reset/reuse and the full clock are
charged; spectroscopy alone does not supply such an adapter.

The [existing exact Raman replay](checks/architecture/raman_baselines.py)
uses an unwrapped frequency line, energy-sector unitary contacts,
all native Bell flags and the ordinary midpoint rejects/late flags.
It checks coherent spectral/reference maps, certified CP/TNI field
filters, added-error ledgers and norm/support ingredients. These are
declared lossless fixtures, not the device's full bath-loss instrument;
the general diamond and unitary-support proofs remain analytic. Known-input
Bell preparation is a different endpoint. The following fixed-contact
comparison closes its yield in this lossless fixture when the stated
passive port processors and time eraser are supplied. A remaining physical
application needs its actual frequency/bath instrument and ordinary ports;
noncommuting elastic diagonal blocks remain outside the support argument.

<a id="nr-r11-passive-inelastic-bell"></a>

**A fixed-order passive-port Bell factory needs no frequency converter.**
Prepare $A=B=0$ and consume the photon to deliver a known Bell pair on
$AB$. This is not an unknown-input gate or a retained-photon service.
Use the declared lossless stationary fixture on an unwrapped integer
frequency line, with memory gaps $\Delta_A=1,\Delta_B=2$, zero $C/S$
port splittings, and fixed active responses

$$
t_j(E)=\frac{E-j/2}{E-j/2+i},\qquad
r_j(E)=\frac{-i}{E-j/2+i},\qquad j=0,1
\tag{IG5}
$$

for $A,B$ respectively. Equal $S$/memory values are dark identity; an
exchange $|s,a,\omega\rangle\mapsto
|a,s,\omega+\Delta_j(a-s)\rangle$ has coefficient
$r_j(\omega+\Delta_ja)$, and its unchanged path has coefficient $t_j$
at the same energy. All intermediate frequencies are retained.

Supply the four coherent photon $C/S$ ports, a normalized
$\Phi^+_{CS}$ source at $\omega=0$, one constant frequency-preserving
$U(4)$ between contacts, a constant terminal $C/S$ analyzer,
port-resolved broadband time detection, and local spin phase/Pauli
feedback. The route must preserve all four ports into the required
contacts. These are paid ports, not implied by a native order router or
spectrometer. Neither static retuning, active frequency translation,
spectral source replacement nor an abstract field-only projection is used.

The first contact is always $A$. Since $t_A(0)=0,r_A(0)=-1$, it gives
$[|A0,C0,S0,\omega0\rangle-
|A1,C1,S0,\omega{-1}\rangle]/\sqrt2$. Put
$a=\sqrt{7/20}$, $b=\sqrt{13/20}$. The midpoint unitary has columns

$$
\begin{array}{ll}
|00\rangle\mapsto|11\rangle,&
|01\rangle\mapsto b|10\rangle-a|01\rangle,\\
|10\rangle\mapsto-a|10\rangle-b|01\rangle,&
|11\rangle\mapsto|00\rangle .
\end{array}
\tag{IG6}
$$

They are orthonormal. The minus sign in column $10$ compensates the
physical first reflection phase; the unitary does not change frequency.
Contact $B$ second, with its center still $+1/2$. Define
$t_0=(1+2i)/5$, $r_0=(-4+2i)/5$ at $E=0$, and
$t_1=(9+6i)/13$, $r_1=(-4+6i)/13$ at $E=-1$.
Suppressing frequency labels temporarily, the exact joint output is

$$
\frac1{\sqrt2}\bigl[
 |00\rangle_{AB}t_0|11\rangle_{CS}
+|01\rangle_{AB}r_0|10\rangle_{CS}
+|10\rangle_{AB}(a|10\rangle+b t_1|01\rangle)_{CS}
+|11\rangle_{AB}b r_1|00\rangle_{CS}\bigr].
\tag{IG7}
$$

Each $AB$ label $|x,y\rangle$ in (IG7) has its own frequency
$\omega=-x-2y$, by conservation of $\Omega+n_A+2n_B$. No frequency record
has been discarded by writing (IG7).

Here is a complete, constant projective analyzer. Put

$$
\begin{aligned}
h_\pm&=t_0|11\rangle\pm b r_1|00\rangle,&
\|h_\pm\|^2&=2/5,\\
u&=r_0|10\rangle,\quad v=a|10\rangle+b t_1|01\rangle,&
\zeta&=r_0/|r_0|=(-2+i)/\sqrt5,\\
k_\pm&=u\pm\zeta v,&
\|k_\pm\|^2&=2(4\pm\sqrt7)/5 .
\end{aligned}
\tag{IG8}
$$

The four normalized vectors are an orthonormal $C/S$ basis:
$|t_0|^2=|br_1|^2=1/5$,
$\|u\|^2=\|v\|^2=4/5$, and
$\langle u|\zeta v\rangle=\sqrt7/5$ is real. The $h$ and $k$ sectors
have disjoint helper support. Thus (IG8) specifies a physical four-port
projective basis under the supplied coherent $U(4)$ interface, rather
than only invoking an HJW existence claim. Its real insertion loss and
phase/path requirements remain costs.

At time phase zero, the $h_\pm$ flags give $\Phi^\pm$ with probability
$1/10$ each. The $k_\pm$ flags give
$(|01\rangle\pm\zeta^*|10\rangle)/\sqrt2$, with probabilities
$(4\pm\sqrt7)/10$. Apply $Z_A$ for $h_-$; for a $k$ flag apply
$\operatorname{diag}(1,\zeta)_A$, $Z_A$ for the minus sign, and $X_B$.
The four corrected flags are

$$
\rho_\ell=p_\ell|\Phi^+\rangle\langle\Phi^+|,\qquad
(p_\ell)_\ell=
\left(\frac1{10},\frac1{10},
      \frac{4+\sqrt7}{10},\frac{4-\sqrt7}{10}\right).
\tag{IG9}
$$

They sum to one. The passive-reference extension is
$p_\ell|\Phi^+\rangle\langle\Phi^+|\otimes\rho_R$ for an arbitrary
independent $\rho_R$, not a statement about unknown $ABR$ inputs.

On the integer line use the ideal time/angle instrument
$\langle\theta|\omega\rangle=e^{-i\omega\theta}/\sqrt{2\pi}$,
$0\le\theta<2\pi$. Frequency $-x-2y$ gives only the local spin byproduct

$$
D_A(\theta)D_B(2\theta),\qquad
D(\phi)=\operatorname{diag}(1,e^{i\phi}).
\tag{IG10}
$$

Apply its inverse **before** the fixed corrections containing $X_B$
in (IG9), or conjugate the phase frame through that Pauli. The analyzer
is constant in time; port and time detection can therefore be combined.
Each true flag/time outcome delivers the known Bell state with measure
$p_\ell\,d\theta/(2\pi)$. A detector that merely leaves an unread
which-frequency record does not implement this instrument. In this
energy-eigenstate fixture, tracing frequency before detection pinches
$AB$ in its computational basis; even conditioned on a $C/S$ analyzer
outcome it is separable, with corrected Bell overlap at most half its
trace. This guard does not apply to arbitrary coherent spin preparations,
overlapping packets or an actual coherent time click.

The construction also has a finite-packet **approximate** guarantee.
Use a normalized common continuum packet $\phi(\epsilon)$ with
$\sigma^2=\int\epsilon^2|\phi(\epsilon)|^2d\epsilon$ and the same constant
midpoint/analyzer. Frequencies are angular and dimensionless in the
linewidth units of (IG5). On each conserved total-energy-$\epsilon$
fiber, freeze only the contact coefficients at $\epsilon=0$, retaining
every output label $\epsilon-x-2y$. This is a mathematical comparison
isometry, not an extra physical controller. Since $t=1+r$ and
$|r(E+\epsilon)-r(E)|\le|\epsilon|$, each active contact changes by at
most $2|\epsilon|$ in operator norm; dark sectors are unchanged. A
two-contact telescope and orthogonal energy fibers give

$$
\|\Psi_{\rm actual}-\Psi_{\rm frozen}\|\le4\sigma,\qquad
1-F_{\rm Bell}({\rm actual})\le\min\{1,16\sigma^2\}.
\tag{IG11}
$$

For the second inequality apply the **same** full-time
detector/feedforward isometry to both states. The frozen coefficients
make a common Fourier envelope factor out after (IG10), so the frozen
$AB$ output is exactly pure Bell. Its Bell-orthogonal projection
vanishes; the actual bad weight is bounded by the squared norm
difference. This requires the same packet, phase, complete frequency
space and processing dilation. It is a full-window, ideal-lossless
Bell-good-weight bound with unit click yield, not an exact finite-pulse
Bell theorem. A dimensionful linewidth rescales $\sigma$ and the derivative.
For a common window/efficiency and any $0\ldots1$ all-attempt payoff, the
separate absolute discrepancy from the frozen comparison is at most
$4\sigma$; no yield-free normalized postselection bound follows.

For frozen ideal dynamics, additive independent timestamp error $\xi$,
all times accepted, and the displayed phase correction, let
$\chi(q)=\mathbb E e^{iq\xi}$. The $h$ flags have total weight $1/5$
and residual gap $3$; the $k$ flags have total weight $4/5$ and gap $1$.
Thus the aggregate Bell fidelity is

$$
F_{\rm time}=\frac12+\frac1{10}\operatorname{Re}\chi(3)
                      +\frac25\operatorname{Re}\chi(1).
\tag{IG12}
$$

For zero-mean Gaussian jitter of standard deviation $s_t$, replace the
two real parts by $e^{-9s_t^2/2}$ and $e^{-s_t^2/2}$. These are derived
response formulas, not measured jitter or feedback performance.
Finite windows, pulse-dependent errors, frequency drift or correlated
timestamp noise need their conditional distributions instead.
If the common processing already has imperfect timing, the separate
complete-instrument payoff bound gives a discrepancy at most
$\min\{1,4\sigma\}$; the $16\sigma^2$ ideal-Bell infidelity bound cannot
simply be added to an imperfect frozen fidelity without cross terms.

A different **ordinary word and source weights** also remove any proposed
gap-$3$ timing limitation of this benchmark. Keep the contacts and carrier
$\omega=0$ fixed, but use $B$ first, $A$ second, and source
$\sqrt{3/8}|00\rangle_{CS}+\sqrt{5/8}|11\rangle_{CS}$.
At $B$, $t_B=(1+2i)/5$, $r_B=(-4+2i)/5$.
The $B=0$ and $B=1$ photon vectors after that contact are orthogonal,
both of squared norm $1/2$. Their normalized versions are
$\bar u=\alpha|00\rangle+\beta|11\rangle$ and
$\bar v=\rho|10\rangle$, where
$\alpha=\sqrt3/2$, $\beta=t_B\sqrt5/2$, $\rho=r_B\sqrt5/2$.
With $\bar u_\perp=-\beta^*|00\rangle+\alpha|11\rangle$, use the
constant midpoint

$$
U_*=|01\rangle\langle\bar u|
    +|10\rangle\langle\bar v|
    +|00\rangle\langle\bar u_\perp|
    +|11\rangle\langle01|.
\tag{IG13}
$$

The four input vectors are orthonormal. The $B=0$ branch now reaches
$A$ with $S=1,\omega=0$, exactly its unchanged resonance, while the
$B=1$ branch has $S=0,\omega=-2$ and is dark. The full final state is

$$
\frac{-|10\rangle_{AB}|00,\omega=-1\rangle_{CS,H}
      +|01\rangle_{AB}|10,\omega=-2\rangle_{CS,H}}{\sqrt2}.
\tag{IG14}
$$

A $C$-basis $\pm$ measurement and $S=0$ time click therefore give an
odd Bell pair with probability $1/2$ per $C$ flag. Remove the same local
energy phases (IG10); apply $X_B$ and $Z_A$ for the $C=+$ flag, or
$X_B$ alone for $C=-$. This gives unit Bell yield with no terminal
general $U(4)$ analyzer. Its independent-jitter fidelity is
$(1+\operatorname{Re}\chi(1))/2$, the gap-$1$ expression also available
to an ideal native odd-Bell output. No pairwise timing advantage is
asserted. This variant prices coherent unequal source weights and the
ordinary reverse-order route/clock; it changes neither carrier nor contact
detuning. More generally the balancing step works when the first
partial-exchange probability is $R\ge1/2$ and the second contact is
resonant at the original carrier: source weights
$1-1/(2R)$ and $1/(2R)$ make both first-contact branches have norm
squared $1/2$. This is a conditional lossless-port argument, not a
two-upper-level or lossy-device theorem. The original $A$-then-$B$,
$\Phi^+_{CS}$-source construction remains the separately proved
fixed-word/source comparison.

Flat true-photon efficiency $\eta$ and a common accepted window $W$
give frozen true-click yield $\eta\int_W|\phi_t(t)|^2dt$.
The photon is consumed; no-click can damage the spins and is not an
identity retry. Collection, analyzer loss, port-dependent efficiency,
dead time, multi-click veto, reset, spin storage, delay, phase calibration
and feedback latency enter the complete attempt ledger. A false click
after photon loss contributes its actual accepted CP map. For mutually
exclusive true and false masses $s,d$, fidelity is
$(sF_{\rm true}+dF_{\rm false})/(s+d)$; the false state requires the
loss/detection dilation. No free path control survives photon loss.

[Hermans et al., arXiv:2208.07449v1, Secs. II, IV, VI–VII](https://arxiv.org/html/2208.07449v1)
model time-labelled annihilation and frequency-dependent herald phase,
and distinguish temporal-envelope mismatch and fluctuating detuning.
They motivate this conditional time instrument, not these Raman
contacts, retuning, four-port optics, or jitter/feedback guarantees.
The POVM, packet bound and cost analysis here are independent derivations.

Ordinary yield one closes a Bell-yield advantage for **this** lossless
fixture under the supplied passive processors and coherent time eraser.
It improves on a single diagonal-$L_F$ comparison or a selected
$8/17$ ordinary branch, without asserting that an actual optical graph
supplies the two $U(4)$ processors. The independent $C/S$ ports, matched
delays and complete traveling-mode interface remain necessary. This is
not a two-node device fit or a microscopic loss certificate. Native
frequency erasure must be charged on the same terms as ordinary erasure.
The [same Raman replay](checks/architecture/raman_baselines.py) uses exact
$\mathbb Q(i,\sqrt3,\sqrt5,\sqrt7,\sqrt{13})$ arithmetic for literal unwrapped
paths, all normalized analyzer/time flags, passive-reference coefficients,
the no-eraser guard, reverse-word odd-Bell variant and bad-control mutants.
Four Fourier angles on
the four populated frequency labels check finite normalization; the
two distinct feedback circuits also have independent off-grid rational
unit-phase checks and wrong-frame mutants. The
continuous-time and packet bounds remain the analytic arguments above.

<a id="nr-r11-raman-route"></a>

### Native Raman ports need a routed temporal helper

Use one complete bidirectional SPRINT station per node. The physical
photon qubit $P$ is the pair of counterpropagating modes, not an extra
polarization qubit. A Raman flip reverses propagation and changes the
resident ground state. At each physical fibre end an actual three-port
circulator can present a separate incoming and outgoing travelling mode.
Label the left-end input/right-end output $P=0$ and the right-end
input/left-end output $P=1$. Connecting the corresponding outgoing rails
to the next station's incoming rails then preserves the complete
logical $P$ channel, including a Raman reversal; sending only a forward
rail would not do this. There are two such circulators per station,
with their insertion loss, nonreciprocal bias, vacuum/loss ports and
mode-dependent phases included. This is a proposed adapter, not a
claim that the [Rb experiment](https://arxiv.org/pdf/1711.10974),
Methods pp.8--10, used lossless circulators: its Methods use
97:3 beam splitters as functional circulators, attenuating the input
and transmitting most of the output.

There is a sharp dimension obstruction to a simultaneous spatial
helper extension. Four orthogonal $Q\otimes P$ input modes cannot all
enter two physical station input modes by a lossless isometry while
the environment and unused ports carry no $Q$ information. A $2\times4$
single-particle matrix has rank at most two, whereas an isometry would
require its Gram matrix to be $I_4$. Additional temporal, frequency or
polarization modes, a retained memory, or active routing into retained
orthogonal slots is therefore required for an independent helper.
Heralded rejection alone cannot make a uniform four-dimensional
embedding: $J^\dagger J=cI_4$ is impossible for any $2\times4$ matrix
and $c>0$. A restricted heralded processor is a different code.
Circulators separate directions;
they do not remove this dimension count.

Here is a concrete passive, heralded construction with additional time
modes. Put A and B in a directed external ring. At each station and
for each $P$ rail, a two-input/two-output lossless coupler has

$$
\begin{pmatrix}N_j\\D_j\end{pmatrix}
=\begin{pmatrix}\sqrt k&\sqrt{1-k}\\
\sqrt{1-k}&-\sqrt k\end{pmatrix}
\begin{pmatrix}S_j\\C_j\end{pmatrix}.
\tag{RT1}
$$

$N_j$ feeds the circulator adapter and station $j$; both station output
$P$ rails feed the corresponding circulating rails $C_{\bar j}$ at
the other station. $S_j$ is the initial injection rail and is vacuum
thereafter. $D_j$ is an extraction/readout rail. Prepare the independent
order helper by injecting $Q=0$ through $S_A$ or $Q=1$ through $S_B$,
with the same photon $P$ state. The initial injections occur at the same
clock, in different stations. At A, the two helper components encounter
the station in slots $0$ and $L$; B has the opposite assignment.
Each station thus has two $P$ modes in each of two distinct time slots,
rather than four simultaneous modes.

Reject extraction before the two-query window. Accept only the first
round-trip extraction: an A-injected photon visits A then B and exits
through $D_A$ before a third visit; a B-injected photon visits B then A
and exits through $D_B$. Equal link delays and a common final extraction
clock make the two retained routes interfere. Their accepted amplitude
is $-k\sqrt{1-k}$, giving the complete selected map

$$
K_2=-k\sqrt{1-k}\left(
 |0\rangle_{Q'}\langle0|_Q\otimes T_BT_A
+|1\rangle_{Q'}\langle1|_Q\otimes T_AT_B\right).
\tag{RT2}
$$

Here $Q'$ is the extraction-station label, and the two $P$ rails are
both retained. The routing factor is $k^2(1-k)\le4/27$, maximized at
$k=2/3$. Initial reflection, one-query extraction, later round trips,
unused source inputs and loss outputs are actual rejected records.
If one waits for passive loop extinction, the tail must be bounded
before reset or the next launch. A detector gate alone does not remove
the circulating amplitude. Circulator/propagation/detection loss further
multiplies this factor. For contraction-valued nodes, after $N$
completed post-visit coupler decisions the remaining circulating
one-photon weight is at most
$k(1-k)^N$. A finite failure-cycle guard therefore needs a declared
tail error or an actual dump operation. The $4/27$ number is the
optimum of this symmetric coupler construction, not a universal
passive-routing bound.

RT2 requires equality of the actual slot-conditioned accepted
instruments, not just equal marginal CPTP maps. In general it is
$T_B^{L}T_A^{0}$ versus $T_A^{L}T_B^{0}$. Classical drift, free spin
precession and photon-preserving bath records must be retained. In an
ideal one-photon radiative model, any unguided emission loses the sole
photon and cannot enter the final click; the accepted bath is vacuum.
Pure dephasing or an unobserved frequency/time record can instead label
the occupied slot and reduce route coherence. No guard proves those
records absent. Finite pulses need disjoint slots with separately
certified node/route tails and coherent retained spins through the
whole attempt. Matching marginal station transfer functions is not
sufficient.

Each successful history goes once around the complete external ring.
Consequently scalar link phases enter both as $e^{i(\chi_{AB}+\chi_{BA})}$,
and static whole-node factors enter both as $e^{i(\theta_A+\theta_B)}$.
They are common global factors. Source-to-injection and extraction-to-
readout differential phases still need reciprocal matching or a phase
reference. Mode-dependent link matrices do not commute through a Raman
station; they must be retained or calibrated as real port-frame
corrections. A global counterpropagating Sagnac input that swaps the
station's $P$ labels instead of using these complete adapters generally
queries different local operations and is not RT2.

**An achievable ordinary processor on the same two-port station access.**
For definite A-then-B order, encode $Q$ in two input time bins at A and
send both physical $P$ outputs toward B through the same adapter access.
The passive RP1 contraction needs four optical modes between the nodes.
It can be supplied conservatively by a passive temporal decoder,
an ordinary four-rail unitary dilation of $V$, and a passive temporal
encoder before B. After B use another decoder for the complete four-
mode photon readout. Each decoder's central accepted clock maps the two
time bins into two spatial helper rails with amplitude $1/\sqrt2$;
the encoder merges two delayed helper rails into the two physical
$P$ inputs with amplitude $1/\sqrt2$ in its selected port. This gives
an extra adapter factor $1/8$ in probability, besides the intrinsic RP1
filter success and all path loss. If the ring coupler ratios are locked
to the switch setting, its actual injection/extraction factor also
applies. If the same static couplers can be reconfigured, the stronger
ordinary choice is $k_A=1,k_B=0$ with all source bins injected at A:
injection into A, continuation through B, and extraction before a third
A visit then each have amplitude one. This gives deterministic ordinary
A-then-B routing on the same complete physical $P$ ports, before the
helper-codec, node and component losses. Such static configuration is
not photon-controlled routing. A
prepared two-time-bin source can avoid an additional initial encoder.
An active temporal mode converter can improve this factor, but its
controls, losses and timing are additional resources.

Leakage timing must be designed, not silently discarded inside the
processor. For example, let the input bins be separated by $\Delta$.
The first decoder leaves unwanted components shifted by $\pm\Delta$
around its central clock in the same processor rails. Choose the
output-bin separation $4\Delta$, and the final decoder delay $4\Delta$.
Those unwanted components cannot then coincide with the final central
accepted clock. All window separations require the pulse/tail guards.
Choose the ring flight slots longer than the complete processor window
and guard; match the central link delays in the two configurations.
Later round trips must not overlap an accepted codec window.
This constructs an ordinary comparator, not an optimum over passive
temporal networks. The extra processor paths can be placed in a known
configurable link branch, with its direct bypass available to either
protocol; switching that configuration is not controlled by an unknown
photon state. The node adapters, available path graph, complete
readout, memory and rejected ports are shared and charged explicitly.

Neither construction supplies a free $\mathrm{id}_Q$ at the native
station. Both must demonstrate coherent slot access, the relevant
stationarity interval, the full physical phase frame, source/reset
cost and complete output instrument before a finite-rate comparison.

<a id="nr-r11-raman-direct-temporal"></a>

**A direct passive temporal filter includes its source rejection and
exceeds the symmetric-ring minus coefficient.** Work in the same
complete two-rail Raman port frame, with $AB=00$ and static accepted
operators $T_j=a_jI+b_jF_{Pj}$. Both physical counterpropagating outputs
are collected. The ordinary static ring setting $k_A=1,k_B=0$ supplies
deterministic A-then-B routing. The construction below uses one input
photon, vacuum in all other optical inputs, fixed beam splitters and
delays, no additional stationary memories, and a recorded photon
port/time herald. It does not assume a free arbitrary four-mode
processor or a lossless prepared temporal state.

Let $z$ denote one delay $\Delta$ and define
$x=1-z-z^2$, $y=1+z-z^2$. A fully passive source preparer gives the two
kept station-input rails the unnormalized waveforms

$$
x'(z)=\frac{x(z)}{\sqrt{10}},\qquad
y'(z)=\frac{y(z)}{\sqrt{10}},
\qquad w(z)=\frac{1+z^2}{\sqrt5}
\tag{PT1}
$$

in a third, rejected output rail. To realize it, split a single-bin
input into three rails with amplitudes
$(\sqrt{2/5},1/\sqrt5,\sqrt{2/5})$, give them delays $0,\Delta,2\Delta$,
and mix the outer rails into their difference and sum. Send the sum to
the rejected port. Mix the difference and middle rail on another
balanced beam splitter with kept outputs
$P0=(r_0-r_2)/2-r_1/\sqrt2$ and
$P1=(r_0-r_2)/2+r_1/\sqrt2$. The fixed output matrix is

$$
U=\begin{pmatrix}
1/2&-1/\sqrt2&-1/2\\
1/2&1/\sqrt2&-1/2\\
1/\sqrt2&0&1/\sqrt2
\end{pmatrix},\qquad U^\dagger U=I_3.
$$

The two kept rails have total weight $3/5$ and the rejected rail $2/5$.
All of this source rejection is counted. The normalized kept waveform
occupies three bins, but its temporal Schmidt support against $P$ is
two dimensional: the outer antisymmetric pair and the middle bin.
This is an actual temporal code, with its extra duration charged.

Between A and B apply the lossless two-rail interferometer

$$
H(z)=\frac12\begin{pmatrix}1+z&1-z\\1-z&1+z\end{pmatrix}
=H_2\operatorname{diag}(1,z)H_2.
\tag{PT2}
$$

After B, delay $P0$ by $\Delta$ and mix the two rails on $H_2$.
Accept only its plus output in clock bin $2\Delta$, relative to the
common propagation delay. Every other port/clock and the no-click
outcome is a failure record. There is no intermediate temporal gate.

Here is the complete polynomial cancellation. Set
$h_+=(1+z)/2$, $h_-=(1-z)/2$, $c_j=a_j+b_j$. Before the common source
and readout normalization $1/\sqrt{20}$, the plus-port state is

$$
\begin{aligned}
\Phi_+(z)={}&|00\rangle\{c_B[c_Azh_+x+a_Azh_-y]
                  +a_B[c_Ah_-x+a_Ah_+y]\}\\
&+|10\rangle b_A[c_Bzh_+y+a_Bh_-y]\\
&+|01\rangle b_B[c_Azh_-x+a_Azh_+y]
 +|11\rangle b_Ab_Bzh_-y.
\end{aligned}
\tag{PT3}
$$

Use $h_+x=(1-2z^2-z^3)/2$,
$h_-y=(1-2z^2+z^3)/2$,
$h_-x=(1-2z+z^3)/2$ and
$h_+y=(1+2z-z^3)/2$. Extracting $z^2$, the identity, single-A and
single-B monomials $a_Aa_B,b_Aa_B,a_Ab_B$ each have zero coefficient
in every memory basis state. The double term is exactly

$$
[z^2]\frac{\Phi_+(z)}{\sqrt{20}}
=\frac{b_Ab_B}{\sqrt{20}}(|10\rangle-|01\rangle),\qquad
p_{\rm direct}=\frac1{10}|b_Ab_B|^2.
\tag{PT4}
$$

Thus the coefficient $1/10$ includes the $3/5$ passive source success,
all physical beam-splitter amplitudes and the single selected readout
flag. The normalized-kept-source coefficient is $1/6$. The exact
enumeration retains both detector ports in clocks $0,\ldots,4$;
among these ten flags only $(+,2)$ is a coefficient-independent Bell
flag for this fixed circuit. Endpoint I/SWAP and lossless partial-SWAP
checks preserve the complete $3/5$ kept-photon weight across all flags;
the rejected source port completes it to one. For lossy nodes, their
full loss and no-click outputs must also be retained.

There is a limited optimality observation only for this fixed source
shape. On $|z|=1$, the normalized target pair $x/\sqrt6,y/\sqrt6$ has
spectral norm $1-(2/3)\cos2\omega\le5/3$. A time-invariant passive
preparer multiplying this exact shape by a common kept amplitude
$\sqrt\eta$ must have $\eta\le3/5$. PT1 attains it, because the rejected
$w$ completes the column pointwise to norm one. This is not an optimum
over source shapes, interferometers, flags or general ordinary protocols.

The symmetric passive ring's switch-minus coefficient is
$(4/27)(1/2)=2/27$. Consequently

$$
\frac{p_{\rm direct}}{p_{S,-}^{\rm ring}}=\frac{27}{20}>1
\tag{PT5}
$$

under the common static-frame/code/node hypotheses, before differing
component losses and cycle times. This removes that particular bare
minus-flag routing margin even after passive source preparation is
charged. It does not compare all useful plus outputs of calibrated
identical nodes, a different switch router, or arbitrary ordinary
optima. If $\eta_D,\eta_S$ are the additional complete-path detection
throughputs, the ordinary raw-yield comparison requires
$\eta_D/\eta_S\ge20/27$. For average rate the additional condition is
$d_D/d_S\le(27/20)(\eta_D/\eta_S)$, with full generated-photon,
preparation, failed-clock, node-loss, reset and readout durations.

Physical qualifications matter. Passive mixing of $P$ requires matched
optical carriers; the Rb SPRINT experiment already mixes its two
direction modes on beam splitters for equatorial qubits, whereas a
nondegenerate Raman-frequency encoding may require a frequency converter.
The source spans three bins, B receives four, and final detection spans
five. Slot separation needs the actual pulse and node tails, and the
node/bath operation must remain the same throughout those slots. A
finite-bandwidth cavity produces additional temporal tails; accepting a
central clock does not erase their leakage. The polynomial identities
apply exactly in the ideal disjoint-slot model; an actual source needs
a complete-instrument leakage bound and measured clock.
For an explicit obstruction to an unrestricted frequency-dependent
extension, the identity-only polynomial in PT3 is
$a_Aa_B(1+z-2z^3)|00\rangle$. Choose the valid passive scalar kernel
$a_A(z)=(1+z)/2$, $a_B=1$ and $b_A=b_B=0$. Its central $z^2$
coefficient is $1/2$, producing a false product-state click with
probability $1/80$. The kernel's other output completes its passive
instrument. Thus arbitrary stationary LTI kernels do not suffice;
the response/window bound is part of the theorem's access model.
Static whole-
node phases multiply PT4 only globally, and static Raman-leg phases
dress its odd Bell state by exactly the same local gauge as switch
minus. Route-dependent, time-dependent or unobserved bath records are
not covered by that statement. True circulator/adaptor loss, extra
source/interferometer components, stable rail phases and the available
stationarity/coherence interval remain measured costs, not consequences
of the finite replay.

<a id="nr-r11-raman-temporal-tail"></a>

### Finite response tails, accepted Bell quality and the clock budget

The direct filter has a finite-response extension under an explicit
stationary kernel premise. Suppose that, in the same complete two-rail
carrier/spin frame, the accepted one-photon scattering multiplier is
$T_j(\omega)=a_j(\omega)I+b_j(\omega)F_{Pj}$. Its accepted unobserved
environment must be the common vacuum. Every other radiative channel
loses the sole photon and cannot produce the final selected click.
This premise excludes an unaccounted photon-preserving bath record;
it is stronger than stationarity of a marginal transfer function.
Ground-spin dynamics, frequency conversion and temporal/spatial mode
matching must be included in the actual kernel or separately bounded.
No assumption about Gaussian classical noise is made.

**Frequency dependence and a physical clock window.** The scalar
multipliers commute with $z=e^{-i\omega\Delta}$, so (PT3) remains a
pointwise polynomial identity with frequency-dependent $a_j,b_j$. For
a normalized source mode $f$, define the four actual wavepackets
$\psi_{aa}=a_Aa_Bf$, $\psi_{ba}=b_Aa_Bf$,
$\psi_{ab}=a_Ab_Bf$, and $\psi_{bb}=b_Ab_Bf$.
Multiplication here means composition of stationary scalar filters.
Each $z^k$ translates its entire wavepacket by $k\Delta$; detecting
clock 2 does not automatically extract a polynomial coefficient.

Choose a common base interval $I$ of width $w<\Delta$, its time
projector $P_I$, and the accepted translated window $I+2\Delta$.
Put $\tau_v=\|(I-P_I)\psi_v\|$ and
$B_I=\|P_I\psi_{bb}\|^2$. For $k\ne2$, disjointness gives
$P_{I+2\Delta}D^kP_I=0$ and hence
$\|P_{I+2\Delta}D^k\psi_v\|\le\tau_v$, where $D$ is the delay.
After undoing the common $2\Delta$ translation, the accepted vector
therefore differs from
$(|10\rangle-|01\rangle)\otimes P_I\psi_{bb}/\sqrt{20}$ by at most

$$
\epsilon_D\le
\frac{4\tau_{aa}+2\sqrt2\,\tau_{ba}
 +(2+\sqrt2)\tau_{ab}+(2+\sqrt2)\tau_{bb}}{\sqrt{20}}.
\tag{TG1}
$$

To verify the constant, the squared norms of the spin-vector
coefficients of each side clock in (PT3), before $1/\sqrt{20}$, are
$aa:(1,1,4)$ at clocks $(0,1,3)$;
$ba:(1/2,1/2,1/2,1/2)$ at $(0,1,3,4)$;
$ab:(2,4)$ at $(1,3)$; and $bb:(1,2,1)$ at $(1,3,4)$.
Their norm sums are respectively $4,2\sqrt2,2+\sqrt2,2+\sqrt2$.
The only central term is the double-Raman Bell vector. Thus if every
$\tau_v\le\tau$,

$$
\epsilon_D\le C_D\tau,\qquad
C_D=\frac{4+2\sqrt2}{\sqrt5}\simeq3.053765446.
\tag{TG2}
$$

The ideal compact accepted yield is $B_I/10$, including passive source
rejection. It factors as the Bell spin state times its actual common
wavepacket, so discarding that wavepacket does not damage the Bell
factor. The useful strength is **$B_I$**, rather than automatically
$|b_A(0)b_B(0)|^2$. In particular,

$$
B_I\ge B_{\rm band}-\tau_{bb}^2,\qquad
B_{\rm band}=\int |b_A(\omega)b_B(\omega)f(\omega)|^2\,d\omega.
\tag{TG3}
$$

If the two ring routes have the same complete accepted scalar kernels,
their $b_A,b_B$ commute and give the same untruncated $\psi_{bb}$.
The matched compact ring-minus ideal then has yield $2B_I/27$.
Its actual router still needs its own accepted error certificate
$\epsilon_S$, including circulating, extraction and rejected paths;
(TG1) does not supply that certificate.

**A sufficient node-tail certificate.** For a compact photon input in
an interval $J$, require uniformly on the declared rail/spin input
space, with passive references allowed,

$$
\|P_{\text{nonvacuum radiative output after }\sup J+g_j}
 V_j\|^2\le\delta_j(g_j).
\tag{TG4}
$$

This refers to the complete node dilation. Residual module excitation
at the cutoff can be bounded separately by the same decay estimate;
it is not added again as an independent late-photon event. A fitted
probe's mean output intensity does not establish (TG4).

In the stationary kernel model, the accepted eigenkernels $a_j+b_j$
and $a_j-b_j$ are contractions and obey the same tail bound.
Their half sum and difference show that $a_j,b_j$ individually are
contractions with tail norm at most $\sqrt{\delta_j}$. For a compact
source duration $t_p$, truncate A's output after $t_p+g_A$ only for
the estimate. The omitted vector has norm at most
$\sqrt{\delta_A}$. The retained pulse may be distorted and entangled
with retained spins; (TG4) at B applies uniformly to this whole compact
input space. Contractivity on the omitted vector and B's uniform bound
on the retained vector give

$$
\tau_v\le\sqrt{\delta_A(g_A)}+\sqrt{\delta_B(g_B)},\qquad
w=t_p+g_A+g_B.
\tag{TG5}
$$

This is a stage-by-stage norm argument, not an assumption that B sees
the original Gaussian pulse. One sufficient clock condition is
$\Delta>w$. If accepted node-kernel errors on the complete reachable
input code are $\xi_A,\xi_B$, telescoping through the other
contractions adds at most their sum. Source, passive-component,
mode-mismatch and detector errors need their own certified norms, so

$$
\epsilon_D\le C_D(\sqrt{\delta_A}+\sqrt{\delta_B})
 +\xi_A+\xi_B+\epsilon_{\rm source}+\epsilon_{\rm components}.
\tag{TG6}
$$

The constant $C_D$ concerns the prepared $AB=00$ and (PT1) temporal/rail
code. It includes a passive reference entangled with the declared
source-mode input when the hypotheses are uniform on that code.
Extending to arbitrary spin inputs requires recomputing coefficient
**operator** norms; uniform (TG4) alone does not extend the same $C_D$.
Likewise, a per-bin state estimate is not automatically a uniform
temporal-code bound. For $n$ orthogonal input bins with per-bin operator
errors $e$, Cauchy--Schwarz only guarantees $\sqrt n\,e$ on the whole
code unless a stronger orthogonality estimate is proved. The coherent
source and processor coefficients have already been charged in (TG1).

**Including a cavity in the radiative guard.** The
[uniform record guard](#nr-r11-uniform-record-guard) has the following
sufficient extension. After the last compact input, let $Q$ be the
integer total stored optical excitation, including cavities, trions
and any other retained optical storage. Assume no later input or
drive, $[H,Q]=0$, radiative jumps lowering $Q$ by one, and
$\sum_a L_a^\dagger L_a\succeq\kappa_* Q$ with a certified
$\kappa_*>0$. Excitation-preserving jumps commute with $Q$ and must
annihilate the entire optical ground-spin manifold in the actual
vacuum dilation. Then $\mathcal L^*(Q)\preceq-\kappa_*Q$.
If $Q\le n_{\max}$ on the reachable code, Gronwall gives

$$
\delta_j(g)\le\min\{1,n_{\max}e^{-\kappa_*g}\}.
\tag{TG7}
$$

For the record statement, its positive future-record effect is at
most identity and vanishes on the vacuum-preserving ground manifold.
Positivity kills its off-diagonal blocks with that manifold, so the
effect is at most $P_{\rm exc}\preceq Q$. This proves (TG7) uniformly
for reference-entangled inputs; the residual excitation probability
obeys the same bound. Only after this uniform effect bound may its
square root be used as a tail amplitude.

For independent cavity and emitter decays
$L_c=\sqrt{k_c}\,c$ and $L_e=\sqrt{k_e}\,\sigma^-$,
$\kappa_*=\min(k_c,k_e)$ is sufficient in the one-excitation sector.
These are **population** rates: an amplitude-decay convention requires
the corresponding factor of two. Shared channels can introduce cross
terms, so their complete radiative Gram floor must replace the bare
linewidth minimum. Nearly dark modes can make the floor arbitrarily
small. A weighted Lyapunov inequality for the full generator is another
possible certificate, with its operator inequalities and norm constants
checked separately. No nominal cavity linewidth is turned into a
measured bound here. Ground-spin dephasing or spin--phonon records are
not bounded by trion excitation. Drives, feedback delays and unmodeled
storage also require an enlarged certificate. Even (TG7) does not
prove the common-vacuum stationary kernel premise.

For an arbitrary source mode with tail mass $\zeta$ outside a declared
compact interval, its normalized truncation differs in vector norm by
$\sqrt{2-2\sqrt{1-\zeta}}\le\sqrt{2\zeta}$ and in half trace
distance by $\sqrt\zeta$. Subsequent complete instruments are
contractive. Gaussian **intensity** is only an optional source model:
$\zeta=\operatorname{erfc}(L/\sqrt2)$ for a window
$\pm L\sigma_I$. It imposes no Gaussian law on classical phase noise.

**Accepted states and complete failure outputs are distinct norms.**
Let $K,K_0$ be accepted Stinespring contractions in one common record
space with $\|K-K_0\|\le e$. Their accepted CP maps differ in diamond
norm by at most $e(\|K\|+\|K_0\|)\le2e$, including references and
all retained spins. For the Bell-preparation input let $a=\sqrt{p_0}>0$
and suppose the ideal accepted vector is Bell tensor its actual
retained records. Triangle and projection inequalities give

$$
\begin{gathered}
(a-e)_+^2\le p\le\min\{1,(a+e)^2\},\qquad
q_{\rm Bell}\ge(a-e)_+^2,\qquad p-q_{\rm Bell}\le e^2,\\
F_{\rm Bell}=q_{\rm Bell}/p\ge\max\{0,1-e^2/p_0\}\quad(p>0).
\end{gathered}
\tag{TG8}
$$

For the last inequality, the distance from the ideal vector to the
line through the actual vector is at most $e$. Their squared sine
angle is at most $e^2/p_0$, and projection onto the whole Bell
subspace is at least projection onto the ideal vector's line.
Tracing true inaccessible records preserves this Bell inequality.
Normalization counts all failure histories through $1-p$, but an
accepted-only bound does not control their raw spin density matrices:
identical zero accepted maps can have rejected spin channels $I$ and
$X$.

To include those quantum failure outputs, certify the **complete**
experiment's isometries on a common dilation by
$\|V_X-V_{X,0}\|\le E_X$, including source-reject rails, every
clock/port, loss modes, no-click flags and final retained spins.
Pure-state trace distance, contractivity and the ancilla-stable
operator norm give complete flagged half-diamond distance at most
$E_X$. Complete node-instrument errors telescope through an ordinary
causal network; a coherent router needs a common dilation bound rather
than independently chosen Kraus gauges. Every accepted or Bell-good
joint probability then changes by at most $E_X$. For accepted blocks
$A,A_0$, the rejected block supplies
$\|A-A_0\|_1+|p-p_0|\le2E_X$, whence
$D(A/p,A_0/p_0)\le E_X/\max(p,p_0)$ when both are nonzero.
An ideal Bell therefore gives $F\ge\max\{0,1-E_X/p_0\}$.
Signed all-launch rewards in $[-1,1]$ change by at most $2E_X$.
There is no rare-herald guarantee independent of useful yield.

**Accuracy required to preserve the comparison.** With matched
$B_I>0$, complete flagged errors preserve ordinary Bell-good yield
above this symmetric ring-minus flag if

$$
E_D+E_S<\frac7{270}B_I.
\tag{TG9}
$$

The stronger accepted-amplitude criterion is

$$
\epsilon_D+\epsilon_S<c_{\rm margin}\sqrt{B_I},\qquad
c_{\rm margin}=\frac1{\sqrt{10}}-\sqrt{\frac2{27}}
 \simeq0.044062239.
\tag{TG10}
$$

Indeed, compare the direct lower yield
$(\sqrt{B_I/10}-\epsilon_D)^2$ with the ring upper yield
$(\sqrt{2B_I/27}+\epsilon_S)^2$. Complete-path throughputs
$\eta_D,\eta_S$ replace the right side of (TG10) by
$\sqrt{\eta_DB_I/10}-\sqrt{2\eta_SB_I/27}$, which must be positive.
Direct Bell infidelity at most $\zeta_B$ follows from
$\epsilon_D^2\le\zeta_B\eta_DB_I/10$; the generic complete-error
criterion is $E_D\le\zeta_B\eta_DB_I/10$.

For equal direct-node tails $\delta\le m e^{-\kappa_*g}$, (TG6)
gives $\epsilon_D\le e_{D,\rm fixed}
+2C_D\sqrt m\,e^{-\kappa_*g/2}$. If the ring separately supplies
$\epsilon_S\le e_{S,\rm fixed}+C_Se^{-\kappa_*g/2}$ and a
certified useful-strength floor $B_I\ge B_{\min}>0$, a sufficient
guard is

$$
g>\frac2{\kappa_*}\log
\frac{2C_D\sqrt m+C_S}
 {c_{\rm margin}\sqrt{B_{\min}}-e_{D,\rm fixed}-e_{S,\rm fixed}},
\tag{TG11}
$$

provided the denominator is positive; a negative right side permits
$g\ge0$. The ring constant cannot be inserted without its actual
route certificate. If only $B_{\rm band}$ is known, (TG3)--(TG5)
give $B_I\ge B_{\rm band}-4m e^{-\kappa_*g}$; one may require the
subtracted term to be at most $B_{\rm band}/2$ and use
$B_{\min}=B_{\rm band}/2$. Thus weaker Raman conversion or slower
dark poles demand a longer guard. No strength-independent guard is
inferred as useful conversion tends to zero.

The three-bin source, four-bin B input and five-bin final output
also charge this accuracy in time. With
$\Delta>t_p+g_A+g_B$, one sufficient optical schedule extends through
$4\Delta+t_p+g_A+g_B$, plus common propagation; a $5\Delta$ envelope
suffices for these declared windows. Generated-photon preparation,
source rejection, unused clocks, detector/reset and spin-coherence
costs remain charged. These are sufficient schedules, not latency
lower bounds. The ring must be timed at the same certified accuracy.

The [exact replay](checks/architecture/raman_temporal_tail.py) rebuilds
the side-clock coefficients, rational radical enclosures, false LTI
herald, margin and finite complex norm identities. The uniform kernel,
node-tail, decay and complete-dilation arguments above are analytic
conditional inputs. A device comparison still needs those operator
certificates on all reachable distorted inputs, uncertainty bounds
for every cavity/dark/feedback mode and ground-spin record, common
carriers/modes, and actual source/router/detector losses. An accepted
photon response or a fitted linewidth alone supplies none of the
missing full failure-spin certificate. The result makes the finite
architecture comparison quantitative under these premises; it does
not assert a measured finite-cavity advantage.

<a id="nr-r11-raman-passive-filter"></a>

### A passive photon filter gives a coefficient-independent ordinary Bell pair

Extra retained stationary memories are not necessary for every robust
ordinary construction. For the same known-frame family
$T_j=a_jI+b_jF_{Pj}$, prepare $AB=00$ and
$|\psi\rangle_{PQ}=\sqrt p|01\rangle+\sqrt q|10\rangle$,
where $q=1-p$ and $0<p<1$. Put $s=p/(1+p)$ and define orthonormal
photon vectors

$$
|a\rangle=\sqrt s|00\rangle+\sqrt{1-s}|11\rangle,\qquad
|b\rangle=\sqrt s|01\rangle+\sqrt{1-s}|10\rangle.
$$

Between the two ordinary node encounters, use the fixed photon processor
$V$ with columns

$$
V|00\rangle=|a\rangle,\quad V|01\rangle=\sqrt q|b\rangle,
\quad V|10\rangle=-\sqrt p|b\rangle,\quad V|11\rangle=0.
\tag{RP1}
$$

It is a valid contraction:
$V^\dagger V=|00\rangle\langle00|+|v\rangle\langle v|$ for
$|v\rangle=\sqrt q|01\rangle-\sqrt p|10\rangle$.
A passive unitary dilation can route its rejected components to
additional vacuum output ports. Those paths, rejected photons and
their actual collection/heralding behavior are charged resources.
After $T_BVT_A$, accept the two orthonormal photon readouts

$$
|f\rangle=\sqrt{1-s}|00\rangle-\sqrt s|11\rangle,\qquad
|g\rangle=\sqrt{1-s}|01\rangle-\sqrt s|10\rangle.
$$

The identity and single-B terms vanish because $V|\psi\rangle=0$;
the single-A term vanishes because both readouts are orthogonal to
$\operatorname{ran}V=\operatorname{span}\{a,b\}$.
The remaining double-SWAP terms are exactly

$$
\begin{aligned}
|\chi_f\rangle&=\frac{\sqrt{pq}}{1+p}b_Ab_B
                    (|01\rangle+|10\rangle),\\
|\chi_g\rangle&=\frac{\sqrt q}{1+p}b_Ab_B
                    (p|00\rangle+|11\rangle).
\end{aligned}
\tag{RP2}
$$

In the second outcome, a successful local A filter
$\operatorname{diag}(1,p)$ gives a Bell pair. It is a contraction
with its own success flag and failure branch; learning the kept spin
basis label would destroy the Bell coherence. Counting both readouts
and the filter success gives

$$
p_{\rm passive}=\frac{2p(1-p)}{1+p}|b_Ab_B|^2.
\tag{RP3}
$$

The derivative in (RP3) has sign $1-2p-p^2$, so the family is
maximized at $p=\sqrt2-1$, with coefficient
$6-4\sqrt2$; $p=1/2$ already gives $|b_Ab_B|^2/3$.
This is an achievable comparator, not an ordinary optimum. It uses
one retained photonic helper, no initially entangled stationary
ancillas, and actual passive-filter loss ports, complete photon
readout and local spin-filter apparatus. All failed launches and
resets are included. The useful component is independent of the
unknown node coefficients; the fixed processor must still preserve
the actual photon code and bandwidth. As in the ordered-kernel
argument below, cancellation holds term by term with operator-valued
coefficients, retaining the physical product $B_BB_A$.

The exact replay checks the $p=1/2$ construction in Gaussian rationals
extended by $\sqrt2$, including the optical contraction, orthogonal
readouts, local-filter effect, three canceled polynomial terms and
both retained Bell outputs. Its normalization can be made explicit:
use unnormalized source $|01\rangle+|10\rangle$,
$W=\sqrt6V$, and readouts $\sqrt3f,\sqrt3g$; their net physical
factor is $1/6$. The coefficient $1/3$ in (RP3) includes all these
factors. No sharp bound for adaptive, lossy, higher-mode ordinary
processors is inferred from this construction.

**Four helper levels strengthen the ordinary achievable coefficient.**
Let $h_0,h_1,h_2,h_3$ be orthonormal levels of a preserved flying helper,
so the joint photon code has eight modes. Put $q=1-p$ and prepare

$$
|\psi_4\rangle=\sqrt p|0,h_0\rangle+\sqrt q|1,h_1\rangle,
\quad
|a_4\rangle=\frac{|0,h_0\rangle+|1,h_1\rangle}{\sqrt2},
\quad
|b_4\rangle=\sqrt s|0,h_2\rangle+\sqrt{1-s}|1,h_3\rangle.
$$

The intermediate photon contraction $V_4$ has only three nonzero columns:

$$
V_4|0,h_0\rangle=\sqrt q|b_4\rangle,\qquad
V_4|1,h_1\rangle=-\sqrt p|b_4\rangle,\qquad
V_4|0,h_1\rangle=|a_4\rangle.
\tag{RP4}
$$

For $|\xi\rangle=\sqrt q|0,h_0\rangle-\sqrt p|1,h_1\rangle$,
$V_4^\dagger V_4=|\xi\rangle\langle\xi|
+|0,h_1\rangle\langle0,h_1|$ is a projector, proving that
$V_4$ has a passive unitary dilation with rejected output ports.
Moreover $V_4|\psi_4\rangle=0$, so the identity and single-B terms
vanish. The single-A term has photon support in
$\operatorname{span}\{a_4,b_4\}$.

The following four photon vectors are orthonormal and orthogonal to that
support:

$$
\begin{aligned}
|r_{00}\rangle&=\sqrt{1-s}|0,h_2\rangle-\sqrt s|1,h_3\rangle,
&|r_{01}\rangle&=|0,h_3\rangle,\\
|r_{10}\rangle&=(|0,h_0\rangle-|1,h_1\rangle)/\sqrt2,
&|r_{11}\rangle&=|0,h_1\rangle.
\end{aligned}
$$

Projecting the double-SWAP output onto their span gives exactly

$$
b_Ab_B\left[
\sqrt{pqs(1-s)}|r_{00}\rangle|00\rangle
+\sqrt{pq(1-s)}|r_{01}\rangle|01\rangle
+\frac{\sqrt q}{2}|r_{10}\rangle|10\rangle
+\sqrt{q/2}|r_{11}\rangle|11\rangle\right].
\tag{RP5}
$$

Choose $p(1-s)=1/4$, with $1/4\le p<1$, and read the four photon
outcomes $(r_{00}\pm r_{11})/\sqrt2$ and
$(r_{01}\pm r_{10})/\sqrt2$. The latter two already give Bell states.
For the former two, the local A filter
$\operatorname{diag}(1,\sqrt{s/2})$ balances the retained amplitudes;
its complementary effect is $\operatorname{diag}(0,1-s/2)$.
All four successes have known Pauli frames. The two even outcomes
contribute $qs/2$ and the two odd outcomes contribute $q/2$, giving

$$
p_{\rm four\ levels}
=(1-p)\left(1-\frac1{8p}\right)|b_Ab_B|^2.
\tag{RP6}
$$

The derivative of the coefficient is $-1+1/(8p^2)$, so this family is
maximized at $p=1/(2\sqrt2)$, $s=1-1/\sqrt2$, with coefficient
$9/8-1/\sqrt2\simeq0.417893$. The rational setting
$p=1/3,s=1/4$ gives $5/12$. Thus extra flying helper levels improve
the two-level construction without initial stationary ancillas.
This remains an achievable coefficient below the switched-minus
coefficient $1/2$, and supplies no ordinary optimality claim.

The [four-level replay](checks/architecture/raman_multimode_helper.py)
checks the full $p=1/3,s=1/4$ instrument in
$\mathbb Q(\sqrt2,\sqrt3)$: source normalization, the contraction and
its rejected complement, four orthonormal readouts, the twelve zero
heralded identity/single-node branches, all four filtered Bell outputs,
and local-filter success/failure effects. In the double-SWAP branch,
processor rejection, photon-readout rejection, spin-filter rejection
and Bell success have respective probabilities
$1/9,13/72,7/24,5/12$, summing to one. The parameter-family optimum
and its physical access assumptions remain analytic.

The larger photon code, rejected ports, complete joint readout and local
spin filter must be preserved by the actual node and priced. This needs
the physical extension $T_j\otimes I_H$ on all eight joint modes;
the two-level temporal codec above does not by itself implement it.
Arbitrary processors that do not annihilate the source between nodes
and adaptive local filtering remain open ordinary comparisons. The
timed-spin compiler below accounts for closed known-frame conjugations;
their physical controls and actual vacuum extension still need pricing
before a hardware bound covering all ordinary protocols can be claimed.


<a id="nr-r11-raman-timed-controls"></a>

#### Closed timed spin controls have an exact photon compiler

Consider the same accepted family $T_j=a_jI+b_jF_{Pj}$ in a known
common SWAP frame, extended as $T_j\otimes I_H$ on a preserved flying
helper. A known unconditional spin-pulse schedule has cumulative
propagator $U_k$ just before photon slot $k$ and complete no-photon
propagator $K$. Its post-slot propagator is $KU_k^\dagger$, so the
occupied-slot operator is $KU_k^\dagger T_jU_k$. A common restoration
$K^\dagger$ after all slots gives
$U_k^\dagger T_jU_k$ and identity on every vacuum history. All pulses
run after lost and rejected photons as well. This factorization requires
the drive to lie outside the complete photon interaction and its
unresolved dwell; each gap includes actual pulse time and tail guards.

For every known qubit unitary $U$, the SWAP identity gives

$$
(I_P\otimes U_j^\dagger)F_{Pj}(I_P\otimes U_j)
=(U_P\otimes U_j^\dagger)F_{Pj}
=(U_P\otimes I_j)F_{Pj}(U_P^\dagger\otimes I_j).
\tag{TC1}
$$

The identity term transforms the same way. Therefore (TC1) also holds
with $F_{Pj}$ replaced by $T_j$, coefficient by coefficient, for unknown,
unequal complex $a_j,b_j$. It is an operator equality on every input and
reference. Since the helper is preserved, a helper-controlled spin
conjugation equals $C_jT_jC_j^\dagger$, where
$C_j=\sum_k|k\rangle\langle k|_H\otimes U_{j,k}$ is the corresponding
known controlled **photon** gate.

For an arbitrary intermediate photon/helper contraction $V$, including
one that mixes helper labels, the complete ordinary sequence factors as

$$
C_BT_BC_B^\dagger V C_AT_AC_A^\dagger
=C_BT_B(C_B^\dagger VC_A)T_AC_A^\dagger.
\tag{TC2}
$$

Absorb $C_A^\dagger$ into the prepared photon/helper state,
$C_B^\dagger VC_A$ into the intermediate processor and $C_B$ into the
final joint photon readout. The processor remains a contraction. Common
spin output frames $K_A,K_B$ commute past the other node and the photon
operations and can be restored locally. Every polynomial term and any
subsequent accepted spin filter is preserved. Thus these closed timed
spin conjugations add no capability to the already arbitrary
photon/helper source, processor and readout in this known-frame
accepted family. Their physical durations, losses and control references
remain separate costs.

An explicit physical schedule for four Pauli rays is
$\mathrm{bin}_0;R_x(\pi);\mathrm{bin}_1;R_y(\pi);
\mathrm{bin}_2;R_x(\pi);\mathrm{bin}_3;R_y(-\pi)$.
Its pre-slot propagators are $I,-iX,iZ,-iY$ and its total propagator is
$I$. It uses four actual XY $\pi$ pulses. A virtual frame update alone
does not rotate the spin seen by the scattering device. A snake through
all sixteen independent pairs of these frames uses twelve physical
transitions/restoration pulses at A and four at B. These are achievable
schedules rather than minimum pulse counts. Long helpers add spin
exposure, coherent time-bin storage, pulse errors and phase stability
requirements on every attempt.

The known-frame and instrument scope is essential:

* If the physical family is
  $T_R=(I\otimes R)(aI+bF)(I\otimes R^\dagger)$, a laboratory spin
  $U$ compiles to the photon gate $R^\dagger UR$. An unknown Raman-leg
  frame $R$ therefore requires its actual phase reference or calibration,
  unless the chosen control commutes with it. Equation (TC2) does not
  remove unknown relative Raman phases.
* Spectator coefficient operators may be retained only when they commute
  with the compiled controls and preserved helper. A frequency-changing
  control cannot be commuted through an unknown frequency kernel by this
  scalar identity. Helper-changing node operators also invalidate it.
* Equality of accepted operators does not specify rejected spin/bath
  outputs. For example a valid all-loss channel resetting the spin to
  $0$ has accepted $T=0$. Spin $X$ conjugation resets it to $1$, whereas
  photon $X$ conjugation followed by vacuum still resets it to $0$.
  Full loss-instrument equality needs a separate intertwining of its
  actual Kraus operators and vacuum action. Losses, resets and records
  remain charged.
* Pulses overlapping the optical dwell, changes to coupling or detuning,
  nonunitary spin control during the query, and nonfactorizing spin/bath
  dynamics define a different driven or multi-time primitive. Its full
  instrument requires a new comparison.

The [timed-control replay](checks/architecture/raman_timed_controls.py)
checks full reference-complete one- and two-node operator identities,
complex coefficient examples, noncommuting helper-mixing processors,
known twisted frames, the pulse chronology and the stated counterexamples.
No upper bound for arbitrary photon processors or adaptive ordinary
protocols is inferred.

<a id="nr-r11-raman-late-flip"></a>

#### A calibrated timed photon flip gives direct ordinary Bell heralds

There is a separate direct comparator for two identical calibrated
nodes $T=tI+\beta F$, $t=1-\beta$, $0\le\beta\le1$, in a known
real Raman frame. Prepare
$(|\mathrm{early},P0\rangle+|\mathrm{late},P1\rangle)/\sqrt2$ and
spins $00$, and route A then B through the complete two-port adapters.
One balanced beam splitter followed by a delay on its $P1$ output
prepares these two bins from one single-bin photon. Both orthogonal
output rails enter A, so this preparation needs no selected source port.
Between the nodes apply an unconditional classical photon-rail $X$
gate during the late bin. This timed physical rail operation and its
drive, loss and phase reference are part of the ordinary apparatus.
The full no-loss output is

$$
\frac1{\sqrt2}\left[
|\mathrm{early},P0,00\rangle+
|\mathrm{late}\rangle\left(t|P0,00\rangle+
\beta t|P1,10\rangle+\beta^2|P0,11\rangle\right)\right].
\tag{LF1}
$$

Accept $P0$ and both central-clock ports of a balanced passive time-bin
$X$ decoder. Its bras are
$(\langle\mathrm{early}|\pm\langle\mathrm{late}|)/2$, so their
total effect is $I_Q/2$. The two spin vectors are

$$
\frac{(1\pm t)|00\rangle\pm\beta^2|11\rangle}{2\sqrt2}.
\tag{LF2}
$$

For the corresponding flag use the local A filter
$\operatorname{diag}(\beta^2/(1\pm t),1)$. Both are contractions:
the minus ratio is $\beta$, and
$2-\beta-\beta^2=(1-\beta)(\beta+2)\ge0$ proves the plus ratio
is at most one. At $\beta=0$ the minus click is zero and is rejected.
Each filter success has a known Bell frame and probability $\beta^4/4$.
Counting both ports therefore gives

$$
p_{\rm late\ flip}=\frac{\beta^4}{2}.
\tag{LF3}
$$

All-launch accounting follows directly from (LF1). Node-loss rejection,
$P1$ rejection, offcentral photon rejection, spin-filter rejection and
Bell success have respective probabilities

$$
\beta(1-\beta)(1+\beta^2),\quad
\frac{\beta^2t^2}{2},\quad
\frac{1+t^2+\beta^4}{4},\quad
\frac{(1-\beta)(\beta^3+\beta^2+2)}4,\quad
\frac{\beta^4}{2}.
$$

They are nonnegative and sum to one. This circuit uses the displayed
passive central-clock decoder directly. Prepared source bins, the timed
photon flip, spin filters, complete port access, pulse/tail guards,
reset after failures and actual component losses remain charged.
Known $\beta$ and a sufficiently calibrated relative Raman phase are
needed for the filters and Bell frames; (LF3) is not the uniform
unknown-coefficient construction (RP1)--(RP6).

Against the specified symmetric passive ring (RT2), with routing factor
$4/27$ and intrinsic both-flag yield $\beta^2(1+t^2)$, the ideal
difference is

$$
\frac{\beta^4}{2}-\frac4{27}\beta^2(1+t^2)
=\frac{\beta^2}{54}(19\beta^2+16\beta-16).
$$

It is nonnegative for
$\beta\ge(-8+4\sqrt{23})/19\simeq0.5886$.
An equal physical scalar spectator attenuation on both two-query
protocols multiplies their yields by the same factor. Unequal,
frequency-dependent or helper-dependent kernels and the actual
component loss require their full comparison. This is a comparison of
the stated circuits and adapters, with no universal routing optimum.

The same exact replay reconstructs (LF1)--(LF3) as rational polynomial
identities, checks both physical central-clock flags and filter effects,
the nonnegative failure factors, total probability and threshold.
Finite rational guards support transcription; the displayed polynomial
identities establish the whole interval.


<a id="nr-r11-raman-local-ancillas"></a>

### Local quantum memories strengthen the ordinary Raman comparison

An ordinary comparator may prepare entanglement **within** a station.
That is different from granting initial entanglement between the two
stations. The following circuits use a local Bell pair $AA'$ at station
A, a local Bell pair $BB'$ at station B, and a Bell pair $PQ$ of two
degrees of one flying photon. Nodes preserve $Q$ and couple only $P$
to the active spin $A$ or $B$. Apply the two nodes in ordinary order
A then B, jointly Bell-measure $PQ$, and apply its known teleportation
Pauli correction on A. The extra stationary qubits $A',B'$ and the
coherent local operations below are real, priced resources. These are
achievable ordinary protocols, not optimality or hardware-rate theorems.

**A coefficient-independent filter.** In a known common SWAP frame let
$T_j=a_j I+b_jF_{Pj}$, where $F$ denotes SWAP and the scalar coefficients
may be unknown, unequal and complex. The accepted operators on $AB$
after the four photon Bell outcomes are

$$
\begin{aligned}
L_I&=\left[a_Aa_B+\tfrac12(b_Aa_B+a_Ab_B)\right]I
       +\tfrac12b_Ab_BF_{AB},\\
L_\mu&=\tfrac12b_Aa_B I+
       \tfrac12a_Ab_B\sigma_\mu\otimes\sigma_\mu
       +\tfrac12b_Ab_BF_{AB},\quad \mu=X,Y,Z.
\end{aligned}
\tag{RA1}
$$

To derive them, expand the two ordered $T$ factors and contract their
photon index with the prepared and measured Bell states. The identity
$F_{AB}=(II+XX+YY+ZZ)/2$ gives the remaining terms. All source and
readout normalization is included in (RA1); the ideal $a_j=0,b_j=1$
limit recovers (RS13).

Use the orthonormal local Pauli-Bell bases
$|e_\mu\rangle=(\sigma_\mu\otimes I)|\Phi^+\rangle$ on $AA'$ and
$BB'$, with $\sigma_I=I$, and put $d=b_Ab_B/4$. Acting on the two
local Bell pairs, each (RA1) state is diagonal in
$|e_\nu,e_\nu\rangle$. In outcome I its only coefficient beyond $d$
is on $|e_I,e_I\rangle$; in outcome $\mu$ the only two such
coefficients are on $|e_I,e_I\rangle$ and $|e_\mu,e_\mu\rangle$.
Consequently fixed **coherent subspace projections** at A give

$$
\begin{array}{c|c|c}
\text{photon outcome}&\text{local subspace retained at A}&\text{state retained}\\
I&\{e_X,e_Y,e_Z\}&d\sum_{\nu=X,Y,Z}|e_\nu,e_\nu\rangle\\
\mu&\{e_\nu:\nu\ne I,\mu\}&d\sum_{\nu\ne I,\mu}|e_\nu,e_\nu\rangle.
\end{array}
\tag{RA2}
$$

This is not a measurement revealing the individual Bell label, which
would destroy the desired entanglement. The rank-three branch is a
maximally entangled qutrit. On A apply the three pair projectors
$P_{XY},P_{XZ},P_{YZ}$ divided by $\sqrt2$. Each label occurs in two
pairs, so their effects sum to identity on the retained support. Every
outcome gives a Bell pair; communicate the pair and locally decode it
at both stations. Each other photon outcome already retains a Bell
pair on two labels. Thus the complete exact-Bell yield is

$$
p_{\rm fixed}=9|d|^2=\frac9{16}|b_Ab_B|^2.
\tag{RA3}
$$

Every rejected subspace and lost photon remains charged. Preparations,
corrections, projections and decodes use no unknown coefficient.
In comparison, the switched minus operator is
$b_Ab_B[F_{PB},F_{PA}]/2$. On $PAB=100$ it gives an exact Bell pair
with probability $|b_Ab_B|^2/2$. Equation (RA3) exceeds that
**minus-only** yield by a factor $9/8$, conditional on the extra local
resources. It does not compare the additional useful plus flags of
identical calibrated nodes. The cancellation is coefficient-independent
in the specified common frame; unknown Raman-leg phases or basis
misalignment are not granted away.

The scalar result holds record by record if every accepted Kraus
operator is in the span of $I,F$. With independent slot records its
yield is $\frac9{16}(\sum_r|b_{A,r}|^2)(\sum_s|b_{B,s}|^2)$.
Each retained Bell state factors from those records. Common preserved
frequency labels can likewise be averaged after applying (RA3)
pointwise, rather than discarded before the comparison.

**Ordered auxiliary kernels need not commute.** A stronger ordinary
statement retains a common auxiliary field/memory space $W$. Suppose
the complete accepted node operators have the declared form

$$
T_j=A_j\otimes I_{Pj}+B_j\otimes F_{Pj},
\tag{RA4}
$$

with arbitrary operators on $W$, an independent prepared logical Bell
pair $PQ$, and actual identity action on $Q$. The four coefficients
in $T_BT_A$ are, in their physical order,
$A_BA_A$, $A_BB_A$, $B_BA_A$, $B_BB_A$. The fixed contraction and
projections above annihilate the first three logical terms separately.
Every retained logical coefficient is $B_BB_A/4$. After the fixed
conversion, the known Bell output factors from the ordered auxiliary
kernel, including any input reference; the branch norms therefore give

$$
p_{\rm fixed}=\frac9{16}
 \operatorname{Tr}(B_BB_A\rho_WB_A^\dagger B_B^\dagger).
\tag{RA5}
$$

For accepted Kraus families, sum this ordered expression over the
actual labels. No coefficient commutation is used. This supplies a
full-mode ordinary filter when a microscopic model really has (RA4);
it does not establish that unequal Raman legs, shifted carrier codes
or an arbitrary optical bath have this form. In particular there is
no general switch-minus Bell comparison for noncommuting auxiliary
kernels. All environments and lost outcomes must retain their actual
physical completion.

**Calibrated flat nodes retain still more ordinary outcomes.** Set
$a_A=a_B=1-\beta$, $b_A=b_B=\beta$ in (RA1), and define

$$
A_0=(2-\beta)^2/4,\quad B_0=\beta^2/4,\quad
C_0=\beta(2-\beta)/4,\quad q_0=1-\beta+\beta^2.
\tag{RA6}
$$

The four unnormalized Schmidt vectors are
$(A_0,B_0,B_0,B_0)$ for I and, up to known local permutations,
$(C_0,C_0,B_0,B_0)$ for each other flag. The latter factor into an
exact logical Bell pair times a bipartite junk state after a local
basis relabeling; their full norms are useful. Their total norm,
including the I branch, is $q_0^2$, so photon loss is $1-q_0^2$.

The optimal single-Bell conversion probability of an unnormalized
pure state with norm $n$ and largest squared Schmidt weight $\lambda$
is $\min\{n,2(n-\lambda)\}$, the Bell-target case of
[Vidal's conversion theorem](https://arxiv.org/abs/quant-ph/9902033)
with [Nielsen's deterministic majorization criterion](https://arxiv.org/abs/quant-ph/9811053).
Achievability for the I branch is explicit here. Let
$\lambda=(A_0^2,B_0^2,B_0^2,B_0^2)$. A local edge filter $i,j$ with
entries $\sqrt{w_{ij}/\lambda_i}$ and
$\sqrt{w_{ij}/\lambda_j}$ leaves
$\sqrt{w_{ij}}(|i,i\rangle+|j,j\rangle)$, of Bell yield $2w_{ij}$.
If $A_0^2\ge3B_0^2$, choose $w_{0i}=B_0^2$ for the three other
labels and zero other edges. Their effects sum to
$\operatorname{diag}(3B_0^2/A_0^2,1,1,1)\le I$; the remaining
separable failure weight is $A_0^2-3B_0^2$.
If $A_0^2\le3B_0^2$, choose
$w_{0i}=A_0^2/3$ and
$w_{ij}=(B_0^2-A_0^2/3)/2$ for $1\le i<j\le3$.
The incident weights sum to $\lambda_i$ at every vertex, so the
effects sum to identity and all outcomes succeed. The zero-yield
$\beta=0$ endpoint needs no division by a zero Schmidt weight.
The I-flag yield is thus $\min(A_0^2+3B_0^2,6B_0^2)$, giving

$$
p_O=\min\left\{q_0^2,
 \frac38\beta^2(4-4\beta+3\beta^2)\right\}.
\tag{RA7}
$$

All four photon outcomes, loss and local-filter failure are counted.
Below $\beta_*=2/(1+3^{1/4})$, its difference from (RS5) is
$\beta^2(\beta^2+4\beta-4)/8$; above that threshold all no-loss
outcomes are retained and the difference is $(1-\beta)^2$.
Hence (RA7) strictly beats the stated switch when
$2(\sqrt2-1)<\beta<1$, with equality at perfect coupling. At
$\beta=0.9$ it gives $0.8281$ versus $0.8181$.
This is a constructive obstruction to applying a pure-active-spin
converse to initially encoded local memories. It is not an ordinary
optimum or a claim that the extra gates are cheaper in a real device.

There is a separate small exact certificate at $\beta=7/10$:
[rational circuit data](checks/architecture/raman_bell_certificate.json)
and [standalone replay](checks/architecture/verify_raman_bell_certificate.py).
Prepare local pairs $PQ,AA',BB'$ with amplitudes
$(\frac{1-v^2}{1+v^2},\frac{2v}{1+v^2})$, respectively
$v=(297,541,645)/1000$. Between the two node interactions apply the
data's photon unitary $U$, then apply $R$ before a complete four-outcome
photon readout. Both are reconstructed as
$(I+iH)(I-iH)^{-1}$ from explicitly Hermitian rational $H$ matrices.
The replay verifies their unitarity, the normalized six-qubit input,
the node's positive loss completion and every actual output coefficient.
For each four-by-four station coefficient matrix $M_j$ it reconstructs
$G_j=M_jM_j^\dagger$, $n_j=\operatorname{Tr}G_j$, and proves
$g_jI-G_j>0$ by an exact LDL factorization with positive pivots, where
$g_j=(0.051614,0.047928,0.050957,0.123143)$.
The conversion theorem therefore attains at least

$$
\sum_j\min\{n_j,2(n_j-g_j)\}>0.5473
>p_S+0.013,\qquad p_S=0.5341.
\tag{RA8}
$$

The constants are exact terminating rationals; approximate eigenvalues
are not used as a certificate. The lower-bound direction follows from
$\lambda_{\max}(G_j)<g_j$, so it certifies an attainable protocol,
not an ordinary upper bound. All four readouts and failed local
conversions are included. The executable data is the sole owner of the
two detailed $H$ matrices, with this proof supplying their task meaning.

These protocols retain one extra stationary qubit per station. Preparing
its local entanglement, preserving it, implementing a coherent subspace
filter without learning a kept label, any additional measurement
ancillas/apparatus, local decoding, classical feedforward and restoration
all require their actual duration, noise and availability. The order
helper alone does not supply these operations. Their existence changes
the strongest ordinary comparison; a delivered-rate comparison must
price them instead of either granting them for free or excluding them
without an architecture reason.

The exact replay reconstructs the six-qubit circuits, local filter
effects, complex unequal-coefficient projections and two noncommuting
auxiliary-operator examples. Its finite identities support the analytic
linear cancellation, concentration and resource scope above; they do
not certify a physical memory interface or a native advantage.

<a id="nr-r11-raman-cavity-frontier"></a>

### Complete balanced-cavity amplitudes and the design frontier

This
screen applies to one photon, identical balanced three-level nodes,
matched Raman gaps/carrier codes and the complete two-mode port encoding.
Both cavity modes have the same detuning relative to their respective
code carriers. It does not infer such a node or
router from the Hallacy charged-dot experiment. Let $\kappa_i$ and
$\kappa_{\rm ex}$ be intrinsic and external cavity amplitude decay,
$\kappa=\kappa_i+\kappa_{\rm ex}$, $\gamma$ the free-space atomic
amplitude decay, and $g$ the coupling on each leg. Population decay
rates are $2\kappa$ and $2\gamma$. The conventions and imperfect
multilevel extension follow [Rosenblum et al., §§III--V](https://arxiv.org/html/1412.0604v3).

In the symmetric one-excitation model, the cavity bright state couples
to the excited atom at $G=\sqrt2g$ and its dark state is uncoupled.
For real detunings the monitored spectator and bright amplitudes are

$$
c=1-\frac{2i\kappa_{\rm ex}}{\Delta_c+i\kappa},\qquad
h=1-\frac{2i\kappa_{\rm ex}(\Delta_a+i\gamma)}
 { (\Delta_c+i\kappa)(\Delta_a+i\gamma)-2g^2},
\qquad T=cI+(h-c)P_B.
\tag{CF1}
$$

This follows directly by inverting the bright cavity/atom $2\times2$
resolvent; the dark resolvent is $(\Delta_c+i\kappa)^{-1}$. Intrinsic
cavity outputs and every free-space final-spin output complete its
isometry. A known fixed local basis/phase conjugation taking $P_B$ to
$P_-=(I-\mathrm{SWAP})/2$ gives
$T'=uI+f\,\mathrm{SWAP}$ with $u=(c+h)/2$, $f=(c-h)/2$ and $u+f=c$.
The phase frame must actually be calibrated and routable at both nodes.
For $c\ne0$ one can algebraically factor $T'=c[(1-b)I+b\,\mathrm{SWAP}]$,
$b=(1-h/c)/2$. The real flat-loss parameter interpretation
$b=\beta\in[0,1]$ requires real $h/c$ in $[-1,1]$; it is not a general
property of detuned or multilevel devices.

With $P=1,A=B=0$, an independent order helper and both retained order
flags, the switch's photon-$0$ herald prepares $\Psi^\pm_{AB}$.
The yield for identical $T'$ is
$p_S=|f|^2(|c|^2+|u|^2)$. Pointwise frequency dependence only changes
the scalar envelope of each Bell flag in this perfectly matched model.
An ordinary photon coherently split into two routes, one visiting only
$A$ and the other only $B$, with the Raman outputs coherently collected
and read in a path $X$ basis, gives the same Bell task with
$p_1=|f|^2$. This comparator needs only one occupied node visit per
history. It requires a real bypass/collection path, balanced amplitudes,
common Raman frequency code and the known path phase; it does not
exist for free in an arbitrarily restricted one-port graph. Source,
all paths, readout, reset and memory costs must be charged.

There is an analytic design frontier, so intentionally adding cavity
overcoupling to reach a smaller effective $\beta$ does not by itself
yield an advantage if the same coupling adjustment is available to
the ordinary route. Assume $\kappa_i,\gamma,g>0$ and put

$$
D=\frac{2g^2}{\kappa_i\gamma}=s^2-1,\quad s>1,\quad
r=\frac{\kappa_{\rm ex}}{\kappa_i},\quad
x=\frac{\Delta_c}{\kappa_i},\quad y=\frac{\Delta_a}{\gamma},
\quad z=x+i(r+1),\quad d=z(y+i)-(s^2-1),\quad
m=\frac{s-1}{s+1}.
$$

The denominators are nonzero: $z$ has positive imaginary part, and
$\operatorname{Im}d=0$ would give $x=-(r+1)y$, making
$\operatorname{Re}d=-(r+1)(1+y^2)-(s^2-1)<0$.
Then $c=1-2ir/z$ and $h=1-2ir(y+i)/d$. Direct expansion gives

$$
1-\frac{|f|^2}{m^2}-|u|^2
=\frac{2r}{|zd|^2}\left\{
(s^2+1)[(r-s)^2+x^2]
+2[(r+1)^2+x^2]y^2-2(s^2-1)xy\right\}\ge0.
\tag{CF2}
$$

For completeness, let $H=s^2+1$, $a=r+1$ and $e=r-s$.
The two AM--GM inequalities
$He^2+2x^2y^2\ge2\sqrt{2H}|exy|$ and
$Hx^2+2a^2y^2\ge2\sqrt{2H}a|xy|$ bound the braces from below by
$2[\sqrt{2H}(|e|+a)-(s^2-1)]|xy|\ge0$.
Here $|r-s|+r+1\ge s+1$ and
$2(s^2+1)-(s-1)^2=(s+1)^2\ge0$. Also $|c|\le1$, from
$|z|^2-|z-2ir|^2=4r$. Therefore

$$
p_S=|f|^2(|c|^2+|u|^2)
\le m^2(1-|u|^2)(1+|u|^2)\le m^2.
\tag{CF3}
$$

This is pointwise for arbitrary real detunings, so any normalized
finite-pulse spectrum preserves the upper bound. At $x=y=0$,
$f$ has magnitude $rD/[(r+1)(r+1+D)]$. Its maximum is $m$, attained at
$r=s$: the identity
$(r+1)(r+s^2)-r(s+1)^2=(r-s)^2$ proves this maximum without a numerical
search. The ordinary single-scatter route thus approaches $p_1=m^2$
with a sufficiently narrow pulse at that coupling. This is a raw-yield
design comparison; it does not assert identical finite-duration clocks,
available coupling range, or the exact ordinary optimum for a fixed
fabricated device. In particular, $\kappa_i=0$ or $\gamma=0$ are limiting
cases with $m\to1$, rather than inputs to the displayed normalization.

The actual [Bechler et al. experiment](https://arxiv.org/pdf/1711.10974),
main text p.4, reports nominal $(\kappa_{\rm ex},\kappa_i,g,\gamma)/2\pi
=(60,6,27,3)$ MHz in these amplitude conventions. At its resonant
balanced-model point, $c=-9/11$, $h=18/23$, $u=-9/506$, $f=-405/506$,
and $\beta=f/c=45/46$. Consequently $p_1=164025/256036\simeq0.640633$
already exceeds $p_S\simeq0.429056$ at the same nominal coupling.
The retuned ordinary maximum is
$[(\sqrt{82}-1)/(\sqrt{82}+1)]^2\simeq0.641764$ at
$\kappa_{\rm ex}/2\pi=6\sqrt{82}\simeq54.3323$ MHz.
The real device has finite pulses, polarization crosstalk,
position-dependent couplings, atom-presence heralds, and inferred or
corrected transfer fidelities. These numbers are conditional model
estimates, not measured Bell-pair yields. A different finite advantage
would need a useful task that survives the ordinary routing/renewal
comparison, actual mode and bath records, calibrated phase frames,
source/reset/clock costs, and a demonstrated two-node interface.

<a id="nr-r11-raman-source-clock"></a>

### Raman Bell yield must be compared at source and clock cost

The following achievable ordinary comparison requires coherent which-node
photon paths, collected Raman outputs and known relative Raman/path
phases, or an actual complete phase eraser. It is not inferred from a
sealed abstract SWITCH. The active memories are reset to a pure product
state after each unsuccessful trial. All reset, routing and reference
costs enter the clock comparison below.

**Keep the physical spectator amplitude.** For two identical balanced
monochromatic monitored nodes, write
$T=aI+bW$, where $W=\mathrm{SWAP}$, $s=a+b$ is the spectator amplitude,
$q=|b|^2$, and $h=|a|^2+|b|^2$. Passivity implies $|s|^2\le1$ and
$h\le1$. In the balanced cavity model,
$a=(t_0+s_B)/2$, $b=(t_0-s_B)/2$, so $s=t_0$.
Lost photons are rejected with all attempts charged; photon-preserving
errors and residual frequency/bath records need the full instrument.

On $P=1,A=B=0$, the two accepted order histories are

$$
\begin{aligned}
|\Phi_0\rangle&=a^2|1,00\rangle+bs|0,10\rangle+ab|0,01\rangle,\\
|\Phi_1\rangle&=a^2|1,00\rangle+ab|0,10\rangle+bs|0,01\rangle.
\end{aligned}
\tag{RF1}
$$

Prepare the order helper in plus, retain photon outcome $P=0$, and
read the helper in $X$. The two unnormalized spin states are
$b(s\pm a)(|10\rangle\pm|01\rangle)/2$. Thus both flags give Bell
pairs after their known frame correction, with total probability

$$
p_S=q(|s|^2+|a|^2).
\tag{RF2}
$$

An ordinary coherent which-node path sends the photon through only $A$
on one branch and only $B$ on the other. Its selected Raman output is
$b|0\rangle_P(|0\rangle_O|10\rangle+|1\rangle_O|01\rangle)/\sqrt2$.
Both helper-$X$ outcomes give Bell pairs, so one incident-photon node
visit achieves $p_1=q$. This uses no entangling gate between the remote
memories. A photon carrying both path and Raman mode can be measured
with one joint-mode click; resolving two degrees of freedom does not
automatically square the detection efficiency. A separate matter helper
has its own coupling and readout costs. Physical vacuum/idle extensions
and the accessible one-node termination paths must still be established.

**Repeated photons change the budget comparison.** Two independent
ordinary attempts, with herald/feedforward and product reset after
failure, achieve

$$
p_2=2q-q^2,\qquad
p_2-p_S=q(2-|s|^2-h)\ge0.
\tag{RF3}
$$

They use at most two photons and two incident-photon node visits, with
the second skipped after success. Their expected number of attempts is
$2-q$. Two pulses sent without waiting for the first herald and resetting
the same memories do not automatically implement this protocol; the
first success could be overwritten. Parallel trials instead need more
memory pairs or a validated multiplexing interface.

The switch's mean number of incident-photon visits is $c_S=1+h$:
the first node loses the photon with probability $1-h$, so the second
then has no occupied encounter. Counting these losses gives

$$
q c_S-p_S=q(1+q-|s|^2)\ge q^2,
\qquad p_S/c_S<q\quad(q>0).
\tag{RF4}
$$

This is an actual incident-photon ledger, rather than charging two
nominal query windows independently of occupancy. Ordinary renewal
therefore gives higher yield per mean visit under these premises.
For a finite comparator within the switch's mean-visit budget, use a
second ordinary attempt after failure with probability
$u=\min\{1,h/(1-q)\}$ for $q<1$. Its cost and yield are
$1+u(1-q)\le1+h$ and $q[1+u(1-q)]$. If $u<1$, its gain over (RF2)
is $q(1+q-|s|^2)$; if $u=1$, (RF3) applies. It matches or beats the
switch without a larger mean visit count, although its photon cap and
wall time can differ. At $q=1$ the first ordinary attempt already succeeds.
With unrestricted stopping and only mean visit cap $B$, launching a
geometric repeat-until-success round with probability $\min(1,qB)$
achieves success $\min(1,qB)$ at mean cost at most $B$. This needs
stationarity, reset and a valid Bell frame over the whole reuse window;
it is not a hard deadline or fixed photon cap.

**Use an all-outcome source and clock ledger.** Let $Q_k$ be the
probability of the required single-photon input on a source-clock
attempt, and $e_k$ the remaining independent routing/detection/erasure
efficiency, excluding intrinsic node success $p_k$. Only under these
actual factorization assumptions may success be written
$y_k=Q_ke_kp_k$. State-dependent loss, multiphoton events, dark counts
and unresolved records instead require the complete instrument and a
common delivered-fidelity threshold. A normalized selected-state
fidelity is not an unconditional yield.

Let $d_k$ be the mean complete cycle duration over every outcome. It
includes source waiting, preparation, propagation, interaction, detector
dead time, no-click timeout, classical herald/feedforward, failed-memory
reset, and the successful hand-off needed before hardware reuse. For
restored independent cycles, with arbitrary correlation between duration
and success within one cycle, renewal gives

$$
\mathbb E T_k=d_k+(1-y_k)\mathbb E T_k=d_k/y_k,
\qquad R_k=y_k/d_k.
\tag{RF5}
$$

For first-success time, the cycle ends at success and resets only after
failure. For sustained rate, include the required successful hand-off
or reset before starting the next cycle. Pipelining across memory pairs
requires a separate occupancy ledger. Grouping two ordinary trials gives
$y_2=y_1(2-y_1)$ and $d_2=(2-y_1)d_1$, so $y_2/d_2=y_1/d_1$.
The two-photon probability in (RF3) alone is not a rate comparison.

If $g_k$ is the mean number of generated probe photons in one cycle,
all rejected photons included, then photons per success are $g_k/y_k$.
For a vacuum-or-one source $g_k=Q_k$; for a coherent probe of mean $g_k$,
$\Pr(\text{exactly one})=g_ke^{-g_k}$, while its multiphoton branches
need separate treatment. Preparation/pilot photons, pump energy and
rejected atom loading are additional costs.

To beat even the explicit one-node ordinary renewal comparator, the
switch must satisfy

$$
\frac{d_S}{d_1}
<\frac{Q_Se_S}{Q_1e_1}(|s|^2+|a|^2).
\tag{RF6}
$$

This is necessary against that feasible method, not sufficient against
every ordinary protocol. For a heralded source with common mean waiting
time $H$, put $d_k=H+d'_k$ and
$G=(e_S/e_1)(|s|^2+|a|^2)$. The condition is
$H+d'_S<G(H+d'_1)$. If $G\le1$ and $d'_S\ge d'_1$, no source wait
helps. If $G>1$, a positive numerator requires
$H>(d'_S-Gd'_1)/(G-1)$. If $G<1$ but $d'_S<Gd'_1$, a win requires
$H<(Gd'_1-d'_S)/(1-G)$. At $G=1$, it requires $d'_S<d'_1$.
No unmeasured source, timing or routing values are assigned.

The nominal spectator-loss comparison is given by (CF1)--(CF3);
dropping that attenuation would change the source budget.

The [primary SPRINT experiment](https://arxiv.org/pdf/1711.10974),
pp.6,8--10, uses approximately $50$ ns swap pulses, detector-related
separations above $200$ ns, attenuated coherent inputs, atom-presence
tests and an erasure pulse. Its quoted detector efficiency is $55$--$60\%$,
with additional path loss. These measurements do not specify a
two-node Bell cycle or a heralded ideal one-photon source. Its pulse
length is not the complete $d_k$.

The complete [phase-reference comparison](#nr-r11-raman-phase-reference)
below retains physical Raman legs, reciprocal event times, shared pilots
and the ordinary coefficient filters; scalar channel phases alone do not
establish a physical reference saving.

<a id="nr-r11-raman-phase-reference"></a>

### Raman phase references require a complete port and spin instrument

Reciprocal propagation can suppress a specified physical phase process.
It does not remove every Raman or spin-frame phase, and scalar node
phases also cancel in the ordinary two-node filters above. The following
instrument identities distinguish those cases while retaining the actual
frequency, time, pilot and spin records. They supply a finite comparison
once the device kernels and noise law are measured; they do not establish
a device rate advantage from a choice of channel phase convention.

**Physical phases and arbitrary frame changes.** Let $P$ be the collected
photon mode, $Q$ an independent helper when present, and $j=A,B$ the
retained ground-state memories. On a short, flat accepted interaction,
write

$$
\begin{aligned}
T_j(t)&=e^{i\gamma_j(t)}
 \left[a_j(t)I+b_j(t)W_j(\phi_j(t))\right],\\
W_j(\phi)&=D_j(\phi)F_{Pj}D_j(\phi)^\dagger,
\qquad D_j(\phi)=|0\rangle\langle0|
                  +e^{i\phi}|1\rangle\langle1|.
\end{aligned}
\tag{PR1}
$$

Here $F$ is SWAP. Consequently $W_j|1,0\rangle
=e^{i\phi}|0,1\rangle$, $W_j|0,1\rangle
=e^{-i\phi}|1,0\rangle$, and the equal-bit states are unchanged.
The Raman-leg phase $\phi_j$ is defined relative to the actual input,
output and spin-control frames. A scalar $\gamma_j$ is physical only
relative to a specified vacuum/bypass path or other coherent reference.
All rejected optical and loss rows remain part of the complete
instrument. Equation (PR1) is a flat limit, requiring negligible variation
of the stated coefficients and phases across the pulse.

Frame covariance holds more generally than this SWAP family. For any
unitary changes $G_{\rm in},G_{\rm out}$ of the full prepared/readout
registers, including photon ports, memories and any retained reference,
transform

$$
\rho'=G_{\rm in}\rho G_{\rm in}^\dagger,\qquad
K'_{d,e}=G_{\rm out}K_{d,e}G_{\rm in}^\dagger,\qquad
M'_d=G_{\rm out}M_dG_{\rm out}^\dagger.
$$

Direct substitution and cyclicity of trace give
$\operatorname{Tr}(M'_dK'_{d,e}\rho'K_{d,e}'{}^\dagger)
=\operatorname{Tr}(M_dK_{d,e}\rho K_{d,e}^\dagger)$, term by term in
the actual records. The output state and the declared Bell target
transform by the same $G_{\rm out}$, so their fidelity also remains
unchanged. This proves covariance for arbitrary input states entangled
with a reference, rather than only the product-state examples below.
For a time-dependent frame $G(t)$, the propagator becomes
$G(t_{\rm out})U(t_{\rm out},t_{\rm in})G(t_{\rm in})^\dagger$ and
the Hamiltonian becomes $GHG^\dagger+i\dot G G^\dagger$.
In particular $G=D_j(\theta(t))$ changes the spin splitting to
$\Omega_j-\dot\theta$ while the instantaneous Raman phase becomes
$\phi_j+\theta$. Preparation and readout phases change with it.
Varying only $\phi_j$ while holding those physical operations fixed
describes a different experiment, rather than a basis change.

A unitary relabelling of unobserved Kraus records likewise leaves
$\sum_eK_{d,e}\rho K_{d,e}^\dagger$ unchanged. Coherent optical routing
instead uses a specified dilation, including its vacuum action. Changing
only an occupied-path phase while retaining a fixed vacuum phase can
change that physical dilation. It cannot be introduced as an arbitrary
Kraus gauge and then counted as measured device noise.

**Finite-dwell Raman kernel and the spin clock.** Let $\Omega_j(u)$ be
the local splitting, $t_R$ the Raman emission time and $T_m$ the time of
spin use. The collected Raman amplitude has the causal form

$$
\mathcal R_j(t_D,T_m)=
\int dt_R\,dt_{\rm in}\,
 G_{{\rm out},j}(t_D,t_R)
 B_j(t_R,t_{\rm in};\lambda)u_{{\rm in},j}(t_{\rm in})
 \exp\!\left[-i\int_{t_R}^{T_m}\Omega_j(u)\,du\right].
\tag{PR2}
$$

The incident and outgoing kernels retain the source phase, physical
carriers, directed propagation, collected port and detector mode.
$B_j$ is the full causal node response: it retains absorption and
emission times, cavity/excited-state dwell, and both coupling-leg phases.
Only in the flat instantaneous limit does it reduce to
$b_j(t_R)e^{i\phi_j(t_R)}\delta(t_R-t_{\rm in})$. Elastic and spectator
kernels, each lost optical mode and each detector/environment record
must be included alongside (PR2). Sequential kernels compose in their
actual physical order.

For static energy-matched carriers
$\omega_{\rm in}=\omega_R+\Omega$, the instantaneous carrier factors
obey the exact identity

$$
e^{-i\omega_{\rm in}t_R}
e^{-i\omega_R(t_D-t_R)}
e^{-i\Omega(T_m-t_R)}
=e^{-i\omega_Rt_D-i\Omega T_m}.
\tag{PR3}
$$

The $t_R$ coefficient is $-\omega_{\rm in}+\omega_R+\Omega=0$.
This proves why a Raman frequency shift without its spin evolution can
create a spurious early/late phase. A stationary finite-dwell transfer
function enforces the same total-energy balance while retaining its
actual response phase and envelope. Unequal or fluctuating splittings,
physical leg phases and unresolved photon records still leave residuals.
The [Stockill et al. primary supplement, phase-reference analysis](https://eprints.whiterose.ac.uk/id/eprint/119392/7/PRL_Supplemental.pdf)
explicitly retains excitation, Raman-photon and Larmor timing in the
remote-spin phase. A reported detector time permits only the corresponding
recorded spin-frame correction.

**Reciprocal retarded propagation.** In a reciprocal nondispersive guide
of length $L$ and group speed $v$, let $n(x,t)$ be a real index
fluctuation with the deterministic carrier phase removed. For a photon
launched at $t$,

$$
\varphi_\omega^+(t)=\frac\omega c\int_0^L n(x,t+x/v)\,dx,
\qquad
\varphi_\omega^-(t)=\frac\omega c\int_0^L n(x,t+(L-x)/v)\,dx.
\tag{PR4}
$$

Both directions acquire $e^{+i\varphi}$. Reversing propagation does
not complex-conjugate the dynamical phase. For frozen reciprocal noise,
$\varphi^+=\varphi^-$, so a round trip adds twice the phase. A
*difference between interfering traversals* can cancel it. With angular
noise frequency $\nu$, equal-time counterpropagation has distributed
filter
$Y_\omega(x,\nu)=(\omega/c)
[e^{-i\nu x/v}-e^{-i\nu(L-x)/v}]$. A localized fluctuation is therefore
sampled at two times separated by $(L-2x)/v$ and generally survives.
A spatially uniform $n(x,t)=n(t)$ is a special exact cancellation:
both integrals cover the same time interval. Stationarity or equal
marginal spectra alone does not identify either situation. Dispersive
media require the measured frequency-dependent propagation and its
cross spectrum.

**Four histories of the two-order route.** Initialize $PAB=100$, prepare
the independent order helper in plus, and select $P=0$ and helper
$X$ outcome $\epsilon\in\{+1,-1\}$. The memory coefficients are

$$
\begin{aligned}
u_{A,\epsilon}
 &=\frac12\left[
 \mathcal S_B^{\rm late}\circ\mathcal L_R^+
                       \circ\mathcal R_A^{\rm early}
 +\epsilon\mathcal R_A^{\rm late}\circ\mathcal L_{\rm in}^-
                       \circ\mathcal E_B^{\rm early}\right],\\
u_{B,\epsilon}
 &=\frac12\left[
 \mathcal R_B^{\rm late}\circ\mathcal L_{\rm in}^+
                       \circ\mathcal E_A^{\rm early}
 +\epsilon\mathcal S_A^{\rm late}\circ\mathcal L_R^-
                       \circ\mathcal R_B^{\rm early}\right].
\end{aligned}
\tag{PR5}
$$

$\mathcal E,\mathcal S,\mathcal R$ denote the active-elastic,
spectator and Raman kernels. Each term is its actual ordered integral,
with external input/output/helper paths and the applicable spin-evolution
intervals retained; the notation does not permit commutation of kernels.
The first term of $u_A$ flips early A and subsequently encounters
spectator B. Its second term is elastic early B followed by late Raman A.
The two $u_B$ terms give the other two histories. Each amplitude carries
its own retained frequency and time record. A spin density matrix is
formed only after their actual measurement overlaps have been included.

There is also an accepted-record guard before Raman phases are
considered. For fixed scalar node coefficients and otherwise global
route phases $\Phi_{AB},\Phi_{BA}$, direct expansion of the two ordered
node products gives the helper-minus coefficients

$$
\begin{aligned}
c_{10}&=\frac{e^{i\phi_A}b_A}{2}
 \left[e^{i\Phi_{AB}}s_B-e^{i\Phi_{BA}}a_B\right],\\
c_{01}&=\frac{e^{i\phi_B}b_B}{2}
 \left[e^{i\Phi_{AB}}a_A-e^{i\Phi_{BA}}s_A\right],\\
c_{P1}&=\frac{a_Aa_B}{2}
 \left[e^{i\Phi_{AB}}-e^{i\Phi_{BA}}\right],
\qquad s_j=a_j+b_j.
\end{aligned}
$$

The first two multiply $|0,10\rangle$ and $|0,01\rangle$.
The third multiplies $|1,00\rangle$: these are the elastic-elastic
histories in opposite routes. Unknown route phase invalidates calling the entire
minus flag a Bell output. Selecting $P=0$ rejects that component, but
the remaining Raman amplitudes must still satisfy the population and
phase conditions below.

In the restricted frozen, identical-node, compensated-spin-frame limit,
put $\mathcal R_j=b e^{i\rho_j}$, $\mathcal E=a$ and
$\mathcal S=s=a+b$, and match the external arms. Then

$$
\begin{aligned}
u_{A,\epsilon}&=\frac{b e^{i\rho_A}}2
 \left[s e^{i\varphi_R^+}
                  +\epsilon a e^{i\varphi_{\rm in}^-}\right],\\
u_{B,\epsilon}&=\frac{b e^{i\rho_B}}2
 \left[a e^{i\varphi_{\rm in}^+}
                  +\epsilon s e^{i\varphi_R^-}\right].
\end{aligned}
\tag{PR6}
$$

If the link is frozen and reciprocal at **each physical carrier**,
$\varphi_\omega^+=\varphi_\omega^-$, substitution gives
$u_{A,\epsilon}e^{-i\rho_A}
=\epsilon u_{B,\epsilon}e^{-i\rho_B}$. Thus each nonzero flag is a
Bell state after its known sign and relative spin-frame correction,
even when $\omega_R\ne\omega_{\rm in}$. The relative
$\rho_A-\rho_B$ remains. With $a\ne0$, time-dependent directional
differences can change the two magnitudes as well as their phase; one
scalar visibility does not then describe the complete instrument.
Factoring $\rho_j$ across early and late events requires the static
compensated limit justified by (PR2)--(PR3), rather than stationarity
alone.

**Ordinary shared paths and echo.** A coherent which-node route has
one-Raman amplitudes $b_AC_A/2$ and $\epsilon b_BC_B/2$ at its two
path-erasure outcomes. $C_j$ contains the full source-to-node phase,
Raman leg, outgoing Raman propagation and spin frame at a common time.
Its correction uses the same available pilot and detector records.
If an actual geometry places conversion before or after a shared segment,
and both alternatives traverse that segment in the same direction at
the same retarded times, its differential phase is
$\varphi_R-\varphi_{\rm in}$. Under the additional common
nondispersive-index model, this is proportional to
$\omega_R-\omega_{\rm in}$ rather than optical $\omega$.
Selective bypasses, conversion ports, group delays and external arms
must implement those histories. An inline Raman reflector which sends
the photon away at the first node supplies a which-node geometry, not
two completed opposite-order node calls.

**Ordinary double heralding needs temporal stability, not an absolute phase.**
An explicit stronger echo identity uses the spin-preserving single-click
operator $L_k=c_{A,k}n_A+s_kc_{B,k}n_B$, where
$n_j=|1\rangle\langle1|$ and the recorded detector sign is $s_k=\pm1$.
This is a cycling-emission instrument, not a compilation from one balanced
Raman SWAP call. Define the physical local pulse axis by
$X_j(\eta_j)|0\rangle=e^{i\eta_j}|1\rangle$ and
$X_j(\eta_j)|1\rangle=e^{-i\eta_j}|0\rangle$.
Multiplying the three operators gives

$$
\begin{aligned}
K&=L_2X_A(\eta_A)X_B(\eta_B)L_1\\
 &=s_2c_{A,1}c_{B,2}e^{-i(\eta_A-\eta_B)}
           |01\rangle\langle10|\\
 &\quad+s_1c_{B,1}c_{A,2}e^{i(\eta_A-\eta_B)}
           |10\rangle\langle01|.
\end{aligned}
\tag{PR7}
$$

Indeed $L_1$ annihilates $00$, while the intermediate flips take $11$
to $00$, which $L_2$ annihilates. On $10$, the first click contributes
$c_{A,1}$, the flips contribute $e^{-i(\eta_A-\eta_B)}$, and the second
click contributes $s_2c_{B,2}$; the other odd input gives the second term.
For a product source with local preparation phases $\chi_A,\chi_B$,
the relative output phase, apart from the recorded sign, is

$$
\arg\frac{c_{B,1}c_{A,2}}{c_{A,1}c_{B,2}}
+\chi_B-\chi_A+2\eta_A-2\eta_B.
$$

If each unknown complex node amplitude is unchanged between rounds,
both terms contain $c_Ac_B$. Static node/path offsets cancel, while
the local preparation and pulse axes remain explicit. With
$c_{j,k}=r_{j,k}e^{i\varphi_{j,k}}$, the residual optical phase is
$(\varphi_{A,2}-\varphi_{A,1})-(\varphi_{B,2}-\varphi_{B,1})$.
Its temporal filter is $1-e^{-i\nu T}$, rather than zero for arbitrary
drift. Unequal envelopes at different click times can also unbalance
the magnitudes. All actual click, missed-photon, relaxation and failed
round records must be included in the physical completion.

[Barrett and Kok, PRA **71**, 060310(R) (2005)](https://doi.org/10.1103/PhysRevA.71.060310)
([full source](https://arxiv.org/pdf/quant-ph/0408040)) provide the
ordinary physical architecture: two excitation/detection rounds, spin
flips and relaxation waits, with ideal matched-emitter success
$\eta^2/2$. This supplies a competitor when its cycling transitions,
two emitted/detected photons and complete wait/control costs are
available. Loss, unobserved mode distinction and memory decoherence
retain their actual consequences; those resources are not inferred
from the single-photon Raman interface.


**Scalar-phase closure and actual Raman-leg covariance.** In either
ordinary coefficient filter above, every interfering logical term has
the same fixed chronological node encounters. It therefore receives
the common factor $e^{i[\gamma_A(t_A)+\gamma_B(t_B)]}$. That factor
cancels from the accepted density operator even for phases fresh on
each attempt. Conditional on the remaining common-frame and helper-port
premises, the achievable yields remain $|b_Ab_B|^2/3$ for the photon
filter at $p=1/2$ and $9|b_Ab_B|^2/16$ for the local-ancilla filter.
This is not yield dominance over all switch flags: $1/3$ is below the
minus-only coefficient $1/2$, while $9/16$ prices extra local memories.

The two-order route instead compares
$\gamma_A(t)+\gamma_B(t+\tau)$ with
$\gamma_B(t)+\gamma_A(t+\tau)$. Their difference has filter
$(1-e^{-i\nu\tau})(\gamma_A-\gamma_B)$. Frozen values cancel;
general temporal variation does not. Scalar node noise therefore cannot
establish that only a switch prepares a known Bell pair, once these
ordinary two-node instruments are available.

For true Raman-leg phases, memory rotations commute with every photon
processor. Since $AB=00$ is unchanged by the input rotations,
$T_B(\phi_B)VT_A(\phi_A)|\psi\rangle_{PQ}|00\rangle_{AB}
=D_AD_B T_B(0)VT_A(0)|\psi\rangle_{PQ}|00\rangle_{AB}$.
The same covariance holds through the photon readouts and the fixed
diagonal local filter. Applying it to (RP2) at $p=1/2$ proves the exact
unnormalized kept vectors

$$
\begin{aligned}
|\chi_f\rangle&=\frac{b_Ab_B}{3}
 \left(e^{i\phi_B}|01\rangle+e^{i\phi_A}|10\rangle\right),\\
|\chi_g\rangle&=\frac{b_Ab_B}{3\sqrt2}
 \left(|00\rangle+e^{i(\phi_A+\phi_B)}|11\rangle\right).
\end{aligned}
\tag{PR8}
$$

Their norms are $2|b_Ab_B|^2/9$ and $|b_Ab_B|^2/9$.
A scalar $\gamma$ contributes only a global factor. The first flag
sees the Raman **difference**, while the second sees the **sum**.
Independent uniform leg phases destroy their known-frame Bell
coherences; common leg noise preserves $f$, and opposite leg noise
preserves $g$. Neither branch is universally reference-free. The frozen
switch's one-excitation flags likewise retain the Raman difference,
with further early/late sensitivity in the general kernel model.

This comparison can be strengthened to a complete spectral-state
identity. For matched routes and a common preserved spectral coordinate
$\nu$, let the two accepted node maps have arbitrary scalar
$a_j(\nu),b_j(\nu),\phi_j(\nu)$ in (PR1). The switched-minus coefficient
on $|10\rangle$ is
$b_A(s_B-a_B)e^{i\phi_A}/2=b_Ab_Be^{i\phi_A}/2$, and that on
$|01\rangle$ is
$b_B(a_A-s_A)e^{i\phi_B}/2=-b_Ab_Be^{i\phi_B}/2$.
Here $s_j=a_j+b_j$ pointwise and the elastic-elastic terms cancel.
Comparison with (PR8) gives

$$
Z_B|\chi_f(\nu)\rangle
 =\frac23|\psi_{S,-}(\nu)\rangle.
$$

This equality survives coherent integration of any input spectral
envelope with its retained photon/reference coordinate. Partial trace
and a common stochastic or pilot-record average therefore give
$\sigma_{f,\mathrm{corrected}}=4\sigma_{S,-}/9$.
For each nonzero outcome, the normalized reduced memory states have
identical Raman phase and spectral response, while their probabilities
have ratio $4/9$. This supplies a lower-yield ordinary comparator;
it does not assert that either state is a perfect Bell pair for arbitrary
$\nu$ dependence. It requires matched physical Raman codes, routes and
record kernels. Arbitrary noncommuting auxiliary kernels or unrelated
order-dependent propagation do not satisfy this scalar spectral proof.
In the same (RP1)--(RP2) family the $f$ flag alone has coefficient
$2p(1-p)/(1+p)^2$, with derivative $2(1-3p)/(1+p)^3$.
Thus $p=1/3$ gives $|b_Ab_B|^2/4$ and the same pointwise normalized
spectral/phase state after its known correction: half the matched
switch-minus probability, with rejected photon outcomes still charged.

For local-ancilla inputs, use
$(D_j^\dagger\otimes I)|\Phi^+\rangle_{jj'}
=(I\otimes D_{j'}^\dagger)|\Phi^+\rangle_{jj'}$.
Moving the input rotations to the otherwise untouched ancillas proves
that the **uncorrected** photon-outcome branch is

$$
\begin{aligned}
|v_m(\phi_A,\phi_B)\rangle
 &=G(\phi_A,\phi_B)|v_m(0,0)\rangle,\\
G&=(D_A\otimes D_{A'}^\dagger)
                 \otimes(D_B\otimes D_{B'}^\dagger).
\end{aligned}
\tag{PR9}
$$

After the known photon-outcome correction $C_m$ on A, the rotation on
the corrected zero-phase branch is
$(C_mD_AC_m^\dagger\otimes D_{A'}^\dagger)
\otimes(D_B\otimes D_{B'}^\dagger)$. The required fixed Pauli-Bell
projections and decodes do not all commute with those rotations.
Consequently Raman phase noise requires averaging this complete rotated
instrument, rather than granting the scalar yield $9/16$ as known-frame
Bell delivery. Supplying or estimating the missing frame restores the
stated construction with its actual cost.

The photon processor and helper also require their physical code.
Arbitrary passive mixing within a degenerate rail/polarization space
does not supply rotations between nondegenerate frequency bins.
Such a rotation needs an actual converter/modulator or equivalent
resource, with its pump phase, loss and duration. A common-path circuit
label does not supply that transformation.

**All-record noise law and causal pilots.** Let $\lambda$ be the full
physical noise history, $r$ the observed pilot record, $d$ the detector
record including its reported time, and $e$ any unobserved optical,
detector or bath record. With the source launch conditioned as declared,
the accepted unnormalized state is the completely positive map

$$
\sigma_{k,d,r}(\rho)=
\int p(d\lambda,r)\sum_e
 K_{k,d,e}[\lambda]\rho K_{k,d,e}[\lambda]^\dagger.
\tag{PR10}
$$

The $K$ are constructed from the actual ports, kernels, filters and
memories. Recorded spin-frame feedback applies a specified
$U_k(d,r)$ to (PR10). No-click, rejected-port, pilot-rejection,
filter-failure and reset flags complete the experiment; their weights
are not renormalized into success. For a history expansion, each cross
term retains the actual unobserved-record overlap and conditional
characteristic functional
$\mathbb E[e^{i(\Phi_h-\Phi_{h'})}\mid r]$.
This formulation remains valid for non-Gaussian stationary noise.
A PSD alone is insufficient: a static random sign $\pm\sigma$ and
a static Gaussian with variance $\sigma^2$ have identical covariance
and PSD, but unit-weight coherences $\cos\sigma$ and
$e^{-\sigma^2/2}$.

For linear phase functionals of a jointly Gaussian stationary vector
$x(t)$, use the two-sided cross spectrum with convention
$\mathbb E[x(t)x(t')^\mathsf T]
=\int S_x(\nu)e^{-i\nu(t-t')}d\nu/(2\pi)$.
If $Y$ is the history-difference filter, then

$$
V=\int_{-\infty}^{\infty}\frac{d\nu}{2\pi}
       Y(\nu)S_x(\nu)Y(\nu)^\dagger,
\qquad |\mu|=e^{-V/2}.
\tag{PR11}
$$

This follows by evaluating the variance of the linear functional and
then the Gaussian characteristic function. Shared-path, correlated-node
and spin/reference cross spectra must be retained. For distributed
guide noise the integrand includes the spatial double integral with
the retarded filters of (PR4). Independent-spectrum replacements can
destroy the very common-path cancellation being tested. If amplitudes
vary between histories, (PR10) remains necessary; (PR11) alone does not
describe the accepted state.

For a finite available Gaussian pilot vector $m$ with independent
measurement-noise covariance $N$, the Schur complement of its joint
Gaussian covariance gives the conditional residual phase variance

$$
V_{\rm res}=V_{\delta\delta}
 -V_{\delta m}(V_{mm}+N)^{-1}V_{m\delta}.
\tag{PR12}
$$

Only samples available before spin use belong to $m$. Waiting for later
samples adds storage noise and latency. For stationary pilots
$y=H*x+\eta$ and a specified causal linear correction $W$, the
residual spectrum is
$(Y-WH)S_x(Y-WH)^\dagger+WS_\eta W^\dagger$.
Pointwise unconstrained Wiener minimization generally gives an acausal
smoothing bound, rather than a realizable controller. The pilot model
must also include its backaction and quantum-window leakage or establish
their negligible contribution.

Equation (PR12) is a Gaussian **pilot-conditioned** covariance. Applying
it directly to an accepted branch additionally requires the actual
accepted-record law to remain jointly Gaussian, or acceptance weights
independent of the phase variables. A detuning-dependent herald can
reweight a Gaussian prior into a non-Gaussian accepted law. In that
case the full amplitudes and records in (PR10) determine the coherence.

**Time records, Bell qualification and renewal rate.** For an odd-parity
branch, write the pilot-conditioned unnormalized entries as
$P_A=\mathbb E[|u_A|^2\mid r]$,
$P_B=\mathbb E[|u_B|^2\mid r]$, and
$C=\mathbb E[u_Au_B^*\langle e_B|e_A\rangle\mid r]$,
with all actual unobserved records summed or integrated. Then

$$
\begin{aligned}
\sigma&=P_A|10\rangle\langle10|+P_B|01\rangle\langle01|
       +C|10\rangle\langle01|+C^*|01\rangle\langle10|,\\
F_{\rm best\ phase}&=\frac12+\frac{|C|}{P_A+P_B}.
\end{aligned}
\tag{PR13}
$$

The second line follows by maximizing the phase of a normalized Bell
target against the off-diagonal entry. The recorded spin correction
removes the conditional argument of $C$; $C=0$ supplies no phase
estimate. This is a Bell-state overlap, not a unitary balancing of
unequal populations. For balanced weights and Gaussian phase alone in
the actual accepted law,
$F=(1+e^{-V_{\rm res}/2})/2$, so $F_*>1/2$ requires
$V_{\rm res}\le-2\log(2F_*-1)$.

For Raman bands separated by $\Delta$, temporal intensity $w(t)$,
and detector response $h(\tau|t)$, keep
$w_\tau=\int h(\tau|t)w(t)dt$ and
$z_\tau=\int h(\tau|t)w(t)e^{i\Delta t}dt$ in the corresponding
diagonal and coherence entries. Ideal true-time detection can allow a
known spin correction; an unobserved frequency-sensitive detector record
can prevent it. A Gaussian timing-jitter multiplier requires the actual
pulse and response assumptions, rather than the carrier separation alone.

At one common delivered-fidelity threshold $F_*$, the unconditioned
qualified yield and sustained delivery rate are

$$
y_k=Q_k\sum_d\int dr\,
 \mathbf1\{F_{k,d,r}\ge F_*\}\operatorname{Tr}\sigma_{k,d,r},
\qquad
R_k=\frac{y_k}{\mathbb E[\text{complete cycle duration }k]}.
\tag{PR14}
$$

Here $Q_k$ is a separately declared independent launch probability only
when (PR10) is conditioned on that launch. If source probability or its
noise correlations are already inside the instrument, include them
there once and omit the extra factor. The rate is the renewal-reward
rate for regenerative cycles; stationary ergodic cycle records with
finite means give the same long-run reward/time ratio. It does not
assert a geometric first-success law for correlated attempts.

Complete duration includes unsuccessful source triggers, rejected photons
and filters, detector timeouts, pilot duty, feedforward/storage, reset and
success handoff. Signal photons, pilot photons, conversion pumps and
memory/controller energy are separately measured resource axes. Every
physically compatible comparator receives the same available pilot
record, causal correction class and qualification rule. An ordinary
common-path, echo or frequency-erasure construction enters only with
its actual ports and complete costs. These identities therefore require
a measured multi-port instrument comparison before either route can be
assigned a physical phase-reference advantage.

**Shelving can rephase a specified local optical fluctuation.**
[Uysal and Thompson, PRA **110**, 052606 (2024)](https://doi.org/10.1103/PhysRevA.110.052606)
([primary full text](https://arxiv.org/html/2406.06497)) propose an
ordinary correction using a shelving transition whose spectral diffusion
is correlated with the emitting transition. In its two-photon protocol,
put $\Delta\tau=\tau_2-\tau_1$; the accumulated phase changes as

$$
\begin{aligned}
\phi_T&=-(\omega_2-\omega_1)\Delta\tau
         -(\omega_{L,2}-\omega_{L,1})T,\\
\phi_{T,\rm rephased}
       &=-(\omega_{L,2}-\omega_{L,1})(T+\Delta\tau).
\end{aligned}
\tag{PR15}
$$

Holding the appropriate emitter for $|\Delta\tau|$ removes its
quasistatic unknown frequency error. Coherent optical/spin pulses,
a sufficiently long-lived correlated shelving level, timing and
storage are real resources; shelving decay and control errors remain.
The single-photon variant retains a static differential path phase,
whereas the two-photon variant cancels it under the stated stability
premises. These are the source's Hamiltonian-model statements.

For arbitrary local pulse phase $\chi_j(t)$, an excitation/de-excitation
pair contributes
$e^{-i\chi_j(t_a)}e^{i\chi_j(t_b)}
=e^{i[\chi_j(t_b)-\chi_j(t_a)]}$. Thus constant local offsets cancel
but temporal increments need a measured law and consistent local spin
axes. Extending the argument to a quantum bath additionally requires
matching the final conditional bath states up to scalar phase on the
actual bath input. Equal classical mean phases do not erase a which-node
bath record.

**A measured ordinary shared-spatial-link bus has a different native gate.**
[Daiss et al., Science **371**, 614–617 (2021)](https://doi.org/10.1126/science.abe3150)
([full paper and supplement](https://arxiv.org/pdf/2103.13095))
successively reflect a polarization ancilla from two Rb-cavity modules
linked by 60 m of fibre, then herald by polarization detection and
apply local feedforward. They approximate the photon with a weak
coherent pulse. Its cycling conditional-phase gate differs from balanced
SPRINT. In the ideal circuit a scalar phase on the shared spatial link
multiplies the full polarization state and cancels from the heralded
memory density matrix; this is an inference from the circuit, not a
measured immunity to every optical fluctuation. Differential polarization
phase, birefringence, local Raman-control axes, cavity locks and detuning
still matter. Global carrier-phase stabilization is therefore not an
inherent cost of every ordinary one-photon bus. A claimed saving must
measure the differential phase of the actual competing geometries.

**Measured phase-control ledger.**

**Quantum-dot Raman entanglement.**
[Stockill et al., PRL 119, 010503 (2017)](https://doi.org/10.1103/PhysRevLett.119.010503),
[full paper](https://arxiv.org/pdf/1702.03422), and its [full supplement](https://eprints.whiterose.ac.uk/id/eprint/119392/7/PRL_Supplemental.pdf),
pp.2–4 and Fig.S1, specifies a same-path 956 nm reference, approximately
1.5 million detected counts/s per QD, continuous feedback through a piezo
and electro-optic modulator, suppression through about 1.5 kHz, integrated
noise-power reduction 260 and residual phase FWHM 6.8 degrees. There is
no reported pilot duty interruption; launched pilot power is not supplied.
The supplement also attributes extra visibility loss
to local electrical detuning, estimated at 300–500 MHz FWHM, despite the
path lock. Its phase-data analysis rejects intervals failing resonance
or phase criteria; it does not provide an all-clock rate with free control.

Its actual measured spin/tomography phase is

    Δφ = ωR(t1A−t1B) + ωB(t2A−t2B)
         + ωLarmor(t3A−t3B).

The first and second delays refer to excitation and detected Raman
propagation; the third fixes the local spin-rotation frame. The source
requires t2A+t3A=t2B+t3B to identify the Rayleigh reference phase with
the entangled-state phase. This is a multi-frequency, time-referenced
interferometer, not two independent scalar Kraus phases.

**A faster drifting multi-emitter interface.**
[Ruskuc et al., Nature (2025)](https://doi.org/10.1038/s41586-024-08537-z),
[complete public Methods and supplement](https://arxiv.org/html/2402.16224v2),
Methods B and Extended Data Fig.5, measure a path-phase correlation time
of approximately 282 μs. They use a 10 μs, 987.9 nm heterodyne probe,
with AOM phase compensation on every entanglement attempt. A separate
validation uses a 30 μs delay and 984.5 nm probe. The residual phase
standard deviation is 0.037×2π rad. The published correlation measurement
and noise spectra do not specify launched pilot power or isolate the
entire stabilization fraction of the full reset cycle. Separately, optical
spectral diffusion has correlation time 1.42±0.04 ms. Their ordinary
protocol uses the detected photon time in dynamic rephasing and local
feedforward; a 500 ns acceptance window gives readout-error-corrected
remote-pair fidelity 0.723±0.007 at 3.1 Hz. These are different temporal noise components
with a demonstrated ordinary correction, not evidence for a native
partial-SWAP or Sagnac switch interface on those devices.

**Deployed-fibre reference control.**
[Stolk et al., arXiv:2408.12464v1](https://arxiv.org/html/2408.12464)
characterize the phase-control system used for an NV link with 25 km of
deployed fibre. Their local, fast and global loops have approximately
3 kHz, 220 kHz and 50 Hz bandwidths. Noise includes local mechanical
resonances at 100–1000 Hz, deployed-fibre vibration up to about 5 kHz,
and laser/pump phase noise to 50 kHz. Operation has 2.5 μs dark periods
every 10 μs, rather than continuous pilots during quantum windows.
Frequency-offset stabilization and signal fields also need a correction
from measured fibre-length variation. Attributing all fringe-contrast
loss to Gaussian phase noise gives an inferred 35.5 degrees RMS;
the long-term setpoint spread after the
length correction is below 4 degrees over ten hours. Those two numbers
describe different fluctuations and are not interchangeable. The source
explicitly observes that time-bin protocols need phase stability over
the bin separation, often below 500 ns, rather than the full experiment.
Supplement Table S1 gives stabilization powers about 5 μW at the local
photodiode and 30 nW at the midpoint, plus about 5 mW reference power
there; these have different optical boundaries and costs.

**A measured low-power reference alternative.**
[Jabir et al., Optica 12, 570–576 (2025)](https://doi.org/10.1364/OPTICA.540759),
[full primary paper](https://tsapps.nist.gov/publication/get_pdf.cfm?pub_id=959105),
demonstrate displacement-assisted photon-counting stabilization over a
120 km deployed loop. Its probe-window rate is about 650,000 detected
photons/s (83 fW at the receiver), with a 50% payload duty cycle and probe windows
10–150 μs depending on link configuration. Their out-of-loop PSD
integrated from 1 Hz to the measured upper bandwidth gives 140 mrad
RMS for the deployed loop and 110 mrad for a 100 km spool. This is a
phase-reference experiment, not a remote-memory Bell generator. Receiver
power is not launched pilot power or total pump/control energy. The paper
states that underlying numerical data are not publicly available, so
these integrated values cannot reconstruct an arbitrary alternative
route's filter-function integral.

These sources establish a real control cost and real residual noise.
They do not establish that the same noise acts identically on a proposed
SPRINT route, or that a reverse-order interferometer removes every
measured component. Published PSD plots, their integrated RMS values and
one correlation time do not specify the joint multi-port spectral matrix
needed to compare two different physical routes.

**What the exact checks and the remaining device test establish.**
The [phase-covariance replay](checks/architecture/verify_raman_phase_covariance.py)
checks 64 complete passive branch vectors, 64 norm identities and 128
complete six-qubit local-ancilla branches, including 2,048 coefficients.
The [reciprocal-port replay](checks/architecture/verify_raman_reciprocal_ports.py)
checks 72 complete directional branches, 48 static reciprocal Bell-frame
identities, three energy/time identities and three guards distinguishing
reverse propagation from phase conjugation. The
[route and double-herald replay](checks/architecture/verify_raman_route_and_echo_phases.py)
checks 2,000 full route-phase vectors, 900 unmatched-route nonzero-$P=1$
guards and 1,024 full double-herald vectors with a normalized spin source
and contractive click branches. These finite exact checks support the
displayed identities. General frame covariance, continuous causal kernels,
distributed-noise integrals and physical access are analytic premises;
device spectra, joint records, timing and energy are measured inputs.

A decisive device comparison fixes two actual nodes, both photon-code
ports, an independent order helper and the delivered spin-control frame.
Measure the joint signal/pilot process on each directed segment and each
code frequency; separate propagation, cavity/atom detuning, Raman-leg,
conversion-pump, helper and spin noise. Retain cross spectra and actual
event-time separations, testing Gaussian and stationary approximations
rather than transferring one platform's RMS phase into another's gate.
Apply the same available causal pilot and detection records in (PR10) to
the two-order route, which-node/common-path route, ordinary photon filter,
and admitted local-memory concentration or double-herald/rephasing
instrument. Preserve the retuned-cavity comparator whenever that control
is available. Compare (PR14) at the same fidelity threshold with every
rejected launch, pilot interval, filter, herald timeout, storage/reset
and hand-off charged.

The measured references above establish real control costs and useful
ordinary corrections. They do not supply a matching SPRINT two-order
router, its joint multi-port signal/pilot noise law, or a complete matched
rate/energy comparison. Scalar node phases already cancel in ordinary
serial filters; true Raman-leg and time-dependent propagation noise
require the full instrument. No device-backed native phase-reference
saving follows from these sources alone.

The drift premise itself needs measured support. For example,
[Kuhlmann et al.](https://arxiv.org/html/1301.6381v1) resolve charge and
spin noise and recover transform-limited optical lines above $50$ kHz;
their observations do not establish independent unknown balanced-Raman
coefficients on successive nanosecond trials.
[Chan et al.](https://arxiv.org/html/2205.12844v2) already use ordinary
time-bin scattering, spin echo and reflected-photon heralding to suppress
spectral-wandering error. Its cyclicity $14.7$ interface is distinct from
the balanced Lambda SWAP. A useful drift comparison must keep that
ordinary robustness and the actual local level/phase model.

The generic retained-bus commutator mechanism has prior literature:
[Castaños-Cervantes, Procopio and Bartley](https://arxiv.org/html/2509.02209v2)
study a flying atom coupled to two retained cavity fields. Their
single-excitation Bell/NOON endpoint is also compared by ordinary
calibrated unequal exchange pulses; it is not a strong native Raman
baseline or evidence of a new commutator mechanism here.

The surviving application question is an actual measured constraint on
phase references, local memory/control access or a different microscopic
instrument. Identify the accessible graph, the physical fluctuation and
its joint two-history dilation before claiming a saving. Calibrate and
reuse the ordinary protocols whenever the measured drift window permits;
include phase pilots, within-route stationarity, all photons, lost flags,
local preparation/filters, reset and complete clock durations. The bare
flat-node yield gap, a calibration-free minus flag and long-lived memory
alone no longer establish the needed comparison. No significant native
architecture benefit has been established.

<a id="nr-r11-rydberg-memory"></a>

### Stored-photon subtraction has a position-diagonal ordinary baseline

[Murray et al., PRL **120**, 113601 (2018)](https://doi.org/10.1103/PhysRevLett.120.113601)
give a retained-memory nonlinear task: store gate photons as Rydberg
spin waves, scatter a probe field, and retrieve the gate field with one
photon removed through spatial decoherence. Their
[primary paper, Eq. (2) and Appendices A/D](https://arxiv.org/pdf/1710.10047)
gives the fixed-$n_g$ configuration-space memory model

$$
\mathcal E_j(\rho)(x,y)=\Phi_j(x,y)\rho(x,y),\qquad
\mathcal E_j^{n_s}(\rho)(x,y)=\Phi_j(x,y)^{n_s}\rho(x,y).
\tag{RM1}
$$

Here $x,y$ denote configurations of all stored excitation positions.
The source approximation neglects gate--gate and probe--probe
interactions and evaluates the response to zeroth order in probe
bandwidth. The following deduction is exact for a common complete
position-preserving instrument; reduced-memory tomography alone does
not certify that two-use instrument.

**Keep the records before comparing order.** For a finite spatial
discretization, let every optical outcome and bath record have operators

$$
A_\alpha=\sum_x a_\alpha(x)|x\rangle\langle x|,\qquad
B_\beta=\sum_x b_\beta(x)|x\rangle\langle x|,
\quad \sum_\alpha|a_\alpha(x)|^2=
\sum_\beta|b_\beta(x)|^2=1.
\tag{RM2}
$$

Thus $\Phi_A(x,y)=\sum_\alpha a_\alpha(x)\overline{a_\alpha(y)}$
and likewise for B. These are positive Gram kernels of unit diagonal.
All operators in (RM2) are diagonal in the same configuration basis,
so $B_\beta A_\alpha=A_\alpha B_\beta$ for every complete record.
The ordinary serial channel has kernel $\Phi_A(x,y)\Phi_B(x,y)$.
The corresponding controlled-order record operator is

$$
W_{\alpha\beta}=|0\rangle\langle0|_Q\otimes B_\beta A_\alpha
 +|1\rangle\langle1|_Q\otimes A_\alpha B_\beta
=I_Q\otimes B_\beta A_\alpha.
\tag{RM3}
$$

This is an equality of subnormalized operators on arbitrary memory
inputs and inaccessible reference extensions. An independent $Q=+$
has zero minus probability, and its plus output equals ordinary order.
Keeping a subset of records, or making any common coherent measurement
of accessible probe outputs afterwards, preserves the equality.

The stronger retained-probe statement uses independent fresh
probe/output/bath factors $F_AE_A$ and $F_BE_B$. A common
population-preserving complete isometry has

$$
V_j:|x\rangle\longmapsto|x\rangle|\phi_j(x)\rangle_{F_jE_j},
\qquad \langle\phi_j(y)|\phi_j(x)\rangle=\Phi_j(x,y).
\tag{RM4}
$$

Either sequence maps $|x\rangle$ to
$|x\rangle|\phi_A(x)\rangle|\phi_B(x)\rangle$ on the same labeled
physical output factors. Equality therefore holds before any optical
record or bath is discarded, including cross-record coherences. A
common later retrieval, reset or readout channel preserves it. The
same proof applies to configuration direct integrals. Across different
excitation-number sectors it requires one common controlled isometry
over those sectors; (RM1) alone does not certify their relative phases
or an arbitrary optical Fock-state superposition.

**A shared probe is a different joint process.** Reduced Schur
commutation does not establish (RM4). As a small counterexample, take a
memory qubit M, one probe E initially in $|0\rangle$, and

$$
U_A=|0\rangle\langle0|_M\otimes I_E+
    |1\rangle\langle1|_M\otimes X_E,\qquad
U_B=|0\rangle\langle0|_M\otimes I_E+
    |1\rangle\langle1|_M\otimes Z_E.
\tag{RM5}
$$

With separate fresh probes their reduced memory channels are dephasing
and identity, which commute. With the same retained probe,
$U_BU_A|10\rangle=-|11\rangle$ while
$U_AU_B|10\rangle=|11\rangle$. This counterexample only identifies the
missing product-instrument premise; it supplies no Rydberg router or
memory-recovery advantage.

Physical timestamps and idle evolution also belong to that premise.
Different bath time bins cannot be equated by relabeling an inaccessible
output. Motion, excitation loss or transport, non-diagonal internal
rotations, shared retained bath modes, or retrieval/re-storage between
contacts can invalidate (RM4). They need their actual joint instrument.
Reversing a stationary probe direction can change which excitation
shields the others and hence $\Phi_j$; two such independent
position-diagonal instruments still obey (RM3). A coherent direction
superposition of one shared probe is a different operation. A diagonal
spatial phase imprint also commutes with (RM2); an escape requires
genuine mixing of configurations or another non-diagonal degree of
freedom. Any available ordinary basis rotation, echo or retrieval/pulse
control must then remain in the comparator.

**Use the actual subtraction and source ledger.** Two stored gate
photons and one probe require at least three incident photons before
storage, retrieval and detection losses. The experiment used weak
coherent fields, a $4\,\mu$s storage sequence, retrieval efficiencies
around $0.2$, and a fitted probe-scattering probability around $0.5$.
Finite scattering can decohere more than one excitation. Appendix D's
one-photon output-deficit statistic also counts failed storage and
ordinary retrieval loss. It therefore does not herald that the desired
memory manipulation occurred. Both architectures must compare the
same accepted optical output, probe dose, storage/readout time and all
rejected histories. Neither switched subtraction nor a measured
architecture gain follows from this model-level closure.

The exact replay uses six two-excitation configurations on four sites
and three nontrivial complex probe models. It compares the complete
cross-record/reference coefficients, reduced Gram kernels and coherent
record selections, and checks the shared-probe counterexample. It is
not a continuum fit or a certification of a laboratory two-use bath.

<a id="nr-r11-rydberg-exchange"></a>

### Coherent Rydberg exchange has an ordinary memory-source comparator

The following source and delivery comparators do not assert a
demonstrated Bell source or a native order advantage.

#### EX1. Physical operation and source boundary

[Thompson et al., Nature **542**, 206–209 (2017)](https://doi.org/10.1038/nature20823)
demonstrate exchange between a stored $99P$ excitation and a propagating
$100S$ polariton, a conditioned collision phase $0.48(3)\pi$, and
transverse rail exchange. Their
[primary paper](https://eapg.mit.edu/wp-content/uploads/2018/01/Symmetry_protected_collisions_nature20823.pdf)
reports weak coherent gate/signal means $0.15/0.25$ in the single-mode
experiment, baseline signal transmission $0.56$, and gate write/retrieve
probability $0.06$. The distinct two-rail run uses approximately one
input photon per pulse. Its reported $8.3(5)\%$ exchange probability is
the swapped coincidence count divided by the **total no-interaction
transmitted-pair count**; it is not an absolute incident-pair success
probability. Detector rail mixing is about $10\%$. The
[supplement, Secs. VIII.A, VIII.D and VIII.E](https://eapg.mit.edu/wp-content/uploads/2018/01/Symmetry_protected_collisions_nature20823_Supplemental.pdf)
reports $300$ ms sample preparation, $1000$ shots at $38\,\mu$s repetition,
and $7\,\mu$s trap-off periods. The measured two-rail observables are
intensity correlations, not the off-diagonal memory/rail coherence
required below. The two transverse modes are inside one gas, not two
remote memory nodes. Orthogonal collected photon ports do not alone
certify an orthogonal, independently addressable two-memory spin-wave
code within that gas.

[Khazali, Murray and Pohl, PRL **123**, 113605 (2019), Eqs. (4)–(6) and Fig. 4](https://arxiv.org/html/1903.12442v2)
derive the two-body output kernel
$T\psi(\mathbf r_\perp,\mathbf R_\perp)+
H\psi(-\mathbf r_\perp,\mathbf R_\perp)$.
This is a non-diagonal spatial-exchange target beyond the
[frozen-position Schur screen](#nr-r11-rydberg-memory).
Their three-rail, two-exchange controlled-phase network is a proposal,
not a demonstrated full gate. Its pulse advance and conditional
memory-location/retrieval delays are explicit; their proposed additional
gradient-echo synchronizer is an extra device, not free timing erasure.

[Šumarac et al., arXiv:2601.06345, Figs. 2–4 and Secs. .5–.6](https://arxiv.org/html/2601.06345v1)
experimentally observe exchange/hopping between $2$–$5$ separated
ensembles with optical density about $2$. The reported network tests
monitor population and transmission during weak-probe windows; they
do not demonstrate a coherent rail Bell source. State-selective remote
readout has source-defined combined preparation/detection fidelity
$47(5)\%$ with $30\,\mu$s readout, under a convention assigning zero to
a random guess, or $79(4)\%$ after $20$ repeated preparation/detection
cycles of $10\,\mu$s. These are not a single-shot healthy-memory herald.

#### EX2. A single-exchange eraser with its inaccessible record

Prepare a certified one-excitation memory in rail A and one propagating
photon in rail B. Define the two-dimensional memory code
$|A\rangle=|10\rangle$, $|B\rangle=|01\rangle$. In its successful sector,
the most general pure joint output with the desired exchange correlation
can be written

$$
|\Psi\rangle=
 |A\rangle_M|B\rangle_P|\tau\rangle_{KE}
 +|B\rangle_M|A\rangle_P|\eta\rangle_{KE}
 +|\mathrm{failure}\rangle.
\tag{EX1}
$$

Here K contains every accessible temporal, frequency and transverse
record, while E contains every unobserved bath record and residual
degree of freedom. An unresolved **memory** position that cannot factor
from the code must remain in the joint state or be charged as code
leakage. Projecting it by later retrieval is destructive and is not an
available memory herald before use. The orthogonal failure completion
includes photon loss and code leakage. This decomposition is a
hypothesis to test, not a consequence of rail intensity measurements or
of the protected phase of H alone. A code block below means the
mathematical block $P_{\mathrm{code}}\rho P_{\mathrm{code}}$; it does not
assume an available physical code projector.

Let

$$
a=\langle\tau|\tau\rangle,\qquad
b=\langle\eta|\eta\rangle,\qquad
c=\langle\eta|\tau\rangle.
\tag{EX2}
$$

Interfere the photon rails on a balanced splitter. For every resolved
accessible record k, keep **both** output flags $s=\pm1$ and track their
known memory Bell-sign frame. The conditional post-click joint amplitude
is

$$
\frac{|A\rangle|\tau_k\rangle+
 s|B\rangle|\eta_k\rangle}{\sqrt2}.
\tag{EX3}
$$

After the sign correction and summing all retained $k,s$, the
unnormalized memory state on this code is exactly

$$
\sigma=\begin{pmatrix}a&c\\c^*&b\end{pmatrix},
\qquad p_{\mathrm{code}}=a+b.
\tag{EX4}
$$

To prove (EX4), each flag's density matrix contributes half of the same
corrected outer product. Completeness of the k measurement preserves
$\langle\eta|\tau\rangle$. In particular, interfering accessible optical
rails does **not** erase inaccessible records. With a calibrated scalar
phase, the fidelity with the corresponding Bell state and the
concurrence on this single-excitation support are

$$
F_{\mathrm{Bell}}=\frac12+\frac{|c|}{a+b},\qquad
\mathcal C=\frac{2|c|}{a+b}.
\tag{EX5}
$$

Put passive amplitude attenuators $\alpha,\beta$ in photon rails B,A
**before** the splitter. Their rejected optical ports are explicit
failed flags. The resulting code state is

$$
\sigma'=\begin{pmatrix}
 \alpha^2a&\alpha\beta c\\
 \alpha\beta c^*&\beta^2b
\end{pmatrix}.
\tag{EX6}
$$

For $a,b>0$, choose
$m=\min(a,b)$, $\alpha^2=m/a$, $\beta^2=m/b$.
Both attenuators are contractions, and this gives

$$
p_{\mathrm{code}}=2m,\qquad
F_{\mathrm{Bell}}=\frac{1+\gamma}{2},\qquad
\gamma=\frac{|c|}{\sqrt{ab}}\in[0,1].
\tag{EX7}
$$

Both photon flags count; there is no additional $1/2$ measurement
penalty. For $\gamma=1$, this is an exact distributed-memory Bell source
with yield $2\min(a,b)$ before common source, storage, detector and
memory-survival factors. It uses one exchange collision and ordinary
optical interference, with no order helper or stationary ancilla. It is
a constructive ordinary comparator for a proposed exchange-created
memory-entanglement task, not a universal optimum over optical mode
processors.

Two complete models can have identical $a,b$ but different utility. Set
$|\tau\rangle=(3/5)|e_0\rangle$ and
$|\eta\rangle=(8/25)|e_0\rangle+(6/25)|e_1\rangle$.
Then $\gamma=4/5$; after balancing,
$p_{\mathrm{code}}=8/25$ and $F_{\mathrm{Bell}}=9/10$.
Replacing $|\eta\rangle$ by $(2/5)|e_1\rangle$ keeps all populations
$a=9/25$, $b=4/25$ but gives $\gamma=0$, hence
$F_{\mathrm{Bell}}=1/2$ and a separable memory mixture. Complete loss has
probability $12/25$ in both models. The exact checker replays these full
record states.

#### EX3. False heralds, complete cycles and the physical test to beat

A detector click alone does not establish that a retained excitation
survived. Initial gate-write failure, P decay, background photons and
unrecognized memory-code leakage can all give an accepted photon flag.
Let $\sigma'$ be the accepted code block and $\nu$ the accepted
memory-vacuum weight. Allow code-vacuum coherences: weak coherent
preparation does not automatically supply an orthogonal failure record.
With no further accepted leakage, the Bell fidelity is still

$$
F_{\mathrm{Bell}}=
\frac{m(1+\gamma)}{2m+\nu},\qquad
F_{\mathrm{Bell}}>\frac12\ \Longleftrightarrow\ 2m\gamma>\nu.
\tag{EX8}
$$

Vacuum/code cross terms have zero trace and zero Bell expectation, which
proves (EX8) without assuming that the full state is block diagonal.
Additional accepted leakage must also enter the denominator. This is a
fidelity threshold for this specific source protocol, not an
entanglement no-go: vacuum-plus-single-excitation states can remain
weakly entangled below it, and additional local filtering has its own
yield and controls. Do not substitute a postselected retrieved-gate
click for $\nu=0$ when the requested output is a retained memory state.

Suppose $a,b$ already include exchange survival conditioned on one
successfully prepared memory and one launched photon. Define $q_M$ as
the certified memory-preparation probability, $q_P$ as the single-photon
launch probability, $\eta_{\mathrm{opt}}$ and $\eta_d$ as common extra
optical transmission and detection, and $\eta_{\mathrm{hold}}$ as
retained-code survival until consumption. The useful ideal code yield
per complete attempt is

$$
Y_D=q_Mq_P\eta_{\mathrm{opt}}\eta_d\eta_{\mathrm{hold}}
\,2\min(a,b).
\tag{EX9}
$$

The cycle denominator includes unsuccessful preparation, launch and
herald attempts; both spatial detection flags; rejected attenuator
ports; guard windows; the actual trap sequence; retrieval/readout for
verification; and reset. The quoted $0.06$ single-mode write/retrieve
probability and two-rail $0.083$ normalized swap figure cannot be
multiplied to obtain an absolute Bell rate. A route proposal must
separately measure $q_M,a,b,c,\nu$ and the complete attempt duration on
the same geometry and source state.

The positive physical test is specific: interfere both transverse S
output rails **before** later microwave P-to-S retrieval, retain the
detector/time flag, and use phase-resolved interference of the two
retrieved memory rails to estimate c and vacuum leakage. Characterization
may destroy the memories on those trials. The conditional output on
other trials is usable only after the same output-code/false-herald
instrument has been validated. This is stronger than the existing rail
population test and is already an ordinary architecture. A switch must
beat this measured yield, Bell fidelity and complete-cycle frontier on
the same code; nonzero hopping or a $\pi/2$ optical phase alone is
insufficient.

#### EX4. Ordinary two-exchange delivery with all early and late flags

The [three-rail feedback network in Khazali et al., Fig. 4](https://arxiv.org/html/1903.12442v2)
has another direct workload: deliver a single retained excitation from
A to C. Route only the first exchanged photon output A into a later
input C. Let $T_1,H_1$ and $T_2,H_2$ be the full successful
transmission/exchange kernels, $\mathcal F$ the physical feedback/delay
isometry, and f the incident photon mode. At the three distinguishable
no-loss output records, the map is

$$
\begin{aligned}
|A;B\rangle f\ \longmapsto{}&
 |A\rangle_M|B,\mathrm{early}\rangle_P\,T_1f\\
&+|B\rangle_M|C,\mathrm{late}\rangle_P\,
 T_2\mathcal F H_1f\\
&+|C\rangle_M|B,\mathrm{late}\rangle_P\,
 H_2\mathcal F H_1f\\
&+|\mathrm{loss/leakage}\rangle.
\end{aligned}
\tag{EX10}
$$

Products mean compositions on the complete matched code, continuum and
record spaces, not products of reported intensities. Accepting the late-B
detector flag isolates the double-exchange word without an order
interferometer **within the displayed matched no-loss code**. A usable
transport herald also needs a bound on every accepted out-of-code,
background and rail-mixing contribution to late B. Its code probability
is

$$
p_{\mathrm{delivery}}=\|H_2\mathcal F H_1f\|^2,
\tag{EX11}
$$

reducing to $|h_1h_2|^2$ only for undistorted matched scalar modes. The
full probability completion is $\|T_1f\|^2+\|H_1f\|^2$ before first
loss, then

$$
\|T_2\mathcal F H_1f\|^2+
\|H_2\mathcal F H_1f\|^2\le\|H_1f\|^2,
\tag{EX12}
$$

plus rejected/loss flags. The retained excitation needs no final
retrieval for this transport task; retrieval may test it destructively.
This does not transfer an arbitrary vacuum/one-excitation qubit: without
an excitation, the photon leaves in the rejected early-B record, so the
herald projects on excitation presence.

Actual early-B and late-B wave packets must be distinguishable by
measured guards; tails can make a false late-B event. Every later loop,
if a closed loop replaces the open network, must be included as a
further record. For a polarization controlled-phase gate, the source
paper already explains additional polarization-conditioned spatial and
temporal correlations; their removal and the full basis-state
amplitudes/loss are extra conditions. No common complete A/B-channel
switch is certified by this network map.

#### EX5. Population transport does not lower-bound retained coherence

For any measured conditional site/record distribution $p(k,r\mid j)$,
the instrument

$$
L_{krj}=\sqrt{p(k,r\mid j)}\,|k\rangle\langle j|,
\qquad \sum_{k,r}p(k,r\mid j)=1,
\tag{EX13}
$$

with environment labels $(k,r,j)$ is completely positive and complete.
It produces the same site populations and classical readout records
on every tested localized input j, while destroying every inter-site
off-diagonal. It may be tensored with the demonstrated internal
microwave rotations. Thus separate internal S/P Ramsey coherence and
location-population transport do not by themselves lower-bound c in
(EX2). This is an explicit data-compatible alternative instrument, not
a claim that the actual coherent-exchange experiment is classical or
that all its observables are reproduced. The 2017 conditioned optical
phase is evidence of coherent collision dynamics, but does not
determine this distinct two-rail retained-memory Bell coherence.

#### EX6. A shared-pair survivor screen within the transverse CW model

The [continuous-wave exchange kernel of Khazali et al., Eq. (4)](https://arxiv.org/html/1903.12442v2)
has a second useful ordinary comparison. On the **same transverse S/P
pair-coordinate space retained by that CW model**, let F flip the
relative transverse coordinate $\mathbf r_\perp\mapsto-\mathbf r_\perp$,
leaving the transverse center coordinate $\mathbf R_\perp$ unchanged.
The accepted, no-emitted-bath kernel is
$K_j=T_j+H_jF$, where $T_j,H_j$ multiply wavefunctions. If both
coefficients are even under F, as the source's
$T_j(|\mathbf r_\perp|),H_j(|\mathbf r_\perp|)$ are, then they commute
with F. Since $F^2=I$, direct multiplication gives

$$
\begin{aligned}
K_BK_A
&=(T_BT_A+H_BH_A)+(T_BH_A+H_BT_A)F\\
&=K_AK_B.
\end{aligned}
\tag{EX14}
$$

This is a polynomial operator identity for arbitrary coefficient
values, including complex loss-dependent amplitudes, not a scalar
single-mode approximation. It holds on arbitrary normalizable
transverse joint-pair inputs and references **within that CW model**,
whenever these are bounded accepted contractions. It does not require
a fresh independent probe: the same S/P pair can be retained.
Conditional on that common no-emitted-bath code, an ideal order helper
again factors and its minus amplitude is zero. Any common later optical
eraser, filter or retrieval preserves the serial equality. The screen
distinguishes non-diagonal exchange from noncommuting contacts.

The premises are substantive. Physical propagation/delay between
contacts, site-dependent asymmetry, a different rail-exchange
permutation, shared extra bath, finite-bandwidth dynamics beyond the
CW kernel, or leakage that preserves an accepted photon can invalidate
this form. In particular, the three-rail feedback graph in (EX10)
moves the stationary excitation and changes the next collision
geometry. It is not two applications of one common F on a fixed pair
space, so this screen does not close that graph or any general exchange
network. The lost or leaked full instruments are not identified by this
survivor equality. A destructive two-photon coincidence is not a
nondestructive retained-memory code flag. A claimed native switch still
needs a physical router for those **same complete contacts**, all early
and late output records, and a measured source, memory and throughput
budget before any positive comparison.

The exact checker retains four complex optical/bath record models,
both balanced-splitter flags and the attenuator rejection completion.
It checks the memory density coefficients, vacuum/code coherences,
open-feedback probability completion, a location-dephasing alternative
instrument and the formal common-parity polynomial identity. It is an
exact algebra replay, not a certification of the experimental code,
finite-time kernel or herald instrument.

### Two-photon survivor scattering in a common continuum basis

Nonlinear scattering need not preserve each photon's frequency, so it
cannot generally be replaced by a passive single-particle matrix. There
is nevertheless a common-basis closure for a specified two-level-emitter
model. Use linearized waveguide dispersion, so propagation between
stations contributes only a scalar phase at fixed total energy. The two
order routes have the same propagation phase and matched output modes;
no additional relative-frequency phase or mode transformation is inserted.
Consider a ground-state Markov emitter with coupling rate
$\Gamma>0$ into the monitored forward direction, total radiative decay
$\kappa\ge\Gamma$, and resonance $\Omega$. Accept only the sector in which
both input photons remain in that direction and the emitter returns to
its ground state. Other radiative ports are lost and cannot feed back
into this or another station. There is no phonon dephasing or other
photon-preserving bath record. The resulting accepted field operator is
the single Kraus operator $K_{\Omega,\kappa}$ on the complete two-photon
wavepacket space, rather than a fitted single-mode phase.

The complete extended/bound Bethe basis originates in
[Shen and Fan](https://doi.org/10.1103/PhysRevA.76.062709).
The loss-dependent scattering amplitudes in
[Mahmoodian et al., supplementary Eqs. S2–S5](https://arxiv.org/html/1803.02428v3)
give the following spectral description. At fixed **physical** total
photon frequency $E$, the relative-coordinate basis is the spectral
basis of the self-adjoint half-line operator

$$
H_\Gamma=-\frac{d^2}{dy^2},\qquad
\psi'(0)=-\frac\Gamma2\psi(0),\qquad y\ge0.
\tag{10}
$$

Its continuum eigenfunctions are proportional to
$2u\cos(uy)-\Gamma\sin(uy)$, with eigenvalue $u^2\ge0$.
Its single bound eigenfunction is proportional to $e^{-\Gamma y/2}$,
with eigenvalue $-\Gamma^2/4$. Let $P_\Gamma(d\lambda)$ be its continuum
spectral measure and $P_{\Gamma,B}$ its bound-state projector. These
projectors depend on the monitored rate $\Gamma$, not the emitter
resonance or total radiative loss. Write

$$
x=E/2-\Omega,\qquad z=x+i\kappa/2.
$$

The scattering representation is

$$
\begin{aligned}
K_{\Omega,\kappa}(E)
&=\int_{[0,\infty)}
 \frac{(z-i\Gamma)^2-\lambda}{z^2-\lambda}\,
 P_\Gamma(d\lambda)
 +b_{\Omega,\kappa}(E)P_{\Gamma,B},\\
b_{\Omega,\kappa}(E)
&=\frac{x+i(\kappa-3\Gamma)/2}
 {x+i(\kappa+\Gamma)/2}.
\end{aligned}
\tag{11}
$$

To match the physical eigenvalues, the one-photon amplitude is
$t_\Omega(k)=1-i\Gamma/(k-\Omega+i\kappa/2)$.
The continuum fraction in (11), at $\lambda=u^2$, is exactly
$t_\Omega(E/2+u)t_\Omega(E/2-u)$.
Substitution of $\lambda=-\Gamma^2/4$ into that fraction and cancellation
gives the bound eigenvalue $b$ in (11), equal to the published bound-state
amplitude. The uncancelled fraction has an isolated $0/0$ on the bound
state when $x=0$ and $\kappa=\Gamma$; (11) defines it by its cancelled
continuous limit. Its denominator is nonzero for $\Gamma>0$. All
eigenvalues have modulus at most one when $\kappa\ge\Gamma$, so these
are bounded accepted contractions. At $\Gamma=0$ the interaction is
absent and commutation is immediate.

This also explains the shared generator: away from the removable bound
pole, (11) is the functional calculus

$$
K_{\Omega,\kappa}(E)
=I+(-2i\Gamma z-\Gamma^2)(z^2-H_\Gamma)^{-1},
\tag{12}
$$

with the bound value extended as above. Changing the carrier reference
multiplies the two-photon coordinate wavefunction by
$e^{2i\Omega x_c}$ and relabels the center-of-mass frequency. Once the
physical $E$ is fixed, it leaves the relative projectors in (11)
unchanged. Consequently two stations with the **same monitored coupling**
$\Gamma$, arbitrary resonances $\Omega_A,\Omega_B$, and even different
total radiative rates $\kappa_A,\kappa_B\ge\Gamma$ are diagonal in the
same complete spectral resolution:

$$
[K_{\Omega_A,\kappa_A}(E),K_{\Omega_B,\kappa_B}(E)]=0.
\tag{13}
$$

Both commute with total energy. Direct integration over $E$ proves the
operator identity on arbitrary normalizable two-photon inputs, including
coherences between different total energies and entanglement with a
reference. The isolated bound-pole case is covered by the same cancelled
spectral value or by continuity. This is a consequence of the published
scattering basis; it is not a SWITCH theorem asserted by that source.

Conditional on two-photon survival, each station has the one accepted
Kraus operator just described: its unmonitored radiative environment is
in vacuum. Thus the controlled accepted product is exactly

$$
|0\rangle\langle0|_C\otimes K_BK_A
+|1\rangle\langle1|_C\otimes K_AK_B
=I_C\otimes K_BK_A.
\tag{14}
$$

Its full accepted control–field–reference instrument equals ordinary
serial scattering. With independent initial $C=+$ and an $X$ readout,
the minus probability is zero and the plus probability is the ordinary
two-photon survival probability. That probability can depend on the
input wavepacket; the subnormalized identity (14) preserves it rather
than dividing it away. Any common later spectral selection or readout
retains the equality. The rejected one-photon/vacuum instruments have
not been identified, and all rejected launches still count. Destructive
two-photon coincidence detection verifies a terminal sampling event;
it does not supply a nondestructive success flag for a reusable gate.

For one isolated bidirectional emitter, the monitored rate is
$\Gamma=\Gamma_R$, while
$\kappa=\Gamma_R+\Gamma_L+\Gamma_{\rm other}$; treating backward output
as loss is the single-emitter port mapping used in that source. It does
not permit coherent reflection back through another emitter. Equal total
linewidth alone is insufficient when monitored couplings differ.

The [Nielsen et al. nonlinear processor](https://doi.org/10.1038/s41467-025-66205-w)
is a relevant primitive, using one quantum dot and programmable temporal
linear optics. Its reported effective nonlinear phase combines spectral
overlap with phase, rather than characterizing a single-mode-preserving
gate. The scattering screen above concerns the bare no-phonon accepted
two-forward-photon operators. It is **not** a proof for that whole
processor with its interleaved Mach–Zehnder operations, phonon dephasing,
or its coincidence-normalized efficiencies. In particular, pulse bandwidth
is an input choice, not by itself a second scattering operator.

### The complete relative-coordinate kernel

The same representation permits an explicit calculation when monitored
couplings differ. Write the accepted operator as
$K_{\Gamma,\Omega,\kappa}$ when its dependence on $\Gamma$ matters.
For $\operatorname{Im}z>0$, away from the removable bound pole, the
resolvent in (12) has kernel

$$
G_{\Gamma,z}(y,y')=
\frac{e^{iz|y-y'|}+r_{\Gamma,z}e^{iz(y+y')}}{2iz},
\qquad
r_{\Gamma,z}=\frac{z+i\Gamma/2}{z-i\Gamma/2}.
\tag{15}
$$

Both terms solve $(\partial_y^2+z^2)G=0$ away from $y=y'$ and
decay at infinity. The first derivative jumps by one at $y=y'$, and
$\partial_yG(0,y')/G(0,y')=iz(r-1)/(r+1)=-\Gamma/2$.
These properties give the Green function of $z^2-H_\Gamma$.
Multiplying by $-2i\Gamma z-\Gamma^2$ cancels the apparent bound pole
and gives the regular accepted field operator

$$
\begin{aligned}
(K_{\Gamma,\Omega,\kappa}(E)f)(y)
={}&f(y)-\Gamma\!\left(1-\frac{i\Gamma}{2z}\right)
 \int_0^\infty e^{iz|y-y'|}f(y')\,dy'\\
&-\Gamma\!\left(1+\frac{i\Gamma}{2z}\right)e^{izy}
 \int_0^\infty e^{izy'}f(y')\,dy'.
\end{aligned}
\tag{16}
$$

Here $z\ne0$ since $\kappa\ge\Gamma>0$. Equation (16) therefore
also supplies the continuous value at the cancelled pole. It is the
full two-photon kernel, including the bound contribution, rather than
a product of single-photon phases.

For $f_\beta(y)=e^{-\beta y}$ with $\operatorname{Re}\beta>0$,
the two integrals can be evaluated without a spectral cutoff:

$$
\begin{aligned}
K(E)f_\beta&=A_\beta f_\beta+B_\beta e^{izy},\\
A_\beta&=1+\frac{-2i\Gamma z-\Gamma^2}{\beta^2+z^2},
&B_\beta&=-\frac{\Gamma(2\beta-\Gamma)}{\beta^2+z^2}.
\end{aligned}
\tag{17}
$$

Indeed the first integral in (16) is
$e^{izy}/(\beta+iz)+2iz e^{-\beta y}/(\beta^2+z^2)$ and the
second is $1/(\beta-iz)$. Substitution proves (17). For
$\beta=\Gamma/2$, use the cancelled expression
$A_\beta=(z-3i\Gamma/2)/(z+i\Gamma/2)$ and $B_\beta=0$;
other coincident-exponent cases use the corresponding continuous,
polynomial-times-exponential limit. Norms and matrix elements of finite
exponential sums follow from
$\langle f_\beta,f_\eta\rangle=(\bar\beta+\eta)^{-1}$.
Equations (15)–(17) are direct consequences of the cited scattering
representation, not identities attributed to an experimental SWITCH.

### Unequal couplings: a real relative-mode gate and its serial endpoint

Take lossless forward scattering, $\kappa_j=\Gamma_j$, at a common
resonance $\Omega$. At $E=2\Omega$, the continuum eigenvalue in
(11) is one and the bound eigenvalue is minus one. Thus

$$
K_j=I-2|b_j\rangle\langle b_j|,
\qquad b_j(y)=\sqrt{\Gamma_j}e^{-\Gamma_j y/2}.
\tag{18}
$$

For unequal positive rates, define a real orthonormal relative-mode code

$$
\begin{gathered}
c=\langle b_A,b_B\rangle=
 \frac{2\sqrt{\Gamma_A\Gamma_B}}{\Gamma_A+\Gamma_B},
\qquad d=\sqrt{1-c^2},\\
e_0=b_A,\qquad e_1=(b_B-cb_A)/d,\qquad
J=|e_1\rangle\langle e_0|-|e_0\rangle\langle e_1|.
\end{gathered}
\tag{19}
$$

$J$ is a unitary quarter turn on this two-dimensional code. Multiplying
the two reflections in its basis gives

$$
\begin{aligned}
K_BK_A&=(2c^2-1)I+2cdJ,&
K_AK_B&=(2c^2-1)I-2cdJ,\\
M_+&=(2c^2-1)I,&M_-&=2cdJ,
\end{aligned}
\qquad M_\pm=(K_BK_A\pm K_AK_B)/2.
\tag{20}
$$

These restrictions are on the code; $M_-$ vanishes on its orthogonal
complement. Unequal monitored rates therefore genuinely evade (13).
The minus outcome applies a heralded unitary with code-independent
success $4c^2(1-c^2)$. Its maximum is one at $c^2=1/2$, or
$\Gamma_B/\Gamma_A=3\pm2\sqrt2$. At exactly that endpoint,
however, $K_BK_A=J$ and $K_AK_B=-J$: ordinary serial scattering
already performs the target gate deterministically. The relative sign
is observable in the controller without improving this payload gate.

This code is one qubit encoded in **two-photon relative modes**. It is
not two independently encoded rail qubits. Its input modes are already
correlated; an arbitrary coherent encoder into them has not been
demonstrated in the named device. A fixed desired spectral state also
cannot be credited as an advantage over an ordinary source allowed to
prepare that same state freely.

### Normalizable pulses and exact correct-output mass

A fixed total-energy delta state is not a physical pulse. For any
normalized $G\in L^2(\mathbb R,dE)$, use the reference-entangled input
and target

$$
\begin{aligned}
|\Psi_G\rangle&=\int dE\,G(E)|E\rangle
 \otimes\frac{e_0|0\rangle_R+e_1|1\rangle_R}{\sqrt2},\\
|\Psi_{G,J}\rangle&=(I_{E,R}\otimes J)|\Psi_G\rangle.
\end{aligned}
\tag{21}
$$

The actual minus output has $M_-(E)$ in each energy fiber and can leave
the code. Its subnormalized acceptance and target-test probabilities are

$$
\begin{aligned}
p_-&=\int dE\,|G(E)|^2\,
 \frac{\|M_-(E)e_0\|^2+\|M_-(E)e_1\|^2}{2},\\
q_-&=\left|\int dE\,|G(E)|^2\,
 \frac{\langle e_1|M_-(E)e_0\rangle
       -\langle e_0|M_-(E)e_1\rangle}{2}\right|^2.
\end{aligned}
\tag{22}
$$

The square is outside the integral because the target retains coherent
total-energy amplitudes. $q_-/p_-$ is conditional fidelity for the
specified reference input; it is not a normalized channel fidelity when
the success effect depends on the code input.

There is an exact ordinary comparison for every such $G$. The kernel
(16) is complex symmetric under transpose, defined with respect to
complex conjugation in the relative-coordinate representation. Hence
$(K_BK_A)^T=K_AK_B$. Compressing to the real basis $e_0,e_1$
preserves this transpose, while $J^T=-J$. Consequently, pointwise in $E$,

$$
\frac12\operatorname{Tr}_{\rm code}(J^\dagger K_AK_B)
=-\frac12\operatorname{Tr}_{\rm code}(J^\dagger K_BK_A),
\qquad
\frac12\operatorname{Tr}_{\rm code}(J^\dagger M_-)
=\frac12\operatorname{Tr}_{\rm code}(J^\dagger K_BK_A).
\tag{23}
$$

Transposing the product reverses its order and transposing $J^\dagger$
changes its sign; cyclicity of this finite code trace proves both
equalities. No physical transposition operation is assumed. Integrating
the complex amplitudes in (23) proves
$q_-=q_{BA}$ for the same target (21), where $q_{BA}$ is ordinary
serial processing's target-test probability. The flag can reject
unwanted output mass and raise conditional quality; it does not increase
correct-output mass for this benchmark. This statement does not cover
every spectral target or arbitrary gate input.

The finite-pulse gate approaches (20) continuously. The bounded spectral
values (11), with the cancelled bound value, are operator-norm continuous
near $E=2\Omega$. Their products and code restrictions therefore are
continuous. For normalized pulse densities concentrating at that energy,
dominated convergence gives $p_-\to4c^2d^2$,
$q_-\to4c^2d^2$ and a success effect tending to $4c^2d^2I$
uniformly on the code. Thus normalizable pulses can approximate the
relative-mode gate, including the serial endpoint. Narrowing the total
energy requires longer coherent pulse and routing/storage windows; this
limit makes no fixed-time accuracy claim. No numerical continuum
truncation is needed for these conclusions.

### A photon-preserving flag, its yield, and the logical-sector test

Terminal coincidence detection consumes both photons. A more restricted
passive flag can retain them. Suppose a valid **whole-pair path encoding**
has already produced
$(|20\rangle_{ab}\otimes v_0+|02\rangle_{ab}\otimes v_1)/\sqrt2$,
where $v_0=K_BK_A\psi$, $v_1=K_AK_B\psi$ and the internal pair
state is symmetric. On a balanced beam splitter,

$$
\begin{aligned}
|20\rangle_{ab}&\longmapsto
 \tfrac12|20\rangle_{cd}+\tfrac1{\sqrt2}|11\rangle_{cd}
 +\tfrac12|02\rangle_{cd},\\
|02\rangle_{ab}&\longmapsto
 \tfrac12|20\rangle_{cd}-\tfrac1{\sqrt2}|11\rangle_{cd}
 +\tfrac12|02\rangle_{cd}.
\end{aligned}
\tag{24}
$$

If exactly two photons were launched, none were lost and a detector
ideally resolves vacuum in discarded port $d$, its no-click event leaves
both photons in $c$ with amplitude
$(v_0+v_1)/(2\sqrt2)=M_+\psi/\sqrt2$. A known relative
pair-path phase $\pi$, obtainable as $\pi/2$ per photon, selects
$M_-/\sqrt2$ instead. The useful yield is **half** the abstract
control-outcome yield. For the minus benchmark (22), its acceptance and
target masses are $p_-/2,q_-/2$. The all-attempt score assigning
$+1$ to a target-test pass, $-1$ to a failed accepted output and zero
to rejection is then $q_--p_-/2$. At the narrow-pulse unit-yield
endpoint it tends to $1/2$, whereas serial processing's score
$2q_{BA}-1$ tends to one. By continuity, this passive readout loses
to serial for sufficiently narrow normalizable pulses at that endpoint.

Unmonitored loss or detector inefficiency can instead make no-click
accept one or zero retained photons. A valid-pair flag then needs an
additional number check or independently flagged erasure interface,
with its resources charged. Hong–Ou–Mandel preparation supplies the
assumed pair-path state only for suitable indistinguishable symmetric
inputs; it is not an arbitrary unknown two-qubit encoder. A separate
order ancilla may be measured destructively while preserving the target
photons, but its coupling, routing and readout are additional hardware.

There is also an immediate dual-rail obstruction for the bare emitter
model. If only logical $|11\rangle$ sends two photons through the
nonlinear arm and the other basis states send zero or one, the vacuum
block is identity and the one-photon blocks are commuting multiplication
operators $t_j(k)$. The minus map annihilates the $00,01,10$ logical
components even when $\Gamma_A\ne\Gamma_B$. It is therefore a
filter, not a heralded controlled-phase gate on an arbitrary logical
input. The plus map must balance all logical amplitudes and their full
spectral shapes. Added mode mixing can change this sector argument and
requires its own full-code calculation.

### Known linear dressing and an exact two-reuse ordinary baseline

Unequal rates with equal monitored fraction have a further exact
comparison. For $a>0$, real $\delta$, define a normalized one-photon
frequency transformation and its symmetric two-photon action

$$
\begin{aligned}
(L_{a,\delta}f)(k)&=a^{-1/2}f((k-\delta)/a),\\
(\mathcal L\psi)(E,u)&=a^{-1}\psi((E-2\delta)/a,u/a),
\qquad u=(k_1-k_2)/2.
\end{aligned}
\tag{25}
$$

Both are unitary with the displayed Jacobians. If
$\Gamma_B=a\Gamma_A$, $\kappa_B=a\kappa_A$ and
$\Omega_B=a\Omega_A+\delta$, then

$$
K_B=\mathcal L K_A\mathcal L^\dagger
\tag{26}
$$

on the complete normalizable two-photon space. To prove this, put
$E'=(E-2\delta)/a$, so $z_B(E)=az_A(E')$.
The relative-coordinate unitary $T_af(y)=\sqrt a f(ay)$ maps
the Robin boundary condition for $\Gamma_A$ to that for
$a\Gamma_A$, and
$H_{a\Gamma_A}T_a=a^2T_aH_{\Gamma_A}$.
Its continuum spectral values scale by $a^2$, and it maps the
normalized bound vector to $b_{a\Gamma_A}$. Each numerator and
denominator in (11) scales by $a^2$, and the bound amplitude has
the same invariance. Together with the total-energy Jacobian in (25)
this proves (26) on both spectral sectors and the full direct integral.
The one-photon amplitude has the same covariance and the vacuum is
fixed, so the identity also respects the zero/one/two-photon sectors.

More generally let a reusable accepted single-Kraus primitive be $K$
and a second module be $B=PKQ$, for executable known unitary field
operations $P,Q$. Two chronological calls to $K$ satisfy

$$
\begin{aligned}
&\operatorname{diag}_C(P,I)(I_C\otimes K)
 \operatorname{diag}_C(Q,P)(I_C\otimes K)
 \operatorname{diag}_C(I,Q)\\
&\hspace{25mm}=\operatorname{diag}_C(PKQK,KPKQ)
 =\operatorname{diag}_C(BK,KB).
\end{aligned}
\tag{27}
$$

Multiplication of the two control blocks proves the identity. It needs
neither knowledge nor an inverse of $K$. In (26), take
$P=\mathcal L$, $Q=\mathcal L^\dagger$. For every
control–field input and inaccessible reference, (27) reproduces the
entire subnormalized accepted switched output, including its probability,
any final control basis, and later decoder or spectral filter. Known
interleaved linear dressing can therefore create noncommutativity
without creating a capability gap against this available reuse circuit.

This is an accepted single-Kraus identity, not a simulator of arbitrary
successful phonon records or all rejected instruments. Its two primitive
visit opportunities are charged even on rejected runs; an occupied-pass
or adaptive-shutdown convention needs its own accounting. Coherent
frequency compression/expansion of an unknown output waveform is a
physical transformation, not merely preparation of a narrower input
laser pulse. A time lens, inverse conversion, controlled known optics,
return loop, emitter recovery and their losses, bandwidth and latency
must be available and priced. The nonlinear output's spectral tails also
belong in a finite-band approximation. For two contractions $M,N$,
$\|\operatorname{Ad}_M-\operatorname{Ad}_N\|_\diamond
\le(\|M\|+\|N\|)\|M-N\|$ follows by expanding their
difference into two left/right multiplication maps; it bounds such a
uniform operator approximation before any postselection normalization.
No such device approximation is certified here. Different monitored
fractions or genuinely different nonlinear primitives need not satisfy
(26) or an executable dressing assumption.

### Vacuum routing and the cost of a third scheduled window

Even without known dressing, the specified vacuum-stable survivor model
admits a useful ordinary scheduling comparison. Use chronological
windows $A_{\rm early},B_{\rm middle},A_{\rm late}$.
In one coherent path arm the pair visits early $A$ and then $B$;
in the other it visits $B$ and then late $A$. An unused $A$ window
receives vacuum. Delay and recombine the output modes and phases.

On the two-survivor sector, each occupied station returns to ground
and every unmonitored radiative environment is in the same vacuum.
The unused window acts trivially on vacuum. The two surviving branch
operators are therefore precisely $K_BK_A$ and $K_AK_B$, and the
resulting controlled accepted instrument is the desired one for every
input/reference. There is no additional occupied nonlinear traversal,
dummy photon pair or extra survival factor. The construction requires
stationarity between the two $A$ windows and matched timing/modes.

It uses **three scheduled windows**, rather than two abstract calls,
and may require longer storage and more routing. Each arm still has
one occupied $A$ and one occupied $B$ traversal. This is not a
two-query definite-order comb simulation. The same coherent pair-path
access and stable vacuum interface must be physically available, and
all optical losses and delays remain charged. Photon-preserving bath
records, residual station excitation, resolved arrival-time records or
shared feedback can invalidate its survivor premise. Neither these
loops nor (27)'s full frequency controls are inferred from the
one-emitter Nielsen experiment.

### Photon-preserving Markov records: the complete routed instrument

Adding emitter dephasing need not remove the photons, so a surviving
pair alone no longer selects a single bath Kraus operator. A tractable
optical density-matrix model is supplied by
[Bundgaard-Nielsen et al.](https://arxiv.org/html/2604.18036v2),
including one- and two-photon Fock-pulse scattering, emitter pure
dephasing and off-chip radiative loss. The following vacuum-reservoir
dilation and routed-instrument comparison specify additional physical
assumptions; they are not inferred from a reduced master equation or
asserted as an experimental implementation by that source.

Retain the guided optical field in the payload and let $H_{\rm QED}$
include its coupling to a two-level emitter. Couple independent vacuum
white reservoirs through
$L_\phi=\sqrt{\gamma_\phi}\,n_e$, $n_e=|e\rangle\langle e|$,
and radiative loss operators
$L_\ell=\sqrt{\kappa_\ell}\,\sigma_-$.
This convention gives a bare coherence decay $\gamma_\phi/2$ from
$\gamma_\phi\mathcal D[n_e]$.
Put $H_{\rm eff}=H_{\rm QED}-(i/2)\sum_cL_c^\dagger L_c$.
The complete reservoir record
$r=((c_1,t_1),\ldots,(c_m,t_m))$, $t_1<\cdots<t_m$,
has optical Kraus operator

$$
K_r=\langle g|U_{\rm eff}(T,t_m)L_{c_m}
 U_{\rm eff}(t_m,t_{m-1})\cdots L_{c_1}
 U_{\rm eff}(t_1,0)|g\rangle.
\tag{28}
$$

Summing/integrating all channel-labelled absolute-time Fock records,
including the empty record, gives the full optical map after the emitter
has returned to ground; the empty amplitude is
$K_\varnothing=\langle g|U_{\rm eff}(T,0)|g\rangle$.
At finite $T$, any residual excited-state
output must also be retained to complete the instrument. Dephasing
records preserve optical photon number; radiative-loss records do not.
For input photon number at most two, the full output therefore includes
zero-, one- and two-photon sectors. No surviving-pair normalization is
performed.

For a physical two-history comparison impose all of the following
interface conditions. The stations have independent reservoirs and a
stationary, inactive ground/vacuum state. The early and late active
reservoir supports at each station are disjoint. Every nonempty record
then distinguishes the two histories; the empty reservoir state is
common with the **same phase**. The routed optical outputs and known
propagation phases are matched. Moreover, an independent helper must
coherently route the **whole payload**, remain readable even if payload
photons are lost, and be available and charged in both circuits.
This last premise is necessary for a tensor-control instrument on all
zero/one/two-photon sectors: payload-only path encoding disappears on
vacuum, and a beam splitter acting on $|2\rangle$ creates split-pair
terms rather than an ideal whole-pair history router. Without that
interface, restrict the physical statement to a specified two-survivor
sector and separately define its loss completion.

Let $\Phi_A,\Phi_B$ be the complete optical channels,
$M=\Phi_B\circ\Phi_A$, $N=\Phi_A\circ\Phi_B$, and let
$A_\varnothing,B_\varnothing$ be their empty-record amplitudes.
Assume in addition

$$
K=B_\varnothing A_\varnothing
 =A_\varnothing B_\varnothing.
\tag{29}
$$

For stationary asymptotic no-record Markov scattering, the dephasing
term simply adds $\gamma_\phi$ to the imaginary excited-state
broadening: $\kappa_{\rm eff}=\kappa_{\rm rad}+\gamma_\phi$.
Thus (29) follows in the equal-monitored-$\Gamma$ model from (11)–(13),
also on vacuum and the commuting one-photon frequency blocks. This
observation does **not** show that an arbitrary finite gate/reset or
windowed approximation retains (29). An exactly gated interface must
verify both its empty-product equality and its record-support premise.

Only the empty record contributes to the cross-history map. For
initial independent helper $|+\rangle$, the physical routed output
is consequently

$$
\frac12
\begin{pmatrix}
 M(\rho)&K\rho K^\dagger\\
 K\rho K^\dagger&N(\rho)
\end{pmatrix}_C,
\qquad
\mathcal I_\pm=
 \frac{M+N\pm2\operatorname{Ad}_K}{4}.
\tag{30}
$$

The latter are the subnormalized maps after an $X$ measurement.
All maps may be tensored with an arbitrary reference identity. Positivity
also follows directly: $M-\operatorname{Ad}_K$ and
$N-\operatorname{Ad}_K$ are sums over nonempty bath records.
These are full optical instruments, not just control probabilities.

### An ordinary temporal filter matches the measured instrument

Run fixed order $AB$ in two coherent arms at different times:
$A_1B_2$ and $A_2B_3$. Under the same record assumptions their
diagonal optical maps are $M,M$, and their sole common bath record
is the empty product $K$. The corresponding $X$ maps are
$\mathcal J_{AB,\pm}=(M\pm\operatorname{Ad}_K)/2$.
Fixed order $BA$ similarly gives
$\mathcal J_{BA,\pm}=(N\pm\operatorname{Ad}_K)/2$.
A fair independent classical choice between these two ordinary
experiments therefore gives

$$
\frac{\mathcal J_{AB,\pm}+\mathcal J_{BA,\pm}}2
=\mathcal I_\pm.
\tag{31}
$$

This proves equality on every target/reference input, including the
entire $X$-labelled density matrix, losses, input-dependent survival
and every later spectral or logical measurement. Composing a common
two-survivor projection preserves it; detecting the two photons still
consumes them. The ordinary party may retain its classical order choice.
Its unmeasured control–target state need not equal (30): its diagonal
control blocks are equal rather than $M,N$. Equation (31) therefore
screens this measured order filter, not arbitrary coherent processing
of the unmeasured helper.

The switch histories $A_1B_2,B_1A_2$ use two windows; the ordinary
filters use three. Both have four possible spacetime visits and two
occupied station traversals per arm. The extra delay, helper coherence,
whole-payload routing, reset, mode matching and losses must be charged.
This is an ordinary physical timing construction, not a hard-two-query
comb theorem. For independent calibrated control dephasing, use the
nonnegative visibility convention $0\le v_S,v_F\le1$. The
interference term in (30) is
$2v_S\operatorname{Ad}_K$. The ordinary filter matches it only if
its visibility $v_F=v_S$, or if $v_F\ge v_S$ and extra deliberate
dephasing reduces it. Equal visibility over an extra window is not
automatic. Record-dependent or payload-dependent helper noise requires
its own instrument.

There is an exact mismatch formula when (29) fails. Set
$D_0=B_\varnothing A_\varnothing$ and
$D_1=A_\varnothing B_\varnothing$, keeping disjoint nonempty
records and the same diagonal maps $M,N$. The switch cross terms are
$D_0(\cdot)D_1^\dagger$ and $D_1(\cdot)D_0^\dagger$.
The randomized ordinary filters instead have
$\operatorname{Ad}_{D_0}+\operatorname{Ad}_{D_1}$ as their
interference sum. Hence, for their full classical-$X$-flag maps
$\mathcal F,\mathcal I$,

$$
\mathcal F_+-\mathcal I_+
=\tfrac14\operatorname{Ad}_{D_0-D_1},\qquad
\mathcal F_--\mathcal I_-
=-\tfrac14\operatorname{Ad}_{D_0-D_1},\qquad
\|\mathcal F-\mathcal I\|_\diamond
=\tfrac12\|D_0-D_1\|^2.
\tag{32}
$$

The first two identities follow by expanding
$(D_0-D_1)\rho(D_0-D_1)^\dagger$. The two flag blocks have
opposite copies of the same CP map, whose diamond norm is
$\|D_0-D_1\|^2$; their trace norms add, proving the last
identity. Equal visibility $0\le v\le1$ multiplies the discrepancy by $v$.
This is a quadratic approximation bound, not an exclusion of a useful
noncommuting minus output: that output may be precisely the mass in
(32). An approximate comparison must retain it.

### Uniform tail errors and the finite-window qualification

Gaussian inputs and spontaneous-emission tails are not compactly
supported. A short Lindblad correlation time does not prove the strict
record-support premise. Instead, on a declared input Hilbert space,
write each route isometry as
$V_s=K_s\otimes|\mathrm{vac}\rangle+W_s$, $s=0,1$,
where $W_s$ has nonvacuum reservoir support. Suppose $P_0,P_1$
are orthogonal nonvacuum reservoir projectors for the assigned windows
and uniformly

$$
\|(I-P_s)W_s\|^2\le\delta_s.
\tag{33}
$$

Let $G_s=P_sW_s$. The unwanted cross map is
$\Delta_{01}(\rho)=\operatorname{Tr}_E[W_0\rho W_1^\dagger]$.
Orthogonality gives
$\operatorname{Tr}_E[G_0\rho G_1^\dagger]=0$, so expand
its difference as

$$
\Delta_{01}(\rho)=\operatorname{Tr}_E\!\left[
 (W_0-G_0)\rho W_1^\dagger
 +G_0\rho(W_1-G_1)^\dagger\right].
$$

For any such cross map,
$\|\operatorname{Tr}_E[A(\cdot)B^\dagger]\|_\diamond
\le\|A\|\|B\|$: its bilinear trace dual is
$X\mapsto B^\dagger(X\otimes I_E)A$, and the same
operator-norm bound holds at every ancilla size. Since all Stinespring
pieces here have norm at most one,
$\|\Delta_{01}\|_\diamond\le\sqrt{\delta_0}+\sqrt{\delta_1}$.
The reversed cross map has the same bound. The two $X$ outcomes
change by their sum divided by four and its negative. Thus the full
classical-flag instrument differs from its same-diagonal, vacuum-cross
version by

$$
\|\mathcal I_{\rm actual}-\mathcal I_{\rm vac}\|_\diamond
\le\sqrt{\delta_0}+\sqrt{\delta_1}.
\tag{34}
$$

The corresponding half-diamond bound is half this value. Apply the
same argument separately to each physical ordinary filter; triangle
inequality then compares it with the switch, including any independently
bounded empty-product and helper errors. These are subnormalized
instrument bounds; rare postselection does not give a yield-independent
conditional-fidelity bound. Small pairwise overlaps of
selected bath wavepackets do not imply (33) for their complete spans.
If a tail estimate holds only for a specified state family rather than
uniformly on the input space, the conclusion is the corresponding
state/record trace-distance bound, not an unrestricted diamond bound.

<a id="nr-r11-uniform-record-guard"></a>

### A uniform few-emitter record guard and its clock cost

The change of pulse shape between cascaded scatterers need not be bounded
by assuming that the second sees the original Gaussian. There is a uniform
bound for a specified vacuum-Markov emitter model. It also applies to a
collective emitter module, but does **not** turn that joint module into
independent switch slots.

After a compact incoming pulse has ended at $T$, suppose the retained
system consists of $m$ two-level emitters, with no later drive or input.
Let $N=\sum_j n_j$ be their excitation number. The Hamiltonian may contain
arbitrary number-conserving detunings and exchange, $[H,N]=0$. Radiative
jumps have the form $L_a=\sum_j u_{aj}\sigma_j^-$, including local losses.
Pure-dephasing jumps commute with $N$. The **actual dilation** must leave
the joint ground and all future reservoir modes in vacuum; in particular
each dephasing jump must annihilate the ground, as $\sqrt{\gamma_j}n_j$
does. A nonzero constant in a diagonal jump can generate a coherent idle
reservoir output even when the reduced ground state is stationary.
Subtracting it is a changed record convention and is not free physical
access to an unknown reservoir displacement.

This is a two-level optical-emitter theorem. A resident spin memory can
have several optically ground states with ongoing spin dephasing or
spin--phonon dynamics. Such ground-manifold records are not bounded by
the trion excitation number in (NT1); they require their own enlarged
instrument. In particular this guard is not an automatic spin-memory
noise model for (SP3)--(SP6).

Define the radiative Gram matrix $G_{ij}=\sum_a u_{ai}^*u_{aj}$. Assume
$G\succeq\kappa_* I_m$ for some certified $\kappa_*>0$. The adjoint
Lindblad generator satisfies

$$
\mathcal L^*(N)=-\sum_aL_a^\dagger L_a
 =-\sum_{ij}G_{ij}\sigma_i^+\sigma_j^-
 \preceq-\kappa_* N.
\tag{NT1}
$$

For the first equality use $[N,L_a]=-L_a$; the Hamiltonian and dephasing
terms vanish. For the inequality factor $G-\kappa_*I=V^\dagger V$.
The difference is a sum of positive operators
$\sum_r(\sum_jV_{rj}\sigma_j^-)^\dagger
(\sum_jV_{rj}\sigma_j^-)$. This holds on **every** excitation sector;
it does not treat the emitters as bosonic oscillators. Gronwall's
inequality therefore gives
$\operatorname{Tr}(N\rho_{T+g})\le m e^{-\kappa_*g}$, for every initial
emitter state and passive-reference extension.

To obtain a record bound, let $E_{\rm future}$ be the system effect for
any nonvacuum reservoir record after $T+g$. It is positive and at most
identity. The vacuum-preserving ground has zero such probability, so
positivity forces $E_{\rm future}|g\cdots g\rangle=0$, including its
off-diagonal blocks with that vector. Hence
$E_{\rm future}\preceq I-|g\cdots g\rangle\langle g\cdots g|
\preceq N$. Consequently

$$
\Pr(\text{any record after }T+g)
 \le\delta(g):=\min\{1,m e^{-\kappa_*g}\}.
\tag{NT2}
$$

The effect argument includes coherences with the ground and arbitrary
reference entanglement. Since the bound is uniform over the input, the
late-record part of its Stinespring isometry has squared operator norm
at most $\delta(g)$. It supplies (33) when a route's declared nonempty
window projector excludes only those late records. It is not merely a
population estimate for one fitted probe.

A cascade can instead be truncated stage by stage: first bound the
complete first-stage output after its last incoming time, then propagate
that truncated pulse through the next stage and apply the same uniform
bound after its new last incoming time. The second pulse may be distorted
and entangled with retained outputs; the operator bound does not require
it to remain Gaussian. Projection errors must be added at the isometry
or complete-instrument level. A finite propagation segment that retains
photons, a cavity, a driven emitter, a non-Markov reservoir, or coherent
feedback with an unmodeled delay is additional memory. Applying (NT1)
only to its atoms then fails to bound that memory's late records.

The positive Gram floor is a sufficient condition, not a necessary one
for every fixed Hamiltonian: exchange can mix an instantaneous dark
subspace into bright states. There is no uniform bound from bare atomic
linewidths alone. With $L_+=\sigma_1^-+\sigma_2^-$,
$L_-=\epsilon(\sigma_1^--\sigma_2^-)$ and $H=0$, the antisymmetric
single excitation has late-emission probability $e^{-2\epsilon^2g}$
for $\epsilon>0$. It can be arbitrarily slow. At $\epsilon=0$ it is
exactly dark: it retains memory but emits no future photon. A reset bound
and a late-record bound must not be conflated at that singular limit.

**Gaussian preparation and the complete instrument.** Let a normalized
one-photon mode have Gaussian **intensity** with standard deviation
$\sigma_I$. Truncation to $[-L\sigma_I,L\sigma_I]$ has mass removed
$\epsilon_L=\operatorname{erfc}(L/\sqrt2)$. On the code spanned by zero
through $n_{\max}$ photons in that mode, replace it by its normalized
truncation. The two encoding isometries have overlap
$(1-\epsilon_L)^{n/2}$ on number state $n$. For any reference-entangled
input the overlap is a convex combination of these nonnegative numbers,
at least $(1-\epsilon_L)^{n_{\max}/2}$. Pure-state trace distance and
convexity prove the half-diamond preparation bound

$$
s_L=\sqrt{1-(1-\epsilon_L)^{n_{\max}}}
 \le\sqrt{n_{\max}\epsilon_L}.
\tag{NT3}
$$

All later physical instruments are contractive. When comparing two
protocols, truncating both source encodings therefore costs at most
$2s_L$ in their half-diamond comparison. This is a declared finite-photon
code, not an uncharged conversion of a weak coherent source into a Fock
state. Arbitrary uncontrolled temporal modes do not obey this Gaussian
code estimate.

For a compact-pulse switch and each compact-pulse ordinary temporal filter
let $r_X=\sqrt{\delta_{X,0}}+\sqrt{\delta_{X,1}}$, as in (34).
Provided all the independent-station, matched-mode, empty-product and
visibility hypotheses of (29)--(31) actually hold, triangle inequality
gives the complete flagged-instrument bound

$$
\frac12\|\mathcal I_S^{\rm Gauss}
                -\mathcal F^{\rm Gauss}\|_\diamond
 \le 2s_L+\frac{r_S}{2}+\frac{r_{AB}+r_{BA}}4.
\tag{NT4}
$$

If all six route tails have the same bound $\delta$, the last terms
are $2\sqrt\delta$. An empty-product mismatch adds the half-diamond
quantity $\|D_0-D_1\|^2/4$ from (32), at equal unit visibility. Other
helper or physical errors need their own bounds. In particular, (NT2)
alone proves none of the independent-slot or empty-product hypotheses.
Shared collective jumps or exchange between two supposed stations can
invalidate that factorization even when the entire pair becomes quiet.

If the right side of a complete-instrument half-diamond bound is $e$,
every joint accepted-good probability and the acceptance probability
change by at most $e$; the all-attempt signed good/bad reward changes by
at most $2e$. For normalized accepted outputs the trace-distance allowance
is at most $e/p_{\min}$ when both acceptance probabilities are at least
$p_{\min}>0$. Indeed the rejected block has trace-norm difference at
least the difference of acceptance probabilities; normalizing the
accepted block then gives this inequality. There is no yield-independent
postselection guarantee.

**A nominal device calculation and uncertainty.** In the reciprocal
two-emitter Markov model (35), the complete radiative Gram is

$$
G=\begin{pmatrix}
\Gamma_1&\sqrt{\gamma_1\gamma_2}\cos\phi\\
\sqrt{\gamma_1\gamma_2}\cos\phi&\Gamma_2
\end{pmatrix},\quad \gamma_j=\beta_j\Gamma_j,
\qquad
\kappa_*=
\frac{\Gamma_1+\Gamma_2-
\sqrt{(\Gamma_1-\Gamma_2)^2+4\gamma_1\gamma_2\cos^2\phi}}2.
\tag{NT5}
$$

[Hansen et al., Table S1 and excitation setup](https://arxiv.org/html/2605.18525v1)
report nominal $\Gamma_j/(2\pi\,\mathrm{GHz})=0.388,0.345$,
$\beta_j=0.95,0.85$ and $\phi=0.8\pi$, with Gaussian pulses described
by width $3\,\mathrm{ns}$ and a $20\,\mathrm{ns}$ repetition period.
For those nominal model values, (NT5) is approximately
$\kappa_* /(2\pi\,\mathrm{GHz})=0.0996492$. The conservative value
$0.099$ is certified by a rational $2\times2$ PSD test:
$\cos^2(4\pi/5)=(3+\sqrt5)/8<21/32$ makes the determinant margin
$101541/640000000$ after subtracting $0.099I$ in these units.
This calculation is about the stated Markov model, not a measured
uniform tail bound for that experiment.

There is a direct uncertainty test. For declared rate intervals
$\Gamma_j^-\le\Gamma_j\le\Gamma_j^+$, upper guided rates
$\gamma_j^+$, and $|\cos\phi|\le c^+$, a positive proposed $\kappa_0$
is valid whenever
$\Gamma_j^-\ge\kappa_0$ and
$(\Gamma_1^--\kappa_0)(\Gamma_2^--\kappa_0)
\ge\gamma_1^+\gamma_2^+(c^+)^2$.
For example, the **declared** box
$\Gamma_1/(2\pi\,\mathrm{GHz})\in[0.386,0.390]$,
$\Gamma_2/(2\pi\,\mathrm{GHz})\in[0.343,0.347]$,
$\beta_1\le0.95$, $\beta_2\le0.85$ and
$|\cos\phi|^2\le21/32$ permits $\kappa_0/(2\pi\,\mathrm{GHz})=0.095$:
the rational determinant margin is $580701/1280000000$.
The paper's fitted point estimates and linewidth errors do not establish
that whole box as a confidence region; in particular the required
guided-fraction and phase bounds need independent calibration. Without
them, a nearly dark Gram matrix cannot be excluded by this calculation.

The collective pair in that experiment does not supply the independent
slots of (29)--(31). Its Gram calculation bounds the tail of the **joint**
module. Using a similar number in (NT4) requires a proposed independent
module interface whose six route guards and other hypotheses have each
been separately justified.

As a conditional illustration of that clock budget, declare $n_{\max}=2$,
$\sigma_I=3\,\mathrm{ns}$, $L=5$, $g=30\,\mathrm{ns}$ and the above
conditional $\kappa_0$ as a floor for every required route. Then
$\epsilon_L\simeq5.74\cdot10^{-7}$,
$\delta\simeq3.35\cdot10^{-8}$, and (NT4) is below $0.00251$
before empty-product, helper and other errors. If every declared slot
receives its last input within its initial $2L\sigma_I$ interval and
its full route-tail certificate applies after the following guard, one
can choose the nonoverlapping slot clock
$W=2L\sigma_I+g=60\,\mathrm{ns}$. In that **declared clock**, the
two-window switch and three-window ordinary construction occupy $120$
and $180$ ns respectively, before transport, reset, readout and source
constraints. These are conditional schedule costs, not universal latency
lower bounds. A distorted first-stage output can lengthen the next
stage's incoming interval; the original Gaussian width and a Gram floor
alone do not certify the six route guards at this $W$. A streaming
cascade can also have a different clock. Those input-end times and
window assignments require their own complete route model.
The reported $20$ ns **period is not an idle guard**, and the source's
Gaussian-width convention must be calibrated before identifying it with
$\sigma_I$. No native rate advantage follows from comparing an unguarded
switch clock to a guarded ordinary clock. Conversely the extra ordinary
window has a real delay and visibility cost once both use the same
declared accuracy and slot definition. This finite accuracy/cost test
replaces an inference based only on a fitted dephasing linewidth.

Nor does this white-reservoir model identify a semiconductor's actual
acoustic bath. [Tighineanu et al.](https://doi.org/10.1103/PhysRevLett.120.257401)
show that confined waveguides and membranes can have low-frequency
phonon decoherence different from bulk. A short bulk memory estimate
therefore does not establish early/late record orthogonality in a
particular membrane. A non-Markovian application requires its actual
two-history bath kernel and comparison with the same ordinary spectral
and temporal filters; a fitted linewidth alone supplies neither.

### Scope of the device mapping

Actual two-emitter demonstrations do not automatically supply these two
independent slots. [Hallacy et al.](https://arxiv.org/html/2511.07640v1)
provide independently tunable chiral quantum dots with spin-dependent
correlations; the opposite-helicity transitions couple predominantly
to opposite propagation directions. For a fixed selected transition,
reversal exchanges monitored rates $\Gamma_{j,R}$ and
$\Gamma_{j,L}$, as well as spatial order. Aligning two identical
slot instruments would require an explicit coherent compensation that
also erases branch-dependent spin and bath records.
[Hansen et al.](https://arxiv.org/html/2605.18525v1) instead exploit a
collectively coupled bidirectional emitter system. A minimal coherent
one-photon model can be stated directly from the single-excitation
Hamiltonian in [Henke et al., Appendix F.1](https://arxiv.org/html/2604.06410v1)
and its left/right emitted-field phases. It already distinguishes this
joint scatterer from two independent forward slots.

In this paragraph, let $\Gamma_j$ denote **total population decay**,
$\gamma_j=\beta_j\Gamma_j$ its guided part, and $\omega_j$ the emitter
transition frequency. Assume initial $|gg\rangle$, reciprocal coupling,
a flat Markov waveguide, and no pure-dephasing or spectral-diffusion bath.
Put $z=e^{i\phi}$, $|z|=1$, and $g=\sqrt{\gamma_1\gamma_2}/2$. The bare
effective Hamiltonian and guided rows are

$$
H_{\rm eff}=\begin{pmatrix}
\omega_1-i\Gamma_1/2&-igz\\
-igz&\omega_2-i\Gamma_2/2
\end{pmatrix},\qquad
L_R=\left(\sqrt{\gamma_1/2},\sqrt{\gamma_2/2}\,z^{-1}\right),\qquad
L_L=\overline{L_R}.
\tag{35}
$$

The square roots in (35) are $\sqrt{\gamma_j/2}$, so the two directions
together contribute decay $\gamma_j$. Local nonguided rows
$\sqrt{\Gamma_j-\gamma_j}\langle j|$ complete a radiation matrix $W$
with $H_{\rm eff}=H_{\rm sys}-iW^\dagger W/2$ and Hermitian
$H_{\rm sys}$. For running frequency $\omega$, the one-photon scattering
matrix, with free propagation deembedded, is

$$
S(\omega)=I-iW(\omega I-H_{\rm eff})^{-1}W^\dagger.
\tag{36}
$$

Here $R,L$ label propagation directions. Thus $S_{RR},S_{LL}$ are the
two physical cross-port transmissions, while $S_{LR},S_{RL}$ are
reflections. For real frequency, $M-M^\dagger=iW^\dagger W$ with
$M=\omega I-H_{\rm eff}$ implies $S^\dagger S=I$ on all radiation
ports; tracing out nonguided ports leaves the expected contraction.

Set $a_j=\omega-\omega_j+i\Gamma_j/2$. The resolvent denominator is
$D=a_1a_2+g^2z^2$ and its off-diagonal adjugate entries are $-igz$.
Direct contraction gives
$L_R\operatorname{adj}(M)L_R^\dagger
=(\gamma_1a_2+\gamma_2a_1)/2-ig^2(1+z^2)$; the left contraction is
identical. Consequently

$$
T_R(\omega)=T_L(\omega)
=\frac{(a_1-i\gamma_1/2)(a_2-i\gamma_2/2)}
       {a_1a_2+g^2z^2}
=\frac{t_1(\omega)t_2(\omega)}
       {1-r_1(\omega)r_2(\omega)z^2},\qquad
t_j=1-\frac{i\gamma_j}{2a_j},\quad
r_j=-\frac{i\gamma_j}{2a_j}.
\tag{37}
$$

The denominator is the reciprocal round-trip feedback. A literal
geometric series converges for $|r_1r_2|<1$; its rational expression
extends to nonsingular lossless limits. Omitting it gives the independent
forward cascade $t_1t_2$, which describes a different network unless
returns are suppressed or demonstrably negligible. Reference planes at
the emitter ends add the same one-pass propagation phase to both
transmissions. They do not equate the two reflection amplitudes:
reciprocity fixes cross-port transmission, while an asymmetric pair can
have different same-port reflections.

For a normalizable one-photon spectral envelope $f$, transmission is the
operator $(M_Tf)(\omega)=T(\omega)f(\omega)$, with mass
$\int|Tf|^2d\omega$. Therefore (37) gives
$M_{T_R}=M_{T_L}$ on **finite pulses**, after known reference phases,
delays and output modes are matched. A hypothetical balanced coherent
comparison of the transmitted directions has
$(M_{T_R}-M_{T_L})/2=0$. Equal classical spectra alone do not supply that
coherent routing interface. Nor is this equality a statement about the
reflected instrument, photon-preserving inelastic output or unobserved
bath records. Directional radiation from a separately prepared excited
state does not contradict this initial-ground-state transmission result.

The rational transfer in (37) is nonzero almost everywhere and tends to
one at large frequency. Its isolated monochromatic zeros therefore do
not create a nontrivial $L^2$ pulse kernel. At ideal dark-mode points,
cancel removable resolvent factors before taking the limit. If retardation
is relevant, the linear transfer network must retain $z(\omega)$ and
the propagation phase; a constant-phase Markov Hamiltonian is not a
measured delay bound.

Known phase or delay correction cannot generally turn (37) into
$t_1t_2$, since feedback changes moduli as well as phase. A formal
transmitted-mode filter has ratio
$F=(t_1t_2)/T=1-r_1r_2z^2$. It is a no-gain spectral contraction only
where $|F|\le1$; a scaled contraction can incur additional selection loss.
Physical filtering also needs its causal implementation and resource
cost. This observation does not exclude arbitrary ordinary processing of
all accessible ports. A useful detuning/phase decision or delivered state
must still be compared with ordinary transmission/reflection measurements,
pulse optimization, spectral selection and coherent delayed paths.

The sources' reported linewidths, guided fractions, coupling phase,
dephasing, diffusion and Fano parameters identify a starting model;
they are not fitted by (35)–(37). In particular, pure dephasing cannot
in general be replaced by photon disappearance while preserving the
one-photon instrument. The enlarged native bath and nonlinear
two-photon dilation remain to be characterized. This coherent-component
calculation neither supplies two independently callable slots nor
establishes a new switch, a photon-preserving order flag, the gate above,
or a hardware advantage. The two-photon proofs preceding this subsection
retain their explicitly stated independent-slot hypotheses.

There is a separate conditional test for the **same full joint
device**. Let $V_T$ be its actual field--emitter--bath dilation at a
fixed common finish, retaining emitter memory $M$, all Fock sectors
and all loss/dephasing records. Suppose the ordinary interface
independently supplies the proposed input-only external R/L encoder
$W_{\rm in}$, any retained source/helper register $C$, and terminal
processor/readout $W_{\rm out},N_z$.
Both strategies then have the identical recorded operators

$$
A_z=(N_zW_{\rm out}\otimes I_E)(I_C\otimes V_T)
       (W_{\rm in}\otimes I_{ME}),
$$

with the same initial emitter/bath state. Equality before tracing
inaccessible $E$ proves equality of every retained-field, $M$,
reference, accepted and lost-output instrument, including nonlinear
connected multiphoton scattering. Tensoring a passive reference
preserves the equality. This does not follow from a fixed
global Hamiltonian alone. An input-only encoder cannot hide a genuine
internal SWITCH router, and its ordinary availability cannot be inferred
merely because a native proposal assumes it. The reported classical
detuning knobs do not by themselves provide independently open photon
oracles. This identity neither simulates arbitrary independent A/B
oracles uniformly nor establishes causal separability or extends
(37)'s reciprocity claim. A distinct coherently controlled internal
dynamics or feedback during unresolved dwell needs its own full
instrument and strongest ordinary comparison; being outside this
input-only premise does not establish an advantage.

<a id="nr-r11-moving-caps"></a>

### Retained atomic motion and a passive order-flag bound

The [moving-atom CAPS component](methods/moving-caps.md) supplies a
source-based energy-shifting reflection model for the retained-inelastic
question. It proves a passive-resolvent bound on the surviving minus
flag in terms of full motional energy-transfer moments, and a
source-specific recovery limit for that measured flag. Its optional
finite-packet thermal study compares retained spin/photon outputs with
ordinary random order and paid spectral filtering. The displayed
plus-only service has no all-launch target-good advantage. Missing
loss records, routing phases, actual helper ports and numerical tails
remain explicit; the component establishes no native hardware benefit.

### Boundary of the scattering reductions

Mode-changing scattering, multiphoton events, order-dependent arrival
times and a shared bath can violate (9). A bus-bin flip before one
station's contraction is already a finite counterexample to that
common-label premise. Equations (10)–(14) close the equal-monitored-rate
survivor case despite individual-frequency redistribution. Unequal rates
can be noncommuting, but (18)–(27) give explicit operational and ordinary
screens for the stated relative-mode target and known-dressing family.
They do not close every unequal-fraction kernel, group-velocity
dispersion, frequency-dependent mode mixing, additional internal levels,
photon-preserving bath record or coherent bidirectional device.

The [Raman comparison](#nr-r11-raman-swap) now supplies that
ground-state-changing instrument and a useful Bell-pair target under
explicit matched-mode hypotheses. Its ideal SWAP endpoints have ordinary
partial-SWAP, helper-fanout and teleportation comparators. The
[local-memory filters](#nr-r11-raman-local-ancillas) also close the
unknown-coefficient minus-only argument and several calibrated lossy
points. The [complete balanced-cavity frontier](#nr-r11-raman-cavity-frontier)
and [source/clock ledger](#nr-r11-raman-source-clock) prevent treating
spectator loss, detuning or occupied visits as a sufficient architecture
gain. A remaining case needs a measured phase-reference or control-access
constraint and a complete instrument on the same physical graph.
A stimulated classical Raman rotation does not by
itself supply the required single-photon branch. Retained shared quantum
memory is a distinct possibility, subject to the ordinary controls and
native-interface test in the [architecture assessment](architecture.md).
Neither a diagonal quarter-phase example nor a quiet Markov tail supplies
the remaining positive application.

A remaining application needs its full instrument, executable input
code or constrained source, surviving output/flag, and a gain after
ordinary pulse/detuning optimization, spectral and temporal filtering,
reuse, routing and rejected-attempt costs. The
[existing passive energy-time-entangled pair source](https://doi.org/10.1038/s41567-024-02543-8)
is an ordinary comparator, including its spectral filtering and timing
selection. A favorable commutator or coincidence-normalized phase is
insufficient. The linked finite replay checks an elastic state-carving
instrument and a bin-flip example, the retained-spin parity/photon-bus
identities (SP1)--(SP6), the ideal Raman helper/teleportation and flat-loss
survivor identities (RS1)--(RS13), and full finite-emitter number, ground-vacuum,
nominal-Gram and near-dark identities supporting (NT1)--(NT2). The
semigroup, infinite-future effect, Gaussian-code and complete-instrument
bounds are analytic proofs. Neither they nor the continuum scattering
arguments are certified by finite frequency-grid sampling, a hardware
fit or a Lean formalization.
