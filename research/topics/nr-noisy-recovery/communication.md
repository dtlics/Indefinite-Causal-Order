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

## NR-R11 — Accepted cavity and nonlinear-scattering instruments

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

This screen applies to the elastic two-time-bin state-carving model of
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

The retained-spin next test must therefore keep a mechanism outside the
diagonal photon-bus family: Raman/spin-changing scattering with its
frequency and polarization outputs, or an explicitly retained shared
quantum memory. Specify a heralded spin Bell-pair or gate target and
derive the full ground-state-changing optical kernels and bath records
for that actual device. A stimulated classical Raman rotation does not
by itself provide a large coherent single-photon Raman branch. Compare
ordinary spectral heralding, the parity instruments (SP1)--(SP2), the
available fixed-order bus and spin echo (SP5)--(SP6), and all rejected
launches at matched source, readout, memory and reset cost. Neither the
diagonal quarter-phase example nor a quiet Markov tail supplies that
remaining positive application.

A remaining application needs its full instrument, executable input
code or constrained source, surviving output/flag, and a gain after
ordinary pulse/detuning optimization, spectral and temporal filtering,
reuse, routing and rejected-attempt costs. The
[existing passive energy-time-entangled pair source](https://doi.org/10.1038/s41567-024-02543-8)
is an ordinary comparator, including its spectral filtering and timing
selection. A favorable commutator or coincidence-normalized phase is
insufficient. The linked finite replay checks an elastic state-carving
instrument and a bin-flip example, the retained-spin parity/photon-bus
identities (SP1)--(SP6), and full finite-emitter number, ground-vacuum,
nominal-Gram and near-dark identities supporting (NT1)--(NT2). The
semigroup, infinite-future effect, Gaussian-code and complete-instrument
bounds are analytic proofs. Neither they nor the continuum scattering
arguments are certified by finite frequency-grid sampling, a hardware
fit or a Lean formalization.
