# Communication links: exact reductions and resource bounds

[Architecture assessment](architecture.md) · [Local baselines](architecture-baselines.md) · [References](references.md) · [Checks](checks/README.md)

These finite-dimensional results distinguish an abstract switch placement from a physical network cut. Local operations, classical communication (LOCC), encoding, quantum memory, distillation and rejected attempts belong in the comparator. A usable control wire across a cut is an additional communication resource; an abstract provider-owned order control does not automatically supply that wire. The proofs below are analytic, with finite identities replayed by the linked checks. They have not been formalized in Lean, and no priority claim is made.

<a id="nr-r09"></a>

## NR-R09 — Pure absorbing loss adds only a receiver-preparable flag

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

<a id="nr-r11"></a>

## NR-R11 — Elastic local-node instruments have no extra order syndrome

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

Mode-changing scattering, unresolved frequency dynamics, multiphoton
events, order-dependent arrival times and a shared bath can violate (9).
For example, a bus-bin flip before one station's contraction generally
breaks commutation. A nonzero signal in such a different model still
needs to improve stored Bell-pair yield after ordinary filtering and
routing costs. The finite replay verifies an elastic state-carving
example and a bin-flip counterexample; it is not a fitted model or a
claim that every experimental error is elastic.
