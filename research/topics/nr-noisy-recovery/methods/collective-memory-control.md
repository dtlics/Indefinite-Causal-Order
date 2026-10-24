# Ordinary symmetry control at a fixed memory deadline

This is a proof component of [NR-R14](../backaction.md#nr-r14), using the
[two-logical-qubit storage task and code](../backaction.md#nr-r14-two-qubit-deadline).
It supplies a conditional ordinary comparator, including finite control
errors and elapsed time. It establishes neither a fitted device channel
nor a quantum-switch advantage.

Permutation symmetrization and noiseless-subsystem control are established
mechanisms: [Zanardi, Example 4 and Eq. (12)](https://arxiv.org/html/quant-ph/9809064v2)
and [West and Fong, Eqs. (20)--(26)](https://arxiv.org/html/1203.4296)
are relevant precedents. Their ideal pulse limits do not provide the
finite-duration controls assumed and priced below.

## The averaged generator and its limits

Let $P$ be the four-spin singlet projector defined in the owning source,
$J_\alpha=\tfrac12\sum_i\sigma_i^\alpha$ and
$J_\pm=\sum_i\sigma_i^\pm$. Use angular-frequency Hamiltonians $h=H/\hbar$.
For constant offsets during a cycle, write

$$
h=\sum_{i<j}J_{ij}(\sigma_i^+\sigma_j^-+\sigma_i^-\sigma_j^+)
  +\frac12\sum_i\delta_i Z_i.
$$

Full site permutations $U_\pi$, $\pi\in S_4$, give

$$
\bar h=\frac1{24}\sum_\pi U_\pi^\dagger hU_\pi
 =\bar J(J_x^2+J_y^2-2I)+\bar\delta J_z,
\quad
\bar J=\frac16\sum_{i<j}J_{ij},\quad
\bar\delta=\frac14\sum_i\delta_i.
\tag{SC1}
$$

Each unordered pair and each site occur equally often in the sum.
Since $J_\alpha P=0$, $\bar hP=-2\bar JP$. Its scalar phase has no
logical effect. The nominal hopping values in the owner give
$\bar J/(2\pi)=3.135\,\mathrm{MHz}$. Also
$U_\pi^\dagger J_\pm U_\pi=J_\pm$ in every frame.

Independent local Markov errors behave differently. Their exact average is

$$
\frac1{24}\sum_\pi\mathcal U_\pi^{-1}
 \left[\sum_i d_i\mathcal D[\sigma_i^-]+u_i\mathcal D[\sigma_i^+]\right]
 \mathcal U_\pi
 =\bar d\sum_i\mathcal D[\sigma_i^-]
  +\bar u\sum_i\mathcal D[\sigma_i^+],
\tag{SC2}
$$

where $\mathcal U_\pi=\operatorname{Ad}_{U_\pi}$. Averaging introduces
no cross terms between sites. It does not produce
$\bar d\mathcal D[J_-]+\bar u\mathcal D[J_+]$. Local Markov dephasing
likewise remains local. Quasistatic Hamiltonian offsets in (SC1) and
independent Markov phase jumps must not be interchanged.

## Three-level transmons require a subsystem decoder

For actual three-level operators $a_i$, put $A=\sum_i a_i$ and
$N=\sum_i a_i^\dagger a_i$. The binary slice satisfies $AP=0$, but

$$
PAA^\dagger P=4P.
\tag{SC3}
$$

Indeed $[a,a^\dagger]=\operatorname{diag}(1,1,-2)$, and its four-site sum
equals $4I$ on this slice. The binary part of $A^\dagger P$ cancels;
its nonzero output has double occupancy. A decoder that merely projects
back onto $P$ therefore loses collective thermal trajectories.

There is a stronger ideal ordinary comparison when full site permutations
and an appropriate encoder/decoder are supplied. Schur--Weyl decomposition
of $(\mathbb C^3)^{\otimes4}$ has a $[22]$ block
$\mathbb C^6_{\rm gauge}\otimes\mathbb C^2_{\rm logical}$.
The $S_4$ character on cycle types $1^4,2\,1^2,2^2,3\,1,4$ is
$(2,0,2,-1,0)$. Its central projector is

$$
P_{22}=\frac2{24}\sum_\pi\chi_{22}(\pi)U_\pi,
\qquad
\operatorname{Tr}P_{22}=\frac2{24}\sum_\pi\chi_{22}(\pi)3^{c(\pi)}=12.
\tag{SC4}
$$

The original binary singlet representation is this two-dimensional
$S_4$ irrep in one fixed gauge state. Every Hamiltonian and **each error
operator** commuting with target permutations acts as a gauge operator
times $I_{\rm logical}$ on this block. This follows from the irreducible
representation decomposition and Schur's lemma. With fixed gauge/bath
preparation independent of the logical/reference input, the entire
collective evolution preserves that logical input. A supplied subsystem
decoder traces the gauge; it does not project back onto the original
binary slice. One other logical qubit in an actually protected helper
then gives identity on all two-logical-qubit/reference operators in the
collective-only ideal limit.

This reasoning applies to the full symmetrized coupling, not just its
reduced dissipator. For example, target-only permutations average

$$
\begin{aligned}
\sum_{i<j}J_{ij}(a_i^\dagger a_j+a_j^\dagger a_i)
 &\longmapsto\bar J(A^\dagger A-N),\\
\sum_i U_i n_i(n_i-1)/2
 &\longmapsto\bar U\sum_i n_i(n_i-1)/2,\\
\sum_i g_i e^{i\phi_i}b_i^\dagger a_i
 &\longmapsto\frac14\left(\sum_i g_i e^{i\phi_i}b_i^\dagger\right)A.
\end{aligned}
\tag{SC5}
$$

The resonators are not physically permuted. Their unequal frequencies,
Hamiltonians and resonator-only errors act on the gauge/bath side.
Collective $A,A^\dagger$ also commute with target permutations. In
contrast, covariance of the **sum** of local Lindblad dissipators does
not make each local error a gauge operator. Such errors remain in the
ledger. Correct SWAP action on a two-level computational subspace does
not specify the control on the reachable third levels.

## A finite-period, finite-pulse bound

Use a validated finite-dimensional GKSL model on the full retained
target/helper/bath domain needed for composition. Let $\mathcal L_a$,
$a=1,\ldots,q$, be the constant toggling generators, with $q=24$ and
$\bar{\mathcal L}=q^{-1}\sum_a\mathcal L_a$. Every generator and every
positive partial sum generates a CPTP semigroup. Define

$$
\mathcal C_\tau=e^{\tau\mathcal L_q}\cdots e^{\tau\mathcal L_1},
\qquad
S=\sum_{a<b}\|[\mathcal L_a,\mathcal L_b]\|_\diamond.
$$

For two generators, differentiate
$e^{(\tau-s)(\mathcal A+\mathcal B)}e^{s\mathcal A}e^{s\mathcal B}$.
Its derivative contains
$[e^{s\mathcal A},\mathcal B]
=\int_0^s e^{(s-u)\mathcal A}[\mathcal A,\mathcal B]e^{u\mathcal A}du$.
Every surrounding forward semigroup is a diamond-norm contraction.
Integration gives a $\tau^2\|[\mathcal A,\mathcal B]\|_\diamond/2$
bound. Iterating over positive partial sums and telescoping $K$ cycles
therefore gives, for $T_f=Kq\tau$,

$$
\frac12\|\mathcal C_\tau^K-e^{T_f\bar{\mathcal L}}\|_\diamond
\le\epsilon_{\rm av}
:=\frac{K\tau^2}{4}S
=\frac{T_f^2}{4Kq^2}S.
\tag{SC6}
$$

The full generators include the Hamiltonian. A nonzero cycle is not
asserted equal to its average. If only
$\|\mathcal L_a\|_\diamond\le B$ is available, then
$S\le q(q-1)B^2$, often a pessimistic bound. A vacuous estimate does not
prove physical failure. Unbounded oscillator generators may have
infinite norms: a cutoff requires a uniform model/process-error bound,
including its effect throughout the protocol and for reference inputs.
Independent isolated system-channel fits do not supply same-bath
composition or such a truncation bound.

For offsets varying about fixed $\delta_i^0$, a further half-diamond
allowance is
$\tfrac12\int\sum_i|\delta_i(t)-\delta_i^0|dt$ over the free holds.
This follows from Hamiltonian Duhamel comparison. Neither this allowance
nor its statistical confidence follows from a Ramsey $T_2^*$ alone.

Let actual pulse $\ell$ take $t_\ell$ and have composable half-diamond
defect $\epsilon_\ell$ from its required ideal permutation on the stated
retained domain. Include finite-width evolution, loss, leakage, phases
and spectators in that defect. Let $\epsilon_{\rm other}$ include the
codec, helper, model and residual drift allowances. Then

$$
F_{e,4}^{\rm actual}\ge q_0-\epsilon_{\rm av}
 -\sum_\ell\epsilon_\ell-\epsilon_{\rm other},\qquad
T_{\rm deadline}\ge t_{\rm enc}+t_{\rm dec}+T_f+\sum_\ell t_\ell.
\tag{SC7}
$$

Here $q_0$ is the identity-channel weight justified next. Pulse duration
reduces the available free hold; noise during pulses is inside the pulse
defect, not omitted. Replacing pulses by zero-duration reference gates is
only a comparison construction. Statistical failure probabilities and
discarded preparations also enter an all-attempt guarantee.

In the spin model, collective terms and $\bar h$ preserve $P$. The
no-local-jump rate operator is
$R=\bar dN+\bar u(4I-N)=2(\bar d+\bar u)I$ there. Thus the complete
decoded channel has a CP decomposition

$$
\bar\Lambda=q_0\operatorname{id}_4+\mathcal B,
\quad q_0=e^{-2(\bar d+\bar u)T_f},
\quad\mathcal B\text{ CP},\quad
\operatorname{Tr}\mathcal B(\rho)=(1-q_0)\operatorname{Tr}\rho.
\tag{SC8}
$$

It retains every other unobserved trajectory. It grants no jump herald;
positivity of its Bell overlap gives $F_{e,4}(\bar\Lambda)\ge q_0$.

The spin exponent cannot be imported into the qutrit subsystem. There,
$R_{\rm loc}=\sum_i[\bar d a_i^\dagger a_i+\bar u a_i a_i^\dagger]$
commutes with permutations and has norm at most
$R_{\max}=4\max\{\bar u,\bar d+2\bar u,2\bar d\}$.
All records with no **local** jumps, including arbitrary collective and
gauge events, still preserve the logical factor. Their trace obeys
$p'(t)=-\operatorname{Tr}(R_{\rm loc}\rho_t)\ge-R_{\max}p(t)$.
With fixed initial gauge/bath state this gives a state-independent
identity weight

$$
q_0\ge e^{-R_{\max}T_f}.
\tag{SC9}
$$

Use this conservative lower bound in (SC7) only with the actual subsystem
decoder. Additional local dephasing/heating/leakage must be included in
the no-jump rate or separately bounded. The source's omitted terms and
unreconciled rates are not set to zero by this argument.

## Pulse and waveform costs

A cyclic Steinhaus--Johnson--Trotter path visits all 24 permutations with
24 adjacent full SWAPs, including closure. A literal path uses the three
nearest edges 9, 6 and 9 times per cycle. In an isolated **two-level**
pair with $h_{XY}=J(XX+YY)/2$, three equal intervals of length
$\pi/(4J)$, conjugated by local quarter-turns, obey

$$
e^{-i\pi(XX+YY)/8}e^{-i\pi(XX+ZZ)/8}e^{-i\pi(YY+ZZ)/8}
 =e^{-i\pi/4}\operatorname{SWAP}.
\tag{SC10}
$$

The Pauli-pair terms commute; their sum and
$\operatorname{SWAP}=(I+XX+YY+ZZ)/2$ prove the identity. This compiler
uses 72 exchange intervals and 192 unmerged local quarter-turns per
cycle. With the nominal nearest-edge couplings, exchange-on time alone
is about $1.534\,\mu$s. This is one conditional synthesis, not a speed
limit or measured gate time. Isolation, settling, rotations, leakage,
phase compensation and the codec add costs. A single XY iSWAP gives
$-i$ on exchanged single-excitation states and cannot be made a full
SWAP with local $Z$ frames; it entangles $|++\rangle$. Equation (SC10)
also supplies no qutrit permutation certificate.

A cheaper available sign-control route must be compared. Four Hadamard
sign patterns obey $\sum_s s_i s_j=4\delta_{ij}$ and average off-diagonal
XY hopping to zero. For real physical phases
$U_Z(t)=e^{-i\sum_i\theta_i(t)n_i}$, the toggling frame sends
$a_i\mapsto e^{-i\theta_i}a_i$. Choosing an engineered coupling phase
$\phi_i(t)=\phi_i^0+\theta_i(t)$ keeps
$g_i e^{i\phi_i(t)}b_i^\dagger a_i$ fixed in that frame, provided its
amplitude is maintained. The frame derivative is
$-\sum_i\dot\theta_i n_i$, requiring a physical control
$+\sum_i\dot\theta_i n_i$; equivalently
$\omega_i^{\rm phys}(t)-\dot\theta_i(t)=\omega_i^0$ for fixed target
occupation frequencies. These are full waveform requirements.

Intrinsic collective Purcell loss instead acquires the phase pattern.
Its four-sign dissipator average becomes $\sum_i\mathcal D[a_i]$,
including the analogous upward terms. Local $Z$ offsets are not refocused
by $Z$ signs. A virtual analysis frame does not physically toggle the
hopping. Frequency changes can alter coupling amplitudes, detunings and
spectra, and resonator transients must be included. The demonstrated
sideband ramp in the owning source does not supply instantaneous or
continuously compensated phase controls.

## A fixed-code local-loss recovery limit

Let $|\psi_0\rangle=u_0/2$, $|\psi_1\rangle=u_1/\sqrt{12}$ be the
owner's orthogonal codewords. This paragraph fixes that encoding and
uses only uniform unobserved local amplitude damping, with survival
probability $0\le\eta\le1$. It does not assume the simultaneous source
Hamiltonian, collective terms or arbitrary gauge dynamics.

For $\mathcal J(\rho)=\sum_i\sigma_i^-\rho\sigma_i^+$, use orthogonal
single-excitation vectors
$v_{12}=(1,-1,0,0)/\sqrt2$, $v_{34}=(0,0,1,-1)/\sqrt2$,
$w=(1,1,-1,-1)/2$. Direct lowering gives

$$
\mathcal J(\rho_0)=P_{v_{12}}+P_{v_{34}},\qquad
\mathcal J(\rho_1)=\tfrac13(P_{v_{12}}+P_{v_{34}})+\tfrac43P_w.
\tag{SC11}
$$

Each jump output has trace two. The complete damped state has a
two-excitation term $\eta^2\rho_j$, one-excitation term
$\eta(1-\eta)\mathcal J(\rho_j)$, and the common vacuum term
$(1-\eta)^2|G\rangle\langle G|$. These sectors are orthogonal.
The jump-output difference has eigenvalues $2/3,2/3,-4/3,0$.
Consequently their trace distance is

$$
D=\tfrac12\|\mathcal E_\eta(\rho_0)-\mathcal E_\eta(\rho_1)\|_1
 =\eta^2+\tfrac43\eta(1-\eta)=\frac{4\eta-\eta^2}{3}<1
\quad(\eta<1).
\tag{SC12}
$$

Thus no subsequent CPTP recovery perfectly restores this logical qubit.
Uniform local loss is permutation covariant, so ideal site permutations
alone do not remove this obstruction. For any final qubit decoder,
write its correct basis-output probabilities as $A,B$ and its Choi
coherence as $z$. Helstrom gives $A+B\le1+D$, while the positive Choi
principal minor gives $|z|\le\sqrt{AB}$. Hence

$$
F_e\le\frac{A+B+2\sqrt{AB}}4\le\frac{1+D}2.
\tag{SC13}
$$

At $\eta=3/5$ this upper bound is $21/25$; tightness is not asserted.
For the fixed product channel $\operatorname{id}_{C}\otimes\mathcal E_\eta$,
arbitrary joint decoding cannot exceed the optimal single-qubit recovery
fidelity. Prepare a fresh normalized Bell pair $C_0F$ inside a constructed
single-qubit decoder, apply the joint decoder to $C_0$ and the noisy
qubit, then project its $C'$ output and $F$ onto the normalized Bell
state. This is a TNI map whose unnormalized Bell-pass probability equals
the joint $F_{e,4}$. Completing failure branches to a CPTP map can only
add Bell overlap. Thus (SC13) also bounds that fixed-product endpoint.
It is not a converse for new joint encodings, intermediate correction,
accessible loss records or the full four-transmon model.

## Decision and verification scope

First characterize the full permutation or compensated waveform on the
reachable $0/1/2$ sector, with phase, spectator, bath and timing effects.
Then choose cycles within the actual deadline and compare (SC7), or a
direct held-out logical-channel test, with modulation-off storage and the
paid $F_{e,4}=1/2$ classical fallback. Keep all available records and
include unobserved events in the full channel. A negative or vacuous
bound leaves performance unresolved; it does not certify failure.

The existing [loss-memory checker](../checks/architecture/loss_memory_qualification_guards.py)
replays finite group, code, pulse-identity, sign, hazard and local-loss
ingredients. The general Schur decomposition, full reference-channel
arguments, Duhamel/error budgets and physical ports are analytic or
explicit assumptions. No measured pulse, decoder or storage fidelity is
certified by these finite identities.
