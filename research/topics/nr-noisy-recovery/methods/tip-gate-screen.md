# Required TIP gates: shared-qubit checks, timed faults and selector costs

This is a proof component of [NR-R06](../architecture-baselines.md#nr-r06).
It compares a required pair of adjacent entanglers with ordinary shared-qubit
checks, then retains physical clock records in declared relaxation and
coupler-dephasing models. The analytic results below do not establish a
native architecture advantage or a calibrated multi-transmon selector.

<a id="nr-r06-required-tip-entanglers"></a>

## Adjacent TIP entanglers have a paid shared-qubit baseline

[Shirai et al., Physical Review Research 8, 033261 (2026)](https://doi.org/10.1103/zglk-gd95)
demonstrate a $140\,\mathrm{ns}$ microwave TIP CZ and partial gate-error
detection by coupler readout after a Clifford. The [detailed primary](https://arxiv.org/html/2511.01260v2),
V and F/I, retains data during readout but reports incomplete detection and
measurement-related changes in leakage dynamics. The declared data idle is
$470\,\mathrm{ns}$ with overlapping $420\,\mathrm{ns}$ integration;
these are not additive or a complete reset/feedback clock. Readout
assignment probabilities and RB decay do not determine all accepted and
rejected data/reference maps. The proposed adjacent-gate extension below
is not this measured three-transmon device.

**A single local code-closed fault needs only the shared $Z_B$ check.**
Let $A_0=\mathrm{CZ}_{AB}$, $B_0=\mathrm{CZ}_{BC}$ and $W=B_0A_0$ on
three logical qubits. Refine one AB-supported logical fault after $A_0$
to an arbitrary operator $E$, and put

$$
E_e=(E+Z_BEZ_B)/2,\qquad E_o=(E-Z_BEZ_B)/2.
$$

The $B$-diagonal blocks commute with $B_0$; its off-diagonal blocks pick
up $Z_C$. Thus $B_0E_eB_0=E_e$, $B_0E_oB_0=E_oZ_C$, and the standard
module-paired plus operator with that same refined fault is

$$
K_+=\tfrac12(B_0EA_0+EA_0B_0)
=[E_e+E_o(I+Z_C)/2]W.
$$

Ordinary fixed order with a clean helper checking $Z_B$ coherently before
and after accepts $K_o=E_eW$. Lift these operators to dimension $d=8$.
Off-diagonal $B$ blocks have zero trace and are Hilbert--Schmidt orthogonal
to diagonal blocks, so their unnormalized target Bell-good weights and
maximally mixed acceptance probabilities satisfy

$$
q_o=q_+=|\operatorname{Tr}E_e|^2/64,\qquad
p_+=p_o+\|E_o(I+Z_C)/2\|_{\rm HS}^2/8\ge p_o.
$$

Consequently $p_o-q_o\le p_+-q_+$: the ordinary accepted bad weight is no
greater. A BC-supported fault has the same proof with $Z_A$ replacing
$Z_C$ and the same shared-$B$ check. This is a refined single-fault,
plus-branch Bell comparison, not arbitrary-input acceptance ordering or
full-decoder dominance. Its controlled-$Z_B$ gates, helper and readout
are paid physical controls.

**The microscopic return problem remains different.** Both proposed
blocks orient shared $B$ in the source's active higher-frequency role.
The full Duffing Hamiltonian retains all exchange edges and both couplers:
an undriven private coupler still interacts with $B$. A $B$-f excursion
can affect $C$ and return to $B$-e while endpoint couplers return to ground.
Such a history need not be an AB- or BC-supported logical fault above.
Spectator A/C relaxation during the other block is outside that support
hypothesis too; the check does not close common-clock idle errors.
A physical $(-1)^{n_B}$ also changes the signs of its exchange edges;
effective logical $Z_B$ identities cannot be used as in-gate full-Hamiltonian
echoes without their actual multilevel implementation and frames.

**A selector's actual coupling also belongs to the ordinary side.**
Abstract helper-conditional linear coupler drives do not by themselves
provide a nondemolition excitation marker. If the selector instead uses
$\chi_{DB}n_Dn_B$, the two active transitions
$|e_B,g_j\rangle\leftrightarrow|g_B,f_j\rangle$, $j=u,v$, both shift by
$-\chi_{DB}n_D$ in that effective number-state description. In the isolated
or refocused number--number model, a logical $\mathrm{CZ}_{DB}$ takes
$\pi/|\chi_{DB}|$; the before/after check costs $2\pi/|\chi_{DB}|$ plus
frames, refocusing/helper pulses and noise. A full-$H_0$ calibrated
implementation must supply its actual duration and corrections instead;
a bare wait is not exact under $H_0$.
No measured $\chi_{DB}$ is supplied. The native pulses also accumulate
this coupling's conditional phases throughout their duration and need
joint calibration. Frequency selectivity is one possible design, not a
necessary large-detuning condition: closed off-branch cycles may also be
designed. A private $\chi_{Du},\chi_{Dv}$ implementation instead motivates
coupler-level spectral markers, with their actual selectivity and clock.
Neither case establishes a complete noisy order compiler or a bath-record
matching identity from a system Hamiltonian alone.

A strong conditional ordinary extension stores **one midpoint flag** in
the same helper, initially $0$. For a calibrated good-prefix projector
$P$, nominally $P_{B,ge}P_{u,g}P_{v,g}$ in the chosen dressed/code frame,
and $Q=I-P$, the unitary
$M=P\otimes I_D+Q\otimes X_D$ marks a bad prefix while preserving every
good unknown logical input/reference. Execute the first gate, $M$, then
the second gate; its drive may be gated on $D=0$ if that rejection service
is admitted. Common idle Hamiltonian evolution continues on both branches.
Do not overwrite $D$: combine its final record and separately retained
actual PED records classically. A later coherent return cannot erase that
stored prefix absent a helper fault. There is no midpoint classical
readout requirement in this ideal construction.

Implementing $M$ still needs calibrated joint state-selective controls,
including a coherence-preserving $B$ code-versus-f predicate when a
coupler-only marker misses the path. Coupler number parity alone misses
f occupation. Helper-induced detunings, relaxation of the stored flag,
backaction, readout and reset all count; within-block excursions returning
before the midpoint remain untested. Neither a classical leakage herald
on another device nor abstract conditional pumping grants this quantum
marker. The next comparison must characterize these ordinary controls and
the native selector's full common-clock accepted/rejected instrument at a
common deadline. No returned-leakage rate or native fault advantage follows
from the published pair's PED fractions or a fitted reduced noisy-CZ map.

**A source-model return channel is not automatically a useful fault.**
In the full coupled-Duffing model, let $u$ be the coupler and use the
positive gap $\Delta=\omega_u-\omega_B$. First-order static dressing gives

$$
\langle\widetilde{e_Bg_u}|a_u|\widetilde{g_Bf_u}\rangle
=\sqrt2g_{Bu}\left[\frac1{\Delta+\alpha_u}-\frac1\Delta\right]+O(g^2).
\tag{TR1}
$$

The initial dressed state contains
$\sqrt2g_{Bu}/(\Delta+\alpha_u)|e_Be_u\rangle$; the final one contains
$-g_{Bu}/\Delta|g_Be_u\rangle$. Applying $a_u$ proves the two terms.
This is the same first-order drive/return structure as source Eq. 3
after reconciling its detuning orientation; the formula above explicitly
uses the positive physical gap rather than silently changing that sign.
One emitted photon can therefore return dressed coupler f directly to
the data-like B-e state, without two successive local f-to-e-to-g losses.

Its nominal bare frequency is $(2\omega_u+\alpha_u-\omega_B)/(2\pi)$,
6193 MHz for the source parameters, versus the nominal bare f-e line
5432 MHz. These are model frequencies before dressing, not extra measured
spectral data. For a frequency-resolved weak bath, its rate is
$\kappa_u(\omega_{\rm ret})|m_B|^2$ with $m_B$ given by (TR1).
The measured $T_{1f}$ does not fix the spectral rate at both lines.
A bare admixture alone is not a fault or an accepted readout event;
preparation, bath transitions and readout must use consistent dressed
states. The leading one-block B-return is diagonal on the code and
commutes with the other ideal CZ. Code-closed transfer to A flips B
and meets the shared-$Z_B$ check; returns leaving a data transmon in f
must remain in the leaked-output ledger until an actual data check.
More general driven, retained-coupler histories still need their own
complete maps. Loss of a surrogate charge label alone proves no benefit.

<a id="nr-r06-tip-warm-model"></a>

## Warm inputs require a joint gate and preparation model

The required service remains $W=\mathrm{CZ}_{AB}\mathrm{CZ}_{BC}$ on every
unknown logical $ABC/R$ input, with logical dimension eight. Both private
couplers, idle exchange, data leakage, helper states and every rejected
output remain in the common release instrument. [The same primary,
Table III](https://arxiv.org/html/2511.01260v2), reports
$P_e+P_f=0.13(1)$ for its single coupler; separate $e,f,h$ populations and
joint $u,v$ initialization are unspecified. A product warm distribution,
copied second-coupler temperature or zero higher-level weight is therefore
an additional model assumption. An infinite Gibbs state of a negative
quartic Duffing oscillator is invalid: its spectrum is unbounded below.
Use physical transmon levels or a declared low-occupation source with an
explicit omitted-mass and dynamical-boundary account.

Preparation is a channel. If unknown data are already resident, its
always-on coupling, measurement/cooling backaction and exposure clock belong
inside the launch map. A clean ready boundary instead needs an actual
operation preserving every unknown $ABC/R$ state while preparing a specified,
data-independent auxiliary/preparation-bath state. A calibrated joint dressed
embedding is another possible contract; independent maximum-overlap
eigenvector labels do not automatically define an isometry. Permit ordinary
preparation before data arrival, off the critical path or amortized across
reuse whenever the real ingress and ready ports support it, charging its
actual cost. No preparation schedule is forced merely to disadvantage that
baseline.

**Hidden warm components cannot cancel accepted logical errors.** Suppose
the initial joint coupler state $\tau=\sum_a w_a|a\rangle\langle a|$ is
independent of $ABC/R$, with any purifier permanently inaccessible and
nonreinteracting. The couplers themselves remain dynamical outputs.
For a fixed physical controller, all actual records, acceptance policy and
decoder, let $J_a$ be the accepted corrected data-output marginal Choi matrix,
normalized using $|\Phi_8\rangle$, with accepted leakage/erasure retained as
orthogonal output and $W$ embedded in the physical code. The decoder first uses every supplied
coupler/helper output; those outputs are traced only for this necessary test.
Linearity and positivity give

$$
J=\sum_a w_aJ_a,\qquad
p=\sum_a w_ap_a,\quad q=\sum_a w_aq_a,\quad
p-q=\sum_a w_a(p_a-q_a)\ge0,
\qquad
p_a=\operatorname{Tr}J_a,\quad
q_a=\langle\Phi_W|J_a|\Phi_W\rangle.
$$

If $J=p|\Phi_W\rangle\langle\Phi_W|$, every positive-weight accepted
constituent has that same one-dimensional support: its expectation on every
vector orthogonal to $\Phi_W$ is nonnegative and their sum is zero.
Equivalently every accepted fine Kraus row is proportional to $W$ or zero.
Order amplitudes may interfere within each initial component, but not
between different hidden mixture labels. A retained or reinteracting source
purifier requires the complete joint input instead of dephasing its reduced
warm state. A joint logical/auxiliary output Choi matrix can have higher rank
while its logical marginal is unitary. These observations are necessary
cleanliness tests, not native-versus-ordinary optimality bounds.

The same distinction limits a claimed ready-identity midpoint marker. In a
closed prefix with no extra entropy recipient, a $d$-dimensional logical code
and rank-$r$ warm support have a $dr$-dimensional unitary image. A projector
that accepts that entire image with certainty must contain it; a rank-$d$
cold projector cannot do so when $r>1$. On maximally mixed logical input its
mean cold-projector acceptance is at most $\|\tau\|_\infty$, since the
initial state is bounded by $\|\tau\|_\infty I/d$. Count every helper and
entropy recipient in this rank statement. Real cooling or measurement/reset
escapes its closed-unitary premise and retains its preparation cost.
Warm occupation may itself be the fault to detect: rejecting it is a valid
ordinary policy, with its changed unknown-data map and acceptance charged.
The rank argument only excludes calling that rejection ready-identity on the
whole warm reference service.

### A reference-complete total-excitation cutoff

For a declared full five-oscillator RWA model, write $H/\hbar=H_0+V$,
$N=\sum_j a_j^\dagger a_j$, $[H_0,N]=0$, and
$V(t)=\sum_j[\xi_j(t)a_j^\dagger+\xi_j(t)^*a_j]$ in angular-frequency
units. All Duffing drift and physical exchange edges stay in $H_0$.
Let $P_K=1_{N\le K}$, $\Pi_K=1_{N=K}$ and $Q_K=I-P_K$.
The finite basis has $\binom{K+5}{5}$ states. Unlike a rectangular per-mode
qutrit cube, this cut has no exchange boundary: only the linear drive raises
total number across it.

Optionally include specified vacuum Markov loss operators $L_\mu$ lowering
total number with $[L_\mu^\dagger L_\mu,N]=0$. Bare oscillator loss is one
declared example, not a bath law inferred from the measured lifetimes.
Compare the full model with the full-space Hamiltonian
$H_0+V-A_K-A_K^\dagger$, keeping the same loss operators, where

$$
A_K=Q_KVP_K=\Bigl(\sum_j\xi_j a_j^\dagger\Bigr)\Pi_K,
\qquad
A_K^\dagger A_K\le (K+1)\|\xi\|_2^2\Pi_K.
$$

The inequality follows by rotating the driven combination into one normalized
collective mode $b$, with $b^\dagger b\le N$. Starting inside $P_K$, the
comparison evolution stays there, and its restriction is exactly the finite
Lindblad evolution with $P_KHP_K$ and $P_KL_\mu P_K$. In particular
$L_\mu P_K=P_KL_\mu P_K$, so its finite anticommutator has no omitted upward
loss term. For its state $\sigma_K$, the generator residual has half trace
norm
$\|A_K\sigma_K\|_1\le\sqrt{\operatorname{Tr}(A_K^\dagger A_K\sigma_K)}$.
Duhamel and contraction therefore bound the endpoint system/reference error
by the integral of this square root.

For any fixed preparation/code channel $\mathcal E$ from the
eight-dimensional logical input with output supported in $P_K$, let $\mathcal T_K(t)$ be that finite
evolution. Its positive logical effect
$B_K(t)=\mathcal E^\dagger\mathcal T_K(t)^\dagger(A_K^\dagger A_K)$
gives the following half-diamond bound on the induced logical-input channels:

$$
\delta_K\le\min\left\{1,\int_0^T
       \sqrt{\lambda_{\max}(B_K(t))}\,dt\right\}
\le\min\left\{1,\int_0^T\sqrt{8(K+1)}\|\xi(t)\|_2
                   \sqrt{\bar p_K(t)}\,dt\right\},
$$

where $\bar p_K(t)$ is the boundary population evolved from
$\mathcal E(I_8/8)$. The second inequality uses positivity and
$\lambda_{\max}(\mathcal E^\dagger\mathcal T_K^\dagger\Pi_K)
\le\operatorname{Tr}(\mathcal E^\dagger\mathcal T_K^\dagger\Pi_K)
=8\bar p_K$. An arbitrary passive reference does not change these
physical-only expectations. Maximizing separately at each time is a safe
bound, without assuming one input maximizes every time.

Retained emitted-field records require a further specified common dilation,
not just equality of reduced dissipators. For identical input vacuum fields,
$L_\mu$, field scattering and controller inputs, their common unitary Markov
dilations differ only by $A_K+A_K^\dagger$. Joint-vector Duhamel on any
purification gives
$\|\Psi(T)-\Psi_K(T)\|\le\int\sqrt{\operatorname{Tr}
(A_K^\dagger A_K\sigma_K)}dt$: the equal field terms cancel and
$\Psi_K\in P_K\otimes I_{\rm field}$. Half trace distance is at most that
vector distance. Thus the same bound covers the specified common system/field
output and subsequent record measurements. A reduced endpoint-state proof
alone cannot certify a refined bath-record instrument.

One can first work in a larger finite total-number space. With initial
support $N\le n_0$, $K\ge n_0$, drive area $\Lambda=\int\|\xi(t)\|_2dt$ and
$m=K-n_0+1$, the drift/loss propagator never raises that support. A drive
commutator on support $N\le n$ has trace norm at most
$4\|\xi\|_2\sqrt{n+1}$ times the input trace norm. The two Dyson expansions
agree through order $m-1$, giving the uniform reduced-channel consistency
bound

$$
\delta_K\le\min\left\{1,\sum_{k\ge m}
 \frac{(4\Lambda)^k}{k!}\sqrt{\frac{(n_0+k)!}{n_0!}}\right\}.
$$

Its successive ratio $4\Lambda\sqrt{n_0+k+1}/(k+1)$ eventually decreases
below one, so the series converges and supplies the cutoff limit on finite
number inputs. Drive area alone is often much too loose for a useful cutoff;
the actual boundary integral keeps detuning and pulse selectivity. This
mathematical oscillator-model limit is not a physical high-level transmon
completion.

If the full initial source is a data-independent classical mixture with
omitted auxiliary-sector weight $\epsilon$, its complete-channel error is
at most $\epsilon+(1-\epsilon)\delta_K$. A coherently retained source
purifier instead generally needs a $\sqrt\epsilon$ projection bound; it
cannot be dephased for free. Neither initial tail is a receiver herald.
A sampled boundary curve, ordinary solver tolerance or agreement at two
cutoffs is diagnostic only. A validated continuous residual or propagator
bound must control the time integral and finite-solver error. Heating,
counterrotating drives, number-changing selectors and actual frequency-dependent
baths need their own residuals or model, and cannot inherit this certificate
unchanged. Complete common postprocessing contracts the resulting bound;
rare accepted fidelities require a separate denominator estimate.

The next calculation first calibrates the required cold $W$ in the joint
device and fixes its bare or dressed preparation/readout frame, then forms
component-resolved warm maps under the same physical clock. Both ordinary
pulse orders, supplied local frames, pulse shaping, paid shared-$B$ checks,
midpoint markers, preparation/cooling and accessible records remain admitted.
A missing native selector is not supplied by classical pumping, nor is an
uncalibrated pulse or small-cutoff calculation evidence of an error-filtering
advantage. Rejected unknown inputs remain retained; time per accepted launch
describes throughput across independently supplied jobs, not free retries of
the same input.

## Finite TIP pulses preserve an idle-error signal, but not a source-like benefit

This is a declared cold effective-model screen, not a full-Duffing device
prediction. It uses two-level data A/B/C and qutrit private couplers u/v,
ideal pulse selection, ideal common-boundary phase operations, local white Markov
data relaxation, ideal final coupler PED and ideal helper operations.
It contains no coupler noise, selector noise, readout backaction or latency.
Both data gates are required, and all fine final flags are retained.

**Physical phase convention.** The source's Eq. 63 displays a traceless
selected two-state block. At its closed-pulse duration that literal matrix
is minus identity in both control sectors, and, with zero dark-state
energy, does not implement CZ. To retain the physical relative phase
specified by source Eqs. 6--9, the active pair uses

$$
 H_q/\hbar=\delta_q|0_Bf\rangle\langle0_Bf|
       +\frac\Omega2(|0_Bf\rangle\langle1_Bg|+\mathrm{h.c.}),\quad
 \delta_q=(-1)^q\frac\pi T,\quad \Omega=\frac{\sqrt3\pi}{T}.
\tag{TI1}
$$

The returned B-excited state acquires $+i$ for control q=0 and
$-i$ for q=1. The endpoint frame $F=S_B^\dagger$ therefore gives
exact CZ. In the 72-dimensional pilot, the idle terms
$\delta_A P_{uf}+\delta_C P_{vf}$ remain in **both** windows; only
the selected u or v drive switches. For equal windows, F is the same
operation at each common boundary on both helper branches. Both ideal schedules return the couplers to g and equal
$W=CZ_{AB}CZ_{BC}$ on all eight logical columns to numerical precision.

The bath is common in chronological time: its data-lowering operators
are $L_j=|0\rangle\langle1|_j$, independent of the order helper.
For a jump of type j at actual time t, use each schedule's propagators
to form $K_{r,j}(t)=U_r(t_f,t)L_jU_r(t,0)V$, including the endpoint
frames, where V embeds clean couplers. The native operators are
$(K_{uv,j}\pm K_{vu,j})/2$. The *same* emitted-record type and time
are paired; records are never swapped by module name. This white-bath
model does not determine a frequency-resolved driven device dilation.

**Equal-window result.** Define all-launch Bell-good weight for target W
by $|\operatorname{tr}(W^\dagger K)|^2/64$, and bad weight on a
retained branch by $\operatorname{tr}(K^\dagger K)/8$ minus that
good weight. Every single data-relaxation history has zero target trace.
The table gives integrated weights in units $\gamma_j T$:

| Fine output or rule | A or C relaxation | B relaxation |
| --- | ---: | ---: |
| All native outcomes | 1 | 5/8 |
| Native order +, both couplers g | 183/256 | 15/32 |
| Native order -, both couplers g | 55/256 | 5/32 |
| Coupler excitation, summed over order flags | 9/128 | 0 |
| Ordinary fixed order, both couplers g | 119/128 | 5/8 |
| Ordinary even Z_B parity and both couplers g | 119/128 | 0 |

The ordinary comparator coherently checks Z_B before and after the
two required gates, using the same ideal final PED. Its refined
operators are $(K\pm Z_BKZ_B)/2$. The native plus/gg and ordinary
even/gg branches have the same first-order Bell-good weight,
$1-T(\gamma_A+5\gamma_B/8+\gamma_C)$; their accepted bad weights
are given by the corresponding rows. All discarded flags are paid
rejects. The native acceptance rule improves this restricted bad-weight
comparison only if

$$
24\gamma_B<11(\gamma_A+\gamma_C).
\tag{TI2}
$$

This is a real idle/control-error signal within the surrogate. It also
shows why a shared-B-only calculation was insufficient: the ordinary
Z_B check misses code-closed A/C lowering. However, source-like
$T_{1A}=168\,\mu s,T_{1B}=80\,\mu s$, and illustrative
$T_{1C}=T_{1A}$, fail (TI2). The native accepted bad weight is then
about 30% larger before control/readout overhead. C's lifetime is not
measured by the source and is not a property of the proposed seed.

**Brief exact derivation.** For x=pi t/T and s=sin x, the active
B-excited survival probability is $1-3s^2/4$, whose average is 5/8.
For a control-relaxation jump during its active pulse, the returned
ground-coupler amplitude after F is
$v=e^{ix}[1-s^2/2-is\cos x]$; hence
$|v|^2=1-3s^4/4$ and its average is 23/32.
Summing the two common clock windows gives native plus/gg norm
$5/8+|v|^2/8$, minus/gg norm $(1+|v|^2)/8$, and ordinary
gg norm $1/2+(1+|v|^2)/4$. These integrate to the table.
For B jumps the native plus/minus norms are 3/4 and 1/4 of the
B-survival probability, respectively. The remaining flags complete
the total jump weights; no probability is lost to an omitted outcome.

The table does not rank arbitrary branch-dependent recovery. An available
paid global $Z_AZ_BZ_C$ parity check plus PED rejects all first-order data
relaxation in this model. The selector's actual couplings may enable
stronger ordinary checks, and simultaneous classical drives or optimal
control may shorten the required service. No optimal-control failure is
an ordinary lower bound. The source-like comparison therefore rejects
this particular proposed benefit; it does not certify a hardware ranking.
Private coupler noise and its temporal correlations need a separate
calculation instead of being inferred from this data-relaxation table.

## Coupler-f dephasing: temporal filtering does not rescue the copied-rate case

Use the equal-window, physically framed cold TIP surrogate in the
finite-T1 note, with common chronological bath records and all final
order/PED flags retained. Add independent local Markov jumps
$L_{\phi r}=\sqrt{2\gamma_{\phi r}}P_{rf}$, r=u,v, throughout
the two windows. This is a declared white-noise extension. Shirai
Appendix D/Fig. 12 measures e-f **Hahn echo** and fits a master equation
with this P_f jump; it is not Ramsey. Its fitted Markov model is a
legitimate surrogate premise, but the echo fit does not specify the
short-gate, two-order common-time bath correlation instrument.

For one active pulse, let $p_f(t)=3\sin^2(\pi t/T)/4$. The closed
two-level propagator is a scalar on each selected pair at T. Thus
inserting P_f and returning to coupler ground gives, relative to the
required logical W,

$$
 E_g(t)=\sqrt{2\gamma_\phi}\,p_f(t)P_{B=e}.
\tag{TF1}
$$

It is independent of the control bit: the backward return amplitude is
the conjugate of the forward f amplitude times the clean return phase.
On the maximally entangled logical input, $\operatorname{tr}P_{B=e}/8=1/2$.
Therefore the ordinary accepted single-jump weights for each private
coupler are

$$
 p_j=\int\gamma_\phi p_f^2dt=\frac{27}{128}\gamma_\phi T,
 \qquad q_j=\frac{p_j}{2}=\frac{27}{256}\gamma_\phi T,
 \qquad p_j-q_j=q_j.
\tag{TF2}
$$

The total jump weight is $\int\gamma_\phi p_fdt=3\gamma_\phi T/8$,
and the coupler-f endpoint weight is $21\gamma_\phi T/128$.
The no-jump contribution to Bell-good weight loses the full total
jump weight at first order; it cannot be omitted when comparing q.

In the native two-window schedule each private coupler is active in
only one history at any given clock time. The other history has that
coupler in g and its P_f jump is zero. Both order outcomes therefore
receive half the ordinary accepted ground-coupler single-jump CP
contribution, and half each integrated endpoint weight, with no
relabeling of bath records. For acceptance of order + and both
couplers g, the first-order metrics per private coupler are:

| Rule | Bell-good loss | Accepted bad | Rejected weight |
| --- | ---: | ---: | ---: |
| Ordinary serial Z_B check + PED | 69/256 | 27/256 | 21/128 |
| Native order + + PED | 165/512 | 27/512 | 69/256 |

Entries multiply $\gamma_\phi T$. Z_B checking does not remove
(TF1), which is diagonal. For utility $U_\lambda=q-\lambda\,bad$,
native minus ordinary is
$(\lambda-1)27\gamma_\phi T/512$. At lambda=1 the loss of
Bell-good and reduction of bad exactly cancel; for larger lambda the
white-noise order flag exchanges some unlocated bad weight for a
located reject. This is not an all-outcome or optimal-decoder dominance
claim, and every reject remains part of the resource/service ledger.

Combining both private dephasers with the finite data-T1 result, define
$C=15\gamma_B/32-55(\gamma_A+\gamma_C)/256$ and
$H=27(\gamma_{\phi u}+\gamma_{\phi v})/512$.
The native differences are extra good loss HT and extra bad (C-H)T;
hence $\Delta U_\lambda=-HT-\lambda(C-H)T$.
As a copied-rate **illustration only**, set A=C=168 microseconds,
B=80 microseconds and both private rates to
$1/(26\,\mu s)-1/(64\,\mu s)=0.02283654/\mu s$, using the
source's fitted relation for u and copying it to the unmeasured v.
Then C=0.003301711/us, H=0.002408541/us and C-H=0.000893170/us.
Native is worse for every lambda>=0 even before selector, helper,
readout or recovery costs. Neither C's lifetime nor v's dephasing is
measured by this source; these copied rates are not a device forecast.

Two guards prevent interpreting (TF2) as an order-specific noise cure.
First, a coherent definite-order schedule with branches
[u,v,idle] and [idle,u,v] has the same **accepted ground-coupler**
white-P_f filter in three windows. Its data-T1 exposure includes an
additional window, and its conditional timing/frame controls are paid.
It is a stronger ordinary comparator than serial Z_B alone. This is
not an equality of all rejected data CP maps: the native order can
change whether the other CZ preceded a leaked-coupler history.
No optimal two-window ordinary pulse-path filter has been excluded.

Second, hold a common detuning offset $\epsilon_u P_{uf}+
\epsilon_vP_{vf}$ fixed across both order histories. The accepted
ground-coupler maps of each block are diagonal, and a leaked private
f state cannot return while its drive is off in this cold surrogate.
The two accepted products commute, so their native minus/gg operator
is **exactly zero**, for arbitrary held offsets. Accepted diagonal
error can remain. Any order-minus leaked-coupler mass is already
flagged by PED. Thus the white-jump detection signal depends on the
noise's temporal correlation. It does not follow from a dephasing
time alone. The finite pilot verifies both held-offset and common-time
white-noise cases; an actual joint pulse/bath/readout instrument is
still needed before a positive architecture claim.

## The simplest rectangular selector has a separate exact obstruction
Declare a selected transition with the complete phase embedding
$h(\delta)=\begin{pmatrix}0&\Omega/2\\\Omega/2&\delta\end{pmatrix}$,
dark B-g states of zero energy, $\Omega>0$, and one rectangular pulse
of duration $T$. Its returned phase after $k$ closed cycles is
$\pi k-\delta T/2$. In helper sector 0 the A-conditioned detunings are
$\pm\Delta/2$; in helper sector 1 they are $\chi\pm\Delta/2$, with
the same $\Omega,T$. Require exact active CZ, inactive identity, and
return on both A inputs, allowing local data phases and a helper-only
phase but no extra nonlocal correction.

Let $r$ count active cycles and put $l=\Delta T/(2\pi)$.
The active entangling ratio is $e^{i\pi l}$, so $l$ is an odd integer.
Let $m,n$ count the inactive cycles. Their entangling ratio is
$e^{i\pi(n-m+l)}$; inactive identity makes $m-n$ odd. Setting
$x=\chi/\Delta$, the squared closure equations give

$$
m^2-n^2=2l^2x,\qquad
m^2+n^2-2r^2=\frac{(m^2-n^2)^2}{2l^2}.
\tag{TS1}
$$

The second left side is an integer and the right side has odd numerator
and even denominator, a contradiction. Local Z frames act on both
dark and addressed computational sectors and cancel from the entangling
ratio; they cannot remove it. Thus this exact single-pump design fails.
This is not a device no-go, an approximate-error bound or a speed limit:
shaped/joint pulses, different envelopes, extra levels, static ZZ phases
and paid entangling corrections change the premises. A co-designed
two-window operation need not implement literal active/inactive modules.
Its complete phases, cross-history bath map and costs must be verified
rather than inherited from a classical TIP calibration.


## Physical helper relaxation changes the selected drive

Retain the equal-T cold TIP model and set its other noise to zero for
this calculation. Write $U_0$ for uv, $U_1$ for vu, and $V$ for the
ground-coupler embedding. The helper D starts in $+$, controls those
complete Hamiltonians in its physical 0/1 basis, and is read in X.
Assume the common chronological white jump
$L_D=\sqrt{\gamma_D}|0\rangle\langle1|_D\otimes I$.
For actual emission time t and endpoint coupler record r,

$$
 K_{D,+,r}(t)=K_{D,-,r}(t)
 =\frac{\sqrt{\gamma_D}e^{-\gamma_Dt/2}}2\langle r|
 U_0(2T,t)U_1(t,0)V. \tag{TH1}
$$

The helper decay switches the active physical drive at t. This is the
exact block reduction of the controlled 144-dimensional model, rather
than a late classical record error. Initial-plus and final-X overlaps
supply the two factors $1/\sqrt2$. Summed over both helper outcomes and
all coupler flags, the jump weight is $\gamma_DT$ to first order. The
no-jump plus operator is
$[(1+e^{-\gamma_DT})/2]VW$, with first-order Bell-good loss
$\gamma_DT$; the no-jump minus weight starts at second order.

**First-order moment derivation.** The attenuation in (TH1) changes jump
probabilities only at second order in $\gamma_DT$ in the following table.
For fixed data controls a,c, only
$b=|e_B,g_u,g_v\rangle$, $u=|g_B,f_u,g_v\rangle$ and
$v=|g_B,g_u,f_v\rangle$ participate. The idle diagonal is
$(0,\delta_a,\delta_c)$ and a selected drive couples b/u or b/v.
For $x=\pi t/T$ and $\beta_q=(-1)^q/2$, put

$$
 a_q(t)=e^{-i\beta_qx}(\cos x+i\beta_q\sin x),\qquad
 r(t)=|a_q(t)|^2=1-3\sin^2x/4.
$$

Before the helper factor 1/2, the first-window ground-return amplitude
is $-i(-1)^c a_c(t)a_a(T-t)$; the second is its time reversal.
Relative to W the first is $e=a_c(t)a_a(t)^*$. Averaging a,c gives
$\mathbb E|e|^2=r^2$ and $\mathbb Ee=\eta$, since
$\mathbb E_q a_q=\cos^3(x/2)$ and $\eta=\cos^6(x/2)$.
Initial B-g is dark. For one helper sign the ground norm and target-good
densities are $(1+r^2)/8$ and $(1+\eta)^2/16$.
The elementary averages
$\langle r^2\rangle=59/128$, $\langle\eta\rangle=5/16$ and
$\langle\eta^2\rangle=231/1024$ therefore give, after both windows:

| Single-jump quantity, for each helper sign | Weight per $\gamma_DT$ |
| --- | ---: |
| All coupler records | 1/2 |
| Both couplers g | 187/512 |
| Target Bell-good within gg | 1895/8192 |
| Bell-bad within gg | 1097/8192 |
| u-f only | 69/1024 |
| v-f only | 69/1024 |

All remaining flags vanish in this single-jump model. The two leakage
entries follow from $\langle p_f(1+r)\rangle/8=69/1024$.
Including the no-jump term, accepting only plus/gg gives

$$
 q_N=1-\frac{6297}{8192}\gamma_DT+O((\gamma_DT)^2),\quad
 bad_N=\frac{1097}{8192}\gamma_DT+O((\gamma_DT)^2),\quad
 reject_N=\frac{325}{512}\gamma_DT+O((\gamma_DT)^2).
 \tag{TH2}
$$

**Ideally equivalent ordinary checks occupy different physical noise
bases.** Prepare D in 0, apply CNOT B-to-D before and after the same
D-independent two-gate evolution, and measure Z. A helper decay gives
$K_{odd}=\sqrt{\gamma_D}WP_{B=e}$ and $K_{even}=0$ at every t.
The integrated odd weights are $p=1$, $q=bad=1/2$, in units
$\gamma_DT$. The no-jump even good loss is one. Rejecting odd gives
$(good\ loss,bad,reject)=(1,0,1)$, whereas keeping it gives
$(1/2,1/2,0)$ in these units.

Alternatively prepare D in $+$, use direct $CZ_{DB}$ tags before and
after, and measure X. The same physical decay gives
$K_+=K_-=\sqrt{\gamma_D}WZ_B/2$. Each integrated flag has
$p=bad=1/2$ and $q=0$. Correcting the observed minus flag by $Z_B$
makes that isolated flag fully good; keeping both then gives
$(good\ loss,bad,reject)=(1/2,1/2,0)$. Boundary tags, basis rotations
and the correction remain paid controls.

A physical $Z_D$ phase flip becomes a final helper X-flag flip with
ideal data in the native and direct-CZ encodings; in the CNOT parity
store it becomes data $Z_B$. More explicitly, for
$L_{\phi D}=\sqrt{2\Gamma_D}P_{D=1}$, the native and direct-CZ refined
operators are $K_\pm=\pm\sqrt{\Gamma_D/2}\,W$, while CNOT has
$K_{even}=\sqrt{2\Gamma_D}WP_{B=e}$ and $K_{odd}=0$.
Thus ordinary helper phase noise need not be an unlocated data error.

These are isolated-bath identities. Different hidden faults can share
the same observed helper/coupler flag. Sum their rate-weighted CP maps
before choosing one flag-dependent decoder or acceptance rule; a
helper-only correction is not an oracle for the hidden bath. The
ordinary side may also omit D entirely and use the required gates with
bare PED, incurring no helper noise. For $U_\lambda=q-\lambda bad$,
(TH2)'s isolated-helper differences from CNOT parity reject and parity
keep are respectively
$(1895-1097\lambda)\gamma_DT/8192$ and
$(-2201+2999\lambda)\gamma_DT/8192$. Neither orders the complete
protocols. A full comparison must retain that helper-free alternative,
all actual flags, common decoders and every noise contribution.

## Ordinary helper echo preserves the whole measured check

Let $Z=Z_B$ be a specified Hermitian unitary on the full retained
space, and $C=P_{D=0}\otimes I+P_{D=1}\otimes Z$ the actual boundary
tag. Prepare $+$, apply C, an arbitrary D-independent core, C again,
and read X. Its refined outcome-s operator is
$(K+sZKZ)/2$, $s=\pm1$, for each core Kraus record K.
For held helper detuning $H_\delta=\delta Z_D/2$, insert one
instantaneous $X_D$ between the core's two halves and apply Z to the
output data. If the two noise exposures are $t_1,t_2$ and
$\varphi=\delta(t_1-t_2)$, the corrected operator is

$$
 ZK_s^{echo}=\frac{s}{2}
 [e^{-i\varphi/2}K+s e^{i\varphi/2}ZKZ]. \tag{TE1}
$$

Indeed, the detuning rotations commute with C and every D-independent
core operator, $R(t_2)X_DR(t_1)=X_DR(t_1-t_2)$, and
$CX_D=X_DZC$. The helper X measurement contributes only the scalar
s. When $t_1=t_2$, both CP branches equal the original ideal check,
including their probabilities and arbitrary input/reference correlations.
No measured record is dropped or renormalized. Identical tag durations
place the required noise midpoint at the core's center; equality of
the actual exposures is the premise.

Pay the original two helper basis-rotation pulses and two boundary
tags, the additional midpoint pi pulse and the terminal data phase.
Finite-pulse noise/duration, residual helper coupling, and calibration
must be supplied. Leakage is included only if the tags and terminal
correction implement the same chosen Z on those sectors: a logical
$Z_B$ alone does not specify its physical f/h action. This arbitrary-K
identity requires D isolated from the enclosed core apart from its
detuning. It is not a free echo under the full TIP Hamiltonian.

For a native schedule an X pulse swaps the helper's selected branches.
Restoring the intended histories requires exchanging the complete
after-midpoint conditional propagators. Relabeling pumps alone does
not account for
$X_D\chi n_Dn_BX_D=\chi n_B-\chi n_Dn_B$; its residual need not be
an endpoint phase through noncommuting TIP dynamics. Frequency tracking,
frames or redesigned waveforms could repair this, with joint calibration.
This is a physical-control obligation, rather than an impossibility.

White projector dephasing is different:
$\mathcal D[I-P_{D=1}]=\mathcal D[P_{D=1}]$, so an ideal X echo does
not cancel that Markov generator. The
[short-time transmon study of O'Malley et al.](https://arxiv.org/html/1411.2613v3)
directly resolves gate-scale phase noise that a long Ramsey fit misses,
and compares echo implementations. It supports measuring the relevant
short-time law, rather than transferring one fitted decay time.

The separate [strong-ZZ constituent of Long et al., Appendix B/Table II](https://arxiv.org/html/2103.12305v1)
reports $T_1=76.98/79.71\,\mu s$ and Ramsey
$T_2^*=50.65/17.09\,\mu s$. This is not a measured TIP/helper system.
Converting those Ramsey values to
$\Gamma_D=1/T_2^*-1/(2T_1)$ is an additional exponential white-noise
premise. A real $\chi_{DB}$ selector can make helper emission frequencies
and matrix elements depend on the retained system. The tensor-I jump
in (TH1) is therefore also a premise. A local white lowering operator
with the conditional Hamiltonian retained can itself carry which-frequency
information; frequency-resolved backaction must not be added twice.
Neither a measured $T_1$ nor an ideal endpoint gate specifies the full
joint instrument. Selector drift, all pulse and storage times, readout,
reset and recovery latency remain part of the next physical comparison.

The [exact finite guard](../checks/architecture/tip_helper_guards.py)
checks rational moment ingredients for the data, coupler and helper
ledgers, isolated-helper utility arithmetic, and finite matrix-unit echo
operator identities. The propagator reduction, continuous-time integrals,
general echo identity and physical bath/control premises remain analytic.
It is not a numerical propagation of the full Hamiltonian or a new
architecture advantage.

<a id="nr-r06-tip-recovery"></a>

## One measured flag can benefit from a non-Pauli ordinary recovery

In the equal-T cold model, consider the **observed** direct-CZ-helper
minus/gg flag after summing every hidden bath and emission time. Keep
identity on the ideal plus/gg branch. Put $\gamma=\gamma_D$,
$\Gamma=\Gamma_D$ and $O=5\gamma_B/8$. Per unit T, the minus/gg map
relative to W contains $\Gamma\operatorname{id}$,
$(\gamma/2)\operatorname{Ad}_{Z_B}$, and the data-B lowering channel
of total norm O. The latter has output B=0 and uniform A/C population.
No A/C relaxation or private-f dephasing enters this flag in this model.

Apply the same accepted recovery operator to the whole flag,
$F=aP_{B=0}+bP_{B=1}$, with $0\le a,b\le1$.
The complementary operator $\sqrt{I-F^\dagger F}$ supplies its rejected
outcome. This is a quantum instrument with a new acceptance record,
rather than a hidden-fault correction or classical reweighting of data.
For $S=\Gamma+\gamma/2$ and $D=\Gamma-\gamma/2$ its accepted norm and
target-good coefficients are

$$
 p_F=S(a^2+b^2)/2+Oa^2,\qquad
 q_F=[S(a^2+b^2)+2Dab]/4. \tag{TR2}
$$

The B-lowering term has zero target trace under this diagonal filter.
Its contribution to $U_\lambda=q-\lambda bad$ is therefore

$$
 g_\lambda=(1-\lambda)S(a^2+b^2)/4
 +(1+\lambda)Dab/2-\lambda Oa^2. \tag{TR3}
$$

At $\lambda=1$ and $0<D<2O$, this family is optimized by
$b=1$, $a=D/(2O)$, giving $g_1=D^2/(4O)>0$.
For the explicitly hypothetical Q1 white-noise rates
$\gamma=1/(76.98\,\mu s)$,
$\Gamma=1/(50.65\,\mu s)-\gamma/2$, and
$\gamma_B=1/(80\,\mu s)$, this gives $a\simeq0.432189$ and an
extra utility $0.00145927\,T/\mu s$. Here even identity has
$g_1=D-O<0$ and every Pauli/reject choice is no better than rejection.
Thus a restriction to Pauli corrections can miss a feasible ordinary
improvement. The separate constituent's Ramsey value does not establish
the assumed white bath, and the filter's control, measurement, erasure
record and duration still need a physical implementation.

**Reference support gives a recovery bound.** Suppose a measured flag has
$K_h=K_hP_{B=1}$ for every hidden history. Its joint output/reference state
then has reference B=1 support, which output-only CP recovery preserves.
The target maximally entangled vector has squared norm 1/2 in this
subspace. Hence $q\le p/2$ after **any** trace-nonincreasing CP recovery,
so $g_\lambda\le0$ for $\lambda\ge1$. This applies to all excited-coupler
flags and ordinary CNOT-store odd/gg in the cold model. Full-Duffing
return channels and readout backaction are outside this support argument.

**For this direct-CZ flag the quadratic is the full recovery optimum
when $D>0$ and $\lambda\ge1$.** Each fine operator has a fixed data
bit-XOR shift, so the summed flag map is covariant under all diagonal
Pauli Z strings. W is diagonal. Twirling a recovery by this symmetry
preserves q, p and trace-nonincreasing feasibility. Its Choi matrix splits
into eight positive blocks labelled output XOR input. Blocks outside the
diagonal block have good weight only from B lowering, to which the
reference-support bound applies; helper I/Z terms only add norm there.
They may be discarded for $\lambda\ge1$.

In the diagonal block the good coefficients are
$[\Gamma+(\gamma/2)z_i z_j]/64$, $z_i=(-1)^{B_i}$, and are nonnegative
when $D>0$. For fixed Choi diagonal, positivity bounds each off-diagonal
entry by $\sqrt{d_i d_j}$; one aligned rank-one filter attains them all.
For fixed diagonal weight in each B sector, Cauchy--Schwarz makes the
A/C amplitudes equal. The norm penalty depends only on those sector
weights, since B lowering has uniform A/C population. This reduces the
entire trace-nonincreasing CP optimization to (TR3).

For example, at $\lambda=5$ its matrix is

$$
 M=\begin{pmatrix}-S-5O&3D/2\\3D/2&-S\end{pmatrix}.
$$

The Q1 values are exactly $S=20/1013$, $D=20/1013-50/3849$ and
$O=1/128$, per microsecond. Negative diagonal and
$\det M=S(S+5O)-9D^2/4>0$ prove $g_5\le0$, attained by erasing this
flag. A stronger recovery changes the $\lambda=1$ comparison without
making this flag useful at every error penalty. This is an optimization
for the stated observed flag and encoding, not a global ordinary control
optimum. Different helper codewords, pulse schedules, additional checks
and their physical costs remain part of the architecture comparison.

### Weak boundary tags with arbitrary common helper rotations

This replaces the static-only scope of the weak-codeword bound. It is a
fixed-lambda first-order statement in the same declared cold TIP model.
A B-controlled helper tag C=sum_b P_b tensor U_b prepares arbitrary pure,
possibly nonorthogonal complex codewords d_b=U_b|ready>. Its inverse is
applied after the entire D-independent two-gate body of duration 2T.
During that body permit any prescribed common helper-only unitary R(t),
with R(0)=I, and undo R(2T) before untagging. An independently established
equivalent terminal frame/readout convention is also sufficient. The
noiseless ready/gg flag must preserve W and use identity. Every rare
measured helper/coupler flag may use arbitrary trace-nonincreasing CP
recovery, completed with a retained reject outcome. The recovery sees
neither hidden bath labels nor jump times.

The physical local-white helper jumps remain L_1=sqrt(gamma)|0><1| and
L_phi=sqrt(2 Gamma)P_D1 in their fixed physical basis, including while R(t)
is applied. The data/coupler Hamiltonian and baths are independent of D.
Exact factorization also assumes initially independent data/coupler and
helper environments with independent generators, or a supplied tensor-
factorized joint dilation. This is material; no retained-chi isolation is supplied.

Here is the full fine-operator convention, retaining all data/coupler
outputs and any untouched reference. Let K_h be any chronological fine
operator of the D-independent body, and V_j any chronological helper
fine operator including the physical R drive, all no-jump survival
operators and that helper bath record. After the terminal inverse put
Q_j=R(2T)^dagger V_j. The exact measured helper-f operator is

 K_(f,h,j)=sum_(b',b) P_b' K_h P_b
                <f|U_b'^dagger Q_j U_b|ready>.                 (D1)

This is a tensor-factorization identity, also valid before projecting a
coupler flag. For example the exact helper record with jumps at t_1<...<t_m
uses V_j=N(2T,t_m)L_m N(t_m,t_(m-1))L_(m-1)...
N(t_2,t_1)L_1 N(t_1,0), with every intervening no-jump factor present, where
N(t_2,t_1)=time-ordered exp integral[-i H_D(t)-sum_L L^dagger L/2]dt.
Thus (D1) does not omit pre-jump survival or swap bath records by gate name.

To first order a helper jump at t has Q_L(t)=R(t)^dagger L R(t), while
Q_0=I-(1/2)integral R(t)^dagger sum_L L^dagger L R(t)dt. With no system
fault, the clean completed W preserves B and returns both couplers, so

 K_(f,L)(t)=W sum_b P_b
       <f|U_b^dagger R(t)^dagger L R(t)U_b|ready>.              (D2)

All leading jump amplitudes in (D2) are to be squared and integrated in
the same actual clock; exact finite-rate trajectories instead use (D1).
No-jump good loss is retained. Rare no-jump amplitudes are first order
but their probabilities are second order. With no helper fault, (D1)
reduces exactly to sum P_b' K_h P_b <f|U_b'^dagger U_b|ready>, so every
system-bath flag map is unchanged by any common R(t).

Write R(t)d_b=c_b(t)|0>+s_b(t)|1>, p_b(t)=|s_b(t)|^2 and
t_b(t)=c_b(t)^*s_b(t). Common unitaries preserve the distinguishability

 a=1-|<d_0|d_1>|^2=|t_0(t)-t_1(t)|^2+[p_0(t)-p_1(t)]^2.

The mandatory ready-flag helper bad-weight density is exactly, to first
order, gamma|t_0-t_1|^2/4+Gamma(p_0-p_1)^2/2. If Gamma>=gamma/2 it is at
least gamma*a/4 at every time, hence at least gamma*a*T/2 over the full
2T clock. For the helper-only instrument completed with the same chosen
recovery, q+bad=p_accepted<=1; good loss is therefore at least accepted
bad, which includes the mandatory ready component. Its utility cost is
at least (lambda+1)gamma*a*T/2, whatever the rare-flag recovery.

The system-fault comparison is unchanged. The accepted B-lowering norm
is O*T, O=5 gamma_B/8. Boundary tags send fraction a to the rare helper
flag and leave fraction 1-a mandatory. Each such history has original/
reference B=e; output recovery cannot change that reference support, so
q<=p/2 for any CP recovery. For lambda>=1 rare lowering utility is
nonpositive and moving it out of the mandatory flag can improve utility
by at most lambda*O*a*T. Accepted B-preserving faults are unchanged.
Excited-coupler flags also have reference B=e and nonpositive recoverable
utility. Apply these bounds to the same fixed recovery after summing
hidden histories, then use first-order additivity and maximize 0<=a<=1:

 U_ordinary-U_bare <= max[0,lambda O-(lambda+1)gamma/2] T.       (W1)

Thus W1 covers all static pure weak boundary codewords, every common
unconditional R(t)/echo trajectory, and arbitrary rare-flag TNI CP
recovery within this full-interval D-independent body. It does not say
bare PED is optimal. For the already audited Q1 nominal-white rates at
lambda=5, the unchanged exact arithmetic is

 gamma_A=gamma_C=1/168, gamma_B=1/80,
 gamma_phi,u=gamma_phi,v=1/26-1/64,
 gamma=50/3849, Gamma=20/1013-25/3849, all per us;
 W1 <=15*T/164224 per us;
 feasible native plus/gg minus bare
     =373165517*T/1453311455232 per us;
 feasible native minus every member of this enlarged family
     >=240421997*T/1453311455232 per us
      =0.0001654304699*T/us.                                 (W2)

The last number would give only 2.32e-5 utility units at illustrative
T=0.14 us before higher orders or overhead. It is not a finite-rate
positive bound or an architecture gain. The source 140 ns waveform is
not transferred; C/v rates are copied and Gamma is an assumed exponential
white subtraction from a separate constituent Ramsey T2*, not a measured
TIP/helper bath. Real retained chi, system-resolved helper emissions,
selector activation, finite boundary-tag/terminal-frame/control costs,
readout/recovery latency, and stronger ordinary schedules remain open.
In particular this proof does not cover data- or record-conditional
intermediate retagging, time-varying codeword overlap, measurement/reset, new error-
correcting ancillas, or a general dynamic-control converse. A physical
common R(t) must be paid; it has not been compiled through retained chi.

<a id="nr-r06-tip-moving-encoding"></a>

### A stronger moving encoding changes the ideal comparison

W1/W2 above remain valid for fixed boundary tags, common helper rotations
and the D-independent body they specify. The following construction
admits the stronger encoded-Hamiltonian service written explicitly below.
Even a constant nontrivial encoding conjugates the physical exchange
drives, so this is a different control resource. It beats the earlier
feasible native-plus rule in that enlarged mathematical model; it neither
beats every native decoder nor establishes an available physical protocol.

This concerns a mathematically supplied encoded Hamiltonian, not a
compiled physical TIP/helper port. Let H_0(t) be the full equal-T cold
two-TIP body, V(t)=U_0(t,0), and F=U_0(2T,0). Let E inject the d=8
logical A/B/C space into the couplers-ready space, Q=EE^dagger, and
F E=E W. Occupied couplers remain retained outside Q.
Take C(t)=P_B0 tensor I_D+P_B1 tensor X_D during selected intervals,
and C(t)=I outside them, with C(0)=C(2T)=I. The admitted physical
Hamiltonian is C(H_0 tensor I)C^dagger+i dot(C)C^dagger. In its moving
frame the clean body is exactly H_0 and the fixed physical jumps become
tilde(L)(t)=C(t)^dagger L C(t). The boundary steps below mean exact
controlled-X kicks; smooth finite interpolations are discussed at the end.

For any helper outcome f and measured final coupler flag z, the full
leading one-jump operator, valid also on arbitrary input/reference, is

```text
K_(f,z,L)(t)=P_z F <f|V(t)^dagger tilde(L)(t)V(t)|0>_D E. (M1)
```

The reported p,q,bad and utility coefficients specifically use the
d=8 maximally-entangled Choi/Bell input, not arbitrary input averages:
p=Tr(K^dagger K)/8 and q=|Tr[(E W)^dagger K]|^2/64 for the kept
ready/gg map, with bad=p-q. All other observed outcomes here are rejected.
Project a final coupler flag only after forming the full operator. With A=sum L^dagger L,
the no-jump interaction-picture operator is
I-(1/2)integral V^dagger C^dagger A C V dt to first order. Exact finite-
rate records instead require chronological no-jump propagators between
every physical jump. Independent initially factorized system/helper baths
are assumed; no hidden bath/time labels enter the decision rule.

For each pulse at internal time u, the source-normalized closed two-level
block has ready-hub population

```text
r(u)=1-(3/4)sin^2(pi u/T)=5/8+(3/8)cos(2pi u/T).
```

The exact ready compression is E^dagger V^dagger P_B1 V E=r P_B1,
identifying the right-side P_B1 on the logical code. This remains
true in pulse 2 because pulse 1 has completed its diagonal target gate.
For a general conditional pair U_b(t), helper-ready amplitudes l_b give
J_ready,gg=W[l_0 I+(l_1-l_0)r P_B1]. Consequently the mandatory bad
density is r^2[gamma|Delta t|^2/4+Gamma(Delta p)^2/2], rather than the
unweighted expression in the common-R proof. This observation alone
does not neglect the rejected coupler outcomes; they are counted next.

Start D in 0. In each pulse turn the moving CNOT encoding ON only for
u/T in [1/3,2/3], and keep it OFF otherwise. Keep the actual ready/gg
outcome with identity; reject all D=1 and every excited-coupler outcome.
These are observed flags; there is no hidden-fault decoder. During ON,

```text
C^dagger sigma_D^- C=P_B0 tensor sigma_D^-+P_B1 tensor sigma_D^+,
C^dagger P_D1 C=P_B0 tensor P_D1+P_B1 tensor P_D0,
C^dagger sigma_B^- C=sigma_B^- tensor X_D.
```

Thus every physical helper-T1 jump and every B-T1 jump is flagged D=1.
All A/C lowering and private-coupler P_f jumps commute with C and retain
their bare-PED maps. With L_D1=sqrt(gamma)sigma_D^- and
L_Dphi=sqrt(2 Gamma)P_D1, the ON helper outcomes are exactly:

 * T1: total jump norm gamma*r/2, all D=1 and rejected. Its gg norm is
   gamma*r^2/2; the rest is excited couplers and also rejected.
 * phi: total jump norm Gamma*r. Ready/gg has operator
   sqrt(2 Gamma) r W P_B1, p=Gamma*r^2, q=bad=Gamma*r^2/2. The remaining
   Gamma*r(1-r) is excited couplers and rejected.
 * helper no-jump good loss is S*r, S=gamma/2+Gamma, per unit clock.

These full outcomes sum to total helper jump norm S*r; no-jump good loss
is counted, so the resulting helper utility cost at lambda>=1 is

```text
S*r+(lambda-1)Gamma*r^2/2.                              (M2)
```

B-lowering jump norm is gamma_B*r/2, with zero target-good component.
During ON it moves from the compulsory bare flag to D=1, improving
utility by lambda*gamma_B*r/2. Outside ON helper 0 is dark to both helper
jumps and all maps agree with bare PED. First-order contributions add
under this single fixed flag rule. Therefore the exact net gain per T
for the two central-third windows is

```text
G=2[A R_1-B R_2],
A=lambda*gamma_B/2-S, B=(lambda-1)Gamma/2,
R_1=5/24-3sqrt(3)/(16pi),
R_2=59/384-111sqrt(3)/(512pi).                          (M3)
```

Use the same hypothetical Q1 white rates as W2 and lambda=5:
gamma_B=1/80, gamma=50/3849, Gamma=20/1013-25/3849.
Then A=1/32-20/1013, B=40/1013-50/3849 and G is approximately
0.0006073820595 per us. The all-rational replay certifies bounds on
sqrt(3)/pi that establish G greater than both the static W1 upper bound
15/164224 and the known feasible native-plus excess
373165517/1453311455232 over bare PED. Thus unweighted W1/W2 cannot be
extended to these B-conditioned moving paths, even after paying every
helper/coupler rejected outcome in the first-order utility. This does
not establish dominance over all native decoders or actual hardware.

A short exact certificate uses sqrt(3)>433/250 and pi<22/7, hence
sqrt(3)/pi>3031/5500. The coefficient of sqrt(3)/pi in G is positive.
It gives G>9975181247/16469532288000 and a strict excess over the known
feasible native-plus witness of 2091658216283/5994909752832000, about
0.0003489057 per us. The pi bound follows directly from the positive
integral integral_0^1 x^4(1-x)^4/(1+x^2)dx=22/7-pi.

The discontinuous limiting path can be replaced by finite smooth
controlled-X transitions, still using the supplied exact encoded H.
For example U_0=I, U_1(s)=exp[-i(pi s/2)(X-I)] interpolates I to X,
with p=sin^2(pi s/2). Under the same fixed reject rule its exact net
first-order density relative to bare is

```text
A*r*p-(lambda-1)r^2[gamma*p(1-p)/4+Gamma*p^2/2].
```

All rare helper/coupler jump operators still have original-reference
B=e support; ready/gg helper q equals bad as displayed in this formula.
The sum of affected squared jump-operator norms is bounded by
M=gamma+2Gamma+gamma_B.
For a completed fixed decoder the utility effect operator has norm at
most lambda (lambda>=1), while ||D[L]||_(1->1)<=2||L||^2. Replacing the
step path on total clock measure epsilon changes its first-order utility
by at most 4 lambda M epsilon. The strict M3 margin therefore survives
some positive epsilon, proving a smooth finite-H mathematical example.
This continuity argument supplies no useful amplitude, bandwidth,
calibration or fidelity budget; its narrow transitions may be physically
infeasible. Transforming the TIP exchange into the encoded three-body
coupling and producing the derivative controlled drive are charged new
ports, not ordinary free helper rotations or the measured TIP pulse.
Retained chi and frequency-resolved baths remain uncompiled. The result
is a sharp conditional comparator counterexample and a physical-control
hurdle, not an architecture advantage or a source device prediction.

<a id="nr-r06-tip-moving-controls"></a>

### Physical controls required by the moving encoding

Algebra in the declared cold star, not a device no-go or a
minimum-time theorem. The canonical result owner is unchanged.

#### Exact transformation and orientation

Use star-first tensor order and n_B=P_b, with P_0=I_star-P_b. The star
states are b=|B1,u_g,v_g>, u=|B0,u_f,v_g> and
v=|B0,u_g,v_f>; adding the dark B0 ready state changes none of the
following identities. Let

```text
C(t)=P_0 tensor U_0(t)+P_b tensor U_1(t),
h_b^C(t)=i dot(U_b)(t) U_b(t)^dagger.
```

For the helper-independent reference Hamiltonian

```text
H_ref=H_aux tensor I_D
      +(1/2)sum_j[p_j |j><b|+p_j^* |b><j|] tensor I_D,
```

H_aux commutes with P_b; in the declared cold star it is the diagonal
matrix diag(0,delta_a,delta_c). This hypothesis is needed below.

the exact moving-encoding Hamiltonian is

```text
H_enc=C H_ref C^dagger+i dot(C) C^dagger
     =H_aux tensor I_D
      +(1/2)sum_j[
           p_j |j><b| tensor U_0 U_1^dagger
          +p_j^* |b><j| tensor U_1 U_0^dagger]
      +P_0 tensor h_0^C+P_b tensor h_1^C.                 (MC1)
```

The lower-edge |j><b| orientation is U_0 U_1^dagger, not its adjoint.
Both h_b^C are Hermitian.

If instead the reference already includes the retained number-number
term chi P_b tensor n_D, its transformed contribution is

```text
chi P_b tensor U_1 n_D U_1^dagger.                        (MC2)
```

A common helper term I_star tensor h_D in that reference transforms to
sum_b P_b tensor U_b h_D U_b^dagger. These transformed diagonal terms
do not generate or cancel the helper-changing b<->j edge.

#### What the declared common-pump controls can supply immediately

The admitted laboratory control family is

```text
H_lab=H_aux tensor I_D+chi P_b tensor n_D
      +(1/2)sum_j[p'_j |j><b|+p'^*_j |b><j|] tensor I_D
      +I_star tensor h_D(t),                             (MC3)
```

with any extra paid diagonal frames stated separately. Allowing an
arbitrary common Hermitian h_D is already more generous than one fixed
helper-drive quadrature.

At any instant with p_j nonzero, exact equality of MC1 and MC3 requires

```text
p'_j I_D=p_j U_0 U_1^dagger.                              (MC4)
```

Hence U_0 U_1^dagger must be a scalar phase times I_D. The prepared
helper codewords then differ only by phase and have zero
distinguishability a=1-|<d_0|d_1>|^2. For a>0, the missing operator
directions are genuine conditional transitions changing both the
star state and D. The derivative term, fixed chi interaction and
unconditional helper rotations are star-block-diagonal; no choice of
their instantaneous coefficients repairs MC4.

The diagonal matching requirement is separate. For the helper-free
reference, and with no additional B-local scalar frame, it is

```text
h_0^C=h_D, h_1^C=h_D+chi n_D.                             (MC5)
```

An independently supplied B-local phase frame can relax the scalar
part of this equation, but not its traceless conditional part.
If the reference includes retained chi, MC2 must also be included
before making that comparison. A prescribed pair of arbitrary U_b(t)
therefore does not follow merely from a common helper drive.

These are instantaneous linear-span statements. They do not exclude
finite pulse compilation, average-Hamiltonian synthesis or other
controls that supply the missing conditional edges. Nor do they
provide a gate-time lower bound.

#### Exact nontrivial fixture

Take U_0=I and

```text
U_1=[[3/5,-4/5],[4/5,3/5]], a=16/25.
```

At unit lower pump p_u=1,

```text
<u,D1|H_enc|b,D0>=-2/5.                                  (MC6)
```

Every term in the complex linear span of common scalar u/v pumps,
arbitrary common helper matrices, number-number interaction and even
arbitrary scalar star diagonals has this entry zero. The included
[control guard](../checks/architecture/tip_encoding_control_guards.py) directly conjugates the six-dimensional rational
matrix and verifies MC1, MC2 and this separating matrix element. It
checks 12 generous laboratory span generators; conditional derivative
blocks also have zero separating entry. This is an exact matrix
identity, not evidence about a measured transmon.

#### Full number sectors and noisy compilation

The equality n_B=P_b is a declared-star property. In a full Duffing
model, physical n_B has eigenvalues 0,1,2,... . A moving code must be
defined on every admitted number sector, including B-f, with
C_full=sum_m P_m tensor U_m. An edge |n><m| then acquires
U_n U_m^dagger; the derivative is sum_m P_m tensor i dot(U_m)U_m^dagger,
and the retained interaction becomes
chi sum_m m P_m tensor U_m n_D U_m^dagger. Granting only computational
U_0/U_1 leaves a multilevel return path unspecified.

Finite known control sequences can create effective directions absent
from the instantaneous span. Their actual durations, pump caps,
carrier phases, ramps, leakage and conditional B/f sectors must be
included. The existing slow clean retained-chi body construction does
not supply this arbitrary moving-encoding service.

Finally, equality or a norm bound for a compiled clean propagator is
insufficient for the moving-encoding noise calculation. The physical
helper jump during every compiler segment and control pulse must be
transported through the actual trajectory, with no-jump survival and
all coupler/helper records retained. Fast conjugation or toggling can
change the effective jump basis or bath spectrum. A clean C H Cdagger
simulation alone does not preserve the desired fixed physical-white
noise instrument.

#### Consequence for the comparison

A bound or candidate protocol based on current physical-B occupancy
may use MC1 as an explicit control relaxation. It must not silently
claim that common coupler pumps, retained chi and an unconditional
helper drive realize it. The next physical deliverable is either a
measured/specified conditional b<->u/v helper-matrix service or a
finite noisy compiler with its full clock and off-sector completion.
Both native and ordinary implementations should receive any such
service once admitted.

#### Central-third candidate: the exact missing service

For the proposed on/off path U_0=I and U_1=X_D in each pulse's central
third, MC1 requires the active b-to-j pump to carry X_D throughout that
interval. The derivative vanishes inside each constant region but has
ideal controlled-X boundary kicks. A smooth replacement
U_1(s)=exp[-i pi s (X_D-I_D)/2] has the conditional derivative

```text
h_1^C=(pi dot(s)/2)(X_D-I_D), h_0^C=0.                   (MC7)
```

The smooth derivative, the helper-matrix pump and the retained-chi
compensation are separate required terms. Specifying a CNOT endpoint
alone supplies none of the complete noisy continuous service.

A common global helper basis rotation leaves every scalar pump
edge tensor I_D unchanged. It can rotate the number-number interaction
and can help finite Lie/average-Hamiltonian synthesis, but cannot repair
MC4 as an instantaneous laboratory operator identity. Conversely, a
qualified D-resolved pump port could supply an edge proportional to Z_D
by opposite physical drive phases in its two sectors; a paid global
helper conjugation could turn that into X_D. All off-resonant responses,
retained-chi terms, helper rotations and their noise still require a
common model. Any native control port independently supplied in this way
is also admitted to the ordinary comparator.

The required service must hold on all reachable D and star sectors,
including sectors reached immediately after a helper jump. A calibration
on only the clean D=0 ready trajectory cannot establish this contract.

#### Why an endpoint conjugation does not certify the noise path

For a constant encoded interval, the clean target is
C exp(-i H_ref tau) C^dagger. Its straightforward chronological
implementation is C^dagger, an unencoded H_ref interval, then C.
Applied to an initially encoded state, it removes the encoding throughout
the bulk interval. It has the desired endpoint, but the fixed physical
helper jumps occur along a different trajectory. The moving-code
calculation instead requires the transported jump C^dagger L_D C
during the encoded bulk interval. These two statements must not be
identified by clean gate equivalence.

An alternative noisy compiler may still improve the ordinary endpoint,
but its own no-jump survival, coupler rejects, all helper flags and
reference maps must be evaluated. A clean propagator error alone does not
bound the difference in those physical instruments without an additional
noise/dilation estimate. This is a limitation on inference, not a proof
that the service cannot be built.

#### Primary-source control and timing boundary

[Shirai et al.](https://arxiv.org/html/2511.01260v2), Eqs. (1)-(3),
describe a coupled-Duffing device and a classical linear coupler drive.
The demonstrated TIP pulse uses shaped 20-ns edges and a 140-ns gate.
It does not supply an added helper, the X_D-carrying transfer edge above
or an unconditional helper-drive calibration. Its coupler-pump amplitude
cannot be relabelled as a helper-control amplitude or a minimum switching
time.

[Long et al.](https://arxiv.org/html/2103.12305v1), Sec. III and IV,
supply a separate dressed strong-ZZ device and composite unconditional
single-qubit controls. The 9.29-MHz splitting and the free-evolution CZ
clock do not specify the TIP-compatible multilevel port or the
unreported local composite-pulse durations. Dressing, off-sector
transitions and driven bath couplings need one common-device model.
The existing finite clean star-body construction is an allowed building
block, not a compiler for this arbitrary moving-code service.

Thus the current physical deliverable is a finite pulse schedule or
specified interaction implementing MC1 and the boundary/smooth controls,
including its complete retained-chi and off-sector evolution. Count
pump blanking, all auxiliary drift while blanked, ramps and settling,
helper rotations, phase/frame corrections, readout/recovery and reset.
Source pulse shapes alone supply no lower bound on the best such clock.

#### A sufficient robust comparison, not a device error threshold

Complete every accepted/rejected outcome into one normalized final
flag/data/reference state. Let the utility observable have eigenvalues
1 on Bell-good accepted output, -lambda on Bell-bad accepted output and
0 on rejection. If the trace distance between an actual completed state
and its ideal-model state is delta, then

```text
|U_actual-U_ideal| <= (lambda+1) delta.                  (MC8)
```

Indeed E=(G+lambda I)/(lambda+1) is an effect and the state difference has
zero trace, so the trace-distance variational bound proves MC8.
Two implementations with ideal advantage g retain a positive advantage
under the sufficient budget

```text
(lambda+1)(delta_ordinary+delta_native)+e_rem < g,      (MC9)
```

where e_rem is a separately bounded adverse utility contribution from
terms omitted by the declared first-order model. Actual added control
clock and control noise must either be included in the completed
physical states or charged explicitly without double counting.

For scale only, g=5e-5 at lambda=5 would require a worst-case summed
trace-distance budget below about 8.3e-6 if e_rem=0. This is neither a
necessary physical error limit nor a claim about a measured gate;
structured errors may affect the utility much less. Nor does beating
one feasible native decoder establish dominance over optimized native
decoding. The present moving-code witness remains a control relaxation
until its own physical service and the matched native comparison are
evaluated.

<a id="nr-r06-tip-prefix"></a>

### A pulse-independent bound for the declared TIP prefix

This is a clean, closed-system bound in the specified retained-\(\chi\)
star model, not a measured source limit or a full-Hamiltonian speed theorem.
Let \(T_0>0\), \(\delta=\pi/T_0\), \(\Delta=2\delta\), and take angular
frequencies. For \(a,c,d\in\{0,1\}\), on
\(b=|B1,u_g,v_g\rangle,u=|B0,u_f,v_g\rangle,v=|B0,u_g,v_f\rangle\), use
\[
h_{acd}(t)=\operatorname{diag}(\chi d,(-1)^a\delta,(-1)^c\delta)
 +\tfrac12[g_u(t)|b\rangle\langle u|+g_v(t)|b\rangle\langle v|+\mathrm{h.c.}].
\]
The same arbitrary complex physical fields act in every sector, including
off-resonant responses and actual carrier phases. The eight logical
\(B0,u_g,v_g\) columns are dark identity. There are no extra sector-dependent
controls, data/helper flips, or free conditional phase corrections.

The first-prefix contract at a common time \(h\) requires both couplers
to return for all sixteen logical columns, with returned \(b\)-phases
\[
z_{acd}=e^{i\beta}(-1)^{a(1-d)+cd}.
\]
Thus one common \(B\) frame is allowed. This specifies the entire unknown
input/reference isometry; final-only return after two windows is weaker.
The common frame is a clean-code convention, not an inferred action on
leaked \(f/h\) sectors or a bath compiler.

Compare sectors \(s_0=(1,1,0)\) and \(s_1=(0,0,1)\). With
\(P_b=|b\rangle\langle b|\) and \(\kappa=\chi-\Delta\),
\(h_1-h_0=\Delta I+\kappa P_b\): the pump terms cancel exactly.
For their propagators define \(Z(t)=e^{i\Delta t}U_0^\dagger(t)U_1(t)\).
Direct differentiation gives
\[
\dot Z=-i\kappa U_0^\dagger P_bU_0Z,\qquad
\|\dot Z(t)b\|\le |\kappa|.
\]
Exact prefix return requires \(Z(h)b=e^{i(\Delta h+\pi)}b\).
Distance on the complex unit sphere regarded as a real sphere is
\(d_S(x,y)=\arccos\operatorname{Re}\langle x,y\rangle\), and does not
exceed path length. Therefore, without any pulse-family assumption,
\[
L(h):=\operatorname{dist}(\Delta h+\pi,2\pi\mathbb Z)
 \le |\chi-\Delta|h. \tag{TP1}
\]
These relative phases cannot be discarded: the dark columns fix the
references. A common \(B\) frame cancels in the ratio, and marginal
\(A,C,D\) phases multiply the ready and dark columns equally.

There is also a direct approximate version without assuming exact return.
If \(\|U_j(h)b-z_jb\|\le\eta\) for both selected columns, each chord error
costs at most \(2\arcsin(\eta/2)\) in real-sphere angle. Applying the triangle
inequality to \(U_1b,e^{-i\Delta h}U_0b\) and their two targets yields
\[
\eta\ge 2\sin\!\left(\frac{[L(h)-|\chi-\Delta|h]_+}{4}\right). \tag{TP2}
\]
This is a ready-column norm bound, not a separately derived diamond or
average-fidelity estimate. For the declared rounded input
\(\chi/(2\pi)=9.29\,\mathrm{MHz}\), at \(h=T_0=100\,\mathrm{ns}\),
\(|\kappa|h=0.142\pi\) and \(\eta\ge1.24803\).
At \(h=T_0=140\,\mathrm{ns}\), \(\eta\ge0.61624\).

A declared per-pump cap \(|g_j|\le\Omega_{\max}\) strengthens the exact
result. At \(d=0\), fix \(c\) and compare \(a=0,1\); their Hamiltonian
difference is \(-\Delta P_u\), and their target phases differ by \(\pi\).
The relative-vector path length consequently gives
\(\pi\le\Delta\int_0^h|u_1(t)|\,dt\).
Put \(G=\Omega_{\max}/2\), the actual off-diagonal magnitude cap.
Because there is no direct \(u\)-\(v\) edge,
\(|d|u_1|/dt|\le G|b_1|\le G\sqrt{1-|u_1|^2}\).
Exact start and final return make \(\arcsin|u_1|\) a \(G\)-Lipschitz
function with zero endpoints. Hence
\[
|u_1(t)|\le\sin\min\{Gt,G(h-t),\pi/2\},\quad
\frac\pi\Delta\le I_{\rm cap}(h)=
\begin{cases}2[1-\cos(Gh/2)]/G,&h\le\pi/G,\\
h-(\pi-2)/G,&h\ge\pi/G.\end{cases} \tag{TP3}
\]

Take \(T_0=0.1\,\mu\mathrm s\) and the exploratory, not source-hard,
cap \(\Omega_{\max}/(2\pi)=9\,\mathrm{MHz}\). Then
\(\Delta=20\pi\), \(G=9\pi\), \(|\kappa|=1.42\pi\) in inverse microseconds.
Equation (TP1) allows bands
\([(2n-1)\pi/(\Delta+|\kappa|),(2n-1)\pi/(\Delta-|\kappa|)]\).
Its first band is \([50/1071,50/929]\,\mu\mathrm s\).
Throughout it, monotonicity and \(1-\cos x\le x^2/2\), \(\pi<4\), give
\[
I_{\rm cap}(h)\le\tfrac{9\pi}{4}(50/929)^2
 <22500/863041<1/20=\pi/\Delta\quad(\mu\mathrm s).
\]
Thus the whole first band fails (TP3); the next band starts at
\[
h\ge 50/357\,\mu\mathrm s=140.056\,\mathrm{ns}. \tag{TP4}
\]
Two exact intermediate-ready windows therefore require at least
\(100/357\,\mu\mathrm s=280.112\,\mathrm{ns}\) under these assumptions.
The symmetric second window uses the \(v\)-leaf argument. In contrast,
ordinary \(D=0\) serial ideal TIP pulses each take \(T_0\), with
\(\Omega=\sqrt3\pi/T_0<\Omega_{\max}\), and return the couplers;
their product is \(Z_B\,CZ_{AB}CZ_{CB}\), repaired by one common \(B\) frame.
This certifies the clean \(2T_0=200\,\mathrm{ns}\) target only, not its noisy
performance or a compiled helper-independent PCS body.

The bound does not exclude longer or corrected prefixes. A paid conditional
\(DB\) phase \(\zeta\) replaces \(L(h)\) by
\(\operatorname{dist}(\Delta h+\pi+\zeta,2\pi\mathbb Z)\).
Extra controls, dissipation, sector-dependent matrix elements or the full
source Hamiltonian can change the premises; the 9 MHz cap is a model choice.
No prototype, full-device minimum time, noisy dominance or SWITCH advantage
follows. Carrier-only labels and final endpoint equality remain insufficient
to certify the complete physical opposite-order instrument.

<a id="nr-r06-tip-phase-cost"></a>

### Paid phase corrections and a conditional idle sensitivity

These statements use
the declared closed retained-\(\chi\) star, not a calibrated TIP device.
Use \(T_0=100\,\mathrm{ns}\), \(\Delta=2\pi/T_0\),
\(\chi/(2\pi)=9.29\,\mathrm{MHz}\), \(\epsilon=\Delta-\chi>0\), and
the model cap \(\Omega_{\max}/(2\pi)=9\,\mathrm{MHz}\).
Define \(h_a=2\arccos(1-9\pi/40)/(9\pi)\,\mu\mathrm s
\simeq90.066498581\,\mathrm{ns}\). The preceding exact ready-prefix proof
gives a pulse-only duration \(h\ge h_a\) from its occupation bound and
\(\operatorname{dist}(\Delta h+\pi,2\pi\mathbb Z)\le\epsilon h\)
for the unrepaired common-\(B\)-frame prefix. All unknown input/reference
columns and the actual dark-state phase references are retained.

**A forward wait cannot evade the clock bound.** Let a pulse return the
couplers but leave a conditional \(DB\) phase, then append
\(G(\tau)=e^{-i\chi\tau n_Dn_B}\), \(\tau\ge0\), with pumps zero.
To finish at the strict prefix its pre-wait paired-sector ratio must be
\(-e^{i\chi\tau}\), so
\[
\operatorname{dist}(\Delta h+\pi+\chi\tau,2\pi\mathbb Z)\le\epsilon h.
\]
For total time \(L=h+\tau\), some integer \(n\) must satisfy
\[
\chi L+\pi\le2\pi n\le\chi L+2\epsilon h+\pi
 \le(\chi+2\epsilon)L+\pi.
\]
The \(n=1\) possibility needs \(L\le\pi/\chi=50/929\,\mu\mathrm s
\simeq53.821313240\,\mathrm{ns}\),
contradicting \(L\ge h_a\); \(n\le0\) is impossible. Hence
\(L\ge3\pi/(\chi+2\epsilon)=50/357\,\mu\mathrm s
\simeq140.056022409\,\mathrm{ns}\).
Equivalently, this zero-pump wait remains inside the original common-field
Hamiltonian, so the original prefix bound applies to its complete clock.
Time already inside a tested horizon is counted once; appended time is added.

**Reversing the phase adds a control resource.** In the isolated number model,
\[
X_DG(\tau)X_D=e^{-i\chi\tau n_B}e^{+i\chi\tau n_Dn_B}.
\]
A common \(B\) correction therefore leaves the inverse \(DB\) phase.
Restoring physical \(D\) labels uses two unconditional helper \(\pi\) pulses.
One pulse can suffice with an accepted output \(X_D\) frame and verified
retiming of all subsequent branch propagators. Alternatively, omit the
**second** flip when it is adjacent to terminal ideal \(X_D\) readout:
it changes each Kraus operator only by its outcome sign. The remaining
physical flip is before the wait. Neither is an automatic mid-prefix omission.
Alternatively the inverse phase uses a longer forward wait
\(2\pi/\chi-\tau\), with no flips and its full clock counted.

For the inverse correction the pulse-only condition becomes
\(\operatorname{dist}(\Delta h+\pi-\chi\tau,2\pi\mathbb Z)\le\epsilon h\).
Together with \(h\ge h_a\), these necessary conditions first allow
\[
h=h_a,\quad \tau=h_a-\pi/\chi\simeq36.245185341\,\mathrm{ns},\quad
L=2h_a-\pi/\chi\simeq126.311683922\,\mathrm{ns}.
\]
Indeed, for \(h<3\pi/(\Delta+\epsilon)\), the integer cannot be \(n\ge2\);
\(n\le1\) requires \(\tau\ge h-\pi/\chi\). Larger \(h\) already costs more.
This is only a relaxation of two necessary scalar bounds, **not a waveform
or an achievable gate**. Put \(C=50/357\,\mu\mathrm s-(2h_a-\pi/\chi)
\simeq13.744338487\,\mathrm{ns}\). A literal concatenation leaves \(C\)
before reaching the unrepaired lower clock: \(C/2\simeq6.872169243\) ns
per two equal extra pulses, or \(C\) for an accepted one-pulse contract.
These crossover numbers are not source pulse limits. The strong-\(ZZ\)
primary does not report numerical unconditional TAG durations; \(\chi\)
alone sets no helper-\(\pi\) speed limit. Finite pulses also evolve the full
Hamiltonian. The same coupling, rotations and phase/check controls belong
to ordinary implementations; no exclusive selector resource is obtained.

**An extra clean idle has an exact full-flag description.** Assume, separately,
that ideal \(W\) has finished, \(D=+\) is decoupled from payload/reference,
and a genuinely additional idle has only
\(L_\phi=\sqrt{2\Gamma}P_1\). Put \(q=(1-e^{-\Gamma\tau})/2\). Then
\[
\mathcal E_+=(1-q)\operatorname{Ad}_W,\qquad
\mathcal E_-=q\operatorname{Ad}_W,
\]
including the identity on every reference. Both flags are target-good.
Plus-only delivery loses \(q=\Gamma\tau/2+O(\tau^2)\); accepting both with
one common valid decoder has no such loss. More generally, any pre-existing
full flag maps obey
\[
\mathcal E'_+=(1-q)\mathcal E_++q\mathcal E_-,\qquad
\mathcal E'_-=(1-q)\mathcal E_-+q\mathcal E_+.
\]
This follows from \(Z_D\Pi_sZ_D=\Pi_{-s}\); the sum is unchanged.
With different flag decoders, each new branch applies its own decoder to
both mixture terms. A fixed plus-decoder linear utility changes by
\(q[J(\mathcal E_-)-J(\mathcal E_+)]\), not a universal rejection cost.

As a conditional sensitivity only, take
\(\Gamma=20/1013-25/3849=51655/3899037\,\mu\mathrm s^{-1}\) and the
supplied restricted-envelope margin
\(m(T)=240421997(T/\mu\mathrm s)/1453311455232\).
At \(T=0.14\,\mu\mathrm s\), \(m\simeq2.3160265791\times10^{-5}\).
The unit-good clean plus-only model loses this amount after
\(-\log(1-2m)/\Gamma\simeq3.49646\,\mathrm{ns}\)
(first order: \(2m/\Gamma\simeq3.49638\) ns).
This neither reproves the restricted margin nor identifies a physical
white floor. Ramsey \(T_2^*\) is insufficient, echoes can alter correlated
noise, and an actual retained-\(\chi\) correction wait is **not** the
factorized clean idle. Full-Hamiltonian calibration, all reject/reference
maps, the best common/flag-dependent recovery, and matched ordinary controls
are required before interpreting any of these clocks as an advantage.

<a id="nr-r06-tip-finite-body"></a>

### A finite ordinary body under the declared retained-χ model

This is a sufficient closed-model construction, not a measured combined
TIP/helper device, a competitive clock, or a compiler of the noisy
instrument. It keeps all sixteen unknown logical DABC ready columns,
both private couplers, and an arbitrary passive reference. No outcome is
postselected. The control assumptions and all added clocks are explicit.

For each fixed \(a,c\in\{0,1\}\), retain
\(b=|B1,u_g,v_g\rangle\), \(u=|B0,u_f,v_g\rangle\),
\(v=|B0,u_g,v_f\rangle\), and the dark state
\(o=|B0,u_g,v_g\rangle\), each tensored with D. Let
\(n_B=P_b\), \(Z_D=I-2n_D\),
\(H_{aux}=(-1)^a\delta P_u+(-1)^c\delta P_v\),
\(\delta=\pi/T_0\), and \(\Omega=\sqrt3\delta\). The global-frame
Hamiltonian is
\[
 H=H_{aux}+\chi n_Dn_B+
 \tfrac12\sum_{j=u,v}[p_j(t)|j\rangle\langle b|+h.c.]
 +\tfrac12\Omega_D(t)X_D.
\]
The same classical fields apply in every sector. For the numerical clock
example take the exact declared model values \(T_0=0.1\,\mu s\) and
\(\chi/(2\pi)=9.29\,\mathrm{MHz}\); these are not a joint calibration.

During a driven port j, use the lower-edge field
\(p_j(t)=\Omega e^{+i\chi t/2}\), with one absolute-time phase accumulator,
and set the other pump and helper drive to zero. In the continuous common
B frame \(R(t)=e^{-i\chi t n_B/2}\), this gives
\[
 H_+=K_j+V,\quad K_j=H_{aux}+\tfrac\Omega2(|b\rangle\langle j|+h.c.),
 \quad V=-\tfrac\chi2Z_Dn_B,\quad X_DH_+X_D=K_j-V.
\]
The active two-state block of \(K_j\) has return frequency
\(\sqrt{\delta^2+\Omega^2}=2\delta\). Its hub return phase at \(T_0\)
is \(-e^{-i(-1)^a\delta T_0/2}=i(-1)^a\) for port u, and
\(i(-1)^c\) for v. Thus
\(U_{ref}=e^{-iK_vT_0}e^{-iK_uT_0}\) returns every ready column and equals
\(I_D\otimes Z_BW\) there, where \(W=CZ_{AB}CZ_{BC}\). On occupied
auxiliaries, its reference action is this full product, not an inferred W
extension. The dark states are included throughout.

**An exact finite helper flip, including auxiliary drift.** With both TIP
pumps off, drive D at its bare-helper frequency. Conditional on B=0 its
Hamiltonian is \(\Omega_DX_D/2\); conditional on B=1 it is
\(\chi n_D+\Omega_DX_D/2\). The commuting \(H_{aux}\) remains on.
Define \(c_0=(\sqrt5-1)/2\), \(\phi=\arccos c_0\), and
\[
 \Omega_r=\chi\cot\phi,\quad t_r=\pi\sin\phi/\chi,\qquad
 \Omega_q=\chi\cot2\phi,\quad t_q=\pi\sin2\phi/\chi.
\]
Apply the three finite square pieces r, q, r. The negative middle amplitude
means the opposite X phase. Put \(\widetilde Z_D=2n_D-I\). In the B=1
traceless block, the axes are
\(n_r=(\cos\phi,0,\sin\phi)\) and
\(n_q=(\cos2\phi,0,\sin2\phi)\), each with π rotation angle.
The identity
\((n_r\cdot\sigma)(n_q\cdot\sigma)(n_r\cdot\sigma)
 =[2(n_r\cdot n_q)n_r-n_q]\cdot\sigma=X_D\)
makes their product \(+iX_D\). In the B=0 block the total angle is
\(\pi[2c_0+2c_0^2-1]=\pi\), since \(c_0^2=1-c_0\), giving
\(-iX_D\). Retaining the B=1 trace and auxiliary phases, the complete
global-frame primitive of duration \(t_p=2t_r+t_q\) is therefore
\[
 F_g=-i e^{-iH_{aux}t_p}e^{i(\pi-\chi t_p/2)n_B}X_D.
\]
In the continuous centered frame, this becomes
\(F_c=-i e^{-iH_{aux}t_p}Z_BX_D\). These identities hold on every admitted
star state, not merely on the ready columns.

Choose \(L_\pi=2T_0\) and \(q=(L_\pi-t_p)/2\). This is nonnegative:
\(t_p\le3\pi/\chi<2T_0\) at the declared model values. During equal
padding waits before and after the pulse, the centered Hamiltonian is
\(H_{aux}+V\). Because \(X_DVX_D=-V\) and \(H_{aux}\) commutes with
V and X, their exact product is
\[
 e^{-iq(H_{aux}+V)}F_c e^{-iq(H_{aux}+V)}
 =-i e^{-iH_{aux}L_\pi}Z_BX_D=-iZ_BX_D.
\]
The last equality uses \(e^{-2iT_0H_{aux}}=I\) simultaneously for all
a,c. A common B phase correction leaves exactly \(-iX_D\) with a paid
200 ns clock. If implemented as a tracked B frame, it must conjugate all
subsequent pump quadratures; the absolute-time carrier continues through
every drive and idle. If a physical phase gate is required instead, its
clock and noise are additional. No conditional phase is silently discarded.

**Finite symmetric decoupling and its error proof.** For each port split
the free driven duration \(T_0\) into N cycles of length \(s=T_0/N\).
Each cycle is H+ for s/4, the corrected finite flip, H+ for s/2, another
finite flip, then H+ for s/4. Up to a cycle-global minus sign its centered
propagator is
\[
 S(s)=e^{-i(K+V)s/4}e^{-i(K-V)s/2}e^{-i(K+V)s/4}.
\]
The sign from the two \(-iX_D\) flips cancels over the two ports' 2N cycles.

Here is a direct norm proof, without an unlinked product-formula premise.
Set \(A=-i(K+V)/2\), \(B=-i(K-V)/2\), \(C=[A,B]\),
and \(\operatorname{Ad}_U Q=UQU^\dagger\). For
\(S(t)=e^{tA/2}e^{tB}e^{tA/2}\), differentiate and subtract A+B to obtain
\[
 \begin{split}
 D(t)&=S'(t)S(t)^\dagger-(A+B)\\
 &=\operatorname{Ad}_{e^{tA/2}}\left[
 \int_0^{t/2}(\operatorname{Ad}_{e^{-rA}}-I)C\,dr
 -\tfrac12\int_0^t(\operatorname{Ad}_{e^{rB}}-I)C\,dr\right].
 \end{split}
\]
Indeed the unsimplified derivative is
\(\int_0^{t/2}\operatorname{Ad}_{e^{rA}}C\,dr
 -\tfrac12\operatorname{Ad}_{e^{tA/2}}
 \int_0^t\operatorname{Ad}_{e^{rB}}C\,dr\); factoring the first
conjugation makes the two constant C integrals cancel. Unitary conjugation
and its derivative give
\(\|(\operatorname{Ad}_{e^{rX}}-I)C\|\le |r|\|[X,C]\|\).
Consequently
\(\|D(t)\|\le t^2\|[A,C]\|/8+t^2\|[B,C]\|/4\).
Variation of constants,
\[
 S(s)-e^{s(A+B)}=
 \int_0^s e^{(s-t)(A+B)}D(t)S(t)\,dt,
\]
has unitary factors and proves
\[
 \|S(s)-e^{-iKs}\|\le
 s^3\bigl(\|[A,[A,B]]\|/24+\|[B,[A,B]]\|/12\bigr).
\]

The commutator constants are explicit. In the active block use Pauli
\(Z=P_b-P_j\), \(X=|b\rangle\langle j|+h.c.\), and Y. Then
\(K=\delta_a(I-Z)/2+\Omega X/2\), with \(\delta_a=\pm\delta\),
and the D-dependent scalar factor in V has magnitude \(\chi/2\).
Directly,
\[
 [K,P_b]=-i\Omega Y/2,\qquad
 [K,[K,P_b]]=\tfrac\Omega2(\delta_aX+\Omega Z),\qquad
 [P_b,[K,P_b]]=-\Omega X/2.
\]
Thus spectators do not enter, and
\[
 C_K:=\|[K,[K,V]]\|=\frac{\chi\Omega\sqrt{\delta^2+\Omega^2}}4,
 \qquad C_V:=\|[V,[K,V]]\|=\frac{\chi^2\Omega}8.
\]
Since \([A,B]=[K,V]/2\), both nested norms in the defect bound are at
most \((C_K+C_V)/4\). Telescoping N unitary cycles per port and the two
ports proves the full admitted-star operator bound
\[
 \|U_N-U_{ref}\|\le E_N=
 \frac{T_0^3(C_K+C_V)}{16N^2}
 =\frac{\chi\Omega(4\delta+\chi)T_0^3}{128N^2}
 =\frac{2721041\sqrt3\pi^3}{32000000N^2}.
\]
Here \(U_N\) denotes the centered, corrected sequence including the actual
finite flips. The full physical frame additionally contains
\(R(T_{clock})\); the specified final common B correction is
\(Z_B e^{+i\chi T_{clock}n_B/2}\), with the flip-frame updates already
tracked. The corrected ready isometry is within \(E_N\) of
\(I_D\otimes W\). Tensoring any reference leaves the bound unchanged.
All auxiliary amplitudes, including any final leakage, remain in this
comparison; there is no success normalization or discarded output.

For N=22, \(E_N<0.01\). In fact \(\sqrt3<7/4\), \(\pi<22/7\)
give the exact rational upper bound
\(E_{22}<7243411142/758912000000<1/100\).
The construction uses 88 finite composite flips, hence 264 helper-drive
pieces, and its clock is
\(2T_0+4NL_\pi=17.8\,\mu s\), before physical frame pulses,
ramps/buffers, preparation, readout, reset and noise. This is a slow
sufficient construction, not a minimum or a useful-device witness.

**Physical premise and next test.** The
[strong-ZZ primary, Sec. III/Fig. 2](https://arxiv.org/html/2103.12305v1),
supplies the three-piece unconditional-rotation geometry and a separate
9.29 MHz constituent. It does not report the numerical duration of the
derived pulse above or calibrate it in a TIP/helper assembly. The
[TIP primary, Sec. IV](https://arxiv.org/html/2511.01260v2),
uses shaped pump edges; the square, short segments in this construction
do not establish feasibility within its 20 ns edge example. No measured
helper peak/slew/bandwidth or higher-level leakage guarantee is supplied.
For an implemented replacement waveform on a common clock, add
\(\int\|H_{actual}-H_{specified}\|dt\) and any independently bounded
primitive-calibration errors, or recalibrate the complete sequence.
An added interval must retain its full Hamiltonian and clock.

The decisive missing service is a calibrated unconditional helper flip,
or concurrent decoupling waveform, with duration and uniform error over
the actual B/auxiliary/f/h sectors. Its driven relaxation/dephasing
instrument is also needed; Ramsey \(T_2^*\) does not determine a white
Markov floor. The clean construction does not match the full chronological
noisy bath/flag instrument to a helper-independent core. Native selector
prefixes still need their own feasible physical control, while a final-only
\(I_D\otimes W\) endpoint alone does not certify opposite-order histories.
Bare ordinary fixed-D0 execution plus PED and simultaneous ordinary
controls remain admitted. All records, rejects, storage, control and
recovery must be compared at one deadline using the same supplied ports;
no source-backed native or ordinary noise advantage follows here.
