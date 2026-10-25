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

