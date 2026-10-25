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

### A full-interval weak-tag bound with arbitrary flag recovery

This is a fixed-lambda first-order statement in the declared cold TIP
model. A single helper uses static conditional-unitary tags before and
after the entire D-independent two-gate body of duration 2T. Conditional
helper codewords d_0,d_1 may be any pure states, including nonorthogonal
complex states. The noiseless ready flag preserves W and uses identity;
every rare measured helper/coupler flag may use an arbitrary trace-
nonincreasing CP recovery, completed by a retained reject outcome.
Hidden bath labels and times are never decoder inputs. Intermediate
retagging/echo, different pulse schedules and a real dispersive selector
are not part of this family.

Write d_b=sqrt(1-p_b)|0>+exp(i phi_b)sqrt(p_b)|1> and
t_b=sqrt[p_b(1-p_b)]exp(i phi_b). Its distinguishability is

 a=1-|<d_0|d_1>|^2=|t_0-t_1|^2+(p_0-p_1)^2, 0<=a<=1.

For physical white helper jumps sqrt(gamma)|0><1| and
sqrt(2 Gamma)P_D1, the mandatory ready-flag bad weight per T is

 b_0=gamma |t_0-t_1|^2/2+Gamma(p_0-p_1)^2.

If Gamma>=gamma/2, then b_0>=gamma*a/2. With helper noise alone,
every completed recovery instrument satisfies q+bad<=1; hence target-
good loss is at least total accepted bad and at least b_0. Its utility
cost for U_lambda=q-lambda*bad is therefore at least
(lambda+1)gamma*a*T/2, whatever the rare-flag recovery.

Let O=5 gamma_B/8 be the total accepted B-lowering norm per T in this
body. Weak tagging sends fraction a to the rare flag and leaves
fraction 1-a in the mandatory flag. Every such lowering history has
initial/reference B=e. A recovery on the output cannot change that
reference support, and the target Bell vector has squared norm 1/2
there: q<=p/2 for any CP recovery. For lambda>=1, the rare B-lowering
contribution is nonpositive, so its maximum possible improvement over
bare PED is lambda*O*a*T. Other accepted code-closed core faults
preserve B and are unchanged by tag/uncompute. Excited-coupler flags
also have reference B=e and nonpositive recoverable utility.

First-order noise contributions add for the same fixed measured-flag
recovery. Combining the bounds and maximizing 0<=a<=1 gives

 U_weak-U_bare <= max[0, lambda O-(lambda+1)gamma/2] T.       (W1)

This bound can be loose: it does not assert that bare PED is optimal.
It allows arbitrary codeword centers, polar/azimuthal angles, gauge
phases, and general CP recovery throughout the stated tag family.

For the Q1 nominal-white illustration at lambda=5, use
gamma_A=gamma_C=1/168, gamma_B=1/80,
gamma_phi,u=gamma_phi,v=1/26-1/64,
gamma=50/3849 and Gamma=20/1013-25/3849, all per us.
Thus O=1/128, Gamma>=gamma/2, and (W1) is at most
15*T/164224 per us, approximately 0.0000913386594*T/us.

The already derived **feasible native plus/gg** rule, without using
an SDP optimum, exceeds bare PED at these copied rates by
373165517*T/1453311455232 per us. Therefore its first-order excess
over every member of this weak-tag family is at least

 240421997*T/1453311455232 per us
   =0.0001654304699*T/us >0.                              (W2)

All fractions follow from the earlier exact equal-T moments. These
are first-order utility coefficients at fixed lambda, not a finite-rate
error bound. Multiplying (W2) by an illustrative T=0.14 us gives only
2.32e-5 utility units before higher orders or any physical overhead;
the source 140 ns waveform has not been transferred to this model.
C/v rates are copied assumptions and the helper Gamma is an assumed
exponential white subtraction from a separate constituent Ramsey
T2*, not an identified TIP/helper bath. System-dependent helper
emission under real chi_DB, selector activation, finite tag/control
durations, readout/recovery latency and stronger ordinary schedules
remain outside this bound. It establishes a conditional utility
mechanism within a defined comparator family, not an architecture gain.

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
