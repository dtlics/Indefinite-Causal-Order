# Unknown-axis pulse selectors: physical phases, loss and delivery

The [NR21 owner](../unknown-pulse-gates.md#nr-r21) defines
$A^2=B^2=I$, $AB=-BA$, $H=(A+B)/\sqrt2$ and the physical target
$U_\alpha=e^{-i\alpha H}$, with an arbitrary passive reference. Its
Euler word, native branches and causal certificate remain there.
This component determines what a supplied selector or fixed optical
box actually permits. It establishes no hardware advantage.

## Complete selector instrument and the installed-angle cut

Put $D=(A-B)/\sqrt2$ and, for $0<\alpha<\pi/2$, define

$$
\beta=\arctan(\sqrt2\tan\alpha),\qquad
k=\sin^2\alpha,\quad p=\frac1{1+k},\quad r=\frac{k}{1+k}.
$$

A phase-qualified coherent
$\operatorname{SELECT}\{R_A(\beta),R_B(\beta)\}$, balanced helper and
$X$ readout have fine operators

$$
L_+=\frac{R_A(\beta)+R_B(\beta)}2=\sqrt p\,U_\alpha,
\qquad
L_-=\frac{R_A(\beta)-R_B(\beta)}2=-i\sqrt r\,D.
$$

Thus the complete measured instrument is
$|+\rangle\langle+|\otimes p\operatorname{Ad}_{U_\alpha}(\rho)$ plus
$|-\rangle\langle-|\otimes r\operatorname{Ad}_D(\rho)$. Before helper
measurement it is a coherent isometry, including both cross terms.
Discarding the minus target makes an erasure of mass $r$; its retained
misrotation and any reference cannot be omitted otherwise. Against the
encoded normalized Bell target, plus has good mass $p$ and bad mass zero;
keeping minus uncorrected adds bad mass $r$.

The [AP15 selector](../unknown-pulse-gates.md#prior-mechanisms-and-actual-selector-access)
is the $\alpha=\pi/4$ case, not a separate mechanism. For completeness
its general terminal correction follows directly from (AP2): put
$\chi=\arccos(\cos\alpha/\sqrt2)$ and

$$
x=\pi/4+\beta/2,\qquad y=-\chi,\qquad z=\pi/4-\beta/2.
$$

Then $R_A(x)R_B(y)R_A(z)=-iU_\alpha D$, with absolute exposure
$\pi/2+\chi$. Applying it after minus delivers the target on both
branches. It requires signed angles, actual branch handling and
nondestructive output delivery. With a genuinely single occupied SELECT
interval the completed mean is $1+3r$. If selection instead uses two
scheduled named boxes it is $2+3r$ named opportunities. At $\pi/4$
these are two versus three; the latter exceeds the native hybrid's
$7/3$. These currencies cannot enter the original opaque-query dual.

The installed native angle is
$h=\arctan(\tan\alpha/\sqrt2)$, not $\beta$. Equal choice of only the
angle-$h$ boxes gives $\tan\alpha_{\rm choice}=\tan\alpha/2$.
Unequal helper coefficients do not repair this plain two-box linear
combination: equal target $A,B$ coefficients force equal box
coefficients. At $\alpha=\pi/4$ its plus probability is $5/6$ but the
gate is $U_{\arctan(1/2)}$; Bell-good and bad masses relative to
$U_{\pi/4}$ are $3/4$ and $1/12$. Identity/bypass terms, retuning or
multiple calls are additional controls. Fixed-$h$ boxes also do not
grant the variable-angle native terminal repair.

## Physical phase, empty ports and pilot reuse

Let the occupied amplitudes be
$e^{i\phi_A}R_A(\beta),e^{i\phi_B}R_B(\beta)$ and remove their common
phase. With $\delta=(\phi_A-\phi_B)/2$ the actual fine operators are

$$
\begin{aligned}
L_+(\delta)&=\sqrt p\cos\delta\,U_\alpha
                  +\sqrt r\sin\delta\,D,\\
L_-(\delta)&=i\sqrt p\sin\delta\,U_\alpha
                  -i\sqrt r\cos\delta\,D.
\end{aligned}
$$

Since $U_\alpha^\dagger D$ is a traceless Hermitian involution, the plus
effect is

$$
(p\cos^2\delta+r\sin^2\delta)I
 +2\sqrt{pr}\sin\delta\cos\delta\,U_\alpha^\dagger D.
$$

It is generally input dependent and not an exact target subchannel.
On the normalized encoded Bell input, acceptance is
$p\cos^2\delta+r\sin^2\delta$, good mass is $p\cos^2\delta$ and bad
mass is $r\sin^2\delta$. For bad-output penalty $\lambda$, utility is
$p-(p+\lambda r)\sin^2\delta$. A fresh uniform independent relative
phase makes each flag's averaged map
$(\operatorname{Ad}_{R_A}+\operatorname{Ad}_{R_B})/4$; neither flag
then implements the exact target. Stationary matched two-order words
instead share $\phi_A+\phi_B$. That cancellation does not remove slot
drift, direction dependence or bath records.

For a vacuum extension
$\widetilde U_j=e^{i\nu_j}|\mathrm{vac}\rangle\langle\mathrm{vac}|
\oplus e^{i\phi_j}R_j$, A-only and B-only routes have phases
$\phi_A+\nu_B$ and $\phi_B+\nu_A$. The required relative phase is

$$
(\phi_A-\nu_A)-(\phi_B-\nu_B),
$$

including bypass propagation. Occupied CPTP maps and stable vacuum alone
do not specify it. A supplied controlled extension or measured stable
phase calibration is needed. An axis-independent pilot is possible:
on maximally mixed encoded input,

$$
\Pr(+)=\frac{1+\cos^2\beta\cos(2\delta)}2.
$$

Scanning a known route phase gives both quadratures; visibility is $1/3$
at $\alpha=\pi/4$. Finite shots give finite accuracy. Charge pilots,
visits, readout, adjustment and drift monitoring, amortized over the
measured stable window. Angle retuning can change phase, so calibration
at $h$ need not qualify $\beta$.

Filling the unused box with a dummy does not automatically erase branch
information. Outputs $R_B|\xi\rangle$ and $R_A|\xi\rangle$ multiply
the cross term by their overlap when discarded. For $A=Z,B=X$ and
$|\xi\rangle=|0\rangle$, its magnitude is $\cos\beta$, not one.
A mixed dummy retains a purification/environment. A common dummy return
or explicit erasure/uncomputation must be supplied and priced; this is
not a converse against every matched-call compiler.

## The existing fixed-box vacuum compiler remains available

With the stronger coherent vacuum buffer and conditional routing port,
[P3](commutator-apparatus.md#a-three-slot-ordinary-construction-matches-this-whole-service)
already supplies an exact ordinary comparator. Its three named
opportunities A--B--A give the survivor operator

$$
e^{i(\nu_A+\phi_A+\phi_B)}
\left[|0\rangle\langle0|\otimes R_B(h)R_A(h)
     +|1\rangle\langle1|\otimes R_A(h)R_B(h)\right].
$$

No $\beta$ retuning or A-only/B-only phase pilot is required. P3 owns
the proof and loss qualification. It costs three scheduled named
opportunities, two occupied target traversals, a buffer, four controlled
swaps, storage and stable recombination. Reusing A requires its full
stationary temporal service, without residual memory or returning loss
ports. In the passive compositional vacuum model it matches the surviving
helper/target/reference map and a single coarse erasure after failed
target/control outputs are discarded. It does not generally match
lost-time baths or a separately retained control on loss. It is a
stronger physical port than an opaque qubit query with an arbitrary
qubit dummy.

## All-launch loss and clocks

For a restricted passive equal scalar-loss ledger, let every occupied
traversal at the relevant settings have power survival $\eta$. Require
a number-preserving optical dilation with vacuum loss inputs, so a
surviving single photon leaves every loss environment in vacuum.
Vacuum is stable, loss ports never return, and the accessible lost-photon endpoint is a
single coarse erasure, including disposal of any external control. Choice
survivors have Kraus operators $\sqrt\eta L_\pm$ and erasure effect
$(1-\eta)I$. Native two-occupied survivors have $\eta K_\pm$ and erasure
effect $(1-\eta^2)I$. This fixes their reference-preserving accessible
erasure completion, not their discarded environments.

At $\alpha=\pi/4$ exact-plus masses are $2\eta/3$ and
$8\eta^2/9$. Choice is larger for $0<\eta<3/4$, provided the $\beta$
setting actually supplies the same phase, loss and delivery service.
Unequal scalar choice losses spoil the equal coefficients unless
physically rebalanced; mode-dependent loss cannot be normalized away.
These one-attempt formulas do not price a loss-tolerant correction of a
retained unknown input.

For accepted gates on fresh supplied inputs, choice beats native exactly
when $T_S/T_N<p_S/p_N$. Losslessly the $\pi/4$ threshold is $3/4$;
in the equal-loss example it is $3/(4\eta)$ for $\eta>0$. Equal angular
rates and zero overhead give

$$
\beta/(2/3)\simeq1.432975
 > 2h/(8/9)\simeq1.384829.
$$

A common nonnegative per-attempt overhead does not reverse this raw-rate
comparison. Fixed photon flights are a different ledger: one occupied
flight can favor choice if retuning, routing and setup really preserve
that clock. For the displayed lossless terminal-repair policies, mean
active angles are approximately $1.827981$ for choice, $1.521848$ for
native hybrid, and $1.139078$ for ordinary Euler. These are achievable
circuits, not optimized frontiers. Named opportunities, pilots, storage,
branch handling and release remain charged.

With ideal fixed occupied traversal time $\tau$ and native extra latency
$d$, native first-plus yield $(8/9)/(2\tau+d)$ exceeds the Euler
comparator $1/(3\tau)$ only if $d<2\tau/3$, when all Euler angles exist.
This weaker achievable-comparator threshold differs from the main
[all-launched scalar-dual conversion](../unknown-pulse-gates.md#nr-r21-all-launch-query-price).
The latter requires its original query interface and the much narrower
$\tau_C<4\tau/45$ homogeneous-charge condition.

## What measured optical implementations establish

**Reciprocal Sagnac.** [Strömberg et al., PRL 131, 060803 (2023)](https://arxiv.org/html/2211.12540v2), main text and supplement A/B, use engineered reciprocal SU(2) polarization gadgets in a common-path Sagnac and report visibility above 0.9995. Generic counterpropagation gives a basis-dependent transpose of a waveplate gadget; their added Faraday/waveplate construction corrects this. Requested matrices are programmed through calculated settings and characterized. Outputs are detected after polarization analysis. Calibration and long acquisitions are reported, without a matched ordinary layout or per-module group delay.

**Time-bin routing.** [Antesberger et al., PRX Quantum 5, 010325 (2024)](https://arxiv.org/html/2305.19386v2), III.1 and appendix A, use 150 ns time-bin spacing, 60 ns switch response and a 1 MHz maximum switch duty cycle. Fiber lengths enforce the schedule. Reusing an interferometer for control preparation and measurement cancels its phase fluctuations. Free-space waveplate/polarizer sections implement the parties. Final coincidence detection and about 18 dB total insertion loss characterize that apparatus, not excess native loss against a matched gate service.

**Programmed fixed locations.** [Taddei et al., PRX Quantum 2, 010320 (2021)](https://arxiv.org/html/2002.07817v3), IV and VI.2, use liquid-crystal retarders at fixed spatial locations and specified orientations, with electronically controlled retardance from identity to half-wave operation. Active phase stabilization returns to a reference table column between windows. The setting cycle allows 0.2 s settling followed by 0.1 s measurement. Installed optical length and programmed retardance are distinct controls in this implementation.

**Adding control physically.** [Zhou et al., Nature Communications 2, 413 (2011)](https://www.nature.com/articles/ncomms1392), Results and Discussion, use additional inactive levels/spatial paths to add control, extend selection from I/U to two arbitrary operations and their linear combination, and demonstrate a postselected entanglement-based optical realization.

**The controlled extension.** [Araújo et al., NJP 16, 093026 (2014)](https://arxiv.org/html/1309.7976v2), Fig. 1, Eq. (7) and the following direct-sum discussion (PDF p. 3), explain how a known physical bypass supplies an $I\oplus U$ extension beyond standard single-use access to an arbitrary unknown unitary. This distinction is the relevant port qualification here.

## A decision on one measured stable epoch

Declare a useful frame-relative $U_\alpha$ workload and characterize its
repeatable equal-angle orthogonal pair, occupied/bypass phases,
direction/time dependence, losses and output endpoint. Compare native
first-plus, Euler when angle access exists, the selector when its extension
exists, P3 when its vacuum/routing port exists, and compilation from all
available calibrated settings or probes. Fixed-only boxes require their
own heralded ordinary analysis and cannot inherit native completion.

For Hermitian estimates $\widehat A,\widehat B$, Duhamel's formula gives

$$
\|U_\alpha-e^{-i\alpha(\widehat A+\widehat B)/\sqrt2}\|
\le\frac\alpha{\sqrt2}
  (\|A-\widehat A\|+\|B-\widehat B\|).
$$

The half-diamond channel distance is no larger; actual compilation
errors add. This supplies no measured calibration time or sample count.
Use the actual error/cost/reuse curve, including allowed bright probes,
retained settings and stable batch size. Hiding a programmed setting is
an oracle restriction, not by itself an architecture bottleneck.

The [Bell-utility robustness component](pulse-gate-robustness.md) separately
proves finite-penalty existence and an unquantified nonzero separation
neighborhood in the original quarter-turn query model. No certified
numerical error tolerance follows. That mathematical existence result
does not supply measured phase, loss, calibration or release margins.

A plus rail followed by further optics and a final destructive label
check is deferred postselection if all intervening operations/losses are
included. Online known-success delivery additionally requires a
nondestructive flag, retained quantum output and any memory/feed-forward.
Rejected unknown inputs cannot be replaced by fresh retries without a
declared factory task or actual recovery.

When the successful maps retain the stated exact targets with scalar
transmissions $\eta_N,\eta_E,\eta_S$ and complete service times
$T_N,T_E,T_S$, preliminary exact-plus comparisons require

$$
\frac89\frac{\eta_N}{T_N}>\frac{\eta_E}{T_E},\qquad
\frac{\eta_N}{T_N}>\frac34\frac{\eta_S}{T_S}.
$$

These are falsifiable comparisons with particular ordinary circuits,
not converse bounds. None of the inspected sources supplies the complete
unknown-axis workload, measured calibration-expiry constraint, released
output and matched ordinary ledger. The result is a precise next test,
with no native hardware advantage established.
