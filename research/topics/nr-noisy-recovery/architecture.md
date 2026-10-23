# Application assessment and next experiment

[Recovery theorem](theorem.md) · [Ordinary baselines](architecture-baselines.md) · [Literature context](references.md) · [Topic](README.md)

The current results establish an advantage in a specified fresh-frame recovery
game. They do **not** yet establish a useful advantage for calibrating or
operating persistent hardware. The next investigations start from complete
device instruments and available controls, then ask whether switched outputs
improve a deployed decision. Current screens cover calibration transport,
multimode optics, displacement calibration, measurement alignment, network
entanglement, private key detection, braided magic and native computational
layers. A quantum bath or a cheaper control readout is not
enough: the comparison must include native reference encodings, ordinary
echo and spectral checks, and every accepted and rejected outcome. No checked
architecture currently meets all the required assumptions.

## What is established

[NR-R01](theorem.md) concerns physical Bell-frame restoration with a fresh
private frame for each job. For $n\geq8$, each unknown module is followed once
by calibrated local depolarization, with per-qubit strength
$\eta_n=(4/3)(1-0.9^{1/n})$. The receiver must return a physical quantum output
or reject; a passive reference remains inaccessible. Counting every outcome
and allowing arbitrary ordinary memory, coding, adaptation and rare long
learning paths, the two-call switch scores at least $0.7135$, whereas every
ordinary receiver with expected cost at most two module calls scores at most
$0.690605$ (rounded upward). The stated control-visibility variant retains a gap.

This is a mathematical comparison within its interface, supported by the
repository proofs and checks. It is not a persistent-device calibration
theorem, a runtime comparison or a demonstrated fault-tolerant architecture.
The noise layer follows each entire module; it does not represent faults
throughout every gate used to compile that module. Its per-site strength
decreases with $n$. Reusing a frame, providing environment records, or adding
native mode controls changes the inference problem.

## Real workloads and the model mismatch

### Fresh private frames and delegated computation

Privacy can explain why a recovery provider lacks a frame key, but it does
not by itself establish NR-R01's complete interface. The natural Clifford
variant is already covered by [NR-R06](architecture-baselines.md#nr-r06):
Clifford-conjugated Pauli axes with physical Pauli noise are channels in
the public Pauli basis. Ordinary Bell queries sample their actual error
labels and simulate the full switch without learning or revealing the key.
Frame freshness does not remove that simulation. NR-R01 instead requires
its much stronger approximate sixth-design condition; Clifford frames alone
do not satisfy the theorem's premise.

Ordinary blind computation also need not conceal every error record.
[Baranes et al.](https://arxiv.org/html/2505.21621v1) let the server extract
syndromes while the client tracks a private Pauli frame and decodes the
communicated outcomes. This is a specific interactive architecture, not a
universal optimality claim, but it prevents treating blindness as a general
ban on checks or feedforward. The
[distributed solid-state experiment of Wei et al.](https://doi.org/10.1126/science.adu6894)
uses photon measurements and client records for blind matter-qubit gates;
it does not supply NR-R01's two coherent opaque module ports.

A surviving delegated-computation proposal must justify why the source is
offline after issuing the scrambled challenge, why no useful frame-correlated
program or native check can be provided, and how the efficient sixth-design
module circuit retains the stated post-module noise model. It must then
compare a useful confidential computation or recovery task with ordinary
blind error correction, including communication and client latency. The
existing privacy protocols do not currently provide that application.

### Gate-layer calibration and scheduling

Choosing echo settings, concurrent gate groups and recalibration times is a
real persistent workload. For example, [Wu et al.](https://arxiv.org/abs/2610.11477)
study parallel calibration and drift maintenance using ordinary simultaneous
benchmarking. A proposed switch diagnostic must predict the error of the
actual production cycle. Sequential isolated modules need not reveal
crosstalk that occurs only during overlapping pulses.

Full global tomography is an unnecessarily weak default comparator.
[Cycle benchmarking](https://doi.org/10.1038/s41467-019-13068-7) estimates cycle
performance under its randomization and noise assumptions;
[gate-set shadows](https://doi.org/10.1038/s41467-023-39382-9) reuse random
sequence data for multiple gate-set properties. Local or sparse model fitting
can also be appropriate when its assumptions fit the device. Calibration
data and computation must be amortized across subsequent settings and jobs.

The [phase-calibration benchmark NR-R15](metrology.md) checks a stronger
positive starting point: a known switch protocol exceeds every ordinary
strategy restricted to two independent phase/amplitude-damping queries.
An exact dual certificate supports that comparison. It still does not
give an unrestricted calibration rate: an explicit three-query ordinary
feedback round beats the plain two-call switch's information per query, and randomized
launches beat it at mean cost two. A retained cold bath also admits an
ordinary two-visit echo that beats the independent-slot switch. The next
comparison must therefore use actual reset, timing, return and interrogation
rules rather than import a hard two-query bound as a throughput theorem.

The [drifting measurement-alignment benchmark NR-R18](alignment.md) makes
that distinction in an unread-meter model. It proves a finite advantage
under a strict two-call cap, with an exact ordinary adaptive certificate.
Ordinary background-free tests already have the same small-angle scaling;
longer rounds and accessible consistent measurement labels change the
comparison again. Fixed control background destroys the ideal local
null advantage. An application must explain why two modules share a frame
throughout a round, why it is fresh before the next round, and why useful
records and pilots are unavailable. Existing polarization tracking and
recorded-meter experiments do not yet supply that full interface.

A switch minus probability measures Kraus-commutator information, which need
not equal a useful scheduling quantity. Commuting channel superoperators can
produce a nonzero signal. Weak coherent errors can produce a fourth-order
signal even when ordinary repeated sequences amplify their generators.
[NR-R06](architecture-baselines.md#nr-r06) gives exact ordinary screens for
calibrated orthogonal-unitary faults and a continuous-angle scalar example.
These do not settle hardware cost: Bell probes require preparation, storage
and readout, while the switch requires coherent routing and a clean control.

### Displacement-area calibration with a complete optical budget

Transverse optical displacement experiments provide a concrete signal
and a real implementation, rather than only a calibration analogy. The
[displacement result NR-R16](geometric-calibration.md) compares their
one-use interface with the published ordinary conditional-force echo,
a bus-returning loop and classically varied shot orders. Initial probe
energy, maximum energy, repeatable component values and access to later
preparation are different resources. An initial-energy bound with the
same oracle order in every shot does not settle a reusable two-setting
calibration experiment. Native cavity conditional-displacement signal
processing is also an ordinary hardware comparator.

The next finite test is the complete single-photon optical echo, including
polarization-controlled spatial parity, repeat passes, aperture, source
conditioning and every detector port. Measure its launch-normalized
information or global calibration error against the switch at the same
number of displacement elements and drift window. NR-R16 gives the local
loss/visibility threshold and identifies which measured component facts
still fall short of a full comparison. No new native gain follows from
those component values alone.

### Correlated dephasing and live quantum memories

Two concrete tasks already have strong ordinary recovery loops.
[Kurilovich et al.](https://doi.org/10.1103/1bl4-b2f7) identify correlated phase
bursts using monitor measurements and code records, with echo mitigation.
[Loenen et al.](https://doi.org/10.1103/zgm8-6b8l) preserve nuclear-spin memory
during network attempts using spectator information, including both
measurement/feedforward and a gate-based alternative. The appropriate
endpoints are retained entanglement, logical error or usable Bell pairs per
second, including the disturbance and latency of monitoring.

For classical rotations about a common $Z$ axis, every realization commutes:
the elementary switch commutator signal is zero for any phase-correlation
law. Ordinary Ramsey/echo and spectator measurements can still detect severe
memory errors. For calibrated orthogonal rotation axes, two ordinary Bell
probes reproduce the scalar signal in the stated classical-angle model;
other ordinary quadratures can expose sign correlations that it misses.
These scoped screens are recorded in
[NR-R06](architecture-baselines.md#nr-r06).

Quantum correlations do not by themselves remove ordinary alternatives:
[two-qubit quantum-noise spectroscopy](https://doi.org/10.1103/PRXQuantum.1.010305)
accesses cross spectra under its noise model without entangled preparation
or joint readout. A time-routed switch could probe a different joint process,
but its bath history, arrival times, reset and probe backaction must then be
specified. Marginal channel maps alone do not determine that interface;
[latent-time-correlation protocols](https://doi.org/10.1103/PhysRevResearch.3.043147)
make this distinction explicit. A generic switch-based burst alarm is not
supported by the current evidence.

The [shared-bath calibration screen NR-R14](backaction.md#nr-r14) makes the
calibration problem concrete: identical Ramsey data can require opposite
echo-versus-no-pulse storage decisions. Under its native pure-dephasing
coupling, however, an ordinary echo reproduces the complete phase-resolved
switched bath/reference instrument and every later adaptive utility.
Known sensor-only interventions around a shared unknown bath interaction
also have ordinary controlled-dilation implementations. Limited echo data
need not predict a held-out uninterrupted decoupling sequence, so direct
target-sequence calibration and pump/reset/record tests remain comparators.
This is a calibration-transport screen, not an architecture advantage or a
general exclusion of unknown joint interventions.

There is a named optical testbed with a longer-lived oscillator:
[Spinnler et al.](https://doi.org/10.1038/s41467-024-53882-2) couple a quantum
dot to a phononic-crystal mode with frequency $1.466\,\mathrm{GHz}$,
quality factor $2100$, coupling $g_{\mathrm{ep}}/(2\pi)=2.9\,\mathrm{MHz}$
and thermal occupation about $58$ at $4.2\,\mathrm K$. The corresponding
energy-ringdown time $Q/\Omega$ is about $228\,\mathrm{ns}$, whereas the
QD excited-state (negative-trion) lifetime is $1.18\,\mathrm{ns}$. Those
scales permit a bath-memory calculation across optical histories; they do
not establish coherent overlap
of all radiative and other environmental records. The demonstrated response
admits a classical mechanical approximation and is measured by ordinary
photon autocorrelation spectroscopy. Sideband driving, cooling and heralding
are further ordinary baselines. A useful comparison must keep the optical
and mechanical outputs and their reset dynamics, rather than infer quantum
utility from the oscillator lifetime.

This engineered mode must not be conflated with a bulk acoustic bath.
[McCutcheon's quantum-dot model](https://doi.org/10.1103/PhysRevA.93.022119)
uses an acoustic cutoff $\omega_c=2.2\,\mathrm{ps}^{-1}$, whose inverse is a
characteristic cutoff timescale of about $0.455\,\mathrm{ps}$, and exposes
non-Markovian effects in ordinary emission spectra. Such a model does not by itself preserve bath
coherence over nanosecond order routing. Pulse profiles and complete
two-history overlaps remain necessary in either regime.

### Multimode pointer retention

This is the closest operational interpretation of the main paper's fixed
unknown-dephaser model. For complete rank-one dephasers in bases
$\{|u_i\rangle\}$ and $\{|v_j\rangle\}$,

$$
v=\frac1D\sum_{ij}|\langle u_i|v_j\rangle|^4,
\qquad p_-=\frac{1-v}{2}.
$$

Here $v$ is the average survival of a uniformly chosen first-basis pointer
label after the second dephaser. The same unknown basis may persist across
all calibration calls in the channel-only model. A Choi-overlap experiment
has signal $v/D$, but this particular comparator is not an ordinary lower
bound.

Native access can eliminate that suppression. If an encoder prepares
$|u_i\rangle$ and a decoder tests its label, one call to the second module
gives a Bernoulli retention sample. If the first module supplies stable
Lüders outcome records, the ordinary sequence $E$–$F$–$E$ on $I/D$ estimates
$v$ by comparing its first and last labels. Neither method needs a classical
description of the basis. [NR-R08](architecture-baselines.md#nr-r08) states
these shortcuts and the separate role of the number of unread sectors.

Complete rank-one dephasing is entanglement breaking. This interpretation
therefore concerns classical pointer retention, rather than storage of an
arbitrary logical qubit. Quantum-memory applications require the actual
degenerate sectors or noiseless matrix factors, plus an executable encoder
and decoder. Demonstrated
[dynamically generated protected memories](https://doi.org/10.1088/1361-6633/ad6805)
use known symmetry and control structure;
[direct unknown-subspace discovery](https://doi.org/10.1103/PhysRevA.86.052101)
is also an ordinary baseline. A large protected sector is not evidence of
many hidden measurement outcomes.

## Why a photonic implementation needs an instrument-first test

Unmonitored phase averaging is physically plausible, but a frozen multimode
fiber implements predominantly coherent transport, not complete pinching.
An averaged model
$E(\rho)=\int p(x)T(x)\rho T(x)^\dagger\,dx$
reduces to fixed-basis dephasing only under additional conditions. A local
approximation $T(x)\simeq T_0e^{ixQ}$ requires accounting for the transport
$T_0$, checking one generator over the relevant range, and measuring the
remaining off-diagonal coherence. Loss, polarization mixing and leakage
must be included.

Ordinary optical access is powerful. A
[reconfigurable multiplexed quantum photonic network](https://doi.org/10.1038/s41566-025-01806-x)
characterizes its multimode mixer with classical light and a camera.
[Measured transmission matrices](https://doi.org/10.1103/PhysRevX.11.021060)
identify deformation-resilient modes. An unavailable environmental record
does not forbid pilots: pilots measure the probe output. Learning the
transport or delay modes may also supply the native pointer controls needed
for the direct retention test.

There is a narrower motivation for quantum-level verification after
classical stabilization.
[Stevens et al.](https://doi.org/10.1103/63wh-4x54) use simultaneous entangled
probes to detect nonunitary channel effects missed by bright polarization
tracking, with ordinary ancilla-assisted reconstruction. This supplies both
a real verification problem and a strong ordinary comparator; its
polarization-qubit setting does not establish an opaque high-dimensional
pointer channel.

The cost of an ordinary quantum reference is device specific. For a
polarization-qubit target, the path qubit used as a switch control has the
dimension of a full Bell reference. [Yoon-Ho Kim](https://doi.org/10.1103/PhysRevA.67.040301)
demonstrated deterministic preparation and measurement of all four
single-photon path/polarization Bell states using linear optics. A separate
stored photon and a probabilistic two-photon Bell analyzer are therefore
not intrinsic costs of that ordinary diagnostic.

Using this encoding still requires the full path-preserving instrument
$\mathrm{id}_{R}\otimes\mathcal E$, including off-diagonal path blocks.
Equal reduced polarization channels on two paths do not suffice: mode
dependence or arrival-time bath records may corrupt the reference. Native
preparation optics, readout ports, routing and drift must be matched. This
resource observation does not replace unknown-input recovery with destructive
tomography, and a single path qubit is not a full reference for a
high-dimensional target. No demonstrated high-dimensional memory gap is
established by the qubit example.

## Go/no-go protocol

1. **Choose a real decision.** Start with two persistent multimode modules
   under naturally occurring fluctuations. Prespecify whether the diagnostic
   triggers recalibration, selects a link pairing or validates an existing
   mode encoder. Score held-out transmission or decision error, rather than
   precision of $v$ alone. Do not impose a SAME/MUB promise or hide metadata
   that the operator possesses.
2. **Inventory native access.** Record outcome labels, phase settings,
   encoder/decoder controls, inverses, bright and multispectral pilots,
   reference wavelengths, Bell probes and quantum storage. Determine which
   information persists between jobs.
3. **Validate the physical interface.** Test the reduced-channel model,
   stationarity and drift window independently. Verify that both orders use
   the same effective forward modules: reverse propagation can implement a
   different transfer matrix. Characterize control visibility, which-order
   leakage and mode-dependent loss. Count loss and rejection as outcomes.
4. **Run the strongest admitted ordinary methods.** Include recent and
   reused transmission-matrix data, rapid pilots, direct deployed-encoding
   tests, accessible-label retention and entangled probes. Apply
   [NR-R06–08](architecture-baselines.md) before claiming a query advantage.
   In particular, [NR-R07](architecture-baselines.md#nr-r07) shows why
   persistent finite-frame families permit amortized learning; it does not
   promise a practical runtime for exhaustive classical fitting.
5. **Match resources within drift windows.** Randomize acquisition times and
   reserve held-out drift episodes. Charge optical power and detected
   photons, bandwidth and temporal resolution, all device traversals,
   routing loss, reset/readout, storage, hardware occupancy and classical
   fitting latency. For quantum-memory baselines, use measured memory cost:
   [large-scale entanglement-enhanced process learning](https://www.nature.com/articles/s41467-026-75553-0)
   already includes noisy auxiliary memory and sampling overhead.
6. **Use decisive controls.** Check known-pointer or visible-record cases,
   commuting phase noise, calibrated Pauli faults, loss-induced bias and
   timing artifacts. For a gate-layer variant also include
   simultaneous-only crosstalk. These controls test whether a new signal
   actually diagnoses the proposed failure.
7. **Proceed only on downstream benefit.** Require a prespecified,
   statistically supported gain in the held-out decision at matched total
   cost. Stop the architecture claim if ordinary calibration remains valid
   throughout the useful window, native labels recover the direct test, or
   routing and control overhead erase the benefit. A finite hardware gain
   would still require a separate argument for any asymptotic claim.

The multimode calibration candidate still requires a useful persistent pointer-like
channel, inaccessible records, no cheap pointer preparation/readout,
insufficient ordinary calibration within its drift window, and a realizable
coherent-order interface whose extra information predicts a useful action.
The checked primary sources establish individual ingredients and important
ordinary workarounds, not this combination. These assumptions need resolution
on a named device before extending the recovery theorem into an architecture
claim. This is a bounded assessment, not an exhaustive
novelty or priority claim.

## Distributed-computing link screen

Delivering a stored Bell pair for a remote gate is a concrete architecture
objective. [Main et al.](https://doi.org/10.1038/s41586-024-08404-x) demonstrate
distributed trapped-ion computation through a heralded optical link;
[Knaut et al.](https://doi.org/10.1038/s41586-024-07252-z) demonstrate networked
nanophotonic memory nodes. The output to compare is a usable matter Bell pair
per wall-clock time, including waiting-induced memory error.

The [communication results](communication.md) give three precise screens.
Pure absorbing-vacuum loss produces the ordinary serial erasure channel plus
a receiver-preparable flag (NR-R09). A genuinely independent EB slot gives a
one-ebit-per-use rank ceiling; mandatory control dephasing also admits an exact
known-channel simulation with one equally dephased qubit wire (NR-R10).
This does not grant a free wire to every abstract switch placement. Nor can
the local Bell-label readout of NR-R06 be imported across separated labs
without paying for joining the halves.

The elastic accepted state-carving operators in the named cavity-node model
preserve a common photon time-bin label and act on disjoint memories.
Consequently they commute Kraus by Kraus, and the entire accepted switched
instrument is already ordinary serial processing (NR-R11). Elastic contrast
errors and local spin errors preserving those labels supply no extra order
syndrome. Mode-changing scattering is a different hypothesis, not a conclusion
from the documented elastic model.

The remaining narrow optical candidate is retained inelastic spectral
scattering followed by a downstream frequency-dependent reflection. A
[quantum-dot waveguide analysis](https://doi.org/10.1038/s41534-023-00717-5)
identifies near-carrier incoherent scattering that cannot simply be removed
with a distant spectral filter. This is a different platform, and does not
establish that a switched circuit improves its Bell-pair yield. The next
calculation must keep outgoing frequency, which-time bath records, local
spin resets and actual photon heralds. Compare ordinary frequency-resolved
selection, commuting spectral-phase check sandwiches and coherent same-order
delayed paths, as well as both serial orders. In a two-frequency model, a
before/after controlled frequency-$Z$ check preserves a diagonal elastic
instrument and rejects cross-bin jumps. Its spectral resolution, pulse
reshaping, additional delay and helper faults must be included. If bath
emissions resolve the two histories, a switch's rejection of
half the scattered events can be ordinary path error filtration. Charge
extra loops, stabilization, conversion and control coherence on the same
physical graph. A Markov bath does not alone imply resolved histories:
overlapping photon excitation profiles can emit at the same laboratory
times. Compute their actual overlap from the pulse and preceding-node
response, rather than substituting a dephasing rate for a two-history overlap.

The finite two-frequency candidate has failed this stronger ordinary
screen: checks at each node remove all cross-bin jumps, including two
shifts that return to the original bin and evade a single global check.
Two local check sandwiches use four controlled spectral phases. Their
accepted branch can reuse one helper sequentially after plus-port selection
and reset; two simultaneously retained helpers are not a necessary cost.
The physical routing, selection and reset still count. This does not exclude
a finite hardware tradeoff with one order control.
The exact projection identity is replayed in the communication checks.
It is not a continuum scattering calculation or a fit to the named
experiment. Resolve the measured frequency kernel and price these
helpers before treating the formal noncommutation as an application.

### Private key detection

Quantum key distribution supplies a useful endpoint that bright classical
channel pilots cannot replace. The
[photonic proof of principle by Valibouse et al.](https://arxiv.org/html/2608.13561v2)
demonstrates control-based eavesdropping detection without disclosing raw-key
outcomes. Its measurement requires a path-entangled ancillary photon,
postselected two-photon interactions and joint path readout. An eavesdropper
can access the implemented control; the authors do not claim a secure
protocol. Retained-qubit statistics are not secret-key rates.

The displayed ideal selected instrument also has a substantial event cost.
Bob's coincidence map has Kraus operators $P_j/\sqrt2$, with success $1/2$.
For the circular system input, Alice's selected projector and the sum of
Bob's outcomes have accepted mass $1/4$ in either order: the first order
gives $\|P_i|L\rangle\|^2/2=1/4$, while the reverse uses
$\sum_jP_j|L\rangle\langle L|P_j=I/2$. Keeping all control flags preserves
that mass; unbiased same-basis sifting leaves at most
$1/8$ retained events **per generated entangled pair**, before optical loss
and detector inefficiency. This is a normalization bound for those selected
operations, not a key-yield or security bound.

[Spencer-Wood's ordinary two-way private-detection protocol](https://arxiv.org/html/2303.03893v3#S6)
already adds a terminal Alice measurement after Bob returns the measured
state. Bob can destructively measure and prepare a replacement photon in
the recorded state; this needs a source and feedforward latency, but no
order-erasing ancillary photon or preserved quantum reference. Its complete
security analysis is also unresolved, so it is a resource comparator rather
than an equally proved secure replacement. A deployable claim needs full
security and finite-key rates against ordinary one-way, biased-basis and
two-way methods, with source brightness, all postselection, transport,
readout and reset charged. The current experiment establishes no such
matched hardware advantage.

## Native computation and coherent dispatch

The [native-check baselines](architecture-baselines.md#nr-r06) also prevent
promoting a known Clifford layer or a read-only classical-bit lookup merely
because recompiling its full unitary is expensive. Cheap transported checks
can use the same native calls. Helper gates, their noise and memory must be
costed, rather than assumed free by either implementation.

Distinct commuting modules need not have identical ideal unitaries. When
their common eigenbasis is known and accessible, an ordinary coherent
basis-label check rejects off-diagonal single faults with the same Bell-good
weight as the switched plus branch. The first-order comparison does not
extend to arbitrary double faults, and copying a general basis label can
need a full register of helpers. For number-diagonal Kerr or SNAP operations,
a modular-number check supplies a more specific ordinary loss test; one
parity helper detects every first-order photon loss. These are existing
verification resources, not free controls for an unknown eigenbasis or
unavailable traveling-photon QND measurements. NR-R06 states their exact
scope, double-fault counterexample and native costs.

The [recorded parity-braid screen in NR-R08](architecture-baselines.md#nr-r08)
compares an ordinary three-parity-measurement braid with a specified balanced
switch construction using mean six parity measurements and two control
readouts. Reading the control first and skipping a dispensable final parity
measurement reduces the latter mean to $11/2$, with the same control cost.
Both use Pauli and syndrome tracking; any correction needed to return an
untracked physical output must still be implemented and costed. These are
counts for the displayed protocols, not an optimal architecture bound.

The [unitary-braid magic result NR-R17](braided-magic.md) concerns a
different endpoint: a useful non-Clifford gate or raw logical magic state.
Protected Ising braids and fusion records alone cannot supply its coherent
order router. A proposed hybrid spin/position interface also enables
ordinary loop and exchange-interferometer factories; their complete
physical Abelian phases and position-selection losses are essential.
The next comparison needs a named anyon/charge model, a complete
trajectory instrument and distilled/injected logical output at fixed
error per factory space and time. An ideal magic witness or a non-Abelian
fringe does not establish that cost advantage.

The [rewinding-cost analysis in NR-R05](obstructions.md#nr-r05) supplies
another stopping boundary. A particular published adaptive walk completes
almost surely but has infinite mean query count, and independent loss
reduces its delivered success. The tested fixed-axis optical evolution
also admits an ordinary Pauli echo. Compare known-perturbation checks,
ordinary extra-query routing and modern unitary-inversion protocols
before translating a conditional rewinding experiment into a useful
recovery-rate claim. This finding concerns the stated walk and access
model, rather than every quantum rewinding algorithm.

Unknown analogue internals do not automatically prevent ordinary checks.
If a known implementable involution commutes with the ideal Hamiltonian,
the same before/after check in NR-R06 preserves its full evolution and
tests arbitrary interval faults without learning that evolution. Its
controlled helper and readout costs remain real. Short-time coherent
order symmetrization must also be compared with randomized ordering and
ordinary symmetric splitting, including available half-duration controls.
[Vrajitoarea et al.](https://arxiv.org/abs/2602.06108) demonstrate genuine
quantum-controlled many-body dynamics and a many-body echo, but do not
supply two opaque switchable many-body modules. Similarly,
[Kraft et al.](https://doi.org/10.1103/s96t-n8tx) learn Hamiltonian and
dissipative parameters on trapped-ion hardware: their long-time validation
uses classical simulation, while their measurement-only bounds concern
short times. Large Hilbert-space dimension alone is not a calibration
lower bound for these structured generators.

A separate conditional construction concerns coherent subroutine dispatch
through a dephased program register. The
[quantum control machine](https://arxiv.org/abs/2304.15000) motivates coherent
control-flow semantics, but is a theoretical architecture and does not supply
a native faulty instruction interface. The familiar self-switch correction
for anticommuting random unitaries already appears in
[Chiribella and Kristjánsson](https://arxiv.org/abs/1812.05292).
The [dispatch result NR-R12](dispatch.md) gives the exact correction and
the full-output ordinary two-versus-three-call boundary for its opaque
indexed-unitary interface. It also includes a four-call ordinary simulation
in two parallel rounds. Writing the prior mechanism as program-counter
recovery does not establish novelty or a hardware benefit. A surviving
dispatch proposal must specify its native
ports, distinct switchable noisy slots, reusable calibration, direct compiled
and ordinary three/four-call simulations, parallel execution and controller
occupancy. Repeating one noisy processor at two fixed chronological times
does not by itself supply a switch of two independent noisy slots.
Conversely, quasistatic counter-phase noise can cancel in two ordinary
repetitions. A proposed temporal-noise model must preserve the required
switch coherence without inadvertently granting that ordinary echo.

The dispatch note now gives an explicit consistent dilation: private,
coherent visit heads select retained independent fault coins by invocation
number. Both switch histories finish with the same heads, while ordinary
repeats consume fresh coins. This requires protected quantum event memories,
reversible addressing and no exported timestamps. With ideal routing and
equal exponential head dephasing, visibility $0.97$ requires head $T_2$
about $66$ times the separation between visits. It resolves logical
consistency without establishing a cheap native module. Rewind, coin readout
and reset controls cannot be withheld if the operator actually has them.

The same note supplies a stronger physical comparison for time-varying
classical phase fields. Ordinary paths that revisit one station in each
arm produce the same corrected quantum output for every phase history as
paths that interchange stations. For independent identical centered Gaussian
fields, the ordinary alternatives match the best all-outcome postdecoder;
with nonnegative temporal correlation, ordinary same-order filtering also
dominates the entire accepted Bell-fidelity frontier. These statements
require the specified vacuum extension, local delay loops and matched loss
and helper assumptions. They do not cover nonclassical bath backaction.

Noncommuting conditional dynamics have a real constituent model:
[Taminiau et al.](https://arxiv.org/html/1309.5452) give electron-controlled
nuclear Hamiltonians $H_0=\omega_L I_z$ and
$H_1=(\omega_L+A_\parallel)I_z+A_\perp I_x$. An electron flip after
conditional free evolution has the algebraic dispatcher form.
[Hernández-Gómez et al.](https://arxiv.org/html/1808.08222) distinguish
coherently coupled nuclei from a residual stochastic bath and show when
classical bath predictions fail under changed controls. Neither source
supplies two matched routable processors acting on the same nuclear target,
the required coherent vacuum interface, or an event-indexed fault reservoir.
Two NV centres with separate attached memories cannot be substituted for
that missing port. Their calibrated decoupling sequences remain ordinary
competitors, not evidence for switch recovery.

The application must also require the target computation. A standard XOR
lookup squares to the identity; stationary analog evolution squares to a
direct evolution for twice as long. The Quantum Control Machine's
implementation uses fixed, known primitive gates (§5.3, footnote 5), so
its program counter does not establish unknown reusable subroutine ports.
[Oracle Distillation](https://arxiv.org/abs/2609.31596) is a current ordinary
weak-query/QEC comparator for structured unknown Boolean families. It grants
ideal helper operations and memory and leaves physical QRAM noise shaping
open; it is not a theorem for arbitrary unknown unitaries or a demonstrated
native processor.

The [composite-lookup screen](native-lookups.md) tests a different useful
target: a clean phase marking the intersection of two classical datasets.
Measurement-based uncomputation gives an exact ordinary protocol with
mean $2.5$ reads; immediate rejection allows $80\%$ perfect accepted output
at mean two reads. The obvious balanced switch followed by junk-only
erasure succeeds at most one third of the time. A maintained intersection
table is a further ordinary baseline when the operator owns both datasets.
That displayed switch protocol should therefore not be pursued as a winner.

A [superconducting coherent-router demonstration](https://arxiv.org/abs/2505.13958)
provides a concrete small testbed for route–call–return instruments,
including terminal address erasure selection. Its address readout and
classical discard of level-$1$ shots do not demonstrate a nondestructive
binary code-space measurement preserving an unknown address. Data sites
start in physical $|0\rangle$, not an orthogonal vacuum sector. Applying
arbitrary unknown leaf gates also changes unselected sites and can leave
which-address junk; a known leaf phase preserving $|0\rangle$ is a different,
more structured interface.

There is already a precise ordinary screen for the router's address-fault
alarm. Its ideal controlled swaps leave the address unchanged. Switching a
fixed noisy route with a known diagonal address involution has exactly the
same full flagged instrument as an ordinary controlled-phase check sandwich
using one route call. On code-supported inputs, code-versus-leakage detection
needs only a single controlled phase after the route. Pure diagonal address
dephasing triggers neither construction. The
[native address-check proof](architecture-baselines.md#nr-r06) and exact
qutrit replay state the shared-map and helper-cost conditions.

The next native calculation must use the actual noisy gate sequence and
preserved output registers, including leakage, unselected-site states and
reset/readout records. Compare the measured cost of the single post-check
and full check sandwich with any proposed order router. Across these
platforms, charge complete shot time, accepted yield and hardware occupancy;
one control readout does not automatically beat two destructive detections.
Calibration must be amortized within the actual drift window. An exclusive
switch claim cannot follow from granting it a clean known symmetry or a
coherent vacuum port absent from the ordinary hardware. A surviving task
must also beat direct compiled control, conditional uncomputation and reuse.
No present screen establishes that advantage.

### Nonlinear photonic evolution: the next complete-instrument test

A repeated passive photonic operation is not enough to supply an expensive
quantum workload. For a known single-particle mode matrix $M$, compute and
compile $M^2$ into one freely programmable mesh. Second quantization obeys
$\Gamma(M)^2=\Gamma(M^2)$ on every photon-number sector: both sides transform
each creation operator by $M^2$ and preserve vacuum. Thus an exponentially
large multiphoton Fock space does not invalidate this shortcut. A
[20-mode universal processor](https://doi.org/10.22331/q-2023-08-01-1071)
is a concrete instance of the programmable interface; actual programming,
calibration drift and compilation errors must be included.

[Nielsen et al.](https://doi.org/10.1038/s41467-025-66205-w) provide a more
substantive next model: two-photon nonlinear scattering interleaved with
programmable linear optics, used for anharmonic molecular dynamics.
Nonlinearity removes the passive matrix-squaring shortcut. The published
platform has one quantum dot, however, and its measured nonlinear response
includes spectral-mode distortion. A fitted nonlinear fringe phase is not
by itself a reusable controlled-phase channel. Two matched independent
modules and an order router cannot be assumed from that experiment.

The [scattering comparisons in NR-R11](communication.md#nr-r11) now separate
three cases. Bare detuning-only pairs with common monitored coupling commute
on the entire accepted two-photon field. Unequal couplings escape that
identity and give a conditional gate on a specified correlated relative-mode
code. Its best resonant endpoint is already ordinary serial scattering;
for the stated finite-pulse target, a kernel-transpose identity preserves
the same correct-output weight in the ordinary order. Conditional error
rejection alone is therefore insufficient. The minus branch also annihilates
the vacuum and one-photon sectors, preventing its use as a heralded dual-rail
controlled-phase gate in the specified routing. An ideal whole-pair passive
vacuum herald retains both photons at half the abstract branch yield;
unmonitored loss can falsely herald missing photons. An independent order
ancilla can be measured without consuming the targets, but its preparation,
coupling, storage and readout must be supplied and charged.

Photon-preserving bath noise is a separate case. If nonvacuum bath records
resolve the early and late windows while the empty-record products commute,
ordinary randomized same-order delayed paths reproduce the complete measured
order-flag and photon-output instrument. This comparison uses three global
windows instead of two, with the same two occupied traversals; its extra
delay, route loss and visibility matter. A Markov model alone does not imply
disjoint records for finite pulses with long scattering tails. The proof
gives an error bound conditional on a uniform record-tail estimate, but the
native two-emitter estimate remains to be calculated. Retained phonon modes,
overlapping histories and coherent inter-emitter feedback are not closed by
that reduction.

There are now more specific physical starting points than an assumed pair
of copies of Nielsen's processor.
[Hallacy et al.](https://arxiv.org/abs/2511.07640) independently tune two
chiral dots in a shared waveguide and measure spin-dependent photon
correlations. Reversing propagation exchanges directional couplings and
optical transitions; it does not automatically supply the same two local
modules in reverse order. [Hansen et al.](https://arxiv.org/abs/2605.18525)
demonstrate collective few-photon transport through coupled emitters with
both forward and backward outputs. Their device is a joint scatterer, so
its coherent reflection and shared dynamics cannot be replaced by a product
of independent forward channels.

The next test is the full input-output model of one such actual device.
Prespecify a useful detuning or spin-setting decision, or a delivered
few-photon state/gate, and compare ordinary phase/correlation measurements,
pulse optimization, spectral selection and coherent delayed paths. Retain
all output ports, emitter and phonon records, and the valid-output herald.
If a reversed route changes the local interaction, compare that physical
process directly rather than importing the abstract channel-SWITCH bound.
Charge source, routing, storage, reset, selection and every rejected launch.
A significant advantage on this nonlinear platform remains unestablished.
