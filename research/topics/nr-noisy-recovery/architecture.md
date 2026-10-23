# Application assessment and next experiment

[Recovery theorem](theorem.md) · [Ordinary baselines](architecture-baselines.md) · [Literature context](references.md) · [Topic](README.md)

The current results establish an advantage in a specified fresh-frame recovery
game. They do **not** yet establish a useful advantage for calibrating or
operating persistent hardware. The next investigations start from complete
device instruments and available controls, then ask whether switched outputs
improve a deployed decision. Current screens cover multimode calibration,
network entanglement and native computational layers. No checked architecture
currently meets all the required assumptions.

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

A switch minus probability measures Kraus-commutator information, which need
not equal a useful scheduling quantity. Commuting channel superoperators can
produce a nonzero signal. Weak coherent errors can produce a fourth-order
signal even when ordinary repeated sequences amplify their generators.
[NR-R06](architecture-baselines.md#nr-r06) gives exact ordinary screens for
calibrated orthogonal-unitary faults and a continuous-angle scalar example.
These do not settle hardware cost: Bell probes require preparation, storage
and readout, while the switch requires coherent routing and a clean control.

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

## Native computation and coherent dispatch

The [native-check baselines](architecture-baselines.md#nr-r06) also prevent
promoting a known Clifford layer or a read-only classical-bit lookup merely
because recompiling its full unitary is expensive. Cheap transported checks
can use the same native calls. Helper gates, their noise and memory must be
costed, rather than assumed free by either implementation.

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
and full check sandwich with any proposed order router. An exclusive switch
claim cannot follow from granting it a clean known symmetry or a coherent
vacuum port absent from the ordinary hardware. A surviving task must also
beat direct compiled control, conditional uncomputation and reuse. No present
screen establishes that advantage.
