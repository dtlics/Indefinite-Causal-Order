# Application assessment and next experiment

[Recovery theorem](theorem.md) · [Ordinary baselines](architecture-baselines.md) · [Literature context](references.md) · [Topic](README.md)

The current results establish an advantage in a specified fresh-frame recovery
game. They do **not** yet establish a useful advantage for calibrating or
operating persistent hardware. The most promising next investigation starts
from the actual instrument and available controls of an unmonitored multimode
channel, then asks whether switch measurements improve a deployed decision.
No checked architecture currently meets all the required assumptions.

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

The remaining assumptions are substantial: a useful persistent pointer-like
channel, inaccessible records, no cheap pointer preparation/readout,
insufficient ordinary calibration within its drift window, and a realizable
coherent-order interface whose extra information predicts a useful action.
The checked primary sources establish individual ingredients and important
ordinary workarounds, not this combination. The next result should resolve
those assumptions on a named device before extending the recovery theorem
into an architecture claim. This is a bounded assessment, not an exhaustive
novelty or priority claim.
