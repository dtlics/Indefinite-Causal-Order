# NR — Noisy physical state recovery

[Research map](../../README.md) · [Result index](../../RESULTS.md) · [Validation scope](../../../docs/VALIDATION.md)

This topic owns recovery and memory qualification through opaque related modules, with the
ordinary comparison charged for every invocation, including calibration
and rejected histories. It is distinct from universal switch simulation
and includes an operational capacity decision and a scalar entropy witness.

## Canonical results

| ID | Result | Source of truth |
| --- | --- | --- |
| NR-R01 | Local-output-noise recovery against arbitrary ordinary mean-query receivers | [Theorem and proof](theorem.md#nr-r01) |
| NR-R02 | Global replacement-noise gate-product recovery and exact finite certificates | [Global-noise result](global-noise.md#nr-r02) |
| NR-R03 | Obstruction to a uniform-frame local-noise guarantee | [Scoped counterexample](obstructions.md#nr-r03) |
| NR-R04 | Exact unknown-unitary implementation is impossible from full-support noisy queries | [Support argument](obstructions.md#nr-r04) |
| NR-R05 | Rejection, stochastic rewinding and finite-program limits | [Failure, stopping and retrieval boundaries](obstructions.md#nr-r05) |
| NR-R06 | Native checks, calibrated faults and ordinary path baselines | [Fault and check comparisons](architecture-baselines.md#nr-r06) |
| NR-R07 | Polynomial-query calibration of the reused finite-frame family | [Reuse baseline](architecture-baselines.md#nr-r07) |
| NR-R08 | Accessible measurement records and syndrome-sector baselines | [Measurement baselines](architecture-baselines.md#nr-r08) |
| NR-R09 | Optical loss: calibrated reductions and native record constraints | [Loss equivalence](communication.md#nr-r09) |
| NR-R10 | Entanglement-breaking slot, control-quality wire simulation and stopping bounds | [Communication resource bounds](communication.md#nr-r10) |
| NR-R11 | Accepted cavity, Raman and nonlinear-scattering instruments | [Scattering-instrument screens](communication.md#nr-r11) |
| NR-R12 | Exact coherent dispatch with a dephased counter and bounded-query boundary | [Conditional dispatch result](dispatch.md#nr-r12) |
| NR-R13 | Clean composite lookup: ordinary uncomputation and a scoped switch erasure bound | [Composite lookup screen](native-lookups.md#nr-r13) |
| NR-R14 | Shared-bath calibration transfer and exact ordinary echo/instrument baselines | [Bath-backaction screen](backaction.md#nr-r14) |
| NR-R15 | Noisy phase calibration: certified two-call benchmark and native-memory boundary | [Metrology benchmark](metrology.md#nr-r15) |
| NR-R16 | Displacement-area calibration and native ordinary controls | [Geometric calibration](geometric-calibration.md#nr-r16) |
| NR-R17 | Braided magic, coherent trajectory resources and ordinary factories | [Braided magic](braided-magic.md#nr-r17) |
| NR-R18 | Drifting measurement alignment: exact two-query limit and reuse costs | [Alignment benchmark](alignment.md#nr-r18) |
| NR-R19 | Unknown odd couplers: exact correction and expected-query fidelity limits | [Coupler benchmark](backaction.md#nr-r19) |
| NR-R20 | Hidden-basis memory qualification and channel-entropy capacity certificates | [Memory qualification](memory-qualification.md#nr-r20) |

The main result has a fixed-Bell-test formulation and a secret-state
variant. They share one frontier and one result identity. Its analytic
methods are the [local converse](methods/local-converse.md),
[causal acceptance bound](methods/acceptance.md), and
[finite-design transfer](methods/design-transfer.md).

## Reproduce the exact checks

From the repository root, with Python 3.10+ and no third-party packages:

```sh
python -S research/topics/nr-noisy-recovery/checks/run_all.py
```

The [check map](checks/README.md) distinguishes executable identities from
the mathematical arguments and cited representation/design inputs.
Generated reports stay under `_build/noisy-recovery/`; one
[current validation record](checks/validation.json) identifies the
checked sources. The recovery theorems have not been formalized in Lean
or externally peer reviewed. The existing selected Lean endpoints and
manuscript remain separately indexed.

## Interpretation and open questions

Use the canonical statements for numerical constants and noise laws.
The local theorem is an average over fresh private frames, with a local
noise layer after each complete module and per-qubit rate of order
`1/n`. It compares an explicitly declared pass/fail/reject utility under
an expected oracle-call budget. Its order-control tolerance concerns
the specified scalar dephasing model. It supplies a physical output,
without a deployed-runtime or communication-capacity claim.

The [architecture assessment](architecture.md) owns the application
requirements and next-test protocol. A significant architecture benefit
has not been established. The [memory-qualification result](memory-qualification.md#nr-r20)
connects C6 to an asymptotic storage-capability decision, with distinct
proof components for the [general-channel entropy certificate](methods/unital-entropy-capacity.md),
[orthogonal-unitary realization entropy](methods/pauli-entropy-capacity.md),
[overlap-robust extension](methods/unitary-error-overlap.md),
[ordinary support-span learner](methods/pauli-subspace-calibration.md),
[structured memory tests](methods/memory-ordinary-tests.md),
[working-code verification](methods/memory-code-verification.md),
[decoder bootstrap and Petz costs](methods/memory-code-bootstrap.md), and
[native cost screens](methods/memory-native-cost.md). The
[rare-good screening component](methods/memory-stream-screening.md)
prices an explicit survivor code and gives a conditional classical-address
selection saving, while leaving the physical stream and native interface
unverified. The next test must
justify the private orientation, usable encoding and full repeated-slot
interface on one platform. In particular, the fresh-frame converse does
not extend to reused devices after calibration; the ordinary reuse
baseline is in NR-R07. NR-R06 also closes deterministic bare-switch recovery
for calibrated Pauli and tensor-product qutrit Weyl noise using one helper
and checks on at most two physical sites. Its
[product-probe calibration corollary](architecture-baselines.md#nr-r06-deterministic-pauli-calibration)
counts training and reuse for approximate Pauli recovery without a quantum
reference bank. Its common preparation/final-control
noise extension preserves the comparison under its specified ordering;
in-circuit correlated faults and heralded tasks require separate analysis.
The encoded-Pauli comparison separately preserves the full output on the
specified two-qubit code using ordinary decoding, clean control storage
and either two nondemolition reads or two coherent record qubits. These
extra ports and their timed errors remain charged.
The [graded poisoning comparison](architecture-baselines.md#nr-r06-fermionic-poisoning)
extends to arbitrary even mode counts: one ordinary helper matches or
exceeds the minus-filter yield and its best recovered Bell fidelity on
the final parity-accepted code, including receiver filters scored on a
Bell input. Its separate
tetron flag compiler reproduces that code instrument; unequal or correlated
physical poisoning requires a new analysis. Its
[microscopic contact component](architecture-baselines.md#nr-r06-thermal-contact-history)
adds Gaussian bath-correlation bounds and an ordinary compiler for the
specified isotropic contact schedule. Its general Pauli-diagonal,
scalar-cross-map compiler also covers anisotropy with paid known-frame
checks and calibrated parameters. A useful application still needs a
required contact operation and a matched storage/control comparison.
The [required BCS-gate screen](architecture-baselines.md#nr-r06-required-bcs-gate)
derives the clean-gap correlation boundary, a restricted static
retained-bath estimate and ordinary ideal-gate compilers. Two certified
five-pulse witnesses delimit a separate hypothetical drift comparison;
neither the noise law nor a native selector is established by that source.
The finite-energy Jaynes--Cummings comparison
closes its specified equatorial decision benchmark while preserving the
source's isotropic and four-box restrictions.
The [noisy-search component](methods/noisy-search.md) supplies an ordinary
full-channel compiler for calibrated depolarizing slots and separately
counts all-plus Grover restarts, verification and actual controller costs.
The [fault-parity controller component](methods/binary-fault-controller.md)
proves controller-memory requirements for response-uniform fault-parity
instruments, including cross-dual Pauli families and distinct input-arrival
times. It distinguishes closed controls from intermediate records and
reset, and counts the quantum programs needed before future input arrives.
Bypass, calibrated resampling and pure pilots remain stronger ordinary
options for other endpoints. The
[controlled-unitary correlator](methods/memory-native-cost.md#nr-r20-controlled-unitary-correlator)
adds an ordinary one-helper memory test when the specified coherent side
port is available, with conditional records and repeated-use costs charged.
Recorded Lüders measurements have the ordinary baseline in NR-R08.
Its [central-fault comparison](architecture-baselines.md#nr-r08-central-involution)
also distinguishes paired compatibility from individual logical
correctness using a separately charged ordinary known-state probe.

The next application questions concern a physical unmonitored multimode
workload, retained inelastic scattering in a matter-photon link, a
native coherent-dispatch interface, and prediction across control histories
in a retained quantum bath. First establish each instrument,
available records and controls, and the best ordinary method; then
compare useful task outputs at matched time, memory, calls and routing
cost. The [Raman instrument and ordinary SWAP baselines](communication.md#nr-r11-raman-swap)
leave the lossy finite-frequency helper/source comparison open. The
mechanical-memory assessment separately specifies held-out storage
against demonstrated ordinary echo/CP control and its missing coherent
profile interface. The [communication note](communication.md) identifies why pure
loss and the documented elastic cavity model do not suffice. The
assessment gives explicit go/no-go tests and source-specific gaps.
The dispatch result separates its exact hard-query boundary, achievable
ordinary approximation families, qualitative fixed-dimension mean-cost
gap and microscopic temporal models. Its correction mechanism is known.
Native slot cost, useful approximation margins, parallel execution,
compilation and calibration reuse still need an architecture comparison.
The displayed composite-lookup switch fails the ordinary uncomputation
screen. These query statements alone are not deployed runtime gains.
The shared-bath result makes a useful calibration failure explicit, but
ordinary Hahn echo already produces the complete proposed order-controlled
instrument. Known controllable measurement/reset dilations also have an
ordinary chronological implementation. Predicting a useful held-out
memory decision at lower total cost remains the next test, with ordinary
phase-resolved echo, retained records and direct schedule calibration
included.
The [microwave readout comparisons](architecture-baselines.md#nr-r06-readout-noise-floor)
and [full conditional port model](architecture-baselines.md#nr-r06-conditional-microwave-readout)
require fixed cavity loading, measured signal/idler/bath correlations and
all-record error--time--disturbance costs before a native helper advantage.
The [phase-calibration benchmark](metrology.md) independently certifies a
known finite-query switch advantage, but preserves its hard two-call scope.
Longer ordinary rounds, emitted timing records and coherent bath reuse
change that comparison. A native calibration-rate advantage remains open.
Its known-auxiliary-gate analysis gives an exact ordinary pre/post compiler
and separates coherent signal reversal from its two classical direction
channels. The granted joint signal/bath interface must be compared directly;
its reduced channels alone do not justify a noise-protected extension.
The [material-pointer construction](architecture-baselines.md#nr-r08-material-pointer-clock)
supplies a concrete array dilation and common-finish ordinary compiler.
Its next test needs actual cross-history records and available pointer
echo, rather than inferring order coherence from a quoted memory lifetime.
The [Gaussian support extension](obstructions.md#nr-r04-gaussian-displacement)
and [partial thermal-attenuator component](methods/thermal-attenuator.md)
concern exact heralded recovery; they leave approximate-error and capacity
questions open. The thermal component also compares complete vacuum-source
instruments with ordinary number-based preparation.
The shared-spectrum analysis in NR-R08 now specifies a joint-record
test and a bandwidth--delay resource bound before treating two optical
sections as independent unread measurements. NR-R06 separately bounds
raw full-register correct-output weight at fixed terminal site noise. Its
local-output bound also permits arbitrary globally interacting preprocessing
when both terminal noise layers have independent replacement components;
global decoding before discard remains distinct. The same owner gives
full calibrated bosonic noise compilers. NR-R09 separates those storage
comparisons from unknown-loss inference and tests the complete passive
optical transfer matrix and its directional loss records.
NR-R06 also gives a passive two-photon ordinary estimator for the specified
phase-invariant unitary reordering fidelity, with dimension-independent
variance and explicit source/readout costs. Its noisy-channel statistic
is a Choi overlap, rather than the switch's Kraus-interference visibility.
Anisotropic shifts fall outside the simple random-displacement compiler;
an ordinary parity echo nevertheless closes the specified deterministic
ideal-GKP fidelity benchmark. The separate
[finite-energy fixed-decoder comparison](methods/bosonic-logical-frontier.md)
shows that ordinary rotation and finite squeezing dominate the specified
plus-flag score at matched acceptance. After the fixed gauge trace it
also bounds all-control deterministic recovery. Coherent gauge recovery,
physical decoder costs, equal-energy optimization and the general
heralded frontier remain open.
The [heat-code recovery component](methods/heat-gkp-certification.md)
adds exact Gram normalization, certified photon tails and a supplied
finite-code ordinary recovery. At the declared noise point it exceeds
a code-independent upper bound for one raw Weyl switch, even with full
control/target decoding. Intermediate framing, repeated switched blocks,
the heralded frontier and physical decoder costs remain separate tests.
The full-reset ordinary simulation in NR-R10 and the excitation-exchange
decision counterexample in NR-R14 sharpen the remaining state-preparation
and memory-calibration targets without claiming a native advantage.
NR-R10 preserves the prior random-receiver locality advantage while giving
conditional ordinary parity-check and travelling-bus comparisons. Their
controller ports and protected transport must be established on the actual
network; abstract order control does not supply a free wire.
The separate unknown-coupler benchmark NR-R19 gives exact two-query
correction, a full hard-two converse for data dimension at least three,
and a certified qutrit prior-average fidelity ceiling for arbitrary
terminating ordinary strategies with mean query budget two. Its fresh
prior and lack of oracle-dependent advice are essential. An executable
address-selective reflection closes the task even if its matrix is unknown;
persistent-reflection calibration supplies another ordinary route. The
general family also admits a three-call simulation. The remaining target
is a useful native interface with the complete register routed through
both modules, a justified drift window and a matched primitive-level
comparison including calibration, clean memory, delays and routing loss.
Its Andreev-reflection screen excludes the specified single-Majorana
realization and requires a separate analysis for symmetry-restricted
converters; the full unknown-coupler prior cannot be imported into them.
The [passive-converter](backaction.md#nr-r19-passive-converter) and
[Bragg-rank](backaction.md#nr-r19-bragg-rank) guards further require full
mode matching and the actual physical input/output band split before
treating a multimode device as that oracle pair.
The [scattering result](communication.md#nr-r11) now includes unequal-rate
and photon-preserving bath-record comparisons. Conditional spectral
filtering, pair-preserving readout and ordinary delayed/reused paths must
be compared on the complete output. Recent two-dot experiments motivate
a joint physical device model rather than assumed independent swapped
slots. Its finite-emitter record guard requires a certified radiative Gram
floor, a vacuum-preserving physical ground and an explicit pulse/clock
budget. The retained-spin endpoint also has ordinary parity and photon-bus
baselines with specific optical ports. The assessment records the remaining
device and accuracy tests.
The [spin-phase component](methods/remote-spin-phase.md) gives exact
coherent-program realizations and ordinary survivor compilers, with
explicit port and timing qualifications. Its
[retained-photon gate comparison](methods/remote-spin-phase.md#nr-r11-retained-photon-gate)
keeps the unknown photon as quantum output and distinguishes one corrected
flag from multiple corrected records. It also gives an exact ordinary
weak-measurement optimum when intermediate photon instruments are allowed
with four preserved modes. The next test fixes a full physical
node, readout, vacuum and clock instrument, then compares delivery with
ordinary extra modes, actual weak measurements, memories and return
visits. Ideal
accepted weight alone does not establish a hardware advantage.
The [ordinary Raman gate programs](communication.md#nr-r11-raman-swap)
also compare unknown-input gates, helper-space costs and coherently read
identity failures; their ideal identities do not certify lossy retries.
Its [Raman local-memory comparisons](communication.md#nr-r11-raman-local-ancillas)
give stronger ordinary achievable Bell yields, including a certified
intermediate-transfer example and a coefficient-independent minus-flag
comparison. Their local ancillas, coherent filters and preserved photon/helper
ports are charged. The [balanced-cavity frontier](communication.md#nr-r11-raman-cavity-frontier)
also includes ordinary operating-point optimization. The remaining question
is a matched physical source/route/phase/reset and delivery-time comparison,
with within-attempt stationarity established; a bare transfer-probability
gap or a restricted product-spin bound does not answer it.
A [passive-filter alternative](communication.md#nr-r11-raman-passive-filter)
also gives a robust ordinary Bell output without extra retained stationary
qubits. A four-level flying helper strengthens this achievable family;
its extra optical modes, vacuum loss ports and coherent local filter remain
priced, without an unrestricted optimality claim.
The [native-port analysis](communication.md#nr-r11-raman-route) constructs
conditional temporal-helper routes and a same-graph ordinary comparator;
physical code preservation, rejected paths and loop/pulse guards still
require a measured instrument.
Its [direct temporal comparator](communication.md#nr-r11-raman-direct-temporal)
counts source preparation and rejects, while a
[calibrated photon-flip comparator](communication.md#nr-r11-raman-late-flip)
uses explicit timed rail control. Their exact disjoint-slot results leave
finite response leakage, phase calibration and full delivery clocks explicit.
The [phase-reference result](communication.md#nr-r11-raman-phase-reference)
separates scalar-phase immunity from physical Raman/spin/route phases.
Its next test requires measured causal signal/pilot correlations and
retarded route instruments, with ordinary alternatives and all source,
herald and reset costs included.
The [alignment benchmark](alignment.md) separates a strict two-call
advantage from measurement-record access, ordinary reuse and control
backgrounds. Its calibrated one-memory ordinary construction at shrinking
positive angles rules out treating that strict cap as the unrestricted
mean-query frontier; the longer frame-stability and helper costs remain
explicit. Its fresh shared-frame assumptions still need a physical two-meter
realization. The
[displacement-calibration result](geometric-calibration.md)
identifies a more concrete optical comparison: measure the complete
ordinary conditional-displacement echo and switched instrument at the
same setting, including every loss, parity helper, repeat pass and phase
calibration. Component transmissions alone do not establish that comparison.
The [braided-magic screen](braided-magic.md) requires a complete physical
phase and trajectory model, with ordinary loop/interferometer factories
included. The [rewinding analysis](obstructions.md#nr-r05) distinguishes
almost-sure completion from finite mean cost and delivered success under
loss. None of these screens establishes a native architecture benefit.
Other open directions include noise throughout compiled gates, protected
encodings at fixed site error rates, and sharper query frontiers. These
are open questions, not consequences of the present theorem.

Further physical tests now have explicit owning proofs: the
[mechanical record and clock interface](architecture-baselines.md#nr-r08-mechanical-record-strength),
[non-Gaussian cat parity baseline](architecture-baselines.md#nr-r06-cat-reservoir-parity),
[higher-order bath transfer test](backaction.md#nr-r14-high-order-transfer),
[native holonomic controls](backaction.md#nr-r19-holonomic-controls) and
[stored Rydberg-memory instrument](communication.md#nr-r11-rydberg-memory).
Their remaining tests concern complete physical access and useful task
outputs after ordinary controls, rather than record rank, one decay time
or a selected commutator flag. No native benefit is established.

The [memory-algebra qualification task](architecture-baselines.md#nr-r08-memory-algebra)
has a full conditional-output bound and an exact-prior ordinary
stabilizer estimator. Its remaining resource question includes noisy
references and the [one-sided Pauli statistic](architecture-baselines.md#nr-r06-pauli-statistic-memory).
Ordinary alternatives now have separate owning proofs for
[local overlap and readout costs](architecture-baselines.md#nr-r06-local-overlap),
[local generator learning](architecture-baselines.md#nr-r06-local-lindblad-statistic),
[spectral concentration](architecture-baselines.md#nr-r06-pauli-spectral-closure) and
[cross-pair partial-reference estimation](architecture-baselines.md#nr-r06-pauli-coset-scalar).
The remaining native test must preserve the
[complete physical channel port](architecture-baselines.md#nr-r06-pauli-physical-ports).
The [cat physical route](architecture-baselines.md#nr-r06-cat-physical-route),
[mechanical decision model](architecture-baselines.md#nr-r08-mechanical-clock)
and [retained Rydberg exchange](communication.md#nr-r11-rydberg-exchange)
state their full-record ordinary comparators and actual next
instrument tests. A significant native advantage remains open.

The [literature comparison](references.md) credits the existing filtering
and recovery mechanisms. The bounded primary-source check does not
establish priority.

## Updating this topic

Update each result in its owning file. Methods and certificates are
representations or proof components, not additional result identities.
Do not import checkpoint archives, repeated audit narratives or source
ZIPs. After changing checked inputs, rerun the relevant verification and
refresh the current evidence only after success, as documented in the
check map.
