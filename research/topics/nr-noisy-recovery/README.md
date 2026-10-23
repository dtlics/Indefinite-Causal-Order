# NR — Noisy physical state recovery

[Research map](../../README.md) · [Result index](../../RESULTS.md) · [Validation scope](../../../docs/VALIDATION.md)

This topic owns recovery through two opaque related modules, with the
ordinary comparison charged for every invocation, including calibration
and rejected histories. It is distinct from universal switch simulation
and from learning a scalar channel property.

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
| NR-R11 | Accepted cavity and nonlinear-scattering instruments | [Scattering-instrument screens](communication.md#nr-r11) |
| NR-R12 | Exact coherent dispatch with a dephased counter and bounded-query boundary | [Conditional dispatch result](dispatch.md#nr-r12) |
| NR-R13 | Clean composite lookup: ordinary uncomputation and a scoped switch erasure bound | [Composite lookup screen](native-lookups.md#nr-r13) |
| NR-R14 | Shared-bath calibration transfer and exact ordinary echo/instrument baselines | [Bath-backaction screen](backaction.md#nr-r14) |
| NR-R15 | Noisy phase calibration: certified two-call benchmark and native-memory boundary | [Metrology benchmark](metrology.md#nr-r15) |
| NR-R16 | Displacement-area calibration and native ordinary controls | [Geometric calibration](geometric-calibration.md#nr-r16) |
| NR-R17 | Braided magic, coherent trajectory resources and ordinary factories | [Braided magic](braided-magic.md#nr-r17) |
| NR-R18 | Drifting measurement alignment: exact two-query limit and reuse costs | [Alignment benchmark](alignment.md#nr-r18) |
| NR-R19 | Unknown odd couplers: exact two-query correction and ordinary limits | [Coupler benchmark](backaction.md#nr-r19) |

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
has not been established. In particular, the fresh-frame converse does
not extend to reused devices after calibration; the ordinary reuse
baseline is in NR-R07. Calibrated classical Pauli faults and recorded
Lüders measurements have the ordinary baselines in NR-R06 and NR-R08.

The next application questions concern a physical unmonitored multimode
workload, retained inelastic scattering in a matter-photon link, a
native coherent-dispatch interface, and prediction across control histories
in a retained quantum bath. First establish each instrument,
available records and controls, and the best ordinary method; then
compare useful task outputs at matched time, memory, calls and routing
cost. The [communication note](communication.md) identifies why pure
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
The [phase-calibration benchmark](metrology.md) independently certifies a
known finite-query switch advantage, but preserves its hard two-call scope.
Longer ordinary rounds, emitted timing records and coherent bath reuse
change that comparison. A native calibration-rate advantage remains open.
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
ideal-GKP fidelity benchmark. Finite-energy and heralded tasks remain open.
The full-reset ordinary simulation in NR-R10 and the excitation-exchange
decision counterexample in NR-R14 sharpen the remaining state-preparation
and memory-calibration targets without claiming a native advantage.
The separate unknown-coupler benchmark NR-R19 gives exact two-query
correction and a full ordinary hard-two converse for data dimension at
least three. Known-parity and Abelian subfamilies admit two-query ordinary
wrappers, and the general family admits a three-call simulation. A useful
approximation gap and a native unknown-coupler interface remain unproved.
The [scattering result](communication.md#nr-r11) now includes unequal-rate
and photon-preserving bath-record comparisons. Conditional spectral
filtering, pair-preserving readout and ordinary delayed/reused paths must
be compared on the complete output. Recent two-dot experiments motivate
a joint physical device model rather than assumed independent swapped
slots. The assessment records that concrete next test.
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
