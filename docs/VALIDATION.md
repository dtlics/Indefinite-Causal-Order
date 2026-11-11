# Verification scope

## Application-search checks

The [application-search check suite](../research/topics/nr-noisy-recovery/application-search/checks/README.md) has a single [current record](../research/topics/nr-noisy-recovery/application-search/checks/validation.json). It distinguishes exact rational certificates, restricted symbolic searches and seeded numerical tests. It does not independently audit C4/C5/C6/P3, establish publication priority, verify a physical switch interface or perform a Lean rebuild. Sources and source-attachment hashes are retained without importing duplicate generated archives.

Repository organization preserves the distinction between mathematical claims, exact finite checks, computational diagnostics, and a formal proof audit.

| Component | Current evidence and reproducibility |
| --- | --- |
| Research ownership | `python scripts/validate_repo.py` checks canonical result owners, generated indexes, and local links |
| Paper | The current `paper/main.tex` source (`SHA-256 df303d7b3447516e08fbfa2b9e4c7ce353c2d2957e35bcb8bcba0de6468d947c`) compiles with pdfTeX 1.40.29 (TeX Live 2026) with shell escape disabled to 47 pages, with zero errors, zero undefined references, and zero overfull or underfull boxes |
| Overleaf export | `python scripts/package_overleaf.py` deterministically packages the exact `paper/main.tex` bytes |
| Selected Lean source | `python proofs/lean/verify_integrity.py` compares 1,663 modules (`1,615` `ICO` + `48` `QIT`) and entry/configuration files to the recorded verification fingerprints |
| Lean rebuild and kernel audit | See [current proof-verification record](../proofs/lean/audit/README.md) and [rebuild instructions](../proofs/lean/README.md) |
| Exact P3 certificates | `python proofs/lean/certificates/verify_all.py` replays the independent support and sparse separation identities using exact arithmetic |
| P1 | The consolidated proof compiles; exact rational matrix generation and the source manifest check pass. The arbitrary-ancilla claim is analytical, not established by finite sampling |
| P2 | `verify_p2.py --all` passes four certificate replays and eleven exact structural checks; these do not settle the unrestricted optimum or finite attainment |
| RG | The source package documents integrity and certificate tiers, including [supporting helpers absent from the supplied material](../research/topics/rg-routed-graph/source/REPRODUCIBILITY.md) |
| C6 scalar checks | The exact-arithmetic replay checks both the paper's `212/10000` estimate and the formal `215/10000` allowance; it does not replace the shared-Haar proof |
| NR physical recovery | The [canonical analytic proofs](../research/topics/nr-noisy-recovery/README.md) and [standard-library exact replays](../research/topics/nr-noisy-recovery/checks/README.md) have one [current input-hash validation record](../research/topics/nr-noisy-recovery/checks/validation.json). Replays check causal PSD certificates, exact contractions, Weyl/dimension identities, and resource/score constants; they do not prove every prose assertion or constitute a Lean audit |
| NR memory qualification | [NR-R20](../research/topics/nr-noisy-recovery/memory-qualification.md#nr-r20) has analytic capacity/query reductions and a general-channel Choi-entropy certificate with a nonunitality correction, alongside unitary-realization entropy proofs. Standard-library jobs check finite flagged maps, stopping ledgers, code-verification Bell isometries, accepted logical-policy scores/X/Z intervals, full-record/tag fixtures, general Kraus/Choi/Gram/tail/pinching identities, ordinary calibration and full helper-port noise maps. General confidence and record-overlap bounds, entropy integration, coding, all-dimension learning and native resource arguments remain analytic; no new Lean endpoint or measured native advantage is claimed |
| Theoretical QC applications | [C6-R08](../research/topics/c6-hidden-dephasing/applications.md#c6-r08) and [NR-R22](../research/topics/nr-noisy-recovery/noise-model-selection.md#nr-r22) live in `research/topics/` (not in `paper/main.tex`) and have independent analytic reviews and the current 47-job/190-input replay. The application job checks exact finite robust-test constants, pinching-Choi effects, weak-noise spectra, broadcast marginals, Bell-projector overlap, entropy witnesses and a nonmixing fixture. General norm/SDP, arbitrary-basis geometry, adaptive-query, Haar-session and common-code arguments remain analytic, including NR-R22's C6-only reduction, conservative constant, and imported uninformed-user compound coding theorem. The conditional [keyed specialization](../research/topics/nr-noisy-recovery/noise-model-selection.md#nr-r22-keyed) additionally relies on exact Clifford moments, strong forward/inverse PRU security and indexed Clifford generation. Exact devices use expected-polynomial setup; the strict-QPT reduction pays its sampling tail explicitly. Those arguments are analytic, and the keyed lower bound is computational. No new Lean endpoint or hardware-performance claim follows |

The current `paper/main.tex` source checksum is `df303d7b3447516e08fbfa2b9e4c7ce353c2d2957e35bcb8bcba0de6468d947c`, compiled to 47 pages with pdfTeX 1.40.29 on TeX Live 2026 with shell escape disabled via the documented [local build](../paper/README.md#local-build) and packaged in `dist/overleaf.zip` via `python scripts/package_overleaf.py`. Its three headline theorems, supporting lemmas, and Appendix A/B structural claims are mapped in Part 1 of [THEOREMS.txt](../proofs/lean/THEOREMS.txt) to the 221-endpoint Lean 4.30.0 kernel audit in `proofs/lean/` alongside the external port-based teleportation citation in Section 4.4; supplementary endpoints retained from earlier drafts (including SAME/MUB decision, visibility and phase-OTOC estimation, diamond-norm model mismatch, conditional keyed-family transfer, capacity-inherited distance, and `ICO/TwoCallCertificate.lean` / `ICO/TwoCallOperational.lean`) are catalogued separately in Part 2 of [THEOREMS.txt](../proofs/lean/THEOREMS.txt).

The [workload-commutator proof component of NR-R06](../research/topics/nr-noisy-recovery/methods/workload-commutators.md) has separate analytic reviews for QEM bounds, reference-complete state-specific reordering, and algorithmic ordinary baselines. The average-case Trotter-depth theorem additionally has independent math and demand/model reviews covering spectral nonaliasing, the finite-time scalar-to-error bound, sector restriction, false-acceptance coverage and accepted/rejected/expected cost ledgers. The replay fingerprints the note; it does not prove those analytic arguments. The general calibration comparison is against the explicit ordinary reproduction. The restricted complete one-step decision additionally has independent reviews of its actual-error/two-design gap and independent-sign variable-time reduction to Chiribella2012's analytic tester obstruction. It proves an exact two-versus-three contact separation under classical port allocation, and an existential bounded-error gap only under one call per Hamiltonian. It is not an optimal general simulator, a quantified noisy-device bound or a new proof of the primary obstruction. The [application assessment](../research/topics/nr-noisy-recovery/architecture.md) retains explicit Pauli calculation and local-Hamiltonian learning as competitors. The distinct magic-source theorem uses the retained output.

The selected proof-verification record reports 221 endpoints checked with Lean 4.30.0 (`commit d024af099ca4bf2c86f649261ebf59565dc8c622`) at trust level zero, after cleanly elaborating all 1,663 local proof modules (`1,615` `ICO` + `48` `QIT`) from `.lean` source on Windows before running the single-threaded `-t0` kernel audit of `ICO.lean` and `Audit.lean` (a separate Unix build was not run). Source fingerprints and finite Python replays do not replace that audit.

The [logical-policy extension](../research/topics/nr-noisy-recovery/methods/memory-code-verification.md#nr-r20-logical-policy-qualification)
permits temporal memory within a run; its confidence bound separately
requires independent complete validation runs. Measured $X/Z$ returns
do not demonstrate logical $Y$ access, a common quantum decoder or a
coherent schedule selector. It does not transfer the memoryless capacity
ceiling to general non-Markov histories. The generic
[record-overlap bound](../research/topics/nr-noisy-recovery/backaction.md#nr-r14-record-overlap-qualification)
uses actual inaccessible records, not visible histograms alone.

The new NR recovery theorems have not been formalized in Lean or externally peer reviewed. Their mathematical arguments use the explicitly cited mixed-tensor decomposition and approximate-design theorem in addition to the exact certificates. The local result averages over fresh private frames, uses noise once after each whole module with rate of order `1/n`, and bounds a specified signed recovery utility. Its control tolerance is the declared scalar dephasing model. No deployed-runtime, fixed native fault-rate, persistent-frame throughput, or capacity validation is recorded.

The [architecture baselines](../research/topics/nr-noisy-recovery/architecture-baselines.md)
add analytic fault-simulation, reused-calibration and measurement-interface
arguments. Their exact replays check finite full-output examples,
measurement identities and calibration-score arithmetic. The cited
Threshold Search theorem supplies the collective learning bound; the
replay does not implement that learner or determine its asymptotic
constant. These checks do not establish hardware efficiency, source
priority, a general memory-process model or an architecture advantage.

The [known-reflection component](../research/topics/nr-noisy-recovery/methods/reflection-diagnostics.md)
has finite exact measured-X/target/reference fixtures for joint
sector-diagonal inputs, nonunital maps and degenerate sectors, with
intersector/coherent-control boundary witnesses. A separate ideal
reflection-symmetric chain guard checks generator symmetry, sector ranks
and moment/target-bias ingredients. The arbitrary-channel instrument,
state-dependent norm bound, all-size support and Haar-moment arguments
remain analytic. These checks certify neither inexpensive Lueders ports,
an actual four-point diagnostic, noisy-device sector preservation nor
random-design quality.

The [depolarizing-search component](../research/topics/nr-noisy-recovery/methods/noisy-search.md)
adds an analytic full-channel ordinary compiler using known controlled
unitaries, plus an every-flag timing proof and uniform counted-restart
bounds. Native-check replays compare finite raw Kraus maps, arbitrary
incoming controls/references, ordinary controlled-Pauli circuits,
deferred records and exact coefficient discrepancies. Their finite
scope does not establish the all-dimension or asymptotic arguments,
native gate costs or availability of a reliable candidate verifier.

The [final-flag completion component](../research/topics/nr-noisy-recovery/methods/final-flag-completion.md)
adds finite exact random-order CP complements, all plus/minus histories,
common CPTP-decoded payload/reference maps, abort effects/traces,
mean-call ledgers and nonzero cubic witnesses to the native-check job.
Its general full-flag diamond/payoff and survival/error bounds are analytic.
The comparison requires a realizable ordinary completion, an
always-delivered target and a common payload decoder; accepted-only,
branch-dependent and joint retained-control services are outside it.
Equal worst-case calls do not imply equal early-abort means, and static
Strang merging requires actual half-duration ports. No routing or
persistent-bath reduction is certified by these finite fixtures.

The [moving-CAPS component of NR-R11](../research/topics/nr-noisy-recovery/methods/moving-caps.md)
has an analytic passive-resolvent and energy-transfer-moment bound with
exact finite Gram, flux-unitarity, frequency-shift, clock and phase guards.
Separate rank-three input-support fixtures guard its measured-flag decoder
budget. Its isolated-blue-band Bell-factory comparison has exact atomic
score and frontier polynomial identities plus rational source-constant
guards; the motion, sideband and ordinary routing premises are analytic.
The optional NumPy finite-packet study has its own
[current numerical record](../research/topics/nr-noisy-recovery/numerics/moving_caps_record.json),
including source hashes, environment, actual commands and empirical
quadrature/cutoff refinements. The ordinary parity-factory witness counts
both destructive photon-readout ports and traces final photon frequency
and motion. Its biased known-photon preparation has an analytic density
scaling identity; finite packet fidelities remain numerical evidence.
The coherent-carrier comparator has finite complex-rational projection,
whole-analyzer normalization and local Bell-frame guards. Its exact
final-motion isolation and general complex construction are analytic;
finite virtual-motion witnesses do not certify the infinite resolvent
or supply a physical temporal-mode detector.
Frequency-diagonal readout adds normalized per-bin polarization and
corrected-density guards. Its finite-response bad-mass bound is analytic;
sampled bin moments and fidelities remain optional numerical evidence,
with no physical spectrometer, detector-clock or storage certificate.
The standard-library suite fingerprints
those numerical sources and record but does not execute them. Neither
finite convergence nor an omitted initial thermal mass bounds all output
oscillator tails. The model does not certify a complete failed-data
channel, actual coherent router or hardware advantage.

The [thermal-attenuator component of NR-R04](../research/topics/nr-noisy-recovery/methods/thermal-attenuator.md#nr-r04-thermal-visibility)
has an analytic exact visibility formula and sharp mean-energy budget for
identical slots. The finite replay independently lifts complete
total-photon sectors and retains reference/flag/payoff fixtures, with
exact omitted initial thermal-mixture weight. It does not truncate output
photon number. Infinite trace convergence, arbitrary normal inputs,
the sharp energy bound and all-attempt payoff comparison remain analytic.
Finite-code parity/coin-twirl and factorial-moment guards support the
separate parameter-free ordinary receiver; its complete infinite-gain
CP bound and actual control costs are analytic or supplied premises;
no conditional-fidelity optimum, capacity or native hardware is certified.
The clock-port helpers add exact thermal-mean coefficients and a negative-sign
coherence, the standard-versus-fresh vacuum statistic, complete finite-source
beam-splitter sectors/control maps and abstract rational multiarm receiver
matrix units, classical-order difference and thermal norm endpoint guards.
The finite bath mixtures are explicitly non-Gaussian; they
are not thermal Fock-cutoff certificates. The infinite thermal mean trace,
common-occupation full-output compiler, unequal-occupation norm/payoff
bounds and physical gating, clocks and decoder costs remain analytic.

The [unknown-pulse gate result NR-R21](../research/topics/nr-noisy-recovery/unknown-pulse-gates.md#nr-r21)
has a standard-library exact replay of the necessary success-support rank,
literal Pauli-link normalization, causal positive-definite slacks and a
matrix sum-of-squares identity for every real nondegenerate pair of pulse
angles. These are exact polynomial certificates rather than sampled-angle
upper bounds. The proof separately includes classical adaptive instruments,
singular angles, query-type choices and stopping, yielding its ideal exact
expected-call comparison. Full data/reference Euler and flagged maps and
random-order Choi ingredients are also replayed. Global diamond equality,
continuous timing inequalities and the source-specific physical comparison
remain analytic. The [all-launch scalar-price corollary](../research/topics/nr-noisy-recovery/unknown-pulse-gates.md#nr-r21-all-launch-query-price)
and [finite-penalty existence/mean-utility proof](../research/topics/nr-noisy-recovery/methods/pulse-gate-robustness.md)
use those exact ingredients analytically. The latter gives no certified
numerical penalty or error tolerance. The
[selector-port component](../research/topics/nr-noisy-recovery/methods/pulse-selector-ports.md)
has analytic full-instrument, phase, passive-loss and resource arguments
and a primary-source physical screen. These prose extensions add no
executable guard. No approximate ordinary optimum, measured router,
hardware benefit, priority claim or new Lean audit follows.
The separate source-parameter pulse-activation ledger checks scalar
angle/event, on-chip energy-proxy and conditional setup-clock conversions
with standard-library floating point. It is a cost diagnostic, not an
interval certificate, an exact rounded digital gate or a phase-resolved
noisy device model. Its source access and reuse qualifications remain in
the same result owner.

The [fault-parity controller component](../research/topics/nr-noisy-recovery/methods/binary-fault-controller.md)
has analytic closed-controller and general-intermediate-operation memory
bounds and a separate prearrival-programming bound, with exact finite
replays of ordinary qutrit, cross-dual Pauli and read/reset instruments.
Complex finite guards retain internal Pauli anticommutation and the
required reverse-order adjoints in the check banks. The
[controlled-unitary memory test](../research/topics/nr-noisy-recovery/methods/memory-native-cost.md#nr-r20-controlled-unitary-correlator)
has finite exact two-readout, signed-map and phase-drift checks. The
universal dimension, reversible-source, information, timing, uniform-cost, pinching and
concentration arguments remain analytic;
these checks establish neither native hardware ports nor a practical
switch advantage.

The [decoder-bootstrap component](../research/topics/nr-noisy-recovery/methods/memory-code-bootstrap.md)
adds a high-prior mean-cost converse with receiver quantum programs under
an all-instance unassisted deployment interface. Its replay checks complete
compiler, projection/Petz, cost and normalized serial-history rank
identities; C6 and universal interface/rank converses remain analytic.
The [finite-energy bosonic component](../research/topics/nr-noisy-recovery/methods/bosonic-logical-frontier.md)
derives a normalizable code, reduced all-control recovery bounds and
complete coherent-gauge counterexamples. Its fixed-controller recovery
SDP is a method, not a solved Gaussian frontier or native decoder.
Finite guards do not establish equal-energy optimality. The
[heat-code recovery component](../research/topics/nr-noisy-recovery/methods/heat-gkp-certification.md)
adds outward rational interval certificates for full Gram normalization,
uniform exponential moments and source/output photon tails, including
transient squeezing and a common ensemble mean-energy ledger. Its
continuous/operator identities remain analytic. A separate finite witness
certifies an actual supplied-code ordinary recovery using outward
Gaussian matrix enclosures and exact positive/trace-preserving completion.
Its comparison is against an analytic code-independent raw-switch bound,
based on Gaussian broadcasting and a uniform trace-distance estimate.
Neither check validates a physical decoder, intermediate-controller
optimization, repeated switched blocks or the full heralded frontier.
The
[spin-phase component](../research/topics/nr-noisy-recovery/methods/remote-spin-phase.md)
also checks scattering, full entanglement-first gate/resource branches,
scalar concurrence, a rational Bell-yield interval and coherent-spectral
scope guards. Universal comparisons, continuum loss and full-space
recovery obstructions remain analytic; no native router or rate ordering
is certified. Fixed-marginal rank reduction, helper POVM and local-filter
guards support the arbitrary accessible-purifier Bell-assistance proof.
Additional complete finite-state and coherent two-frequency guards
support the constant-optics four-mode reduction and the specified
coefficient-independent survivor compiler. Their all-spectrum proofs
remain analytic; lost-environment records and adaptive intermediate
controls are outside those comparisons.
Additional finite guards support the continuous local-phase gate cone
and the balanced/opposite-phase ordinary gate constructions. The declared
one-pass reflected-success ceiling and cone completeness remain analytic.
Exact eight-mode guards additionally retain coherent frequency and
reference matrix units, complete joint readout and the four-window
ordinary survivor. They check the direct three-window construction with
an explicitly supplied larger middle port and a finite-pulse rank
obstruction for a four-mode middle port. The general program-attainment,
compression and common-frame timing proofs remain analytic. These
guards do not validate native station ports, inaccessible emission
records, physical buffers or throughput.
An additional rational projector-response certificate supplies a
coherent pooled gate primal and ordinary fixed-word duals. Exact
PSD/PPT, phase and complex moment equalities establish a restricted
accepted-CZ separation. Four additional exact sector decompositions extend
the ordinary upper to terminal separable/LOCC correction after complete
photon readout, including amplitude-filter failures: 64 integer identities
and 48 positive leading minors prove the all-complex-product inequality.
The unknown-input Choi-rank/completeness bridge remains analytic. Spin
operations before/interleaved with readout, intermediate matter controls
and hardware rates remain outside that upper bound. The repeated
ordinary survivor compiler remains a stronger paid comparator.
The [source-rate gate comparison](../research/topics/nr-noisy-recovery/methods/remote-spin-phase.md#nr-r11-source-gate-budget)
adds 120 exact positive-principal-minor checks for an ordinary resonant CZ
primal, complex station-order covariance fixtures, and exact rational
fixed-spatial Gaussian error/success budgets. Its all-reference CP-map,
resolvent/Taylor and pure-helper attainment arguments remain analytic.
A separate outward rectangular interval certificate and Gaussian Mills
bound support an exact gate with a stronger joint spatial/spectral POVM.
An exact degree-eight Sturm chain evaluates the native monochromatic
common-detuning ceiling. The finite-packet native bound concerns guaranteed
minimum reflected acceptance, not arbitrary approximate average gate scores.
Both helpers are included in the existing remote-spin-pulse job; actual
ports, click-time coarse-graining, loss recovery and hardware clocks remain
explicit premises or costs.
The [direct-parity failure component](../research/topics/nr-noisy-recovery/methods/remote-spin-phase.md#nr-r11-parity-failure)
adds exact complete accepted/loss maps and finite capped-retry guards.
The [Bell-resource component](../research/topics/nr-noisy-recovery/methods/remote-spin-phase.md#nr-r11-offline-parity)
checks fine and coarse unknown-input parity maps, Bell-error Choi
orthogonality, mixtures and capped delivery ledgers. General instrument
distance and recovery proofs, physical branching, factory isolation,
storage and clock costs remain analytic or supplied premises. Perfect
accepted parity is not a certificate of harmless retries.
The [retained-photon comparison](../research/topics/nr-noisy-recovery/methods/remote-spin-phase.md#nr-r11-retained-photon-gate)
adds exact full-input gate/compiler, four-mode witness and complementary
branch identities, together with polynomial balance, phase-ratio and
loss-ledger guards. An exact formal-phase dual checks the positive
polynomial and balanced Schur-complement attainment without a numerical
optimizer. Its analytic upper bounds distinguish a single
corrected flag with arbitrary photonic memory from the total terminal
instrument with four preserved modes. A further exact certificate checks
the four-mode intermediate photon instrument's positive effects, complete
Kraus budget, all input matrix units and all-angle trace-cost polynomials.
Its pinching/optimization proof remains analytic. A further exact
serial-survivor replay checks both encounter schedules, full control/data
matrix units, both output flags, common atomic phases, nonunitary raw
kernels, raw auxiliary polarization, coherent frequency blocks, middle-port
span guards and regrouping into two event layers. Polynomial checks cover
a declared closed-transition node's normalization, detuning residuals and
carrier balance. Additional polynomial/matrix ingredients cover a common
reliable-meter delivery comparison, energy-decay dispersive reflection
and the relative-sector invariants used in a clean-photonic-ancilla CZ
obstruction. The general clean-return argument and unknown-qubit-preserving
microwave occupancy instrument are not established by finite replay. Its
finite-cap endpoint replay retains coherent time-key blocks and residual
routes in ideal and raw-CZ phase conventions, with a counterexample to
postprocessing a fixed spin basis. An explicit gap-relaxation meter/bath
unitary checks both flags on every vacuum/early/late input matrix unit;
pure dephasing is checked separately. The all-POVM argument, coherent-probe
loss/discrimination tradeoff, SiV ideal storage extension and actual
terminal access/clock remain analytic or physical premises. Its
pointwise elastic identity is distinct from a complete timed loss/bath
dilation or hardware clock certificate. Spin filters before or between
contacts, spin encodings before contacts, physical detector channels and an optimal ordinary rate
are outside those bounds. Finite replay does not certify optical ports,
a measured loss model, novelty or a hardware advantage.
A sequence component adds exact Fourier cut ranks/minors, query-word and
slice guards, nuclear-norm balance identities, weighted encoding fixtures
and average-cost abort comparisons. The all-length rank reduction,
three-lines interpolation, full recorded-prefix determinant bound and
continuous-outcome extension are analytic. No approximate-gate robustness,
expected-query separation or architecture advantage follows from that
strict-visit sequence bound.
A separate outward interval certificate integrates the full declared
Gaussian pulse, with analytic strip and tail bounds. Its physical joint
mode analyzer remains an additional resource. Full Choi twirls in the general-channel replay support the
credited ordinary fidelity-only bound without a unitality premise; its
relative-entropy and coding proof remains analytic.

The [rare-good screening component](../research/topics/nr-noisy-recovery/methods/memory-stream-screening.md)
prices selection, survivor learning, validation and a finite working code.
Its exact guards support probability/stopping and complete code identities;
C6, the all-size selection reduction, continuous prior and concentration
arguments remain analytic. Its conditional classical-address query saving
is not a certified native platform, finite crossover or wall-time gain.
Its independent-erasure extension checks the specific phase-code loss
guard and antidegrading/extendibility identities. The analytic all-block
fidelity converse requires the stated independent loss map and
unassisted fixed-block service; it does not follow from an efficiency
measurement or constrain accepted-branch fidelity alone.

The measurement replay also checks complete recorded parity-braid branches,
initialized-ancilla effects and tracked frame corrections at dimensions
four and eight. The ordinary three-measurement construction is a cited
baseline with an explicit analytic proof. Its comparison to the specified
switch protocol counts retries and permits the same output frame convention;
it does not optimize all coherent measurement protocols or model detector faults.
The [central-fault extension](../research/topics/nr-noisy-recovery/architecture-baselines.md#nr-r08-central-involution)
checks complete paired recorded instruments, including inverse
noninvolutory faults, a covariance counterexample and an ordinary
known-state probe. Balanced cancellation does not certify individual
or odd-use logical correctness; it is not a general diagnostic no-go.
The [delivered-photon screen](../research/topics/nr-noisy-recovery/architecture-baselines.md#pbs-delivered-output)
adds exact two-photon PBS sectors, coherent path instruments and
uniform post-interaction loss/false-herald guards. Its same-graph
known-control argument is analytic. These checks do not fit source,
detector or storage parameters, supply unknown-input injection, or
certify a delivered experimental rate.

The [communication note](../research/topics/nr-noisy-recovery/communication.md)
has exact finite checks of absorbing-vacuum loss, sector-preserving noisy-wire
factorizations, and elastic-node commutation. Schmidt-number, relative-entropy
and finite-mean stopping arguments remain analytic; no channel-capacity theorem
is inferred from finite sampling. The native-layer checks likewise assume
their stated ideal helper operations and leave actual helper noise and routing
cost to the application comparison.
Ordinary ideal Raman gate-program checks additionally preserve all
unknown-input reference coefficients, including coherent early
identity failures, deterministic CZ, arbitrary known-unitary
teleportation and a qualified serialized port. Their ideal retry
argument does not make actual photon loss or partial exchange safe,
and known internal gate synthesis and physical clocks remain charged.

The [conditional dispatch result](../research/topics/nr-noisy-recovery/dispatch.md)
has finite exact flagged-output and routing checks. Its universal exact
query lower bound depends on the cited unitary-switch no-go theorem.
Ordinary achievable approximation curves have finite Choi/projector checks;
the zero-query minimax proof and fixed-dimension qualitative expected-cost
gap are analytic. No evaluated positive-cost approximation converse, runtime
advantage, physical dispatcher validation or new correction-mechanism
priority is recorded. Temporal event-head and classical-phase replays fix
their full occupied/vacuum models. Gaussian optimal-decoder and whole
acceptance-frontier proofs remain analytic and do not fit a hardware bath.

The [composite-lookup proof](../research/topics/nr-noisy-recovery/native-lookups.md)
has complete-address exact Choi checks for all table pairs through dimension
four and a saturating junk-erasure projector. Its $1/3$ upper bound concerns
the displayed balanced switch and fixed junk-only cleanup, not general
switch protocols. No optimized ordinary query frontier or native QRAM cost
advantage is inferred from that replay.

`prepare_verification.py` derives the current import closure and endpoint list offline. It rejects missing local modules and dependency cycles; the wrappers also check endpoint identities and allowed axioms. Their offline checks are separate from running Lean.

The [shared-bath calibration screen](../research/topics/nr-noisy-recovery/backaction.md)
has exact finite flagged-Choi echo/switch identities, a rational held-out
memory counterexample, a maximal ordinary record-correlation example and
symbolic polynomial calibration/storage counterexamples.
Recovery-record fixtures distinguish chronological, module-labelled and
copied records, and check the full accessible monitored one-way
instrument. They do not fit sBs, match discarded purifications or
certify future persistent-bath dynamics.
The all-dimension instrument and known-intervention dilation identities
are analytic. The [pair-memory ingredient](../research/topics/nr-noisy-recovery/checks/architecture/pair_memory_qualification_guards.py)
adds exact Schur-channel, encoded matrix-unit, labelled-record, parallel
phase-estimator and spectator/switch-boundary fixtures. Recovery
optimality, concentration, general model transfer and physical costs
remain analytic or separately assumed. The
[loss-memory ingredient](../research/topics/nr-noisy-recovery/checks/architecture/loss_memory_qualification_guards.py)
adds finite collective/loss, retained-control and paid parity/re-excitation
fixtures on complete encoded matrix units, plus single-carrier dual-rail
success/seed/reject maps. The multiple-survivor extension checks signed
phase cycling, literal CNOT collection/discard, full flagged reference
maps and an unequal-vacuum-record/ordinary-conjugation boundary.
Helper-transfer fixtures include a literal readout instrument and
its same-POVM disturbed-helper counterexample. Two-logical-qubit
fixtures check ideal singlet protection, nominal hopping leakage,
declared thermal/phase channels and intrinsic heating arithmetic;
they do not fit or certify a device storage channel. Group/character,
doublon-Gram, binary pulse, sign/hazard and fixed local-loss
ingredients support the linked ordinary symmetry-control component;
general Schur, finite-period diamond and recovery bounds remain analytic.
Active-gate fixtures check code-fixed recovery, complete dummy/record
outputs, the cavity-only boundary and intermediate accepted heralds,
including finite true-excitation bound ingredients. General isometry and
norm bounds, oscillator tails, actual EsT/AQEC pulse performance and
compound routing remain analytic or physical premises. Final ground-state
postselection does not replace the intermediate instrument; true-excitation,
readout and encoder/SPAM calibration remain required.
Shared-history, arbitrary
decoder, finite-confidence and physical-cost proofs remain analytic;
no experimental selector or bath model is certified. These checks
establish neither a fitted bath model nor a switch sampling or
architecture advantage. The application assessment's
photonic and phononic resource comparisons are primary-source screens,
not hardware experiments or new security proofs.

The [phase-calibration benchmark](../research/topics/nr-noisy-recovery/metrology.md)
has an exact feasible dual witness for all ordinary hard-two-query
independent-channel strategies. Its checker reconstructs every LMI entry,
encloses the radicals by rational intervals and verifies a complete exact
LDL factorization. The direct weak-duality argument and all-input
switch optimization remain analytic. Achievable readout, retained-memory
echo and longer ordinary feedback comparisons delimit the benchmark;
no expected-cost, sustained calibration-rate or native-device advantage
is inferred. Same-unitary physical-path checks also distinguish
quasistatic coins from independent clock noise. Its known-basis and
number-lowering cases now test physical Bell metrics, nonzero Choi cross
terms, the exact no-loss CP remainder and explicit double-fault/parity
limitations. The all-dimension proofs and native helper costs remain analytic.

The [one-marker code-input refinement](../research/topics/nr-noisy-recovery/metrology.md#nr-r15-one-marker-compiler)
has exact Q(sqrt(2),sqrt(3)) fixtures for nine whole-gate matrix units,
36 measured outcomes and a known auxiliary unitary. Its arbitrary-input/
reference and common-dilation proof is analytic, as are the noisy-checker
full-joint-commutation condition and clean-target prefix requirements.
Measured flags and unmeasured quantum helpers have distinct paid
preparation, sampling and auxiliary-control requirements. The replay
certifies no physical marker, shared-bath law, waveform or complete clock.

NR-R15 also has exact known-unitary pre/post compiler identities and
full-output, conditional-channel, syndrome and SLD/QFI checks for two
coherent signal/noise extensions. Its general common-dilation compiler,
continuous-time interpretation and physical sign-control conditions are
analytic. Equal classical direction channels do not certify a coherent
extension; the explicit noisy-extension sensor is an achievable comparison,
not an all-protocol upper bound. No unexamined published platform
supplement or native implementation is certified.

The two-photon proofs in NR-R11 use the complete scattering basis and
resolvent kernel. The unequal-rate relative-mode gate, normalizable-pulse
target-amplitude identity, photon-preserving readout, known-dressing reuse,
time-record instrument reduction and uniform tail bound are analytic.
The existing finite communication replay does not certify those continuum
arguments, actual phonon overlaps, a native pulse-tail bound, a physical
pair router or a hardware performance advantage. No frequency-grid
certificate or fitted single-mode gate is claimed.
The [giant-transmon array component](../research/topics/nr-noisy-recovery/communication.md#nr-r11-transmon-array-modes)
adds finite rational residue, connected-kernel, eigenphase, central-nesting,
commutator and reference-Choi guards. Its all-energy orthogonality,
direct-integral and full-input overlap proofs are analytic statements of
the declared chiral effective kernel, not microscopic all-frequency
certificates. A second helper checks Laguerre coefficients and outward
rational causal-inverse delay/error/rejection examples. The Fourier tail,
Hardy-space lower bound, global delay-padding and passive-implementation
conditions remain analytic or supplied premises. Both helpers run inside
the existing communication job; no physical whole-pair router or filter
synthesis is certified.
The finite-emitter extension proves a uniform late-record bound under a
positive radiative Gram floor and an actual vacuum-preserving ground,
with a Gaussian-code preparation allowance and matched route guards.
Its semigroup, effect and complete-instrument proofs remain analytic;
the replay checks finite full-excitation number identities, vacuum-ground
conditions, Gram-floor enclosures and near-dark counterexamples. Nominal
parameters and a declared uncertainty box are not a measured bath-tail
confidence region, nor do they turn a collective pair into independent
slots. Retained-spin parity and photon-bus identities have exact finite
checks under their elastic QND assumptions. Actual coherent ports, pulse
matching, spin readout, failed heralds and reset costs remain unverified.

The [drifting-alignment benchmark](../research/topics/nr-noisy-recovery/alignment.md)
has exact causal primal/dual null-event witnesses and a native adaptive
realization. Its all-ordinary optimized local limit also uses an analytic
compactness and classical query-choice reduction. This is a strict two-call
comparison, not a mean-cost converse or a demonstrated fresh-frame meter.
The same owner now gives a calibrated one-memory ordinary reuse protocol.
Its exact code, syndrome and differential-channel identities are replayed;
the finite-sample concentration and averaged local-information scaling
are analytic. The bound concerns increasingly long rounds at a shrinking
positive nominal angle, with all calibration queries counted. It supplies
no uniform estimation-risk gain, numeric onset, or noisy-helper guarantee.
The same job now replays rational known-anchor photonic measurement
fixtures, including intrinsic reject weights, the two-angle swap symmetry
and ordinary pointer/output Fisher matrices. The continuous calibration
identities and source interpretation are analytic. These recorded
measure-and-prepare fixtures do not certify a fresh-Haar unread meter,
optimized native readout, full failed-photon instrument or apparatus
throughput.
The [braided-magic result](../research/topics/nr-noisy-recovery/braided-magic.md)
has exact gate-branch, full flagged raw-state, visibility and Pauli-loop
identities. Its [atomic noisy H/S source](../research/topics/nr-noisy-recovery/braided-magic.md#nr-r17-noisy-factory) also has exact eight-vertex joint/decoded moment reconstruction, a full noisy-CS history comparator, symbolic ordinary Clifford-mixture checks and rational distillation-entry arithmetic. Separate bounded mathematical and relevance/model reviews support the conditional magic-distillation source-entry claim. General stabilizer closure, distillation convergence, independence and ideal processor/source premises remain analytic. This is not a hardware threshold, equal-device cost comparison or priority certificate. Protected Ising closure, the complete physical braid phase, position postselection and native factory costs retain their separate analytic conditions.

The [displacement-calibration note](../research/topics/nr-noisy-recovery/geometric-calibration.md)
proves ordinary Weyl-loop, CV shot-order and exact finite-dimensional
global-risk constructions under explicit control and energy assumptions.
Its [two-input force-bus component](../research/topics/nr-noisy-recovery/geometric-calibration.md#nr-r16-two-input-bus)
also proves a full retained-output factorization and a centered-Gaussian
all-decoder fidelity bound with a paid ordinary partial-storage comparator.
These are analytic arguments; source hashes and the finite suite do not
certify their hardware ports, transfer errors or common deadline.
The [rewinding-cost analysis](../research/topics/nr-noisy-recovery/obstructions.md#nr-r05)
derives infinite mean and independent-erasure success for one specified
published recursion. These are analytic proofs; finite replay does not
establish them or an experimental efficiency. Reported optical component
transmissions are not a measurement of the full ordinary echo. None of
these checks establishes a new architecture advantage or source priority.

The current native-interface checks also include exact shared-spectral
Choi/control counterexamples, excitation-exchange schedule and
discrimination identities, and full reset-channel ordinary simulations.
The all-dimension bandwidth--delay bound, terminal fixed-site-noise
bound, thermal filtering inequalities and reciprocal emitter scattering
model are complete analytic arguments in their respective owners.
The calibrated bosonic compilers have exact finite Fock/control and
Gaussian/Weyl coefficient replays; all-Fock extension and the required
Fourier/Gaussian integrations remain analytic. The local-output terminal
noise proof permits globally interacting CPTP preprocessing; finite
replacement cross-map identities and sharp SWAP witnesses are replayed,
while its universal norm and adaptive-use arguments are analytic.
The single-rail transfer component derives its reference-complete
amplitude-damping endpoint, fidelity conversion and delayed-field kernel
analytically. Its separate fresh-channel terminal-filter obstruction is
a Kraus/Choi-rank proof; the existing replays do not certify that general
quantifier or a giant-atom device. No encoded-strategy, approximate-recovery
or measured transfer-rate converse is claimed.

The full passive-vacuum transfer and directional loss-record arguments
are analytic family-level statements under their specified optical model.
The passive two-photon reordering comparison has finite exact seed,
coefficient, second-design and CP-overlap checks; its representation
decomposition, Haar identity and dimension-independent variance bounds
remain analytic. No native source or detector efficiency is certified.
The anisotropic characteristic-function obstruction and ideal-GKP
deterministic-fidelity comparison are analytic, with explicit ideal-code
and syndrome-port assumptions. NR-R06 also has exact finite Pauli/Weyl
separator, sparse qutrit interpolation and common-final-control-noise
checks. Its arbitrary-register deterministic recovery comparisons use
the complete analytic recovery-to-POVM and vertex-grouping proofs. The
product-probe calibration corollary uses the cited population-recovery
theorem and an analytic estimate-selection bound, with training and reuse
charged. These claims do not model faults throughout the check gates or
remove arbitrary unknown preparation/readout errors. The conditional NR-R10
network comparisons have full control/data parity identities and all-branch
travelling-bus checks. Their physical controller ports, protected transport
and source-loading resources remain explicit assumptions.
The [repeatable commutator component](../research/topics/nr-noisy-recovery/methods/commutator-apparatus.md#nr-r06-commutator-apparatus)
adds exact finite chronological passive routed-isometry and coarse-erasure
effects, retained-loss-control counterexamples, a rectangular stored-model
field-residual identity and independent proper-noise moment fixtures.
General arbitrary-reference erasure equivalence, retimed clock/information
and field-confidence arguments remain analytic. Closed stationary vacuum
services, ideal paid routing, actual phase/power/readout bounds and
frequency interpolation are explicit premises. The source's spectral
normality is not a measured commutator, and its transpose port is not an
executable quantum adjoint. No retained-loss-control simulation or measured
native rate/advantage is certified.

The required-projector component adds complete finite local/control
instruments, exact word powers, repeated-contraction and isotropic-trace
guards, and rejected-ground checks. Its all-rank decomposition and
convergence limits remain analytic. The source-derived three-site feedback
component checks complete channels, ground pumping, a compiled third
update, one-pass/nonstationary initialization, and conditional full
control/reference clock-record and clean-ready-meter identities. Full
spin-space local/layer covariance and record-permutation fixtures for
finite even rings guard the analytic many-body translation compiler. These
fixtures do not establish convergence speed or a physical order router.
The required entangling-gate discussion is a primary-source assessment:
measured erasure-selected benchmarks, simulation results, conditional
diagonal-survivor arguments and full herald/reset costs stay distinct.
No new measured instrument, ordinary optimum or native advantage follows.

The required charging comparison is analytic: the full pure-charger
ready-column compiler, fixed-excitation support, chosen-input diagonal
meter instrument, fine-record extension and convex entropy-cost envelope
have explicit proofs in the baseline owner. The replay fingerprints that
note but does not certify a measured meter, actual reset work, equivalence
of additional physical charger/environment outputs, arbitrary-input
identities outside the ready-column scope or physical charging advantage.
The cold entangler's conserved-number/outer-rail argument is also analytic
within the published loss/dephasing surrogate; it is not a full measured
accepted/erased instrument, online-herald or controlled-order certificate.

The [programmed cyclic-chip comparison](../research/topics/nr-noisy-recovery/architecture-baselines.md#nr-r06-programmed-cyclic-chip)
uses the existing known-record compiler. Its four-cycle launched ledger,
BB84 measure-and-prepare bound and coarse-flag identifiability example are
analytic; the replay fingerprints the owner without a new source-specific
guard. They establish no corrected-chip fidelity, raw-data EB fit, retained
unknown-input port or complete clock.

The [thermal-return/cadence component](../research/topics/nr-noisy-recovery/methods/thermal-return-cadence.md#nr-r06-thermal-return-cadence)
adds exact finite generator, reset, formal-composition and deferred-marker
identities for a declared code/vacuum model; complete two-rail GAD flag maps
and retained-control/parity cross blocks at a rational channel point; warm
and stronger-cadence arithmetic; and cold-proof coefficient/envelope
ingredients. Continuous-time semigroup, arbitrary joint terminal recovery
and the all-lambda>=1 cold-regime dominance theorem remain analytic.
The uniform-reset and GAD models are separate, unfitted baselines. A finite
replay certifies neither physical thermal rates nor parity-marker/order
interfaces, clocks or an all-ordinary advantage.

The [joint-vacuum flag comparison](../research/topics/nr-noisy-recovery/architecture-baselines.md#nr-r06-joint-vacuum-flag)
is an analytic ideal-instrument proof and primary-source assessment.
The shared-probe construction, ordinary measured-flag equivalence,
vacuum-sector one-jump kernels and restricted control argument are not new finite-replay or
Lean endpoints. The current replay fingerprints their owning source;
it does not establish a calibrated active-helper pulse, physical coherent
order port, cross-history bath model, complete reuse clock or fault benefit.
The separate transmon symmetric-readout source supplies an ordinary
benchmark, with its integration and device scope kept explicit.

The [TIP gate component](../research/topics/nr-noisy-recovery/methods/tip-gate-screen.md#nr-r06-required-tip-entanglers)
contains analytic shared-qubit, dressed-return, equal-window common-clock
fault, helper-relaxation, ordinary echo and rectangular-selector arguments.
Its exact guard replays rational moments, held-phase echo matrix units,
flag-recovery and common-helper-rotation identities, utility margins,
common-pump prefix ingredients, finite-body coefficient/padding/clock
arithmetic and full-flag post-idle mixing fixtures. The common-rotation
bound requires fixed physical white jumps and a factorized helper-independent
body; conditional retagging, reset and real retained coupling are outside it.
The one-flag CP reduction, continuous prefix/phase arguments and finite-pulse
operator-error proof remain analytic. The slow closed-model body is not a
competitive waveform or noisy-instrument certificate. Neither the finite
fixtures nor the analytic bounds establish a global ordinary optimum,
full-device speed limit or unavoidable all-flag idle penalty. Actual bath
correlations, coupled-sector calibration, extra controls and complete
recovery/readout/reset costs remain physical premises; no new Lean audit,
source-fitted noise prediction or hardware advantage is certified.
The [moving-encoding comparison](../research/topics/nr-noisy-recovery/methods/tip-gate-screen.md#nr-r06-tip-moving-encoding)
adds exact finite helper/B fine operators, full-flag/no-jump rate ledgers
and a rational margin over one feasible native rule in a stronger control
model. The separate instantaneous control-span matrix does not exclude
finite synthesis. General moving-frame/reference, continuity, conditional
edge/derivative and robust-utility proofs remain analytic. The encoded
body, its fixed driven-white baths and actual pulse/clock realization
are supplied premises; neither a physical advantage nor an optimized
native converse is certified.

The separate encoded-Pauli replay checks full code-input and retained-record
channels, mixed/reference states, the deferred coherent-record circuit and
a non-phase helper-noise counterexample. Its proof assumes clean decoded
control storage and the priced nondemolition-read or coherent-record ports.
It preserves the source's restricted fixed-map comparison and does not
establish equal laboratory time or simulate arbitrary joint inputs.
The graded Majorana extension separately uses an even fermionic collision
dilation, independent isotropic mode faults and a measured final code-parity
record. Finite exact checks support its tetron code maps, controlled-even-parity
flags and calibrated stochastic flag processing, together with larger-mode
logical-class weights, balanced even-product checks and common final helper
visibility. The all-even-mode comparison with native decoders and Bell-input
receiver filters, and the general tetron postprocessing proof, remain analytic;
rational-grid replays guard transcription. They do not certify microscopic
poisoning, arbitrary noisy check gates or rejected odd-parity outputs.
The microscopic thermal-contact extension adds finite Gaussian matching,
CAR bath-copy and reference-matrix-unit compiler checks. The continuum
limit, correlation-moment and diamond estimates, symmetry reduction and
adaptation of the cited stability theorem remain analytic. The stronger
uniform-duration estimate concerns code inputs with passive references;
finite algebra does not certify measured spectra or an available coherent
contact selector. The arbitrary-Pauli extension separately checks both
accepted flag maps, anisotropy, zero-weight endpoints and correctly
transported known-gate checks. Its all-dimensional character balance and
full-reference identity remain analytic under Pauli-diagonal and scalar
cross-map hypotheses, with calibration and controlled-gate costs explicit.
A separate multitime guard checks one correlated two-time Pauli history
law, including cancellation, both physical purification/ordinary records,
and positive control effects. The all-time/full-reference identities,
copy-law reduction and dominant-no-error-history payoff comparison are
analytic. The ordinary comparator needs exposed noise slots and actual
transported coherent checks; it is not a generic nonunitary-process or
shared-bath compiler. Signed reconstruction does not certify delivery of
the virtual purified state.
These compiler hypotheses still require derivation for the split-energy
physical model or any application with required contact operations.
The required BCS-gate component instead derives its threshold tail,
signed virtual contraction, full ideal pulse compiler and restricted
static spectral-dressing estimate analytically. No finite replay proves
the continuum limit, the global spectral hypotheses, a fourth-order gate
truncation or an actual coherent selector. Its separate hypothetical
two-point static-drift test has exact Gaussian matrix guards and outward
rational trigonometric certificates for two ordinary five-pulse words,
including delivered Bell fidelity, mean reciprocal retry cost, commanded
area and safe common-window overheads. One witness is pointwise at the
two drift values; its equal-rate companion is a prior-average comparison.
Neither is an optimized native bound or a source-fitted noise/time model.
The Jaynes--Cummings extension checks the explicit ordinary
isometry/measurement and decision identities. Its complete infinite-Fock
inequality for all positive field energies and high-energy remainder are
analytic. The physical equatorial prior, one ideal gate, known energy axis
and actual Bell/qubit/qutrit memory costs remain explicit. Neither result
settles all native noise models or contradicts the cited restricted
ordinary comparisons.

NR-R19 has finite exact corrected-channel and ordinary-wrapper checks;
its all-ordinary dimension-at-least-three exact converse uses analytic
orbit, polynomial and causal-circuit arguments. Its separate qutrit
rank-one-reflection expected-query fidelity certificate is replayed with
standard-library integer and rational arithmetic. The verifier checks
invariant pairings and basis independence, highest-weight raising kernels
and dimension completeness, reconstructs the retained causal equations
and objective, and checks dual positivity and the residual norm allowance.
The full prior/covariance inclusion, physical trace bounds and reduction
of arbitrary terminating strategies to the stopping relaxation are
analytic proof inputs. This is an unconditional prior-average Bell score
with expected cost averaged over the same prior and Bell input, without
oracle-dependent initial advice. It is not a calibrated persistent-device
throughput bound or an optimal ordinary frontier. Its bounded comparison
of polarization, multimode-routing and frequency-bin refresh interfaces
is a primary-source assessment, not a new measured drift/error bound or
an outcome of the finite certificate. Its private-program access check is
an honest ideal operator identity and source assessment, not a new
cryptographic security proof or a certified unknown-coupler interface.
The private-program replay separately checks complete resource/key
matrices and reference-channel units, relative order phases, the known
central-commutator compiler, both fresh-column CCZ encoding factories,
unknown-control injection and rollback, and an explicit nonblank-extension
counterexample. Its ordinary local
controlled-H gates and joint optical CCZ are different priced ports;
the replay establishes neither full physical source/loss instruments,
composable privacy, timed factory performance nor a resource optimum.
Its balanced reflected-source extension replays finite complex-amplitude
fresh columns, input effects, ordinary compiler, corrected factory flags,
inverse-filter weights and singular/noncontractive witnesses. The
reversed-role ingredient checks both three-contact coherent cleanups and
the two-contact retained forward branch. The general one-visit separability
argument, source-model attribution and rejected-bath ambiguity remain
analytic or source audits; no deposited simulation was executed, no device
fit was made and no full hardware loss/clock instrument was certified.
The natural-exchange source screen and its ideal-vector 3/4
constant-hold transfer bound are analytic assessments, outside the finite
certificate's hardware scope. The online detector-feedback comparison
is a primary-source baseline, with experimental, simulated and projected
timing distinguished; no new controller implementation is validated here.
Native coupler access,
primitive errors, routing costs and a finite-energy GKP bound remain
unverified.
The Andreev extension has finite exact reflection-signature,
particle-hole-symmetry, rank-one commutator and bandwidth identities.
Its fixed-dressing family obstruction and device mapping are analytic.
Those results constrain the stated Majorana/converter models and do not
extend the full-Haar certificate to a symmetry-restricted physical prior.
The passive-converter replay reconstructs full exact scattering matrices,
unequal-linewidth matching and mismatch examples. Its Bragg-scattering
checks verify finite rank-one transfer, phase and trace identities for the
specified equal-power model. General family arguments and source-to-device
mapping remain analytic. Detuning, internal loss, conjugate-mode gain,
finite bandwidth, drift and alternative interactions require their full
instruments; measured coherent-tone mode counts alone do not certify the
unknown quantum coupler family or a task advantage.
These checks do not constitute a measured instrument, a new
fault-tolerance threshold or an architecture advantage.

NR-R11 also replays ideal Raman helper fanout and all four corrected
remote-SWAP teleportation branches, including reference matrix units.
The known-gate helper extension checks four-mode heralded CZ and its
coherently read identity-retry completion, eight-mode deterministic CZ,
and sixteen-mode known-target teleportation. Full input/reference matrix
units, every target coefficient direction in the general program and
source-versus-key dephasing guards support those finite identities.
The qualified smaller-port timing construction, actual enlarged helper
ports, gate synthesis, continuum loss and complete clocks remain analytic
or physical premises. Ideal identity flags do not certify photon-loss
recovery or an unrestricted noisy ordinary optimum.
The bare full-SWAP guard checks literal columns and output supports,
terminal completeness, matrix ranks and target-trace inequalities at
$d=2,3$. Its all-dimension, mixed-source and arbitrary-decoder bounds,
including exact-unitary yield under a whole-isometry perturbation
promise, remain analytic. Partial exchange requires its actual complete
instrument; an isolated transfer fidelity does not supply that promise.
The fixed opposite-partial-contact example checks all four native and
six ordinary branch maps, source/contact normalization and full gate
matrix-unit coefficients. Scalar, local two-port and
coherent-frequency guards support the ordinary midpoint filter's selected-map identity;
the continuum extension under the stated common frequency-diagonal
scalar elastic responses is analytic. CZ and corrected early identity
retries refer to the calibrated center. Stopping costs remain analytic; neither
full-instrument equality, optimized yield nor a physical/noisy
implementation is certified.
The two-port extension checks dense local qubit/qutrit contacts, including
code exits, and coherent spectral blocks of declared passive two-bright
responses, without fitting the source device. Contact composition and
paired timed records are premises; final code projection does not exclude
omitted flying-mode return paths.
The one-bright operator-contact fixtures use field dimensions two and
three to check literal selected contractions, common filters, the
acceptance contrast between logical inputs $01$ and $10$, and the
declared fixed-target Choi comparison. The general selected-map and
diamond-distance statements and microscopic bridge are analytic.
The ordinary target-score comparison trades acceptance for conditional
fidelity; it is not a whole-instrument, worst-input, rate or reused-bath
guarantee.
Weighted Raman fixtures include complete declared lossless flags,
coherent field/reference maps and certified CP/TNI filters. Exact ledgers,
Gram and support ingredients guard the diagonal-target comparison and
raw-unitary constraint; the general norm and support proofs remain
analytic. No arbitrary-target fidelity dominance, joint-receiver optimum
or device fit follows.
The [raw parity extension](../research/topics/nr-noisy-recovery/communication.md#nr-r11-inelastic-parity)
adds projected-target, positive-support and retained-dilation fixtures
for even and odd parity outcomes with arbitrary unitary output frames.
Its universal bounds remain analytic. These coefficient fixtures are not
certified Raman contacts and establish neither conditional-fidelity
ordering nor a complete parity instrument.
The passive Bell factory fixtures check prepared-input forward/reverse
source/contact paths, unitary four-port processing, normalized analyzer/time flags and local
corrections. Frequency-discard guards retain the distinction from an
actual coherent time click. The continuous-time and approximate packet
bounds are analytic, not a measured detector, routing or feedback certificate.
The [finite-gain bosonic gate component](../research/topics/nr-noisy-recovery/methods/bosonic-order-gates.md)
checks exact NS success/no-count and higher-number ingredients, all KLM
record probabilities, successful reference units, irreversible/leakage
failure witnesses and the auxiliary-photon source probability ledger.
Infinite primitive normalization, all-count classification, helper
optimality, recovery obstruction and the full failed KLM coherences
remain analytic. The accepted-yield comparison is restricted to the
declared two-primitive helper/readout family; it certifies neither
full-failure utility dominance nor a general optical or hardware optimum.
Finite full-radiative Lambda resolvents and flat symmetric lossy
survivor instruments are checked with exact Gaussian fractions. Its
local-ancilla extension reconstructs the six-qubit source, both scatters,
complete photonic readout, local Schmidt expansions and filter effects.
A separate rational witness reconstructs all branches and photonic
unitaries, then checks positive Hermitian LDL decompositions bounding
their largest Schmidt weights. It supplies an achievable intermediate-
transfer Bell yield; the cited LOCC conversion theorem remains analytic.
Neither finite examples nor an unsuccessful optimization search establish
an unrestricted ordinary optimum or an adaptive local-memory upper bound.

The coefficient-independent Raman projection has exact branch-cancellation
checks. Its comparison concerns the scalar switch's minus-only yield.
The operator-valued extension extracts the actual ordinary ordered field
kernel without an all-switch comparison for noncommuting coefficients.
The passive-filter variant requires no extra retained stationary qubits.
Its exact $\mathbb Q(\sqrt2)$ replay checks the optical contraction,
orthogonal heralds, coherent local-filter effect, normalization and
coefficient cancellation. A stronger four-level flying-helper construction
has a complete exact $\mathbb Q(\sqrt2,\sqrt3)$ contraction/readout/filter
and Bell-output replay at a fixed parameter point; optimization within its
family is analytic. Extra photonic modes, vacuum rejection ports and
filter apparatus are physical costs. Neither construction supplies a
global ordinary bound.
The Raman phase-covariance, reciprocal-port and route/double-herald
replays check full finite accepted vectors, source normalization,
Raman/spin-frame transformations and static phase/time guards. The
continuum retarded kernels, physical joint phase spectra, causal pilot
filtering, accepted-record conditioning and source/duty ledger remain
analytic arguments or measured inputs. Scalar node-phase cancellation
does not establish unknown Raman-frame immunity; the double-herald
identity does not compile cycling emission from an arbitrary Raman SWAP.
No measured matched physical route or delivered-rate advantage is certified.
The temporal-helper port replay checks discrete coupler unitarity,
exit/tail accounting, selected order words and complete formal codec
entries, including a same-graph ordinary configuration. The mode-count
obstruction and universal route/code arguments remain analytic; physical
slot stationarity, pulse tails, loss, phase control and reset remain
device requirements.
The balanced-cavity frontier has exact polynomial and nominal-substitution
checks; its continuous detuning/design proof and narrow-pulse limit remain
analytic. Physical frequency-mode symmetry, accepted/lost ports, local
filters and memories, calibrated Raman/path phases, retuning range and
within-attempt stationarity are declared interface requirements. Source,
pilot, route and reset costs must enter matched all-attempt renewal times;
raw-yield comparisons do not certify a measured Bell-pair rate or a clock
advantage. The mechanical-memory hardware screen is a primary-source
assessment and a held-out test specification, not a new measured result.

The direct temporal Raman replay includes its actual passive source,
all clock/port flags and a non-flat-response counterexample. Its finite-tail
extension checks coefficient norms and exact Bell-state geometry, while the
uniform kernel/dilation and decay-floor premises remain device-conditional.
Accepted-only certificates do not determine raw rejected spin states.
The timed-control replay checks the known-frame spin-to-photon compiler
and calibrated late-photon-flip outputs and failure accounting.

The Gaussian readout replays retain complete noise/idler/loss ports and
finite feedback examples, including ordinary conditional likelihoods and
known squeezing/displacement control phases. The full matrix noise floor,
continuous Gaussian kernels, thermal Fock traces and data-processing proofs
remain analytic. The Gaussian full-support obstruction is an analytic
infinite-mode proof with a finite passive reference; no finite replay
establishes its universal quantifier or an approximate-recovery bound.
No new measured device, global ordinary optimum or native advantage is
certified by these additions.

The material-pointer clock replay checks finite array isometries, record
orthogonality, a fresh-clock counterexample, pointer echo and Markov timing
arithmetic. Its full joint compiler and norm transfer are analytic, and its
hardware model remains a proposed combination of separately demonstrated
primitives. A measured scalar memory lifetime is not a certified
cross-history coherence kernel.

The mechanical extension separately checks exact finite partial-meter
control blocks, Gram/Choi witnesses, passive-dilation covariance and
force-loop algebra. Its numerical scalar exponentials are transcription
guards, distinct from those exact identities. Full thermal/continuum
clock kernels, diamond and physical-control statements remain analytic.
The cat-reservoir module checks full finite parity instruments and formal
CCR/no-jump coefficients, with no finite-time truncation or experimental
memory certificate. Higher-order bath, holonomic/adiabatic/BDI and Rydberg
memory modules likewise replay their finite full-output identities;
general support/control proofs and hardware port, phase, bath and clock
premises are explicitly scoped in their canonical owners. None supplies
a significant native architecture advantage.

The memory-algebra checks include complete finite sector/flag maps and
Haar-coefficient contractions, while its gauge entanglement-breaking
and Schmidt-number bounds are analytic. Uniform subgroup enumeration
and Pauli-statistic/Bell/noisy-reference identities support separately
scoped ordinary estimators, not a scalar-specific lower bound.
Local-overlap checks include exact binary-readout distributions and
calibration-bias examples; local-Lindblad checks include full-support
rate/sampling/projection identities and a gate-orbit ambiguity.
Spectral checks cover deterministic bounds, not an implementation
of the cited population-recovery learner. Cross-pair coset and
covariance checks support an analytic query upper bound whose
classical processing and reference access remain charged. No generic
SPAM, model-identifiability, optimal frontier or native advantage
follows from these finite replays. The cat
physical-route and Rydberg exchange checks keep their complete finite
dummy, field, retained-memory and false-herald models. Mechanical
decision coefficients and endpoint garbling are exact; scalar Gaussian
inequality tests remain numerical guards. Continuous-field/interface,
all-n confidence and measured full-cycle performance claims remain
analytic or unverified as specified in their owners.

Current evidence belongs with the claim it supports. When source changes, rerun relevant checks and update the corresponding record in place after success. Keep temporary output under `_build/`; normal Git history preserves prior versions. Do not preserve intermediate build logs or repeated checkpoint reports as alternate research records.
