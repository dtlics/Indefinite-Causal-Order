# Verification scope

Repository organization preserves the distinction between mathematical claims, exact finite checks, computational diagnostics, and a formal proof audit.

| Component | Current evidence and reproducibility |
| --- | --- |
| Research ownership | `python scripts/validate_repo.py` checks canonical result owners, generated indexes, and local links |
| Paper | The selected source compiles in two pdfLaTeX passes to 19 pages, with no undefined references or overfull/underfull boxes; pages 1, 7, 17, and 18 were visually sampled |
| Overleaf export | `python scripts/package_overleaf.py` deterministically packages the exact `paper/main.tex` bytes |
| Selected Lean source | `python proofs/lean/verify_integrity.py` compares 1,651 modules and entry/configuration files to the recorded verification fingerprints |
| Lean rebuild and kernel audit | See [current proof-verification record](../proofs/lean/audit/README.md) and [rebuild instructions](../proofs/lean/README.md) |
| Exact P3 certificates | `python proofs/lean/certificates/verify_all.py` replays the independent support and sparse separation identities using exact arithmetic |
| P1 | The consolidated proof compiles; exact rational matrix generation and the source manifest check pass. The arbitrary-ancilla claim is analytical, not established by finite sampling |
| P2 | `verify_p2.py --all` passes four certificate replays and eleven exact structural checks; these do not settle the unrestricted optimum or finite attainment |
| RG | The source package documents integrity and certificate tiers, including [supporting helpers absent from the supplied material](../research/topics/rg-routed-graph/source/REPRODUCIBILITY.md) |
| C6 scalar checks | The exact-arithmetic replay checks both the paper's `212/10000` estimate and the formal `215/10000` allowance; it does not replace the shared-Haar proof |
| NR physical recovery | The [canonical analytic proofs](../research/topics/nr-noisy-recovery/README.md) and [standard-library exact replays](../research/topics/nr-noisy-recovery/checks/README.md) have one [current input-hash validation record](../research/topics/nr-noisy-recovery/checks/validation.json). Replays check causal PSD certificates, exact contractions, Weyl/dimension identities, and resource/score constants; they do not prove every prose assertion or constitute a Lean audit |
| NR memory qualification | [NR-R20](../research/topics/nr-noisy-recovery/memory-qualification.md#nr-r20) has analytic capacity/query reductions and a general-channel Choi-entropy certificate with a nonunitality correction, alongside unitary-realization entropy proofs. Standard-library jobs check finite flagged maps, stopping ledgers, code-verification Bell isometries, general Kraus/Choi/Gram/tail/pinching identities, ordinary calibration and full helper-port noise maps. Entropy integration, coding, all-dimension learning and native resource arguments remain analytic; no new Lean endpoint or measured native advantage is claimed |

The paper compilation used MiKTeX 25.12. Shell escape was disabled; its related warning and an update reminder do not affect the required build. The visual sample covers four pages, not a complete visual review or an online Overleaf run. The source checksum is `7aafc806fa3573757f3e3a73ffb3476a770ca1928aac17fb2371829f2a43a33a`.

The selected proof-verification record reports 32 endpoints checked with Lean 4.30.0 at trust level zero, using compiled objects matched to the selected sources. It does not claim a second clean elaboration of every module. A new full Lean rebuild or kernel audit was not performed as part of repository consolidation. Source fingerprints and finite Python replays do not replace that audit.

The new NR recovery theorems have not been formalized in Lean or externally peer reviewed. Their mathematical arguments use the explicitly cited mixed-tensor decomposition and approximate-design theorem in addition to the exact certificates. The local result averages over fresh private frames, uses noise once after each whole module with rate of order `1/n`, and bounds a specified signed recovery utility. Its control tolerance is the declared scalar dephasing model. No deployed-runtime, fixed native fault-rate, persistent-frame throughput, or capacity validation is recorded.

The [architecture baselines](../research/topics/nr-noisy-recovery/architecture-baselines.md)
add analytic fault-simulation, reused-calibration and measurement-interface
arguments. Their exact replays check finite full-output examples,
measurement identities and calibration-score arithmetic. The cited
Threshold Search theorem supplies the collective learning bound; the
replay does not implement that learner or determine its asymptotic
constant. These checks do not establish hardware efficiency, source
priority, a general memory-process model or an architecture advantage.

The [depolarizing-search component](../research/topics/nr-noisy-recovery/methods/noisy-search.md)
adds an analytic full-channel ordinary compiler using known controlled
unitaries, plus an every-flag timing proof and uniform counted-restart
bounds. Native-check replays compare finite raw Kraus maps, arbitrary
incoming controls/references, ordinary controlled-Pauli circuits,
deferred records and exact coefficient discrepancies. Their finite
scope does not establish the all-dimension or asymptotic arguments,
native gate costs or availability of a reliable candidate verifier.

The [fault-parity controller component](../research/topics/nr-noisy-recovery/methods/binary-fault-controller.md)
has analytic closed-controller and general-intermediate-operation memory
bounds, with exact finite replays of ordinary qutrit, many-label and
read/reset instruments. The
[controlled-unitary memory test](../research/topics/nr-noisy-recovery/methods/memory-native-cost.md#nr-r20-controlled-unitary-correlator)
has finite exact two-readout, signed-map and phase-drift checks. The
universal dimension, reversible-source, information, uniform-cost, pinching and
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
accepted-CZ separation; general data filters, intermediate matter
controls and hardware rates are outside that upper bound. The repeated
ordinary survivor compiler remains a stronger paid comparator.
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
The all-dimension instrument and known-intervention dilation identities
are analytic. These checks establish neither a fitted bath model nor a
switch sampling or architecture advantage. The application assessment's
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
The [braided-magic result](../research/topics/nr-noisy-recovery/braided-magic.md)
has exact gate-branch, full flagged raw-state, visibility and Pauli-loop
identities. Protected Ising closure, the complete physical braid phase,
position postselection and native factory costs remain analytic conditions.

The [displacement-calibration note](../research/topics/nr-noisy-recovery/geometric-calibration.md)
proves ordinary Weyl-loop, CV shot-order and exact finite-dimensional
global-risk constructions under explicit control and energy assumptions.
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
the complete analytic recovery-to-POVM and vertex-grouping proofs; they
do not model faults throughout the check gates. The conditional NR-R10
network comparisons have full control/data parity identities and all-branch
travelling-bus checks. Their physical controller ports, protected transport
and source-loading resources remain explicit assumptions.
The separate encoded-Pauli replay checks full code-input and retained-record
channels, mixed/reference states, the deferred coherent-record circuit and
a non-phase helper-noise counterexample. Its proof assumes clean decoded
control storage and the priced nondemolition-read or coherent-record ports.
It preserves the source's restricted fixed-map comparison and does not
establish equal laboratory time or simulate arbitrary joint inputs.
The graded tetron extension separately uses an even fermionic collision
dilation, independent isotropic mode faults and a measured final code-parity
record. Its finite exact checks support parity-accepted code maps,
controlled-even-parity flags and calibrated stochastic flag processing;
the general positivity/postprocessing proof remains analytic, with
rational-grid instrument checks guarding transcription. They do not
certify microscopic poisoning or simulate rejected odd-parity outputs.
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
throughput bound or an optimal ordinary frontier. Native coupler access,
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
