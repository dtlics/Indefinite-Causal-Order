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

The measurement replay also checks complete recorded parity-braid branches,
initialized-ancilla effects and tracked frame corrections at dimensions
four and eight. The ordinary three-measurement construction is a cited
baseline with an explicit analytic proof. Its comparison to the specified
switch protocol counts retries and permits the same output frame convention;
it does not optimize all coherent measurement protocols or model detector faults.

The [communication note](../research/topics/nr-noisy-recovery/communication.md)
has exact finite checks of absorbing-vacuum loss, sector-preserving noisy-wire
factorizations, and elastic-node commutation. Schmidt-number, relative-entropy
and finite-mean stopping arguments remain analytic; no channel-capacity theorem
is inferred from finite sampling. The native-layer checks likewise assume
their stated ideal helper operations and leave actual helper noise and routing
cost to the application comparison.

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

The two-photon proofs in NR-R11 use the complete scattering basis and
resolvent kernel. The unequal-rate relative-mode gate, normalizable-pulse
target-amplitude identity, photon-preserving readout, known-dressing reuse,
time-record instrument reduction and uniform tail bound are analytic.
The existing finite communication replay does not certify those continuum
arguments, actual phonon overlaps, a native pulse-tail bound, a physical
pair router or a hardware performance advantage. No frequency-grid
certificate or fitted single-mode gate is claimed.

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
These checks do not constitute a measured instrument, a new
fault-tolerance threshold or an architecture advantage.

Current evidence belongs with the claim it supports. When source changes, rerun relevant checks and update the corresponding record in place after success. Keep temporary output under `_build/`; normal Git history preserves prior versions. Do not preserve intermediate build logs or repeated checkpoint reports as alternate research records.
