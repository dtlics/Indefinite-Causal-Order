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

Current evidence belongs with the claim it supports. When source changes, rerun relevant checks and update the corresponding record in place after success. Keep temporary output under `_build/`; normal Git history preserves prior versions. Do not preserve intermediate build logs or repeated checkpoint reports as alternate research records.
