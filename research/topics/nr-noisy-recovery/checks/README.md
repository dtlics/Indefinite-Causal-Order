# Exact replay

Run from the repository root with Python 3.10 or newer; no third-party packages are needed:

```sh
python -S research/topics/nr-noisy-recovery/checks/run_all.py
```

Use `--record` to replace the single current [validation record](validation.json) after a successful run. It records relative input hashes, command, environment, outcome and scope. The inputs include the topic's canonical Markdown proofs, the linked C6 application proof, and the required checker/certificate files. A normal run checks the saved fingerprints without changing them and fails if the record is missing or stale. Recorded environment metadata is informative; another operating system or Python version does not invalidate matching inputs and scope. Assertions are proof checks: the runner and verifiers reject `-O`.

The runner copies executable inputs into `_build/noisy-recovery/stage/` and runs each job in a fresh `python -S -B` process. Reports, logs, bytecode and other generated files stay under `_build/noisy-recovery/`; tracked checker sources remain unchanged. Run individual verifiers from the staged copy if their detailed output is needed, because some save a report beside their source.

The optional [moving-CAPS packet study](../methods/moving-caps.md) lives in
`../numerics/` and requires NumPy. Its packet, running-wave, ordinary
parity-factory and coherent-analyzer source files and one
[current numerical record](../numerics/moving_caps_record.json) are
fingerprinted by this runner for integrity, but are not executed by the
standard-library jobs. That record identifies its own commands,
environment, guards and empirical refinement checks. Finite convergence
does not certify oscillator tails or a complete physical loss instrument.

| Directory / job | Proof obligations replayed |
| --- | --- |
| `architecture/verify_theory_applications.py` | Exact finite pinching composition, mixer powers, self-SWITCH visibility, weak hidden-basis noise and trial-count constants for [NR-R22](../noise-model-selection.md#nr-r22) and [C6-R08](../../c6-hidden-dephasing/applications.md#c6-r08). All-dimension diamond norms, Haar identities, adaptive C5/C6 reductions and coherent-session semantics remain analytic; no new formal endpoint or hardware claim. |
| `architecture/moving_caps_resolvent.py` with `moving_caps_rank.py`, `moving_caps_factory.py`, `moving_caps_analyzer.py` and `moving_caps_frequency.py` | Exact finite passive-resolvent/optical Gram and complete three-port flux identities, energy-shifting words, Lipschitz/moment and clock/phase guards, measured-flag rank-three decoder fixtures, isolated-blue-band scores/frontier identities, rational source constants, normalized coherent-carrier photon projections/Bell-frame corrections, and finite-frequency polarization/density/bad-mass guards. Infinite operators, carrier isolation, continuum response bounds and physical analyzer/factory access are analytic in [the moving-CAPS component](../methods/moving-caps.md). Optional NumPy sources are only fingerprinted. No oscillator-tail, full loss instrument, frequency-resolution/clock or hardware certificate. |
| `architecture/anticommuting_pulse_gates.py` with `anticommuting_pulse_dual.py`, `anticommuting_pulse_dual.json`, `anticommuting_pulse_support.py` and `pulse_activation_ledger.py` | NR-R21 exact pulse/Euler/full-flag and random-order Choi identities; universal necessary-success support rank, literal Pauli links, causal positive-definite slacks and a matrix sum-of-squares identity for all real pulse angles. The source-parameter activation ledger is a separately labelled floating-point scalar diagnostic. Adaptive-instrument/stopping inclusion, all-launch scalar-price and finite-penalty existence/mean-utility proofs, general selector phase/loss/clock instruments, global diamond equality and hardware premises remain analytic. The linked prose components add no new executable guard or quantitative penalty certificate. No exact rounded digital gate, numerical error tolerance, noisy source process, approximate ordinary optimum, physical router or hardware advantage is certified. |
| `architecture/verify_binary_fault_controller.py` | Exact qutrit/cross-dual Pauli echoes, complete finite fault-word isometries, weighted flags and read/reset instruments; internal anticommutation and inverse-ordered bank guards. Universal space, reversible-source, information, timing and uniform-cost bounds remain analytic; hardware and reset costs are not certified. |
| `architecture/verify_controlled_unitary_correlator.py` | Exact two-readout instruments and signed/nonselective maps, fixed and approximate pinching, mixed-input and phase-drift guards. All-dimension identities, confidence bounds and availability of a coherent controlled-unitary port remain analytic. |
| `architecture/verify_thermal_attenuator.py` with `thermal_self_visibility.py`, `thermal_clock_ports.py` and `thermal_temporal_receiver.py` | Exact finite full-joint contact identities, Gaussian coefficient polynomials, source flag/modulo instruments, finite-dimensional kernel guards, complete symmetric-power photon sectors, thermal-series coefficients, reference/flag/payoff fixtures with exact omitted initial thermal-mixture weight, and ordinary parity/coin-twirl/factorial-moment ingredients. Infinite-oscillator density/faithfulness, Gaussian integration and thermal trace, sharp energy/payoff and complete-gain CP bounds, and hardware premises remain analytic. Clock-port ingredients add thermal-mean coefficients/signs, a bath-pairing falsifier, complete finite non-Gaussian bath-sector/control units and abstract shared-Kraus multiarm/classical-order receiver identities and thermal norm endpoint guards. Full thermal trace, channel commutation, all-reference norm/conditional-state bounds and physical ports are analytic. No output-photon truncation or approximate-recovery optimum is certified. |
| `architecture/verify_unital_entropy.py` | Exact Kraus/Choi contractions, mixed-adjoint energies, nonunitality, pinching, spectral tails and full flagged maps, plus complete Clifford twirls including nonunital and negative-multiplier cases. Entropy integration, relative-entropy convexity and coding remain analytic. |
| `architecture/verify_remote_spin_phase.py` | Complete detected spin-gate, four-mode and erasure maps; scattering/rank-loss, scalar concurrence and rational Bell-yield guards; two-CZ online branches, coherent-spectrum, full-helper, constant-optics, survivor-compiler and local-phase gate-cone identities. Exact arithmetic also checks balanced/opposite-phase gates, decorated eight-mode programs, joint readout, four-window survivors, qualified three-window ports and a rational pooled-primal/fixed-word-dual CZ separation, including terminal separable/LOCC corrections after complete photon readout. Retained-photon guards add full-input ordinary compilers, the sharp four-mode witness, complementary branches, balance/terminal-phase identities and declared loss ledgers. General instrument bounds remain analytic and retain their intermediate-control, memory and correction restrictions; continuum physics, native ports and clock costs are not certified. |
| `architecture/verify_remote_spin_pulse.py` with `remote_spin_gate_budget.py`, `ordinary_spin_gate.json` and `remote_spin_frequency_budget.py` | Outward rational interval integration of the retained full Gaussian Bell-factory witness, including strip and tail errors; exact resonant ordinary CZ primal and station-order guards, fixed-spatial Gaussian error/success arithmetic, a separate interval/Mills exact full-field gate witness, and a common-detuning Sturm ceiling. Universal moment/POVM attainment, all-reference resolvent/Taylor proofs and the native minimum-acceptance interpretation remain analytic. Physical ports, timing, loss recovery and analyzer/control costs are not certified. |
| `architecture/parity_failure_baselines.py` | Parent remote-spin-phase job ingredient: complete finite direct-parity success/loss maps and capped retries; Bell-resource fine/coarse recorded maps, Choi-error orthogonality, mixtures and deadline ledgers. General diamond/recovery arguments and physical branching, isolation, storage and clock premises remain analytic. |
| `architecture/transmon_array_modes.py` | Parent communication job ingredient: rational source-kernel/factorization identities, normalization residues, finite-U phases, central mode nesting, finite-rank commutator and full-reference Choi fixtures. Universal orthogonality, direct-integral unitarity and logical overlap bounds are analytic within the chiral effective model; no microscopic all-frequency, physical pair-router or hardware gate certificate. |
| `architecture/causal_allpass_inverse.py` | Parent communication job ingredient: inverse-impulse coefficients and outward rational delay/error/rejection budgets, including common-delay padding. Fourier/L1 and Hardy-space arguments remain analytic; a causal contraction is not a supplied finite passive filter, readable herald or complete noisy gate clock. |
| `architecture/bosonic_order_gates.py` | Parent communication job ingredient: exact finite-gain NS success, no-count and higher-PNR ingredients; all KLM record probabilities, successful reference units, failure witnesses and an auxiliary-photon source ledger. Infinite normalization, all-count classification, helper optimum, recovery obstruction and full failed KLM coherences remain analytic; no general optical optimum or hardware rate is certified. |
| `architecture/verify_code_bootstrap.py` | Complete self-switch, projection/Petz and framed-qubit echo instruments, Clifford moments, adaptive cost guards and normalized serial-history rank/completeness examples. C6, universal history bounds, all-instance interfaces and coding remain analytic. |
| `architecture/verify_memory_stream_screening.py` | Optimistic caps, direct-sum/stopping ledgers, native early rejection and likelihoods, pointer learning/perturbation, complete five-use erasure maps and antidegrading/extendibility guards. C6, all-size reductions, concentration and physical addressing/flux/clock assumptions remain analytic. |
| `architecture/verify_bosonic_logical_frontier.py` | Rational retention/prior bounds, Gaussian-control/Weyl and syndrome phases, energy, coherent gauge-tag recovery and finite-SDP bookkeeping. Heat positivity, continuous integration, Fourier completeness, recovery duality and physical decoder costs remain analytic. |
| `architecture/verify_heat_gkp_tails.py` | Outward rational interval certificates for raw heat-code Gram matrices, all-input moments, projection-polar source and Gaussian-circuit photon tails. Continuum/operator formulas remain analytic; no recovery SDP, physical encoder/decoder or native implementation is certified. |
| `architecture/verify_heat_gkp_recovery.py` | Outward analytic Gaussian matrix enclosures, exact finite-code isometry/energy and positive trace-preserving recovery completion. The raw-switch upper uses an analytic broadcasting/distance proof. No intermediate-controller, repeated-block, heralded-frontier or physical decoder optimum is certified. |
| `architecture/verify_orthogonal_entropy.py` | Exact orthogonal non-Pauli unitary bases, Choi entry contractions, commutator energies, threshold bounds and target-dependent full flags. The entropy integral and capacity theorem are analytic. |
| `architecture/verify_approx_unitary_capacity.py` | Exact unitary/Gram overlap corrections, weighted tails, fidelity inversion, commuting counterexample and rational confidence certificate. Finite matrices do not establish the all-dimension entropy proof or a physical error model. |
| `architecture/verify_pauli_local_certification.py` | Exact ordinary OR and known population-estimator identities, correlated error laws, full readout-noise trajectories and the rational population example. Confidence and physical SPAM assumptions remain analytic. |
| `architecture/verify_pauli_noisy_structure.py` | Exact contaminated-subspace moments, hidden-product invariants, short-window extraction and mixed-target prefix-mass identities. Model-selection, concentration and runtime proofs are analytic; exponential classical processing is explicitly charged. |
| `architecture/verify_public_clifford_calibration.py` | Exact mixed-target PCS records, transported Pauli probes and ratio/parameter-error arithmetic. The public-tableau and calibrated known-control premises are physical requirements. |
| `architecture/verify_pauli_slot_noise.py` | Exact local depolarizing-noise kernels, all-parameter polynomial envelopes, complete control/target/memory matrix units and KL constants. Its general helper-port converse does not cover retaining or processing the output target. |
| `architecture/verify_memory_partial_bell.py` | Exact finite partial-Bell kernel Gram forms for commuting error streams, equivalence of streaming and full-kernel tests, and uniform-label detection conditioned on observed local syndromes. The general sample bound and physical controls remain analytic. |
| `architecture/verify_memory_fixed_probe.py` | Exact small-instance fixed-layout likelihood ratios, full-rank syndrome probabilities, total-variation guards and expected-budget constants. Its lower bound excludes changing layouts and coherent multiquery receivers. |
| `architecture/verify_memory_qualification.py` | Finite exact burst compositions, complete flagged target-channel instruments for amplified self-switches, local-mode blindness, helper visibility and a quasistatic counterexample. Also checks history-dependent mean-cost simulation ledgers, the C6 truncation constant, code-verification Bell isometries, accepted logical-policy scores and tight X/Z intervals, full-record counterexamples and pointer-tag cross maps. General full-run confidence, record-overlap norms, capacity coding, all-dimension query reductions and native logical/control ports remain analytic. |
| `architecture/verify_entropy_capacity.py` | Exact character orthogonality, spectral-tail and conditional-identity arithmetic, rational square-root confidence enclosures, a full-support capacity witness and counterexamples. The Shannon tail integral and quantum coding theorem are analytic; finite cases are not a capacity experiment. |
| `architecture/verify_pauli_subspace.py` | Finite low-rank symplectic geometry, injective syndrome readout, span-expansion and false empirical-constraint mass guards. Distribution-free concentration, all-dimension learning bounds and physical preparation/readout costs remain analytic. |
| `algebra/brauer_objective.py --validate` | Independent sparse physical Choi contractions: every diagram at dimension 2, selected diagrams at dimension 4, both device labels and fidelity/probability objectives. Gaussian integers and fractions only. |
| `algebra/brauer_gate_product_exact_check.py` with the deterministic-tree JSON | Dimension-8 global-noise ordinary converse. Rebuilds all objective Gram equations, causal slacks and exact diagram sums of squares. |
| `recovery/expected_cost_D8.py` | Replays the full heralded dimension-8 certificate through the same checker, then checks its homogeneous intercept, expected-cost elimination and Bell/private-state payoffs. A second standalone heralded replay would duplicate this job. |
| `recovery/finite_ensemble_D8.py` | Constructs all 72 projectors in nine mutually unbiased bases using Gaussian integers, verifies their first and second moments and every overlap, then checks the finite-input recovery payoff reductions. The full D8 source certificate is replayed by the preceding job. |
| `acceptance/acceptance_correct_sharp_stdlib_replay.py` | Correct four-port adaptive acceptance dual for all dimensions at least 8. Rebuilds 72 symbolic Gram equations, all 108 principal minors, 16 cup-free characters and the directed causal prefix equalities. Supplied Boolean flags and expression strings are not trusted. |
| `local/verify_structural.py` | Formal cup/Pauli contractions, invariant-component normalization, all adjoint contractions, one-cup weights and exact rook-graph overlap identities. |
| `local/verify_dimensions.py` | All mixed `(3,3)` Weyl dimension identities, multiplicities, physical/commutant dimension sums and polynomial lower bounds. |
| `recovery/scalable_global.py` | Exact global-noise scalar and polynomial corollaries for qubit dimensions `8,16,…`, including expected-query reward and conservative design loss. |
| `recovery/local_recovery.py` | Frozen local-noise intercept, stopping coefficients, approximate-design loss, recovery reward and 97% control-visibility margin for at least eight qubits. |
| `architecture/verify_fault_simulation.py` with `reflection_instrument_guards.py`, `reflection_sector_guards.py`, `passive_contraction_guards.py`, `field_model_pilot_guards.py`, `thermal_cadence_guards.py`, `dualrail_thermal_guards.py` and `thermal_cold_cutoff_guards.py` | Finite exact orthogonal-process and full switched-output examples for the calibrated classical-fault baseline NR-R06; full-control unnormalized-Fock loss/amplifier coefficients, controlled-number phases and Gaussian/Weyl coefficients; passive two-photon seed weights and signed-estimator coefficients; qutrit second-design and CP-overlap identities; a correlated two-time Pauli-history purification/ordinary-check fixture with cancellation, complete flags, launched utility and positive control effects. Reflection ingredients add measured-X/target/reference sector-diagonal fixtures and boundary witnesses, ideal chain symmetry/sector ranks and finite moment/target-bias guards. Passive ingredients add 32 chronological routed isometries, 512 complementary-effect matrix units and retained-loss-control counterexamples. Stored-model ingredients add a rectangular column-residual identity, independent proper-noise moments and a commuting-normal spectral counterexample. Thermal ingredients check 340 finite generator/reset/composition/marker identities; 32 full GAD flag maps and 48 retained-control/parity cross blocks from 256 Kraus pairs per scheme; warm and four-check utility arithmetic; and 112 cold-envelope plus 12 ratio fixtures. Continuous-time, arbitrary joint recovery and all-parameter dominance are analytic proofs; physical rates, full parity access, independent selectable baths and complete check/selector clocks are application premises. Uniform-reset cadence and two-rail GAD are distinct declared models, with no physical or all-ordinary advantage certificate. General passive erasure/reference, retiming/information, model-confidence, reflection instrument/robustness, all-size support, temporal-history, copy-law and transported-control proofs remain analytic; stationary vacuum services, routing, field power/phase/readout and grid regularity are premises, with no native rate certificate. Actual spectral ports, four-point observables and noisy random-design quality are not certified. Infinite-Fock extension, Fourier/Gaussian integration, representation/Haar/variance proofs and native helper costs remain analytic. |
| `architecture/verify_reuse.py` | Rational threshold, spectral-gap, recovered-score and training/rejection crossover arithmetic for NR-R07. The collective learning algorithm and its asymptotic constants are cited inputs, not computed by this replay. |
| `architecture/verify_measurements.py` | Small exact Lüders PVM examples, Choi overlaps, recorded return probabilities, binary trace-filter identities and syndrome-sector scaling constants for NR-R08. Initialized-ancilla parity examples at dimensions 4 and 8 check all recorded braid branches and frame corrections, with a full unread-control Choi identity at dimension 4 and retry-cost arithmetic. Two-photon PBS, coherent path and uniform post-interaction loss guards distinguish true delivery from false heralds; no fitted detector/source model or delivered hardware rate is certified. |
| `architecture/verify_communication.py` | Full Choi equalities for six absorbing-vacuum examples, sixteen rank-one-channel/noisy-qubit-wire factorizations, four rank-two protected-factor factorizations and four tight qubit-activation examples, plus an elastic-node instrument and a bus-mixing counterexample. Also checks the conditional global-Pauli parity compiler, all travelling-Fredkin-bus branches and source-loading identities; few-emitter number-operator, vacuum-ground, Gram-floor and near-dark examples; and full elastic retained-spin parity/photon-bus instruments. Raman checks cover helper fanout, reference-complete remote SWAP, bare full-SWAP support/completeness/rank/target-trace fixtures at dimensions two and three, radiative resolvents, local-ancilla branch/filter identities, a rational intermediate-transfer Schmidt certificate, coefficient-independent projections, ordered field-kernel cancellation and balanced-cavity polynomial identities. General bare-SWAP and robust-yield, entanglement conversion, finite-mean, capacity, semigroup/record-tail, continuum design, pulse-error and physical access proofs remain analytic. |
| `architecture/verify_native_checks.py` with `required_projector_filters.py`, `feedback_cooling_controls.py`, `tip_helper_guards.py`, `tip_common_rotation_guards.py`, `tip_moving_encoding_guards.py` and `tip_encoding_control_guards.py` | Exact finite known-Clifford Pauli-check and classical-bit-oracle comparisons with non-Pauli noise; twenty paired flagged-Kraus identities for qutrit-router address checks, leakage projection and diagonal-phase blindness; same-ideal-unitary Bell-score and full clock-noise Choi comparisons at dimensions 2 and 4. Eight known-basis fault/full-Choi cases include four nonzero coherent-cross witnesses, and 48 number-lowering Kraus-pair cases test the complete accepted CP decomposition. Explicit double-fault and two-photon-loss examples guard the single-fault/parity limits. Also checks common-replacement cross maps and norm factors, sharp SWAP/nonuniform weights, calibrated Pauli/qutrit recovery, common final-control noise, encoded Pauli retained-record channels, graded tetron code flags, larger-mode balanced Majorana checks, thermal-contact bath-copy compilers, finite-energy Jaynes--Cummings comparison identities, complete projector-filter/rejected-ground fixtures and source-derived feedback/meter/clock-record instruments and full-spin even-ring covariance/record permutations. TIP guards retain rational data/coupler/helper moments, held-helper echo matrix units, non-Pauli filter and common-helper-rotation fine-map/geometry ingredients, weak-boundary-tag utility arithmetic, common-pump sector/prefix-band ingredients, finite-body coefficient/padding/clock arithmetic and full-flag post-idle mixing fixtures; The moving-encoding ingredients add nine full-flag/no-jump rate ledgers, eighteen helper fine-operator cases, nine B-lowering/no-jump cases, a strict rational margin and twelve instantaneous laboratory-span generators. General moving-frame/reference, smoothing, robust-utility and control requirements remain analytic and assume the supplied encoded body; no optimized-native or physical advantage follows. Continuous speed, phase correction, finite-pulse norm, CP reduction and physical bath/control proofs remain analytic. The rotation bound assumes factorized helper-independent dynamics and fixed white jumps, not conditional retagging/reset or the real coupled device. The feedback fixtures retain extra-update versus control currencies and one-pass versus stationary objectives; all-rank contraction, general convergence, source mapping and physical costs remain analytic. Universal diamond/dominance, infinite-Fock/energy, physical timing and access arguments remain analytic; no fitted helper-gate or hardware-runtime model. |
| `architecture/verify_dispatch.py` | Thirty-six reference-complete flagged counter/data Choi examples at data dimensions 2 and 3; 96 temporal phase-path identities; nine event-head, three clock-time and six fresh-repeat/rewind cases; the indexed-unitary identity and three/four-call dummy factorizations. Gaussian decoder and whole-frontier arguments remain analytic. |
| `architecture/verify_dispatch_baselines.py` | Forty-eight full accepted-Choi mean-cost examples and twelve hard-two controlled-teleportation examples at data dimensions 2 and 3. Rebuilds CP/TP projector certificates, exact Bell/diamond witnesses and heralded counter-dephasing maps. It does not optimize the positive-cost frontier or compute the qualitative converse's margin. |
| `architecture/verify_lookups.py` | Full-address Choi identities for all 340 Boolean table pairs at address dimensions 1–4, both measured flags, conditional correction and rejection accounting; the four-truth-pattern balanced-switch junk-erasure projector. The general scoped erasure bound and native access assumptions remain analytic. |
| `architecture/verify_backaction.py` | Reference-complete flagged echo/switch Choi identities at bath dimensions 2 and 3; a rational pair with equal first-echo flagged bath outputs but unequal uninterrupted two-cycle memory fidelity; an ordinary three-window record contrast; polynomial calibration/storage families; full corrected odd-coupler channels and ordinary wrappers; chronological/module-labelled recovery records and complete accessible one-way monitored instruments; and finite Majorana signature, particle-hole-symmetry, rank-one commutator and bandwidth guards. The universal instrument, norm, fixed-dressing family obstruction and dimension-at-least-three query-converse arguments remain analytic; no sBs fit or discarded-purification/future-bath equivalence is certified. |
| `architecture/loss_memory_qualification_guards.py` | Parent backaction job ingredient: finite collective and loss-only channels, complete retained control/reference maps, minus-flag and survivor-record boundaries, ordinary parity flags and active recovery; single-carrier dual-rail slots, full success/seed/reject maps and projector-bound ingredients; multiple-survivor phase cycling, literal CNOT collection/discard, and an unequal-vacuum-record/ordinary-conjugation boundary; conditional helper transfer, spectator-readout disturbance, and declared two-logical-qubit singlet/hopping/thermal/heating limits; permutation/character, doublon-Gram, binary pulse, sign/hazard and fixed local-loss recovery ingredients; active-gate/code-fixed recovery, full-system dummy/record, cavity-only and intermediate-herald fixtures with true-excitation bounds. General Schur, finite-period control, shared-history, isometry/norm, arbitrary-decoder and concentration proofs remain analytic; no source pulse fit, physical routing, protected meter, bath reset or timing advantage is certified. |
| `architecture/pair_memory_qualification_guards.py` | Parent backaction job ingredient: exact dedicated-pair Schur factors and encoded channels, labelled/full-record counterexample, parallel classical-phase estimators, phase scores and spectator/independent-switch scope witnesses. General recovery optimality, simultaneous confidence and calibration-transfer proofs remain analytic; no physical model or native advantage is certified. |
| `architecture/private_program_guards.py` | Parent backaction job ingredient: exact fresh-resource/key instruments, relative order phases, central-commutator compiler, CCZ encoding factories, unknown-control injection/rollback and a nonblank-extension counterexample. Balanced reflection fixtures check effects, selected compilers, inverse filtering and singular/noncontractive cases; reversed-role maps check three-contact coherent cleanup and the two-contact forward branch. Complete C/S/reference matrix units are retained. General separability/recovery proofs, source attribution, rejected/loss/clock/control instruments and security remain analytic or unprovided. |
| `architecture/verify_metrology.py` with `whole_gate_marker_guards.py` | Reconstructs the hard-two-query adaptive phase/amplitude-damping dual from Kraus derivatives and one rational witness JSON. Rational square-root intervals and a complete exact LDL reconstruction certify its 16-dimensional LMI. Also checks explicit joint-readout Fisher information, visibility/loss thresholds, the plain-switch/retained-echo polynomial, regular echo arithmetic and the feasible three-query feedback recurrence; known-unitary pre/post compiler identities, equal classical direction channels with different coherent extensions, full output/syndrome identities and exact SLD/QFI examples. The one-marker refinement adds nine whole-gate matrix-unit isometries, 36 measured-flag fixtures and a known auxiliary-unitary check in exact Q(sqrt(2),sqrt(3)); all outputs include retained leakage and reference coherence. Arbitrary-dimension/reference equality, noisy-checker full-joint commutation and clean-target prefix requirements remain analytic; marker preparation/readout, classical sampling, extra coherent helper/unitary and physical clocks are paid premises. Tester semantics, covariance/concavity, continuous-time inclusion, complete native instruments, global risk and physical costs remain analytic. |
| `architecture/verify_braided_magic.py` | Exact quarter-braid gate branches, the extremal stabilizer overlap, both complete flagged raw-state ensembles for five rational helper visibilities, the physical-$S$ half-exchange yield and exposure count, and sixteen Pauli-loop closures. The protected-resource closure, complete physical phase, native position histories and logical factory costs remain analytic. |
| `architecture/verify_alignment.py` with `photonic_alignment_guards.py` | Reconstructs the joint Haar-Choi sectors and exact ordinary adaptive null-event primal/dual certificates with Gaussian integers and rational arithmetic. Checks the native isometry/projector realization, pointwise null event, reversed wire convention, multi-copy coefficients and visibility identities. Also checks the general-axis two-controlled-Z code, its full syndrome channels, known-plane binomial information and differential coherence identities. Known-anchor photonic fixtures include five one-angle and nine two-angle measurement laws, intrinsic reject weights, ordinary Fisher matrices and the native input/output-drift ambiguity. The optimized hard-cap local limit, calibration concentration, growing-round averaged-information and continuous photonic proofs remain analytic; no finite onset or hardware promise is certified. |
| `coupler/verify_mean_query_certificate.py` with `coupler/mean_query_certificate.json` | Qutrit rank-one NR-R19 ordinary expected-two-query fidelity ceiling. Rebuilds all 740 invariant basis matrices, checks highest-weight kernels and dimension completeness for 220 blocks, reconstructs 90 retained causal equations and the normalized objective, and verifies rational dual positivity and the residual allowance. The fresh-prior/covariance inclusion, physical trace bounds and arbitrary stopping reduction remain analytic. |

The five modules in `algebra/` form the shared exact engine. `brauer_exact_replay.py` derives diagram multiplication, adjoints, traces and identity insertions directly from pairings. `brauer_objective.py` constructs canonical Gaussian-integer objectives; `brauer_weingarten.py` inverts their permutation Gram system over fractions. `brauer_sos_certificate.py` checks the actual tensor-operator sum-of-squares residual and its norm margin. The main checker independently verifies every objective Gram equation and reconstructs every certificate slack. Both dimension-8 certificate JSONs are required inputs; search diagnostics and cached slacks cannot substitute for a successful replay.

These checks complement the canonical mathematical proofs. Their finite or polynomial identities do not independently prove representation-sector completeness, stopping-time reductions, physical access assumptions, or approximate-design norm transfer. Those arguments remain in the linked method notes and theorem. This package performs no solver search, floating-point feasibility test, hardware experiment or new Lean kernel audit. Numerical discovery scripts, repeated audit narratives and search caches are intentionally absent.

The native-check job additionally supports the
[depolarizing-search component](../methods/noisy-search.md): raw switch
blocks, full arbitrary-control ordinary compilers, complete deferred
flags, retained references, restart identities and the primary-source
coefficient discrepancy. The all-dimension unitary-basis proof,
arbitrary-length induction and uniform restart bounds remain analytic.
Known control/calibration and reliable verification ports are charged.
The job's [final-flag completion ingredient](../methods/final-flag-completion.md),
`architecture/final_flag_completion.py`, checks finite random-order CP
complements, all plus/minus histories, common decoded payload/reference
maps, abort effects/traces, mean-call ledgers and nonzero cubic terms.
The full-flag diamond comparison and general survival/error bounds remain
analytic. It does not certify physical routing, accepted-only or
branch-dependent recovery, or exact equality of early-abort mean costs.
The measurement job checks [central inverse-fault cancellation](../architecture-baselines.md#nr-r08-central-involution)
on full coherent recorded Kraus operators, noninvolutory faults and
covariance counterexamples, plus a known-state logical probe. These are
scoped instrument examples, not device-level fault certification.

The communication job's ordinary Raman gate programs include four-mode
heralded CZ with a coherent early identity-failure completion, eight-mode
deterministic CZ and sixteen-mode known-unitary teleportation.
It checks all outcome/reference coefficients, complete success/failure
effects, source/key coherence and qualified window serialization.
Actual loss, partial exchange, helper-preserving ports and physical
retry/controller clocks are not certified.
The fixed opposite-partial-contact example checks four native and six
ordinary branch maps, source/contact normalization and complete effects.
The scalar, local two-port and coherent-frequency guards support its
selected-map identity in the stated callable-contact model; the general
block and continuum arguments are analytic. CZ and the specified early
identity retries
refer to the calibrated center. This does not certify full-instrument
equality, an optimal yield or a complete physical/noisy implementation.
Dense two-port fixtures include excitation-changing qubit/qutrit contacts
with local code exits. Contact composition and paired timed records
remain premises; final code projection does not close omitted flying modes.
Two- and three-dimensional field fixtures also check the one-bright
operator-contact selected contractions, common filters, logical-input
acceptance contrast and fixed-target Choi scores. General map-distance
bounds and the microscopic model bridge remain analytic. The comparison
does not certify whole-instrument or rate dominance, arbitrary readouts
or a reused-bath trajectory.
Weighted Raman fixtures retain complete flags and coherent field/reference
outputs, certify common CP/TNI filters, and check target/error, Gram and
unitary-support ingredients. They are declared lossless examples.
The general selected-map norm and raw-unitary bounds remain analytic;
the diagonal-target comparison is not arbitrary-receiver, equal-yield or
device-rate dominance.
The raw parity extension checks projected targets with arbitrary output
unitaries, positive-support and retained-dilation ingredients. Its general
even/odd bounds remain analytic; coefficient fixtures are not certified
Raman contacts, and no conditional-fidelity ordering or complete parity
instrument is established by those selected-map checks.
Passive Bell factory fixtures reconstruct both fixed-order/source
variants, contacts, passive midpoint/analyzer, normalized port/time flags and
corrections, including a frequency-discard/no-eraser guard. The continuous
time instrument and finite-packet bounds remain analytic; these checks
do not certify an unknown-input gate or physical detector/router performance.

The encoded-Pauli checks include the full code-input and retained-record
channels, reference matrix units, actual deferred record gates and a
non-phase helper-noise counterexample. The graded Majorana checks concern
the declared independent isotropic even dilation and final parity-accepted
code: tetron measured-flag processing, larger-mode logical-class weights,
fixed balanced checks and common final helper visibility. CAR and polynomial
identities are exact; rational-grid instrument checks guard transcription,
while the all-mode optimized-decoder comparison and general tetron
postprocessing proof remain analytic. They do not certify a microscopic poisoning bath or
rejected odd-parity outputs. The thermal-contact replay adds exact finite
Gaussian matching, CAR temporal-copy and full code-flag compiler guards.
Continuum convergence, correlation-moment/diamond bounds and the cited
stability-proof adaptation remain analytic, with their code-input and
physical-control assumptions retained.
The separate arbitrary-Pauli compiler replay checks uniform-check
character balance, anisotropic two-flag maps and known-gate transport,
including a non-Clifford fixture. Its general reference-complete identity
assumes a Pauli-diagonal accepted map and scalar copied cross map;
parameter knowledge and actual transported-check costs are charged.
The same job certifies the required-gate component's two five-pulse
witnesses with outward rational sine/cosine/arctangent bounds and exact
physical Pauli products. Its finite two-point drift comparisons retain
static-per-job retry costs, both endpoint fidelities, the companion's
prior-average scope and explicit commanded-time/window-overhead bounds.
The BCS threshold, signed integral, ideal synthesis and restricted static
spectral estimate are analytic; the replay does not validate their
microscopic hypotheses or optimize physical controllers.
The Jaynes--Cummings checks support the explicit ordinary
isometry/measurement and decision identities. The all-positive-energy
infinite-Fock proof, its asymptotic remainder and matched hardware costs
remain analytic; its equatorial prior and one-ideal-gate assumption are
essential. These comparisons preserve the respective sources' restricted
ordinary baselines.

The measurement job also checks the complete shared-frequency Choi and
order-control counterexamples at dimensions two and four. The general
bandwidth--delay, approximate-rank and spectral-tail arguments in NR-R08
remain analytic. The backaction job now includes excitation-exchange
matrix-unit identities, discrimination-norm factors, Choi Gram spectra
and the clock-dependent native-selector comparison. The general norm
proof and the physical selector remain explicit assumptions/arguments.
The communication job checks full reference-complete reset simulations
for identical and distinct noncommuting states at dimensions two and
three. Its thermal inequalities and the reciprocal two-emitter continuum
model are analytic. The terminal-noise bound in NR-R06 is an analytic
CP-order and Hilbert--Schmidt norm proof, rather than a sampled threshold.
Its local-output extension uses an analytic common-replacement diamond
bound, with exact finite reduced-cross-map checks and a sharp SWAP example.
The passive-vacuum channel and reciprocal loss-record arguments in NR-R09
remain analytic; no finite optical hardware or loss-estimation certificate
is inferred from these replays.
The anisotropic compiler obstruction and ideal-GKP deterministic-fidelity
comparison in NR-R06 are analytic. A separate
[finite-energy component](../methods/bosonic-logical-frontier.md) proves
fixed product-decoder plus-flag and reduced all-control dominance by
calibrated ordinary Gaussian controls. Its normalizable encoding,
coherent-gauge counterexamples and exact abstract recovery maps are
derived analytically. Neither full Gaussian coherent recovery, a
finite-cost native decoder nor an unrestricted heralded frontier is solved.
The native-check job also checks local Pauli separators, Weyl-character
images, sparse tensor-qutrit color interpolation, recovery-to-POVM examples
and common-preparation/final-control-noise identities. The arbitrary-register
dominance proofs remain analytic; a common final control channel is not
a model of correlated faults throughout the check gates.

Additional modules run inside the same existing architecture jobs:

- [Projector-gate terminal filters](architecture/projector_filter_dual.py) checks
  four sector decompositions against the existing shared dual, with 64 integer
  entry identities and 48 positive leading minors. These prove the product
  inequality for arbitrary complex amplitudes and phases. The owning analytic
  Choi-rank/completeness argument covers terminal separable/LOCC correction
  after complete photon readout, including all filter failures. It excludes
  premeasurement/interleaved controls, finite-pulse or hardware-rate claims.
- [Retained-photon dual](architecture/retained_photon_dual.py) checks exact
  formal-phase Gram factors, the all-phase positive polynomial and balanced
  Schur-complement attainment. The instrument reduction, positivity and
  arbitrary-memory arguments are analytic; this is not a hardware or
  intermediate-adaptive-controller certificate.
- [Intermediate photon instrument](architecture/retained_photon_middle.py)
  checks positive algebraic effects, the complete two-history Kraus budget,
  every input matrix unit and all-angle trace-cost polynomial identities.
  Its 167 explicit checks also execute under optimized Python. Operator
  convexity, the general optimization and physical weak-readout access
  remain analytic or additional premises.
- [Serial survivor and local response](architecture/retained_photon_serial.py)
  checks the complete controlled and both-flag maps, raw auxiliary
  polarization and coherent frequency inputs, atomic phases, the qualified
  middle-port spans and regrouping into two event layers. Polynomial
  checks cover a declared closed-transition node's normalization, detuning
  residuals and carrier balance. Further exact ingredients check the
  common-meter delivery polynomial, energy-decay dispersive reflection,
  and clean-CZ relative-sector invariants. Their general inequalities,
  clean-ancilla obstruction and physical meter extension remain analytic.
  Finite-cap endpoint guards retain coherent exit/residual cross blocks,
  raw phase conventions and the late-basis counterexample. A separate
  explicit meter/bath unitary checks both flags and all vacuum/early/late
  matrix units for rational relaxation and pure-dephasing fixtures.
  The general meter-POVM obstruction, coherent-probe overlap tradeoff and
  measured-workload interpretation remain analytic; no device rates are fitted.
  These identities do not establish a
  hardware latency gap, two-opaque-query simulation, calibrated router or
  complete timed loss/bath channel.
- [Four-mode sequences](architecture/retained_photon_chain.py) checks exact
  Fourier cut ranks/minors and query-word/slice fixtures, nuclear-norm
  balance identities, weighted photon-encoding maps and average-cost abort
  comparisons. The all-length rank and recorded-prefix determinant proofs,
  interpolation and continuous-outcome extension remain analytic. The
  strict-visit theorem gives no approximate-gate or hardware certificate.
- [Mechanical strength](architecture/mechanical_pointer_strength.py) checks
  exact finite full-control partial-meter blocks and Gram/Choi witnesses;
  [mechanical clocks](architecture/mechanical_pointer_clock.py) checks exact
  passive-dilation/covariance and force-loop identities, with separately
  declared numerical scalar-exponential guards. Infinite-mode thermal,
  diamond and physical record/control arguments remain analytic.
- [Cat reservoir parity](architecture/verify_cat_reservoir_parity.py) checks
  finite complete maps and formal CCR/no-jump coefficients. Its normal
  trace-class symmetry proof and finite-time remainder/access obligations
  remain analytic; there is no finite-error frontier dominance claim.
- [High-order bath transfer](architecture/verify_high_order_bath.py) checks
  proper marginals and full logical Choi examples; the support theorem,
  spectroscopy and sampling costs are analytic/source-qualified.
- [Native matter controls](architecture/native_matter_guards.py) checks
  holonomic, ideal-adiabatic and known-symmetry BDI identities. Physical
  access, decay and pulse error remain device assumptions.
- [Rydberg memory](architecture/rydberg_memory_schur.py) checks complete
  record/reference coefficients and the shared-probe counterexample.
  It does not fit the continuum device or certify its two-use instrument.

The [memory-algebra replay](architecture/memory_algebra.py) checks finite
sector cross/flag maps and measure-and-prepare moments; its
Schmidt-number theorem is analytic. The
[subgroup replay](architecture/verify_subgroup_moment.py) enumerates all
Lagrangians through n=4; the all-n rank/moment/confidence proof remains
analytic and exact-prior conditional. The
[Pauli-statistic replay](architecture/verify_pauli_statistic_memory.py)
checks full Bell/PCS/product-probe identities and noise corrections,
including local/correlated-reference counterexamples. The
[local-overlap replay](architecture/verify_local_overlap.py) checks
complete finite Pauli/axis/readout distributions, correlated supports,
calibration bias and scrambled-generator signal examples. The
[local-Lindblad replay](architecture/verify_lindblad_statistic.py)
checks exact log-rate inversion, clipping/coupling, full-support
sampling, SPAM projection and a Clifford-orbit ambiguity guard. The
[spectral replay](architecture/verify_pauli_spectral.py) checks
deterministic reconstruction-error and character/norm identities;
it does not implement external population recovery. The
[cross-pair replay](architecture/verify_pauli_cross_pair.py) checks
finite coset moments, affine character sums and covariance identities.
All-n concentration, conditioning, complexity and physical access
claims remain analytic, with no ordinary optimality claim. The
[cat physical-route replay](architecture/verify_cat_physical_interface.py)
retains dummy/buffer/field registers and helper phases. The
[Rydberg exchange replay](architecture/rydberg_exchange_eraser.py)
checks ordinary eraser/filter/feedback and population-only countermodels.
The mechanical-clock module additionally checks full fixed-input
coefficients and exact endpoint garbling, with separately marked
numerical scalar inequalities. None is a fitted hardware certificate,
an unrestricted ordinary optimum or a native rate advantage.

The architecture jobs support the [ordinary baselines](../architecture-baselines.md),
[communication bounds](../communication.md) and
[shared-bath screen](../backaction.md), not a positive application claim.
Their examples do not prove the
all-input simulation by sampling, implement Threshold Search, or establish
a useful native-device cost advantage. The general proofs and interface
conditions remain in that canonical note. The
[application assessment](../architecture.md) states the remaining gaps
and concrete next tests.

The communication and native-check replays share Gaussian-rational matrix
helpers with `verify_fault_simulation.py`; all those inputs are copied and
hashed together. Full matrix identities cover the tested reference-complete
channels. Finite examples do not establish the all-history entropy ledger,
Schmidt-number theorem, a general loss convention or a native noise budget.
The dispatch-baseline and lookup jobs also import the dispatch/helper
modules; their entire dependency chain is staged and hashed together.

The [dispatch proof](../dispatch.md) distinguishes a hard worst-case exact
query count from fidelity, expected cost, parallel latency and reuse.
Its replays establish the stated finite achievable channel identities,
not an evaluated positive-cost ordinary converse or a physical processor.
The fixed-dimension qualitative mean-cost separation, zero-query minimax
ensemble argument and Gaussian accepted-output frontier remain analytic.
The event-head construction fixes a coherent-use interface mathematically;
no native implementation or measured cost is certified.

The backaction job uses the same staged Gaussian-rational helpers. It checks
full flagged Choi matrices rather than control probabilities alone. Its
finite counterexamples do not fit a device bath, certify every form of
nonclassical noise, or prove a sampling advantage. The general native-echo
and known-intervention simulation proofs remain in NR-R14.

The separate NR-R19 mean-query certificate has no optimizer, array-package
or pickle dependency. It rebuilds the stated invariant model data from
checkable diagrams, vectors and causal-row addresses. Numerical discovery
outputs are not proof inputs. Its bound concerns unconditional Bell
fidelity and mean query cost averaged over the same declared fresh prior
and Bell input. It includes arbitrary terminating longer-round ordinary
strategies under that budget, but not free oracle-dependent training advice
or amortized reuse of a learned reflection. The native reflection,
calibration, hopping-spectrum and reciprocal-port screens are analytic
interface comparisons, not measurements of a coupler or its routing cost.

The [metrology benchmark](../metrology.md) credits the existing finite-query
separation and gives a direct weak-duality proof for the saved witness.
The metrology job uses no installed optimizer or floating-point feasibility
decision. Its JSON provenance is attribution, not a trusted assertion of
positivity. The three-query construction is an ordinary achievable lower
bound; the two-query certificate is not an expected-cost or information-rate
converse. The continuum two-photon common-basis, unequal-rate kernel,
finite-pulse target-amplitude, photon-preserving herald, known-dressing
reuse, and bath-record/tail arguments in NR-R11 are analytic. They are
not certified by a finite frequency-grid replay or by the existing small
elastic-node examples. No native pulse-tail or phonon-overlap estimate is
recorded as proved by these checks.

The finite-emitter NR-R11 guard uses an analytic radiative-Gram and
vacuum-ground argument, followed by Gaussian-code truncation and route-tail
bounds. The communication replay checks exact finite number-operator and
Gram-enclosure identities, not the physical validity of a Markov bath or
the proposed uncertainty box. It also checks elastic retained-spin parity,
same-rail time-bin spin echoes and conditional resonant-bypass instruments;
actual QND readout, spectral matching, optical ports, reset
and herald costs remain application assumptions.

The [Raman local-ancilla checks](../communication.md#nr-r11-raman-local-ancillas)
reconstruct the ordinary six-qubit circuit and complete photon readout,
verify its local Schmidt-basis expansions and explicit filter effects,
and charge photon loss and filter failure. The intermediate-transfer
witness rebuilds exact source states, photonic unitaries and surviving
matter branches; rational Hermitian LDL bounds certify an achievable Bell
yield. The cited pure-state LOCC conversion theorem remains an analytic
input, rather than a search result or a circuit-cost certificate.
These run inside the existing communication job through
[raman_baselines.py](architecture/raman_baselines.py), including the
[rational verifier](architecture/verify_raman_bell_certificate.py) and its
[witness data](architecture/raman_bell_certificate.json).
Coefficient-independent local projections and the ordered field-operator
extension have exact cancellation checks. Their scalar minus-only switch
comparison is not extended to arbitrary noncommuting field coefficients.
The [passive-filter replay](../communication.md#nr-r11-raman-passive-filter)
uses exact Gaussian rationals extended by $\sqrt2$ to check its optical
contraction, orthogonal heralds, local-filter effect, normalization and
canceled/retained terms. The stronger four-level-helper member is checked
over $\mathbb Q(\sqrt2,\sqrt3)$, including its full photon contraction,
four readouts and Bell outputs. Its family optimization is analytic.
Vacuum rejection ports, extra modes and local filter apparatus remain
charged; these achievable constructions are not a sharp bound for adaptive
or larger-mode ordinary processors.

The four-level flying-helper replay is
[raman_multimode_helper.py](architecture/raman_multimode_helper.py).
The existing communication checker also checks known-gate helper programs,
their full input/reference coefficients, source/key dephasing and coherent
early identity-retry flags. The general program tests all target coefficient
directions; it requires actual synthesis of the known target on the helper.
These are ideal finite identities, with enlarged ports, complete readout,
loss completion and physical timing still charged.
The communication job also includes
[phase-covariant instruments](architecture/verify_raman_phase_covariance.py),
[reciprocal-port guards](architecture/verify_raman_reciprocal_ports.py) and
[route/double-herald phase checks](architecture/verify_raman_route_and_echo_phases.py).
They check complete finite output vectors, normalized source/readout
branches and phase-frame identities. General retarded-kernel, joint
phase-spectrum, causal-pilot and accepted-record laws remain analytic or
measured physical inputs. No unknown Raman-frame immunity, compilation of
cycling emission from a Raman SWAP, or measured source-limited advantage
is certified.

The [native-port replay](architecture/raman_port_routes.py) checks exact
ring couplers, complete exit/tail weights, selected node-order words and
formal temporal-code routing entries. Full code/slot stationarity,
component phases/loss, pulse guards, resets and physical port availability
remain hypotheses; no route-family optimum or hardware rate is certified.

The [balanced-cavity checks](../communication.md#nr-r11-raman-cavity-frontier)
are complemented by the [direct temporal replay](architecture/raman_direct_temporal.py),
which checks the passive source completion, all detector clocks, polynomial
cancellation and a finite-response false herald. The
[tail replay](architecture/raman_temporal_tail.py) verifies exact coefficient
norms and accepted-state geometry; uniform node/kernel error certificates,
continuum pulse tails and actual physical clock costs remain analytic
premises. The [timed-control replay](architecture/raman_timed_controls.py)
checks full known-frame spin/photon compiler identities, pulse chronology,
loss/frame counterexamples and the calibrated late-photon-flip instrument.
Its comparison is with the specified ring, not every possible router.

The balanced-cavity checks
verify exact polynomial frontier identities and rational nominal model
substitutions. The continuum inequality, narrow-pulse design limit,
ordinary retuning permissions, complete source/route/phase/reset ledger
and renewal-time comparison are analytic or physical hypotheses. No
unrestricted ordinary optimum, adaptive local-memory upper bound, measured
Bell-pair yield or hardware clock advantage is certified.

The fault-simulation job also calls the
[Gaussian readout guards](architecture/gaussian_readout_guards.py),
[five-mode SU(1,1) replay](architecture/verify_su11_ports.py) and
[conditional readout replay](architecture/verify_conditional_readout.py).
These check complete finite scattering/noise matrices, independent baths,
Weyl phases, all-record likelihood identities and conditional variance
algebra. General passive-network inequalities, full-Fock thermal traces,
Gaussian integrals, information monotonicity and physical measured-source
comparisons remain analytic. A covariance fit is not a full conditional
instrument or a hardware advantage.

The known-control NR-R15 replay checks the exact compiler and contrasting
coherent signal/noise extensions, including their full states and QFI.
Their continuous-time interpretation and access conditions remain analytic.
It is neither an all-protocol converse for the noisy extension nor an audit
of an unexamined published platform supplement. The NR-R19 Andreev checks
likewise support the specified signature, symmetry, observable and bandwidth
identities; they are not a general superconducting-switch impossibility.
The backaction job's
[native-converter guards](architecture/native_converter_guards.py) check
complete Gaussian-rational scattering inversions, unequal-linewidth
normalization/matching, mismatch probabilities and finite Bragg-transfer
rank/phase identities. Universal matching/rank arguments and the cited
device premises remain analytic. The model excludes unaccounted internal
loss, gain, detuning, bandwidth and drift; the replay is not a quantum
device characterization or an ordinary-recovery optimum.

The measurement job also calls the
[material-pointer clock replay](architecture/material_pointer_clock.py).
Its finite array isometries, independent records, fresh-clock
counterexample, pointer echo and timing-kernel arithmetic guard the
displayed formulas. The complete interaction-picture compiler, norm
transfer and device-access comparison remain analytic. Neither a binary
QND detector nor a multimode cavity alone certifies the full native
unknown-basis pair.

The [alignment benchmark](../alignment.md) proves its all-ordinary strict
two-call local limit analytically using the replayed causal witnesses and
a compactness argument. The same certificate is not a mean-cost converse.
The calibrated-reuse construction has exact code/channel replays, while
its concentration, uniform derivative and rare-launch information bounds
are analytic. It keeps all calibration calls and distinguishes a growing
positive-angle family from every fixed experiment at the exact null. The
[braided-magic result](../braided-magic.md) checks full flagged state
identities, rather than equating selected fidelities alone. Those finite
checks do not certify a coherent anyon trajectory or its physical phase.
The [displacement-calibration constructions](../geometric-calibration.md),
including the [two-input Gaussian-bus recovery comparison](../geometric-calibration.md#nr-r16-two-input-bus),
and [rewinding stopping/loss analysis](../obstructions.md#nr-r05) have
explicit analytic proofs and primary-source assumptions. No finite test
is substituted for the continuum Weyl identities, all-decoder recovery
bound, global-risk proof or infinite-mean stopping argument. All these
canonical notes are included in the runner's input hashes.
