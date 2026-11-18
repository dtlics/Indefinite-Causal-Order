# Result-to-evidence index

This index is a navigation and scope map. The reports own the complete arguments;
the source scripts and current outputs are linked below. **Analytical** means an
argument is supplied in a report, not a new external or Lean proof audit.
**Numerical** means finite floating-point evidence. **Restricted gain** means the
specified decoder or free-resource class improves; it is not an unrestricted
ordinary-query separation.

All channel calculations use square, fixed memoryless CPTP maps and independent
private environments unless the stated example explicitly changes the resource
model. Full-switch simulation concerns arbitrary control-target-reference
inputs; scalar estimation here generally concerns the target input `I/d`.

## A. Constructive ordinary baselines and analytical bounds

| ID | Result and necessary scope | Argument | Executable evidence / current data |
| --- | --- | --- | --- |
| MA-01 | One arm is a mixture of **known HS-orthogonal unitaries**, with unknown weights: full simulation with one query per box. Known measurement/control synthesis is a separate cost. | [Screening §2](screening/report.md#section-2), analytical construction | [ordinary_compilation.py](screening/experiments/ordinary_compilation.py), [30-case output](screening/evidence/ordinary_compilation.json) |
| MA-02 | Two ordinary Choi probes measure the scalar with click probability `2 p_minus / d²`. This is a constant-overhead scalar baseline for qubits, not full simulation. | [Screening §3](screening/report.md#section-3), all-d operator identity | [derived_checks.py](screening/experiments/derived_checks.py), [symbolic checks](screening/evidence/derived_checks.json), [random checks](screening/evidence/sweep_summary.json) |
| MA-03 | A **known** one-site coherent Pauli span has test normalization 2; adding all two-site edge Paulis gives `2 + 6 Δ`. A local generator alone does not imply this exact finite-time Kraus support. | [Screening §4](screening/report.md#section-4); [Code-aware §7](code-aware/report.md#section-7), analytical and combinatorial | [structured_bounds.py](code-aware/experiments/structured_bounds.py), [55 graph counts](code-aware/evidence/structured_bounds.json) |
| MA-04 | Two unknown completed recoveries that return all inputs into the **same known code** and fix it pointwise: full simulation with at most one unknown query and a coarse code-membership measurement. | [Code-aware §2](code-aware/report.md#section-2), theorem and explicit simulator | [retraction_tests.py](code-aware/experiments/retraction_tests.py), [60 full-map checks and partial pumps](code-aware/evidence/retraction_results.json) |
| MA-05 | An extractable quantum program plus a known controllable processor dilation gives full simulation using the program-preparation calls and one other-box query. Includes unknown replacers and known-basis measure/prepare channels. | [Code-aware §9](code-aware/report.md#section-9), analytical construction; environment-seizable concepts credited | [program_and_code.py](code-aware/experiments/program_and_code.py), [42 program checks](code-aware/evidence/program_and_code_results.json) |
| MA-06 | A self-switch is exactly an X-classical flagged instrument on a plus control. Its best final-decoder gain is at most `min(p_plus,p_minus)`; its full distance from the plain serial channel is the largest minus-effect eigenvalue. | [Code-aware §3](code-aware/report.md#section-3), analytical identities and bound | [self_switch_bound.py](code-aware/experiments/self_switch_bound.py), [54 identities and AD-code checks](code-aware/evidence/self_switch_bound_results.json) |
| MA-07 | For independent amplitude damping on the four-qubit AD code, `p_minus = γ³/4 + O(γ⁴)`; the self-switch cannot remove a leading quadratic fixed-code serial-optimum error by final decoding. | [Code-aware §3](code-aware/report.md#section-3), exact effect and expansion | [self_switch_bound_results.json](code-aware/evidence/self_switch_bound_results.json) |
| MA-08 | A stable balanced **one-bit** projective outcome record makes SAME/MUB easy: 21 ordinary calls for error below 1%; the noisy-bit example uses 120. Does not simulate the full switch or arbitrary visibility. | [Code-aware §6](code-aware/report.md#section-6), direct extension of the published recorded ABA experiment | [structured_bounds.py](code-aware/experiments/structured_bounds.py), [partial-record calculations](code-aware/evidence/structured_bounds.json) |
| MA-09 | An independent stochastic fault of rate `p` gives a common no-fault history: any deterministic q-slot ordinary or switched protocol has balanced success at most `1 − (1−p)^q/2`. | [Code-aware §10](code-aware/report.md#section-10), analytical mixture bound | [rare-event constants](code-aware/evidence/structured_bounds.json) |
| MA-10 | The short-time self-signal is the squared Lindblad jump-commutator coefficient at order `t²`; commuting jumps remove that order. A noise-algebra fingerprint, not a scrambling or learning-advantage theorem. | [Screening §7](screening/report.md#section-7); [Code-aware §3](code-aware/report.md#section-3) | [derived_checks.py](screening/experiments/derived_checks.py), [recorded small-time consistency checks](screening/evidence/derived_checks.json) |

## B. Useful-output constructions and strong ordinary comparisons

| ID | Finding and disposition | Argument / model | Executable evidence / current data |
| --- | --- | --- | --- |
| MA-11 | Coherent errors can split into separately correctable plus/minus spaces; the supplied code is perfectly corrected. **Ordinary intermediate recovery and a different noiseless encoding also correct it exactly.** | [Code-aware §4](code-aware/report.md#section-4), analytical construction and counterexamples | [program_and_code.py](code-aware/experiments/program_and_code.py), [40 coherent pairs and 20 DFS comparisons](code-aware/evidence/program_and_code_results.json) |
| MA-12 | A flag improves specified Pauli decoders; five-qubit isotropic improvement first appears at order `p⁴`. Intermediate recovery and MA-01 defeat an unrestricted-query claim. | [Screening §5](screening/report.md#section-5), exhaustive finite histories and exact low-noise polynomials | [qec.py](screening/experiments/qec.py), [43 cases](screening/evidence/qec_results.json), [qec_polynomials.py](screening/experiments/qec_polynomials.py), [exact polynomials](screening/evidence/qec_polynomials.json) |
| MA-13 | Eight fixed-dual-rail decoder optimizations exhibit restricted switch improvements, all beaten by an ordinary unencoded qubit in the tested cases. Collective relaxation is defeated by a noiseless subsystem. | [Code-aware §5](code-aware/report.md#section-5), numerical SDP brackets and analytical ordinary alternatives | [decoder_opt.py](code-aware/experiments/decoder_opt.py), [decoder_screen.py](code-aware/experiments/decoder_screen.py), [SDP results](code-aware/evidence/decoder_optimized_results.json), [collective DFS](code-aware/evidence/collective_dfs.json) |
| MA-14 | In six spin/oscillator cases, ordinary intermediate recovery exceeds the Barnum–Knill upper bound on **every final decoder for the fixed switched encoding/layout**. The inequality is published; inserted fidelities are numerical. | [Code-aware §5](code-aware/report.md#section-5), correctly scoped use of a prior theorem | [summarize.py](code-aware/experiments/summarize.py), [six eliminations](code-aware/evidence/near_optimality_eliminations.json), [57 spin cases](code-aware/evidence/nonpauli_qec_results.json), [12 oscillator cases](code-aware/evidence/bosonic_results.json) |
| MA-15 | Leakage/repump minus outcomes can read the logical population and be entanglement breaking; gauge-only disturbance can leave the logical qubit intact. NCOM is not a logical-error rate. | [Screening §§5–6](screening/report.md#section-5), direct channel examples | [leakage identity](screening/evidence/derived_checks.json), [gauge/recovery output](screening/evidence/qec_results.json), [recovery_policy.py](screening/experiments/recovery_policy.py) |
| MA-16 | Ideal GKP flag likelihood is `(1+c cos(xy))/2`; analog-decoder benefit is tiny at the tested lower-noise points and sensitive to flag error. No finite-energy or all-ordinary claim. | [Screening §6](screening/report.md#section-6), analytic likelihood and numerical quadrature | [gkp_flag.py](screening/experiments/gkp_flag.py), [14 cases](screening/evidence/gkp_flag.json) |
| MA-17 | Stabilizer resets plus a native switch yield a magic state, with reset/control-noise thresholds and a distillation ledger. **Restricted stabilizer-resource separation**; magic activation and distillation are prior work. | [Screening §8](screening/report.md#section-8), derived specialization and cost accounting | [magic_scan.py](screening/experiments/magic_scan.py), [4,332 scanned outputs](screening/evidence/magic_scan.json), [reset_factory.py](screening/experiments/reset_factory.py), [symbolic formula and ledger](screening/evidence/reset_factory.json) |
| MA-18 | Unknown fermionic-mode overlap has an explicit switch signal, but ordinary filled-state two-hole counting can be strictly better. Matrix calculations are for qubit-encoded modes. | [Code-aware §8](code-aware/report.md#section-8), CAR algebra and ordinary probe | [structured_bounds.py](code-aware/experiments/structured_bounds.py), [48 mode pairs](code-aware/evidence/structured_bounds.json) |
| MA-19 | Choi error filtering can collect single rare faults before comparing them; the explicit weak-noise tests beat primitive self-switch sampling. This is not a best-block-switch lower bound. | [Screening §3](screening/report.md#section-3), analytical qubit geometry and explicit tests | [rare_fault_baseline.py](screening/experiments/rare_fault_baseline.py), [costs and error bound](screening/evidence/rare_fault_baseline.json) |
| MA-20 | QEC sensing with a known auxiliary gate has a known-arm ordinary compiler. The reviewed anticommuting-signal proposal supplies additional time-direction/sign access that must be matched. | [Code-aware §11](code-aware/report.md#section-11), source/interface analysis | [Primary source and attribution](SOURCES.md); no new all-protocol impossibility claim |

## C. Breadth of the screen and unresolved target

The broad scan contains 50 base parameterized models / 575 pairings plus 14
extensions / 57 pairings: **64 models and 632 pairings**, not 632 distinct
application mechanisms. The follow-up contains **57 spin-code and 12
finite-level oscillator configurations**, with eight optimized decoder cases.
The [34-entry screening catalog](screening/candidates.md) and
[18-entry follow-up map](code-aware/candidates.md) include overlapping themes,
counterexamples and uncomputed leads.

MA-01 through MA-20 do not close the original application objective by
themselves. Incomplete/different-code nonunital modules and genuinely hidden
correlated backaction require a specified useful output and a matched ordinary
baseline. The absence of a sufficient simulator is not a hardness proof;
full-switch simulation hardness does not transfer automatically to a scalar or
a proposed hardware workload. These limits are part of the preserved results.
