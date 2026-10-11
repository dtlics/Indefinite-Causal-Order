# Reproducing the exact P2 checks

Run from this directory with Python 3.12 and the libraries pinned in requirements.txt. Exact proof calculations use Python integers/Fraction or exact symbolic arithmetic; NumPy object arrays store integers. Floating conversions in certificate summaries are display-only. No SDP solver, internet connection, optimization checkpoint or external workspace is needed for verification.

## Quick commands

    python verify_p2.py
    python verify_p2.py --core
    python verify_p2.py --all

The first command needs only Python's standard library and checks package hashes, exact metadata, outward rounding and strict support separation. It does not itself reconstruct large certificates. The other modes copy the package to a temporary directory and execute arithmetic verifiers there, avoiding changes to delivered records. --core checks the lower, global upper with two implementations, and fixed-five-angle-only upper. --all additionally runs eleven exact structural checks.

Tested: Python 3.12.14, NumPy 2.3.5, SymPy 1.14.0, SciPy 1.17.0. Core execution requires NumPy; the independent upper checker alone is standard-library only. SymPy is needed for symbolic completeness, spectral quotient and rook checks. SciPy is used only for exact integer sparse arrays in the clique-gap checker. A CPU run completed each core verifier in about 7–16 seconds in the recorded parallel run; timings are machine-dependent.

## Direct core commands

From support/:

    python physical-process/certify_reduced_process.py --verify objective/endpoint_lower1653.json objective/endpoint_lower1653_data.json.gz

Expected: VERIFIED_EXACT_REDUCED_PROCESS and exact equality to CERTIFIED_BOUNDS.json's lower rational. Dependencies: NumPy, reduced_process.py, charged_grid_admm.py, grid_process_admm.py. Only the certificate's integer seed/factors and tangent pairs enter the replay. General physical validity also uses the included CP-lift theorem.

    python word-kernels/certify_rational_kernel.py --verify word-kernels/rational_L8_r004_certificate183_factors.json.gz

Expected: VERIFIED_EXACT_RATIONAL_KERNEL, 17 words, four 289-by-289 Grams, 38,148 proportional NS checks, and the exact upper rational. Dependency: NumPy; no other source module.

    python independent-upper-check/independent_rational_check.py word-kernels/rational_L8_r004_certificate183.json word-kernels/rational_L8_r004_certificate183_factors.json.gz --out independent_replay.json

Expected: PASS_INDEPENDENT_EXACT_RATIONAL_KERNEL_AUDIT; 38,148 NS and 1,089 TP coefficient checks, equal projection orders, exact bound equality. Standard library only; imports no author verifier. It need not dump expanded Grams.

    python objective/certify_fixed_angle_dual.py --verify objective/Radau5_fixed_upper165_factors.json.gz

Expected: VERIFIED_EXACT_FIXED_ANGLE_UPPER with K=5 and its exact scoped upper rational. Dependencies: NumPy and the lower verifier modules. This is NOT a global upper bound.

## Structural checks and mathematical roles

REPLAY_COMMANDS.json owns the current exact command arguments. Each check retains its necessary result beside the implementation; repeated execution summaries are omitted.

- check_exact_lift.py: full-charge affine projector and trace identities for K=1,2,3; NumPy and the copied charged-model/projector modules
- check_exact_output_twirl.py: integer dephasing/projector/lift commutation and winning-map identities; same modules
- check_jacobi_coset.py: exact free-word recurrence, overlap, orthogonality and annihilator checks; NumPy and coset_kernel.py plus the small Radau1_lower160.json angle reference
- independent_exact_checks.py, audit_centered_path.py, audit_twirl_transfer.py: exact group/word and symbolic checks accompanying the complete encoder proofs; SymPy
- certify_clique_gap.py: exact physical lower versus scoped clique upper, using Bareiss positivity and integer sparse projectors; NumPy, SciPy, clique_gap_data.json.gz
- check_rook_exact.py: rational non-clique witness and scalar matching identities; SymPy
- check_flat_tester.py: spectral quotient rank witnesses and coherent physical realization example; NumPy, SymPy, exact lower-angle reference and full-charge modules
- check_resume_obstructions.py: positive-lift failure, rank and escaping-mass examples, plus strict slack consequence of the saved independent upper audit; NumPy, spectral quotient module
- check_obstructions.py: rational separating pencils and coherent matrix-unit identities; NumPy

Finite exact tests do not replace proofs of assertions quantified over all levels, representations or supports. Conditional structural proofs retain their explicit hypotheses; the topic README distinguishes verification scope.

The optional check_folner_encoder.py and check_path_encoder.py mix exact combinatorial checks with floating stress tests. They are included for context but excluded from --all, whose listed checks are exact. No numerical solver is called by any documented verification command. Creation/discovery branches still present inside original modules require omitted numerical inputs and are not the package's supported workflow.


SHA256SUMS.txt is the current source/data integrity manifest. Certificate JSON and compressed factor inputs remain byte-preserved. Editing mathematical prose does not recertify a general theorem.
