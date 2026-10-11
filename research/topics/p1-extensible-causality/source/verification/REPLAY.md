# Checking the P1 construction

The complete argument is owned by [PROOF.tex](../PROOF.tex). Its analytical proof supplies the arbitrary-ancilla quantifier; finite programs check the explicit matrices, conventions, and examples.

Run checks in a temporary copy so generated JSON does not overwrite retained evidence:

```sh
python author/generate_exact_ec_certificate.py
python author/check_ec_flag_bridge.py
python independent/independent_audit.py
```

The exact matrix generator needs only the standard library. The remaining programs use [requirements.txt](requirements.txt). The independent implementation imports no author functions. Its retained result includes 262,144 refined-outcome rectangles and 64 causal allocations; the author result includes 3,200 rectangles. These are finite implementation checks, not a proof assistant or an external peer review.

The editable proof can be compiled with `pdflatex -output-directory=_build PROOF.tex` from its directory after creating `_build/`. Build products are not versioned. `python verify_manifest.py` checks the maintained source manifest; it does not prove the mathematical theorem.
