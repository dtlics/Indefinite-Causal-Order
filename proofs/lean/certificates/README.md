# Exact finite certificates

This directory is the single canonical copy of the finite qubit certificate
data. The JSON files and the two arithmetic replay scripts retain the Lean
release's bytes. `readable/` contains exact CSV exports from the standalone
certificate supplement; no rounding is used.

With Python 3.9 or newer and the standard library, run from any directory:

```sh
python proofs/lean/certificates/verify_all.py
```

From this directory, use `python verify_all.py`. Assertions must be enabled;
do not use `-O` or `-OO`. The wrapper copies inputs into
`../_build/exact/`, runs both exact replays there, and leaves the recorded
`support-replay-result.json` and `verify_short_certificate.json` untouched.

The support replay reconstructs the 128-by-25 tensor matrix, verifies all 103
physical annihilator rows, checks `R E = 0` and `L E = I_25`, and verifies the
128-by-128 stacked matrix's inverse modulo 5 under `i -> 2`. The separation
replay reconstructs the causal partial-trace and trace-and-replace gauge rows,
and checks the 30-term, 47-term, and 73-term rational identities, slot swap,
switch coefficient, and vanishing noise sums.

These checks establish exact finite linear-algebra identities. The full
ordinary-query reduction, positivity, support argument, comb constraints, and
dimension reduction belong to the Lean proof and manuscript. The Python output
is not a premise of a Lean theorem.

The historical generation fields mentioning modulus 257 and `i=16` are unused;
the delivered rank witness uses modulus 5 and `i=2`. The unchanged short replay
docstring names an old `certify_switch_support.py`; its current companion is
`verify_support_exact.py`.
