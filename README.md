# Infinite or indefinite: the query cost of simulating the quantum switch

Lean 4 formalization and exact certificates for the paper

> Dantong Li, *Infinite or indefinite: the query cost of simulating the quantum switch* (2026).

The quantum switch applies two black-box operations in a superposition of the
two orders, using each once. The paper asks how many calls to the boxes an
ordinary quantum circuit needs to do the same, where an ordinary circuit calls
the boxes in a definite order and may use classical feed-forward and an
ancillary quantum memory of any size. This repository contains the
machine-checked proofs.

## What is proved

All statements are for general quantum channels. "Ordinary strategy" is the
adaptive circuit model of Definition 4 of the paper; a strategy has budget `q`
if it makes at most `q` calls in total on every run.

| Result of the paper | Lean theorem (explicit form) |
| --- | --- |
| **Theorem 1.** For every dimension `d >= 2` and every finite budget, no ordinary strategy simulates the switch exactly on all pairs of channels. | `ICO.BoundedSwitchObstruction.no_bounded_circuit` (control input fixed to `\|+>`), `ICO.PolarizationOrderedArbitraryControl.no_bounded_full_switch_circuit` (arbitrary control inputs) |
| **Theorem 2.** Simulation to any fixed error below 1/2, in half the diamond norm, needs `Omega(d^(1/4))` calls. | `ICO.C4PhysicalEnsemble.exists_full_switch_error_bound`: error at least `1/2 - 13 r^2/(3d) - q(q-1)/(2r)` on some pair of mixtures of `r` unitaries; `full_switch_fixed_accuracy_constant` (the asymptotic form); `full_switch_one_over_48` (error at most 1/48 and `d >= 64` force `d < 4096 q^4`) |
| **Theorem 3.** Deciding whether a device with dephasing noise of strength `p` in an unknown basis is described by its depolarizing model needs `Omega(d^(1/16)/p)` ordinary calls for `d = 2^n`, and `O(1/p)` calls with the switch. | `ICO.Section54Validation.validation_ordinary_query_lower_bound` (budget greater than `d^(1/16)/(1400 p)`), `ICO.Section54Validation.validation_switch_block_power_upper_bound` (seven uses of the switch, each slot filled by `m >= 3/(2p)` consecutive uses of the device) |

The paper states Theorems 2 and 3 asymptotically; the Lean theorems carry
explicit constants and imply them. [`proofs/lean/THEOREMS.txt`](proofs/lean/THEOREMS.txt)
maps every numbered statement of the paper, by number and LaTeX label, to its
Lean declarations and lists the hypotheses of each. Its second part lists
audited results that are not statements of the paper.

## Verification record

- Lean 4.30.0 with a pinned Mathlib; 1,663 source modules (1,615 in `ICO/`, 48
  vendored from [Lean-QIT](https://github.com/QuAIR/Lean-QIT)), compiled from
  source.
- A kernel audit of 221 selected theorems, including the ones above, reports
  the axioms each proof depends on: `propext`, `Classical.choice` and
  `Quot.sound`, the standard axioms of Lean, and no others. The sources contain
  no `sorry`.
- The record is in [`proofs/lean/audit/`](proofs/lean/audit/README.md). The
  build was run on Windows; a separate Unix build was not run.

## Layout

```
proofs/lean/
  ICO/              the formalization (entry file ICO.lean)
  vendor/Lean-QIT/  the part of Lean-QIT that the proofs import, unchanged
  Audit.lean        prints the type and axioms of each selected theorem
  THEOREMS.txt      paper statement -> Lean declaration
  DEPENDENCIES.txt  pinned versions of Lean, Mathlib and Lean-QIT
  audit/            recorded verification state (hashes, kernel audit log)
  certificates/     exact data for Appendix B of the paper and verify_all.py
  verify.sh, verify.ps1, verify_integrity.py, prepare_verification.py
```

## Reproducing

The finite certificate of Appendix B (integer and rational arithmetic, Python
standard library only, a few seconds):

```sh
python proofs/lean/certificates/verify_all.py
```

Source identity against the recorded verification state (no Lean needed):

```sh
python proofs/lean/verify_integrity.py
```

The full Lean build and kernel audit (install
[elan](https://github.com/leanprover/elan); the build is long):

```sh
cd proofs/lean
lake exe cache get
sh verify.sh          # Windows: powershell -ExecutionPolicy Bypass -File verify.ps1
```

Details are in [`proofs/lean/README.md`](proofs/lean/README.md).

## History of this repository

The default branch contains the release. Earlier commits and other branches
hold working notes and drafts, on this paper and on other topics. They are kept
for the record, are not maintained, and are not part of the release.

## Use of AI

The formalization was developed with AI systems under the author's direction;
see the statement on the use of AI in the paper. Correctness rests on the Lean
kernel check described above.

## Citing

Please cite the paper; see [`CITATION.cff`](CITATION.cff). The formalization
builds on Lean-QIT (C. Zhu et al., arXiv:2607.09632).

## License

The sources of this repository are released under the Apache License 2.0; see
[`LICENSE`](LICENSE) and [`NOTICE`](NOTICE). The vendored Lean-QIT files keep
their own Apache-2.0 license and notices under `proofs/lean/vendor/Lean-QIT/`;
the licenses of Lean and Mathlib are reproduced under `proofs/lean/licenses/`.
