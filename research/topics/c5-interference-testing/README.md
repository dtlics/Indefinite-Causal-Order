# C5 — Constant-gap channel-interference testing

[Research map](../../README.md) · [Status registry](../../status.json) · [Formal statements](../../../proofs/lean/THEOREMS.txt)

## Canonical results

| ID | Result or proof component | Source of truth |
| --- | --- | --- |
| C5-R01 | Ordinary-query interference-testing lower bound, including the measurement-only case | [Theorem map](../../../proofs/lean/THEOREMS.txt), “C5 ordinary-query testing lower bound”; [paper](../../../paper/main.tex), `thm:testing`, `sec:robust` |
| C5-R02 | Fixed-hidden-basis versus depolarizing comparison | [Theorem map](../../../proofs/lean/THEOREMS.txt), “C5 adaptive fixed-basis indistinguishability”; [Lean endpoint](../../../proofs/lean/ICO/OrdinaryHaarStates.lean) |
| C5-R03 | Signed Haar-recording comparison and physical dephasing adapter | [Theorem map](../../../proofs/lean/THEOREMS.txt), “Haar recording comparison used by C5”; [physical adapter](../../../proofs/lean/ICO/MHProtocolHaarRecording.lean) |
| C5-R04 | Constant-use switched-interference estimator, credited to prior work | [Theorem map](../../../proofs/lean/THEOREMS.txt), “Dimension-independent switched testing upper bound”; [experiment](../../../proofs/lean/ICO/SwitchExperiment.lean) |

C5-R02 and C5-R03 preserve a distinct proof mechanism for C5-R01. The current paper gives the robust test as a consequence of C6; that does not make the single-hidden-basis comparison identical to C6's correlated shared-unitary comparison.

## Access and quantitative boundaries

The hidden measurement outcome and environment are inaccessible. The analytical implementation is U-dagger/copy/U with the same U fixed throughout; it does not grant the learner U or U-dagger queries. Mixed inputs, finite entangled memory, adaptive classical box choices and early stopping with a worst-case total budget are included.

Each measurement call becomes two signed-unitary calls in the recording analysis. The physical comparison's range therefore needs the corresponding doubled-query condition; the full-range statement uses a separate trivial-distance branch. Measurement-only low-promise instances require `d>=4`: at `d=2`, rank-one measurements have interference at least one half.

Independent Haar bases are used inside C5's low-distribution argument. They are not the exact MUB promise or the correlated `(Delta_U, Delta_(UH))` distribution of C6.

<a id="c5-r05"></a>

## C5-R05 — Both dephasing and fresh-coordinate support are necessary

The following counterexamples show why the fresh-output identity cannot be generalized by dropping either hypothesis. Set `d=2`, omit user memory, and let A denote the modified forward record insertion. The records below have `R=empty`.

1. **Remove middle private dephasing.** Use the equal superposition of `|x=0,L={(1,1)}>` and `|x=1,L={(0,0)}>`. Both branches satisfy fresh-x support. Insertion produces the same final record with coherent outputs 0 and 1. The visible state is `|+><+|`, whereas the diagonal-block formula predicts `I/2`.
2. **Remove fresh-x support.** Use the equal superposition of `|x=0,L={(0,0)}>` and `|x=0,L={(0,1)}>`. Dephasing x changes nothing. Insertion again yields `|+><+|` instead of `I/2`.

Each discrepancy has half trace distance exactly `1/2`. These are counterexamples to the overextended identity, not to C5-R02. The canonical positive support/erasure proof remains in the selected Lean closure.

## Subnormalization and conditioning rules

Recording contractions can lose mass. Their states must stay subnormalized; renormalizing a successful branch changes the experiment. Complete a contraction K by `F=sqrt(I-K†K)` to identify a positive lost memory marginal after tracing the acted-on systems. Its contribution to half trace distance is half its lost mass; the losses telescope.

For the measurement-only reduction, first replace the two independent hidden bases one at a time while fixing the other basis. Only after those hybrids may the low prior be conditioned into the promise, charging its discarded probability. Applying independence after this conditioning would be invalid. Explicit opposing zero-query instances cover the low-dimensional range left outside a large-dimension Markov argument.

## Next work and updates

The ordinary-query exponent is not claimed optimal. Improvements to the recording comparison and extensions to different, explicitly specified access models are distinct research questions. Update the existing proof owners and this model guidance in place; retain no parallel baseline manuscript or repeated status report.
