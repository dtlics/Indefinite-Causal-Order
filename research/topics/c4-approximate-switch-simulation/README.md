# C4 — Approximate full-switch simulation

[Research map](../../README.md) · [Status registry](../../status.json) · [Formal statements](../../../proofs/lean/THEOREMS.txt)

## Canonical results

| ID | Result | Source of truth |
| --- | --- | --- |
| C4-R01 | Full-output approximation tradeoff and dimension-dependent lower bounds | [Theorem map](../../../proofs/lean/THEOREMS.txt), “Approximate universal simulation (C4)”; [paper](../../../paper/main.tex), `thm:simulation-summary`, `sec:approximation` |
| C4-R02 | Finite approximation via deterministic port-based teleportation | [Paper](../../../paper/main.tex), `sec:simulation`, paragraph “Finite approximation and open questions” |
| C4-R03 | Stable endpoint polarization with a sharp coefficient-extraction norm | [Supplementary proof](stable-endpoint-polarization.md) |

C4-R03 is a separate analytic lemma; it is not a selected Lean endpoint or a premise of C4-R01. The finite-approximation construction is a derived upper bound and does not promise efficient known processing.

## Model and witness boundaries

The error is half diamond distance on the full control-target switch. The hard inputs are fixed equal-weight mixtures of Haar unitaries, reused throughout the run with inaccessible labels. Fresh without-replacement labels are a comparison process used in the proof, not a claimed memoryless input channel.

The distinguishing effect may depend on the hidden realization because it witnesses a worst-case norm. That does not make it an implementable ordinary learner, and it does not by itself prove C5 testing hardness. Fixing the other oracle matrices and independent label permutations preserves the selected pair's Haar law; conditioning on an observed transcript generally does not.

<a id="c4-r04"></a>

## C4-R04 — Final-outcome mass cannot replace parent mass

A U-first circuit can prepare a Choi program for U, apply V to the actual input, and use gate teleportation. The identity Bell outcome implements the subchannel `d^(-2) Ad(UV)`. Its reverse-fidelity score and outcome mass are both `d^(-2)`. For `d>=3`, the reverse-composition factor `b_d=(1/d+d/(d^2-1))^2` is less than one, so a bound by `p_out b_d` is false.

The valid statement uses the completed parent comb: `0<=C_out<=C_parent` implies a score bound by `p_parent b_d`. This counterexample concerns a stronger, invalid normalization rule; it does not refute C4-R01. The current positive formulation is [paper](../../../paper/main.tex), `lem:reverse`.

<a id="c4-r05"></a>

## C4-R05 — Gram concentration alone cannot improve the exponent

In the present proof, aggregate off-diagonal coherence already costs `r^2 sqrt(b_d)=Theta(r^2/d)`, independently of the Gram spectral estimate. Keeping that cost small restricts `r=O(sqrt(d))`; the separate collision term scales as `q^2/r`. Improving Gram concentration alone therefore leaves the quarter-power bottleneck.

This is a limitation of this proof route, not a lower bound on every possible proof technique. A stronger aggregate-coherence argument or another method is required to improve the exponent. Matching query exponents remain open.

## Updating this topic

Maintain C4-R01 and C4-R02 in their stated owners. Update the supplementary lemma in place when its argument changes. Keep genuinely distinct counterexamples and method limitations here rather than making another proof-summary checkpoint.
