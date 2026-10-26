# C6 — SAME/MUB hidden dephasing and channel-access OTOCs

[Research map](../../README.md) · [Status registry](../../status.json) · [Formal statements](../../../proofs/lean/THEOREMS.txt)

## Canonical results

| ID | Result or proof component | Source of truth |
| --- | --- | --- |
| C6-R01 | SAME/MUB ordinary-query lower bound | [Theorem map](../../../proofs/lean/THEOREMS.txt), “SAME versus MUB”; [paper](../../../paper/main.tex), `thm:c6` |
| C6-R02 | Actual shared-Haar comparison and recording-to-cache bridge | [Theorem map](../../../proofs/lean/THEOREMS.txt), same section; [physical endpoint](../../../proofs/lean/ICO/C6SharedPairBound.lean), [raw-to-weighted equality](../../../proofs/lean/ICO/C6RawWeightedEndpoint.lean) |
| C6-R03 | Four-use switched promise test, specializing the known interference experiment | [Theorem map](../../../proofs/lean/THEOREMS.txt), “Four-use quantum-switch upper bound” |
| C6-R04 | Clock-phase OTOC identities, channel commutation, estimation bounds | [Theorem map](../../../proofs/lean/THEOREMS.txt), “Phase-averaged OTOC and channel commutation”; [paper](../../../paper/main.tex), `sec:connections`, `cor:otoc` |
| C6-R05 | Conditional finite keyed-family advantage transfer | [Theorem map](../../../proofs/lean/THEOREMS.txt), “Conditional keyed-family transfer”; [paper](../../../paper/main.tex), `eq:pru` |
| C6-R08 | Exact and robust process certification, with general scalar boundaries | [Full operational proofs](applications.md#c6-r08) |

The recorded formal statements, constants, range conditions and qualified theorem names have one owner in the theorem map. The analytic C6-R08 corollaries are owned by [their application proof](applications.md#c6-r08). The human recording/cache proof is [paper](../../../paper/main.tex), `sec:c6-recording`. C6-R02 is a proof component of C6-R01, not a second independent lower-bound claim.

## Access and scope boundaries

Both boxes use one fixed Haar U throughout the experiment. The low pair is `(Delta_U, Delta_(UH))` with flat H, not two independent random bases. The Bool box-choice tag is memory; it does not double the Haar dimension. Choices are classical and use one total budget.

Equality of dephasing channel maps is the SAME promise. Different phase or basis-label descriptions can represent the same channel. Both SAME and MUB channel pairs commute as superoperators; the switch observes Kraus-product interference.

The OTOC result is for the explicit finite private clock-phase average accessible through the channels. It is not a statement about every local or time-dependent scrambling probe, and it grants no coherent hidden-unitary or inverse access. Four promise-test repetitions do not give arbitrary-precision estimation for general inputs.

C6-R05 retains two keyed-versus-Haar security inequalities. It neither constructs efficient pseudorandom unitaries nor proves asymptotic security, and it does not transfer an unbounded information-theoretic exponential lower bound to an arbitrary finite keyed ensemble.

<a id="c6-r06"></a>

## C6-R06 — Absolute coefficient summation is an obstructed route

For two-chain lengths a and b, the supplied permutation-expansion analysis records the following lower bound on the leading coefficient-weighted absolute-value mass:

```text
((3^a - 1)(3^b - 1))/2 - (2^a - 1)(2^b - 1).
```

This grows exponentially. Summing the absolute values of all coefficients cannot, by itself, produce a polynomial-in-query estimate. Polynomial bounds for selected diagonal families do not control the complete coherent expansion.

This is a documented methodological obstruction, not a selected formal endpoint or a complete general coefficient-classification theorem. No optimal-exponent claim follows from it.

<a id="c6-r07"></a>

## C6-R07 — Creation-only decoupling and early erasure are insufficient

Creation-only bounds miss a potentially order-one left-record retrieval branch. Monotonicity of right-particle number does not make a coherent record classical: a later polar normalization can still access its images.

A valid reduction needs the following mathematical interfaces, supplied by C6-R02:

- Full multiset bosonic creators, restricted adjoints and correct input/output grades; an injective-record shortcut is insufficient.
- Conjugate right labels and one basis adapted to the complete outcome history. Independently selected prefix bases do not identify one permanent final occupation observable.
- Permanent birth/retrieval flags, followed by removal of the image-dependent polar factor, before tracing inert image registers. Temporary branch orthogonality alone is insufficient.
- Exact all-matrix image-erasure identities with entangled learner memory, and retained retrieval as well as birth outcomes until history-dependent weights are identified.
- A globally contractive raw replacement and an all-history CP/TP cache extension. Uniform prefixes can create histories absent from the weighted process; supported-input-only claims cannot justify that hybrid.
- Invariance for each learner-classical branch and cache sector after summing private outcomes. Conditioning on an individual private dephaser outcome can break the required invariance.

These are limitations of tempting proof shortcuts. They are not unresolved premises of the selected physical endpoint.

## Supplementary checks and open questions

The [algorithm-certification corollaries](applications.md#c6-r08) use C6-R01 for reference-complete forgetting and sound, complete deletion certificates. Their [robust extension](applications.md#c6-r08-robust) permits fixed CPTP perturbations, while the [arbitrary-basis analysis](applications.md#c6-r08-arbitrary-bases) gives sharp scalar limitations and near-minimum certificates. These are analytic application theorems, not additional formal endpoints or independent lower-bound methods.

The [memory-capacity qualification corollary](../nr-noisy-recovery/memory-qualification.md#nr-r20)
uses C6-R01 to distinguish positive-rate storage from a zero-capacity
replacement mixture. Its expected-cost reduction and physical access limits
are owned there; it introduces no new C6 recording argument or formal endpoint.

The [architecture assessment](../nr-noisy-recovery/architecture.md) tests
which physical interfaces could support an application. The
[ordinary measurement baselines](../nr-noisy-recovery/architecture-baselines.md#nr-r08)
show why accessible stable outcome records and degenerate syndrome
sectors require different comparisons from the rank-one, unmonitored
hidden dephasers here. Commuting averaged channels or a compatible
syndrome algebra alone do not certify logical correctness.

The [checks](checks/) contain exact symbolic small-sector checks and a constants checker. The SymPy checks cover selected low degrees and image/cache identities; they do not certify every degree or the adaptive physical endpoint. Their recorded outputs concern those exact scripts. Run checks in an ignored build directory when they write output.

The optimal ordinary-query exponent remains open. Sharpening the recording comparison or directly controlling the physical process may improve it. Descriptions of passive, parallel and weaker adaptive bounds without full model definitions or proofs are not treated here as separately established results.

Update the existing theorem/proof owners and these method limitations in place. New evidence must identify its inputs and scope; it should not create another copy of the current theorem wording.
