# RG — Exact native routed-graph universality

[Research map](../../README.md) · [Current status](../../status.json)

The exact dimension-16 quartet is a source-level counterexample to finite bi-univocal weak-loop routed realization with one whole complete monopartite insertion per original qubit. Arbitrary finite fixed auxiliaries and native multiplicities are allowed. The claim does not extend to approximation, enlarged external boundaries, distributed queries, or extra calls.

Read [RG-001: the complete obstruction](source/results/obstruction.md#rg-001), the [precise model](source/FINAL_MODEL_AND_SCOPE.md), and the [proof dependency graph](source/PROOF_DEPENDENCY_MANIFEST.json). The finite certificates supplement uniform private-completeness and graph arguments; this is not a Lean formalization or external peer review.

## Current knowledge

The [shared result index](../../RESULTS.md#rg--exact-native-routed-graph-universality) gives each distinct theorem, lemma, scoped failure, construction and unresolved computation one stable ID and one owning section. Repeated checkpoint reviews have been consolidated into those proofs. A stronger result owns its weaker special cases; separate methods appear as proof subsections, not competing status records.

| Area | Canonical source |
| --- | --- |
| Complete obstruction | [Obstruction](source/results/obstruction.md) |
| Finite-algebra tools | [Foundations](source/results/foundations.md) |
| Exact original-query interfaces | [Native interfaces](source/results/native-interfaces.md) |
| Serial columns, rows and promotion | [Serial interfaces](source/results/serial-interfaces.md) |
| Exchange cuts and layer structure | [Layer structure](source/results/layer-structure.md) |
| Passive core, recurrence and contradiction | [Core obstruction](source/results/core-obstruction.md) |
| Actual graph records and refinements | [Phase records](source/results/phase-records.md) |
| Auxiliary algebras and multiplicities | [Auxiliary interfaces](source/results/auxiliary-interfaces.md) |
| Exact tangent, projector and curvature constraints | [Auxiliary geometry](source/results/auxiliary-geometry.md) |
| Failed shortcuts and scoped construction limits | [Construction boundaries](source/results/construction-boundaries.md) |
| Positive restricted routed families | [Positive routes](source/results/positive-routes.md) |
| Higher-order algebraic structure | [Higher-order results](source/results/higher-order.md) |
| Computed claims awaiting independent audit | [Scoped computations](source/results/scoped-computations.md) |

## Reproduction and maintenance

The executable scripts and exact data stay together under `source/` so their imports and data paths remain reproducible. From that directory run `python verify_proof.py --tier integrity`; `--tier core` and `--tier full` also run the mathematical certificate scripts in a temporary copy. The latter require the scientific packages in `source/REQUIREMENTS.txt`.

Update a result in its owning section. Add a new result only for a distinct statement or method with a different scope. Do not add another dated checkpoint, candidate manuscript, or review copy. Update the relevant dependency hashes and `SHA256SUMS.json` after intentional changes. Existing script outputs describe their exact finite inputs and are not automatically a fresh independent proof audit.

See [reproducibility scope](source/REPRODUCIBILITY.md) for the certificate tiers and supporting helper files absent from the supplied materials.
