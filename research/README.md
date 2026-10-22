# Research map

The eight stable topics below organize current knowledge. Each topic links to its canonical results and states the remaining open questions. [RESULTS.md](RESULTS.md) is the result-level index. [status.json](status.json) owns the topic statuses; the table below is generated from it.

<!-- BEGIN GENERATED RESEARCH STATUS -->
| ID | Topic | Recorded state |
| --- | --- | --- |
| RG | [Exact native routed-graph universality](topics/rg-routed-graph/README.md) | reported-complete: Supplied counterexample proof with exact finite certificates; no Lean formalization recorded. |
| P1 | [Extensible causality without causal separability](topics/p1-extensible-causality/README.md) | reported-complete: Supplied analytic separation proof and exact finite checks; no Lean formalization recorded. |
| P2 | [Unrestricted bipartite GYNI optimum](topics/p2-gyni/README.md) | open: Certified lower and upper bounds remain distinct; exact value and finite attainment unresolved. |
| P3 | [Exact universal quantum-switch simulation](topics/p3-exact-switch-simulation/README.md) | recorded-formal-endpoint: Final supplied Lean package records the physical finite-budget impossibility endpoint. |
| C4 | [Approximate full-switch simulation](topics/c4-approximate-switch-simulation/README.md) | recorded-formal-endpoints: Final supplied Lean package records the full-output error tradeoff and lower bounds. |
| C5 | [Constant-gap channel-interference testing](topics/c5-interference-testing/README.md) | recorded-formal-endpoints: Final supplied Lean package records ordinary-query lower bounds; distinct single-hidden-basis proof retained. |
| C6 | [SAME/MUB hidden dephasing and OTOCs](topics/c6-hidden-dephasing/README.md) | recorded-formal-endpoints: Final supplied Lean package records shared-Haar physical, decision and OTOC endpoints; keyed transfer remains conditional. |
| NR | [Noisy physical recovery with expected-query bounds](topics/nr-noisy-recovery/README.md) | analytic-with-exact-certificates: Physical-output recovery theorem with exact arithmetic replays; fresh-frame average and specified noise/control models. Not Lean-formalized or externally peer reviewed. |
<!-- END GENERATED RESEARCH STATUS -->

## How the parts fit

The selected [paper](../paper/main.tex) presents one connected quantum-switch story. RG, P1, and P2 remain separate research streams. Within the switch work, a one-bit learning problem, approximate full-output simulation, and exact finite-budget simulation have different quantifiers and outputs. A proof of one does not automatically prove the others.

The OTOC consequence depends on the SAME/MUB comparison and an exact identity. The keyed-device transfer retains its computational-security assumptions. The result index links these relationships without counting a change of interpretation as another independent lower-bound method.

NR concerns physical state recovery through related noisy modules and an expected-call budget. Its local-noise theorem, global-replacement theorem, and scoped obstructions have distinct assumptions. The Bell and secret-state tests are operational variants of the same recovery frontier, not independent lower-bound results. Its analytic proofs and exact arithmetic checks do not add endpoints to the selected Lean project or revise the manuscript.

## Maintain current knowledge

- Edit each result at its canonical source. A topic README provides navigation and open questions, not another proof or checkpoint summary.
- Integrate a strengthening into the same result when the earlier assumptions and conclusion are truly covered. Keep different models and scoped negative findings distinct.
- Retain useful failure information as an obstruction, counterexample, or explicit unresolved gap. Do not retain obsolete status reports or repeated audit narratives.
- Update the status registry when a topic's state changes, then run `python scripts/render_research_index.py`. Update result locations in `results.json`, then run `python scripts/render_results.py`.
- Git commits record future revisions. This initial tree has no imported history ledger or checkpoint archive.
