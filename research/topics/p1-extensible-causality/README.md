# P1 — Extensible causality without causal separability

[Research index](../../README.md) · [Current status](../../status.json)

One source owns the mathematical argument: [PROOF.tex](source/PROOF.tex). Update that file when a statement, proof, or scope changes; its compiled PDF is an export.

| Locate | Canonical location |
| --- | --- |
| P1-R01: explicit process and nonseparability | `PROOF.tex`, sections “Definitions and precise statement”, “The rational process and its spectrum”, and “A causal nonseparability witness” |
| P1-R02: arbitrary shared-state extensions | `PROOF.tex`, response maps through the rectangle-cover/max-flow proof |
| P1-R03: parameter family and exact noise robustness | `PROOF.tex`, “Exact white-noise robustness” and “Parameter family and its exact threshold” |
| P1-R04: operational and verification limits | `PROOF.tex`, “Scope and reproducibility” |
| Exact matrices and author implementation | [verification/author/](source/verification/author/) |
| Independent implementation and finite evidence | [verification/independent/](source/verification/independent/) |
| Replay instructions | [verification/REPLAY.md](source/verification/REPLAY.md) |

The proof is analytical, accompanied by exact finite checks. There is no P1 Lean proof. The selected quantum-switch paper is a separate result and does not replace this source.
