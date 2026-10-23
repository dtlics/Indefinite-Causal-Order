# Indefinite causal order

The current research on quantum-switch advantages, causal structure, and the limits of ordinary quantum queries. The repository contains the paper **An exponential quantum-switch advantage for commuting channels**, its proof code, and the results, limitations, and open problems from eight research directions.

| Read or change… | Canonical location |
| --- | --- |
| Paper and Overleaf export | [paper/](paper/README.md) |
| Research directions and current status | [Research map](research/README.md) |
| A particular result, obstruction, or conditional theorem | [Result index](research/RESULTS.md) |
| Noisy physical recovery and its expected-query comparison | [Recovery topic](research/topics/nr-noisy-recovery/README.md) |
| Architecture applications, strongest ordinary baselines, and next tests | [Application assessment](research/topics/nr-noisy-recovery/architecture.md) |
| Communication cuts, optical loss and control-resource bounds | [Communication results](research/topics/nr-noisy-recovery/communication.md) |
| Coherent dispatch, ordinary recovery and microscopic temporal models | [Dispatch result](research/topics/nr-noisy-recovery/dispatch.md) |
| Selected formal theorem statements and hypotheses | [Theorem map](proofs/lean/THEOREMS.txt) |
| Lean proofs and exact finite certificates | [Proof project](proofs/lean/README.md) |
| Literature context and access-model distinctions | [References](references/README.md) |
| Verification scope | [Validation](docs/VALIDATION.md) |
| Where future edits belong | [Contribution guide](CONTRIBUTING.md) |

## Organization

```text
paper/          The single editable manuscript
research/       Current results, scoped negative findings, and open questions
proofs/lean/    Selected formal proof source, certificates, and verification evidence
references/     Literature context; paper citations remain in the manuscript
docs/           Structure, validation scope, and attribution
scripts/        Consistency checks and generated indexes/exports
```

Each result has one canonical owner. The result index and topic READMEs provide navigation; they do not maintain alternate theorem statements. Stronger results incorporate superseded checkpoints where their assumptions permit it. Distinct restrictions, counterexamples, conditional criteria, and unresolved gaps remain explicit. The same result's manuscript exposition, formal implementation, and certificate are linked as representations of that result.

The recovery topic contains an analytic physical-output theorem, its exact replay dependencies, and scoped obstructions. It is separate from the manuscript's existing simulation and decision results and has not been formalized in Lean.

Its architecture assessment distinguishes the fresh-frame theorem from persistent calibration and real device interfaces. Exact ordinary fault simulation, finite-family reuse learning, and measurement-record baselines rule out several proposed extensions under their stated models. A substantial architecture application remains open.

Checkpoint collections, repeated reviews, old drafts, and packaging history are not part of the repository. Revisions belong in ordinary Git commits to the canonical files.

## Use

Python 3.10+ is sufficient for repository checks, packaging, and the standalone exact-certificate replay. Lean, LaTeX, and topic-specific computations have their own documented requirements.

```sh
python scripts/validate_repo.py
python -S research/topics/nr-noisy-recovery/checks/run_all.py
python scripts/package_overleaf.py
```

Upload generated `dist/overleaf.zip` to Overleaf and compile `main.tex` with pdfLaTeX. GitHub Actions also saves an `overleaf` download from each successful check run. Generated files stay under ignored `_build/` or `dist/`.

The scientific statuses reflect the supplied research and its verification record. Repository checks do not constitute a new proof of every mathematical assertion. See [validation scope](docs/VALIDATION.md) and [rights and attribution](docs/RIGHTS.md).
