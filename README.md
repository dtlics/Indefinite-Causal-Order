# Indefinite causal order

The current research on quantum-switch advantages, causal structure, and the limits of ordinary quantum queries. The repository contains the paper **An exponential quantum-switch advantage for commuting channels**, its proof code, and the results, limitations, and open problems from seven research directions.

| Read or change… | Canonical location |
| --- | --- |
| Paper and Overleaf export | [paper/](paper/README.md) |
| Research directions and current status | [Research map](research/README.md) |
| A particular result, obstruction, or conditional theorem | [Result index](research/RESULTS.md) |
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

This is an initialization of the current state of knowledge. Earlier checkpoint collections, repeated reviews, old drafts, and packaging history are not part of the repository. Future revisions belong in ordinary Git commits to these same files.

## Use

Python 3.10+ is sufficient for repository checks, packaging, and the standalone exact-certificate replay. Lean, LaTeX, and topic-specific computations have their own documented requirements.

```sh
python scripts/validate_repo.py
python scripts/package_overleaf.py
```

Upload generated `dist/overleaf.zip` to Overleaf and compile `main.tex` with pdfLaTeX. GitHub Actions also saves an `overleaf` download from each successful check run. Generated files stay under ignored `_build/` or `dist/`.

The scientific statuses reflect the supplied research and its verification record. Repository checks do not constitute a new proof of every mathematical assertion. See [validation scope](docs/VALIDATION.md) and [rights and attribution](docs/RIGHTS.md).
