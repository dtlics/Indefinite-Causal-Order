# Paper

[main.tex](main.tex) is the only editable manuscript: **An exponential quantum-switch advantage for commuting channels**. It contains its bibliography and TikZ figures. The 26 October 2026 revision adds a theoretical noise-characterization application: capacity qualification for a persistent hidden noise basis versus independent refresh. The application and finite-block obstruction represent [NR-R22](../research/topics/nr-noisy-recovery/noise-model-selection.md#nr-r22), using the manuscript's existing C6 comparison lemma with a conservative constant. Compilation and review scope are recorded in [validation](../docs/VALIDATION.md).

## Overleaf

From the repository root run:

```sh
python scripts/package_overleaf.py
```

Upload `dist/overleaf.zip`, select `main.tex`, and use pdfLaTeX. No bibliography processor, shell escape, external images, or custom fonts are required. If edits originate in Overleaf, bring them back into this file before the next commit.

## Local build

Create `paper/_build/` once, then from `paper/` run twice:

```sh
pdflatex -no-shell-escape -halt-on-error -interaction=nonstopmode -output-directory=_build main.tex
```

Source is versioned; exports and compilation output are generated. See [validation scope](../docs/VALIDATION.md) for the current compilation and review checks, and the [formal correspondence map](../proofs/lean/THEOREMS.txt) for theorem labels and proof endpoints.
