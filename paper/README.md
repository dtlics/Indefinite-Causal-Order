# Paper

[main.tex](main.tex) is the only editable manuscript: **An exponential quantum-switch advantage for commuting channels**. It contains its bibliography and TikZ figures. The selected source is the 5 October 2026 revision, with seven main pages and nineteen pages in total.

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
