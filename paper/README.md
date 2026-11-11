# Paper

[main.tex](main.tex) is the only editable manuscript: **Infinite or indefinite: the query cost of simulating the quantum switch**. It contains its bibliography and TikZ figures. It proves three results on the query cost of simulating the quantum switch by ordinary strategies, that is, quantum circuits that call the boxes in a definite, classically adaptive order: exact simulation is impossible with any bounded number of calls; approximate simulation to a fixed error below 1/2 needs Ω(d^{1/4}) calls; and one bit that the switch reads off its control qubit, whether a noisy device dephases in a hidden basis or depolarizes, needs more than d^{1/16}/(1400p) ordinary calls. Compilation and review scope are recorded in [validation](../docs/VALIDATION.md).

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
