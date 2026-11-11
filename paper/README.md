# Paper

[main.tex](main.tex) is the only editable manuscript: **Infinite or indefinite: the query cost of simulating the quantum switch**. It contains its bibliography and TikZ figures. It proves the exact and approximate query lower bounds for simulating the quantum switch by classically adaptive quantum circuits, the exponential query separation for commuting hidden-dephasing channels and channel-visibility estimation, the model-validation and two-call separation results, and the capacity-qualification and keyed-device appendices ([NR-R22](../research/topics/nr-noisy-recovery/noise-model-selection.md#nr-r22) and [NR-R22-KEYED](../research/topics/nr-noisy-recovery/noise-model-selection.md#nr-r22-keyed)). Compilation and review scope are recorded in [validation](../docs/VALIDATION.md).

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
