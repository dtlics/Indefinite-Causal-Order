# Paper

[main.tex](main.tex) is the only editable manuscript: **An exponential quantum-switch advantage for commuting channels**. It contains its bibliography and TikZ figures. The selected source is the 5 October 2026 revision, with seven main pages and nineteen pages in total.

## Overleaf

From the repository root run:

```sh
python scripts/package_overleaf.py
```

Upload `dist/overleaf.zip`, select `main.tex`, and use pdfLaTeX. No bibliography processor, shell escape, external images, or custom fonts are required. If edits originate in Overleaf, bring them back into this file before the next commit.

## Compiled PDF

Read or download the [saved paper PDF](../dist/quantum-switch-paper.pdf). This is the only generated export kept in Git. After a manuscript edit, rebuild it before you commit the change.

In [Repository checks](https://github.com/dtlics/Indefinite-Causal-Order/actions/workflows/checks.yml), open a successful run and download the `paper-pdf` artifact. It contains a fresh compiled paper and a build record with the source SHA-256 fingerprint. GitHub may require sign-in. Artifacts have a retention limit; the saved paper PDF remains in Git.

## Local build

Install pdfLaTeX through TeX Live or MiKTeX. From the repository root run:

```sh
python scripts/build_paper.py
```

The script compiles with shell escape disabled. It runs at least two passes, checks that references have settled, and rejects undefined references and overfull or underfull boxes. It saves `dist/quantum-switch-paper.pdf` and `dist/paper-build.json`. Temporary files go to `_build/paper/`. This is a repeatable build procedure; different TeX versions can produce different PDF bytes.

Source is versioned; exports and compilation output are generated. See [validation scope](../docs/VALIDATION.md) for the current compilation and review checks, and the [formal correspondence map](../proofs/lean/THEOREMS.txt) for theorem labels and proof endpoints.
