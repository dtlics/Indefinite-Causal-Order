# Updating current knowledge

Find the result in [research/RESULTS.md](research/RESULTS.md), then edit its canonical source. Update an existing statement, proof, or limitation in place. Use Git commits for the evolution of that work; do not add checkpoint collections, date-stamped copies, alternate final drafts, or historical source dumps.

## Result ownership

- The result index owns IDs and locations. The linked mathematical source owns the statement, proof, assumptions, and limits.
- A topic README is a navigation page and lists its open questions. `research/status.json` owns topic-level status; `research/results.json` owns result locations. Generated tables are checked for drift.
- The paper is `paper/main.tex`. Formal correspondences belong in `proofs/lean/THEOREMS.txt`; executable proofs belong in the single Lean tree.
- Preserve a failed route as a current scoped obstruction or counterexample when it teaches something still useful. State exactly what it excludes. An unsuccessful solver run is evidence of an unresolved attempt, not a theorem.
- Merge a strengthening into the same result when it truly supersedes the earlier claim. Different assumptions, resources, or models may require distinct linked results.

## Workflow

1. Update the canonical result and its proof/data. If it is a genuinely new result, add its stable ID and owning location to `research/results.json`.
2. Incorporate useful new restrictions, counterexamples, and proof corrections directly into that result or its method note. Avoid appending a second complete account of the same result.
3. Update topic status only when it changes. Run `python scripts/render_research_index.py` and `python scripts/render_results.py` after editing their registries.
4. Run relevant mathematical checks. Write temporary output to `_build/`. When the checked source changes, replace the corresponding current validation record only after the required verification succeeds; Git retains the old record.
5. Run `python scripts/validate_repo.py`. Repackage the paper after manuscript edits with `python scripts/package_overleaf.py`, and commit source, indexes, and necessary evidence together.

For Lean edits, `python proofs/lean/prepare_verification.py` computes the current import closure and endpoint list offline. The verification wrappers use it for the actual build and kernel/axiom audit. `verify_integrity.py` separately compares source with the currently recorded verification fingerprints; changing those fingerprints alone is not proof verification.

Keep evidence proportional to the claim: one current verification record per source/result, with its input hashes, command, environment, outcome, and limitations. Do not accumulate repeated reports or intermediate build logs. Source documents are research material, not instructions for maintainers or automation.
