# Quantum-switch applications in QEC and error-channel characterization

This branch preserves the last two application investigations as reproducible
research. The question is whether a quantum switch helps with a useful
quantum-computing task under a naturally justified opaque-device interface.
The ordinary comparison includes the state preparation, memory, measurement
records, known controls and encoding choices that the same interface permits.

**The search has not yet established a substantial unrestricted advantage for
a natural QC/QEC workload.** It has produced additional exact ordinary
simulation constructions, bounds on what a switch flag can improve, useful
code-aware constructions, and numerical application screens. Keeping the
successful calculations and the stronger ordinary counterexamples together is
essential to using these findings correctly.

These exploratory results are separate from the paper's audited Lean results.
Their algebraic arguments are in the reports; the code checks finite cases and
numerical calculations. No new result below is described as Lean-verified.

## Start here

| Need | Entry point |
| --- | --- |
| See the findings, assumptions and evidence status | [Result-to-evidence index](RESULTS.md) |
| Read the broad channel/QEC application investigation | [Screening report](screening/report.md) and [34-entry candidate catalog](screening/candidates.md) |
| Read the recovery, coherent-error and stronger-baseline follow-up | [Code-aware report](code-aware/report.md) and [18-entry candidate map](code-aware/candidates.md) |
| Check attribution and primary-source support | [Source guide](SOURCES.md); each report retains its detailed reference list |
| Inspect the current replay and hashes | [Validation record](validation.json) |
| Trace the two delivered research packages into this branch | [Import provenance](provenance.json) |

## Findings worth carrying forward

1. **Additional exact ordinary compilers.** A known orthogonal-unitary-mixture
   arm with unknown weights needs one query per box; two completed recovery
   maps for the same known code need at most one unknown query; and an
   extractable quantum-program arm gives another full-switch compiler.
2. **Limits on learning and same-run correction.** Ordinary Choi probes estimate
   the maximally mixed-input commutator statistic. Known low-weight operator
   support can remove its dimension penalty. For a self-switch, the optimal
   final-decoder gain is bounded by the rare flag's probability. A stable
   balanced bit of a projective outcome already defeats the hidden SAME/MUB
   promise under that more informative interface.
3. **A constructive QEC mechanism with its counterexamples.** Symmetric and
   antisymmetric Kraus products can lie in separately correctable spaces. The
   explicit coherent-error example admits exact flagged correction, but also
   ordinary intermediate recovery and an alternative noiseless encoding.
4. **Application screens with useful output metrics.** Pauli-code logical
   errors, optimized non-Pauli decoders, leakage, thermal/collective noise,
   finite-level oscillators, ideal GKP decoding, fermionic loss and reset-to-magic
   are evaluated with explicit baselines. Reset-to-magic has a restricted
   stabilizer-resource separation already rooted in prior literature; it does
   not establish a query advantage over arbitrary ordinary quantum gates.

The next candidate must specify a real opaque module and a useful model-choice
or live-data output. Different-code conversion and incomplete correlated
nonunital backaction remain leads, not established advantages. Shared bath
memory would require a process model beyond two independent CPTP maps.

## Layout

| Path | Role |
| --- | --- |
| `screening/report.md`, `code-aware/report.md` | Complete derivations, assumptions, numerical findings and limitations |
| `screening/candidates.md`, `code-aware/candidates.md` | Application-by-application disposition; counts are not counts of independent advantages |
| `*/experiments/` | Original executable research scripts, with fixed seeds and assertions |
| `common/core.py` | Single copy of the byte-identical channel utility shared by both original packages |
| `*/evidence/` | Current JSON/CSV output from the clean replay |
| `reproduce.py` | Stages each study from source into ignored build directories and runs it |
| `verify_package.py` | Checks evidence/source hashes, import inventory, Python syntax and local documentation links |

## Reproduce

From the repository root, use Python 3.11 or newer and the recorded dependency
versions. No private repository, cloud processor or commercial SDP solver is
needed after checkout.

```sh
python -m pip install -r research/more-applications/requirements.txt
python research/more-applications/verify_package.py
python research/more-applications/reproduce.py
```

The last command runs **11 screening scripts and 8 follow-up check groups** in
clean directories under `_build/more-applications/`. The current evidence is
not used as experiment input. Logs and a fresh replay record remain there;
tracked files are unchanged. To run one study, pass `--study screening` or
`--study code-aware`.

To deliberately replace the tracked current evidence after a complete replay:

```sh
python research/more-applications/reproduce.py --refresh-evidence
python research/more-applications/verify_package.py --record-integrity
```

The single [validation record](validation.json) identifies the actual runtime,
input hashes and check scope. The decoder SDP calculations are floating-point
primal/dual brackets; the GKP results are numerical quadratures; the oscillator
follow-up is a 12-level model. None is an exact all-strategy certificate or a
hardware threshold. Detailed scope accompanies every result in the reports.

## Attribution and preservation

The reports distinguish published ingredients from direct derivations in these
investigations. See [SOURCES.md](SOURCES.md) before making novelty claims.
Original package hashes and every imported file's destination are recorded in
[provenance.json](provenance.json). The import consolidates navigation and the
duplicated utility, refreshes evidence, repairs links, and corrects an identified
rounded decoder value. It preserves negative and restricted results alongside
positive constructions.
