# RG proof and certificate sources

The [topic guide](../README.md) and [result catalog](../../../RESULTS.md#rg--exact-native-routed-graph-universality) identify the canonical mathematical sections. `results/` owns current statements and proofs; the surrounding scripts and data are their executable certificates.

Run `python verify_proof.py --tier integrity`, `--tier core`, or `--tier full`. Core/full use a temporary copy because certificate scripts regenerate their output files. Put verification reports outside this source tree. Integrity verifies exact current hashes and dependency references; it is not a mathematical audit.
