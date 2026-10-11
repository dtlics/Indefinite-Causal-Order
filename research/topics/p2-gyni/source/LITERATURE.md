# Primary literature and theorem dependencies

These references identify the setting and actual external inputs. The scoped proofs and exact certificates under support/ are project materials; no priority or external peer-review claim is made. Metadata and the labelled-projective theorem were checked against primary sources on 1 October 2026. Papers are referenced, not redistributed.

## Required modelling premise

**Zixuan Liu and Giulio Chiribella, “Tsirelson bounds for quantum correlations with indefinite causal order,” arXiv:2403.02749v3, 4 March 2025.** [Pinned source](https://arxiv.org/html/2403.02749v3)

Theorem 1 in Methods and Appendix F allow arbitrary instruments and a process to be replaced by labelled projective instruments and a transformed valid process, preserving all probabilities. Projectors may have equal rank across settings/outcomes. This is the instrument-reduction input to the universal upper's scope. The fixed-dimension theorem for single-trigger correlations is not applied to general GYNI. The package proves the subsequent word NS implication, repair and convergence arguments separately.

## Process and game definitions

- **Ognyan Oreshkov, Fabio Costa and Časlav Brukner, “Quantum correlations with no causal order,” Nature Communications 3, 1092 (2012).** [arXiv:1105.4464v3](https://arxiv.org/abs/1105.4464v3), [DOI](https://doi.org/10.1038/ncomms2076). Positive process matrices and normalization on arbitrary local CPTP maps. Required affine-span implications are proved again in the supplied word theorem and audit
- **Cyril Branciard, Mateus Araújo, Adrien Feix, Fabio Costa and Časlav Brukner, “The simplest causal inequalities and their violation,” New Journal of Physics 18, 013008 (2016).** [arXiv:1508.01704v1](https://arxiv.org/html/1508.01704v1), [DOI](https://doi.org/10.1088/1367-2630/18/1/013008). Equations (4) and (6), and section III: bipartite binary GYNI causal inequality and process-matrix setting; it does not identify P2's unrestricted exact optimum
- **M. L. Almeida, J.-D. Bancal, N. Brunner, A. Acín, N. Gisin and S. Pironio, “Guess your neighbour’s input: a multipartite non-local game with no quantum advantage,” Physical Review Letters 104, 230404 (2010).** [arXiv:1003.3844v1](https://arxiv.org/abs/1003.3844v1), [DOI](https://doi.org/10.1103/PhysRevLett.104.230404). Original game provenance. Its Bell/no-signalling setting differs from unrestricted process matrices; its no-quantum-advantage result is not the present upper bound
- **Ravi Kunjwal and Ognyan Oreshkov, “Nonclassicality in correlations without causal order,” arXiv:2307.02565v3, 27 June 2025.** [Pinned source](https://arxiv.org/html/2307.02565v3). Related logical-consistency and process/correlation background; not a dependency of the new numerical certificates or convergence and conditional-realization proofs

## Inputs to the optional finite-span obstruction

- **Man-Duen Choi, Nathaniel Johnston and David W. Kribs, “The multiplicative domain in quantum error correction,” Journal of Physics A: Mathematical and Theoretical 42, 245303 (2009).** [arXiv:0811.0947v1](https://arxiv.org/html/0811.0947v1), [DOI](https://doi.org/10.1088/1751-8113/42/24/245303). Theorem 8 is the multiplicative-domain fact applied to a UCP retraction in finite_span_obstructions.md, section 1
- **William B. Arveson, “On subalgebras of C*-algebras,” Bulletin of the American Mathematical Society 75 (1969), 790–794.** [Primary announcement scan](https://www.isibang.ac.in/~soumyashant/misc/collected-works-of-arveson/1960s/1969_On_subalgebras_of_Cstar_algebras.pdf). Theorem 1, page 791, is the CP extension theorem used only for the complete-order embedding corollary there
- **R. R. Smith, “Completely bounded maps between C*-algebras,” Journal of the London Mathematical Society (2) 27 (1983), 157–166.** [DOI](https://doi.org/10.1112/jlms/s2-27.1.157). Cited to delimit norm stabilization at a fixed matrix range, not a range-size bound from domain span dimension. The new GYNI interval does not depend on this lemma

Finite SDP duality, rational Gram repair, endpoint pairing, spectral-ideal saturation, sine recurrence and weighted-tail estimates are derived where needed in the included proofs. No NPA convergence theorem is substituted for the explicitly proved process/word hierarchy convergence.
