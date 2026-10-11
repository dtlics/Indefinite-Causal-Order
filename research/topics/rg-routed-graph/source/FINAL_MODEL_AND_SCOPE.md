# Exact realization model and claim

The proved obstruction uses the same finite skeletal construction specified
by Corollary3.1 of Vanrietvelde et al., arXiv2206.10042v3: fixed routed
unitaries fill some native nodes, and complete unitary monopartite supermaps
fill the original-query nodes. The routed graph satisfies both bi-univocality
and weak loops, the validity criteria of Theorem3.1.

For the user-specified exact version, the four original qubit inputs each
occur once, at four actual native vertices, through such complete linear
monopartite insertions. The original past and future are both C16, and the
entire multilinear tensor, rather than only its values at selected unitaries,
must be recovered. Independent private ancillas can be arbitrarily large.

The explicit quartet in [RG-001](results/obstruction.md#rg-001) has full private-ancilla-complete
unitarity but no such finite valid host. Any finite number of fixed entangling
auxiliary nodes, arbitrary native branching and repeated representation
multiplicities are covered. The argument does not cap the auxiliary count.

After each local insertion is normalized by its unitary value at identity,
the private-M2 one-port argument makes it a unital *-homomorphism from M2
to that vertex's actual finite direct-sum algebra. Hence the native-interface
classification covers arbitrary permitted monopartite insertions, not only
an identity placement of a physical Ui or a selected maximal port.

The statement is a counterexample to routed universality in this exact
Corollary3.1, whole-one-use formulation of Conjecture1. It does not claim an
obstruction for an enlarged external boundary, approximate equality, extra
oracle calls, a distributed original query occupying several native vertices,
or a different operation class at a node. No assertion of literature priority
or external peer review is made.

Primary definitions: [Corollary 3.1 and graph validity](https://arxiv.org/html/2206.10042v3#S3) and [the universality conjecture](https://arxiv.org/html/2206.10042v3#S5).

The proof is mathematical and computer-assisted, not a proof-assistant
formalization. Exact finite eliminations support uniform private-completeness
and graph arguments. [RG-001](results/obstruction.md#rg-001) owns the proof;
the [shared result index](../../../RESULTS.md#rg--exact-native-routed-graph-universality)
locates all related scoped findings.
