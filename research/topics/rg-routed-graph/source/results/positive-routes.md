# Positive routes

[Topic index](../../README.md) · [Shared result index](../../../../RESULTS.md#rg--exact-native-routed-graph-universality)

Each result below has one owner. Exact scope and proof are updated here. Source-level mathematical arguments and finite certificates are distinguished from a new formal verification.

<a id="rg-068"></a>

## RG-068 — Classical three-party routes

**Statement.** Classical three-party routes

**Status:** positive construction. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### 1. Setting and finite combinatorial characterization

Let I_i and O_i be nonempty finite sets and write I=product_i I_i, O=product_i O_i. A deterministic process function is w:O→I such that, for every tuple of local functions f_i:I_i→O_i, there is exactly one o∈O solving

    o_i=f_i(w_i(o))  for all i.

Equivalently, every two distinct o,o' have a local orthogonality witness:

    some i satisfies o_i≠o_i' and w_i(o)=w_i(o').                 (W)

Proof of necessity: if no witness exists, prescriptions f_i(w_i(o))=o_i and f_i(w_i(o'))=o_i' are compatible for each i, so choose functions extending them. This creates two fixed points.

Proof of sufficiency: (W) prevents two fixed points for any f. Count all pairs (f,o) satisfying the fixed-point equations. Each o allows product_i |O_i|^(|I_i|-1) choices of f, so the number of pairs is

    |O| product_i |O_i|^(|I_i|-1) = product_i |O_i|^|I_i|,

exactly the total number of f. Since each f occurs at most once, it occurs exactly once. This also covers unequal local dimensions and singleton sets.

Taking o,o' that differ only in coordinate i immediately proves that w_i is independent of o_i, but this nonself-dependence alone is not sufficient for (W).

### 2. Explicit indexed graph

Use internal nodes A_1,...,A_N, a hub X, and a terminal conversion node D. There is an external unsectorized input wire P_i of dimension |I_i| into A_i. (One may instead put a source P and fixed tensor decomposition upstream.) There is an external unsectorized output wire F of dimension |O| from D.

Internal edges:

* R_i:X→A_i, with index x_i∈I_i and each sector one-dimensional.
* T_i:A_i→X, with index (x_i,o_i)∈I_i×O_i and every sector one-dimensional.
* Z:X→D, with index o∈O and every sector one-dimensional.

External wires have trivial index sets, as required by the precise Definition B.5 of arXiv:2206.10042v3.

Routes:

* At A_i, branch A_i^x has input index x and output indices {(x,a):a∈O_i}. Different x give disjoint branches.
* At X, there is one singleton-to-singleton branch X^o for each o∈O. Its input tuple is ((w_i(o),o_i))_i; its output tuple is ((w_i(o))_i,o). All other input/output tuples are outside the practical subspaces.
* At D, there is one branch: every input index o∈O is related to the unique external output index.

These relations are branched. X's practical input/output dimensions both equal |O|. D's practical input/output dimensions also equal |O|. At A_i, the branch input/output dimensions are |I_i| and |O_i|; when unequal, the definition of superunitary allows the same ancillary input/output dimension correction as the original laboratory unitary. For equal local dimensions, every branch is already dimension-balanced without ancillas.

This graph uses no hidden coherent-copy isometry with an enlarged final dimension. The only practical final register is o. Redundant x data live in correlated practical subspaces and are removed reversibly by X, with no postselection.

### 3. Bi-univocality proof

Forward bifurcation choices exist only at the A_i branches. A choice assigns some o_i=f_i(x_i) for every x_i, which is exactly an arbitrary local function f_i:I_i→O_i. At X and D every branch has only one output index tuple, so there are no further nontrivial choices.

A consistent internal index assignment is precisely a solution to

    x=w(o),  o_i=f_i(x_i).

Process-function validity gives exactly one such o and hence exactly one complete index assignment. It determines all branch statuses, so the forward choice relation is a total function.

In the reversed graph, A_i^x has a singleton output index x, and each X^o still has a singleton output index tuple. The only nontrivial bifurcation is at D, selecting any o∈O. This fixes X^o, all x_i=w_i(o), and all A_i^{x_i}; the assignment is consistent and unique. The reversed choice relation is therefore also a total function. The graph is bi-univocal.

### 4. Weak-loops proof

There are no solid arrows between interior branches. For A_i^x and X^o to occur jointly requires x=w_i(o). Conditional on those two branches, the T_i index is the single value (w_i(o),o_i), of dimension one. Hence A_i^x is not a strong parent of X^o. Likewise the R_i index is fixed to w_i(o), of dimension one, so X^o is not a strong parent of A_i^x. Conditional on X^o and D, the Z index is fixed to o, again dimension one, so there is no solid arrow X^o→D. These are all internal edge types. If one adds an explicit source P, its solid arrows point only outwards and cannot lie in cycles.

Every forward nontrivial choice is at A_i^x, so every green arrow has an A branch as source. Some may point to other A branches, and some to X branches. No green arrow has D as target, since D's unique branch always occurs. X branches cannot be green-arrow sources because they have no choices.

Every reversed nontrivial choice is at D. Reversing the influence orientation as prescribed by the definition of red arrows, every red arrow points to D. Thus D cannot lie on a directed loop, X branches cannot lie on a loop, and every arrow on every directed loop is green.

This proof handles arbitrary closed walks, including figure-eight walks, not merely simple directed cycles: every strongly connected component with a cycle contains only A branches and only green edges. The weak-loops condition is satisfied in its stronger intended sense.

By Theorem B.1/3.1 of Vanrietvelde et al., the skeletal graph is a routed superunitary.

### 5. Fleshing out the canonical quantum extension

Identify I_i with the cyclic group Z_|I_i| by any bijection, and let C_i^x act on P_i by C_i^x|p_i>=|p_i+x>. The choice of group labels is merely an implementation convention.

For a laboratory map U_i:I_i→O_i, use the one-slot map

    M_i[U_i] = sum_(x,o_i,p_i) U_i[o_i,p_i+x]
                 |x,o_i>_(T_i) <p_i|_(P_i) <x|_(R_i).

This is realized by a controlled C_i^x on the unsectorized P_i, one application of U_i, and a fixed reordering/sector relabeling. It uses U_i once and preserves the branch label x. It is a unitary monopartite supermap into the route at A_i, including arbitrary private ancillary systems. The same U_i occurs in all branches coherently; no independent copying or querying of U_i occurs.

At X plug the routed unitary

    H = sum_o |w(o)>_R |o>_Z < (w_i(o),o_i)_i |_T.

It maps the practical input basis bijectively onto the practical output basis. At D plug |o>_Z→|o>_F.

Contraction yields

    G_w(U_1,...,U_N)[o,p] = product_i U_i[o_i,p_i+w_i(o)].       (G)

Its underlying process unitary is

    S_w: |p>_P |o>_O → |o>_F |p+w(o)>_I.                     (S)

Thus every canonical reversible extension of a finite deterministic process function is obtained by fleshing out a valid routed graph. Setting p=0 and tracing F recovers the deterministic diagonal process matrix of w.

The claim concerns this canonical extension (and local/global reversible modifications of it), not every possible reversible extension of w and not every permutation unitary process.

### 6. Direct independent superunitarity proof

Let arbitrary private-ancilla-assisted local unitaries have matrix elements

    U_i[o_i,b_i; p_i,a_i],

where a_i,b_i are input/output ancilla indices. The closed map is

    G[o,b;p,a] = product_i U_i[o_i,b_i; p_i+w_i(o),a_i].

For two rows (o,b),(o',b'), their inner product factors over i. If o≠o', choose i from (W). The two shifts agree at i, and summing p_i,a_i gives the inner product of distinct rows (o_i,b_i) and (o_i',b_i') of U_i, which is zero. If o=o' but b≠b', the same argument applies at an i with b_i≠b_i'. Each row has norm one. The global input and output dimensions agree because each local U_i is unitary. Therefore G is unitary.

This also shows why one cannot infer the full conjecture merely from the classical theorem: the proof depends on output rows factoring into local rows and a coordinate witness killing each distinct-row overlap. A general process need not have this product-row form.

### 7. Broader class covered by the same graph

The graph theorem allows arbitrary independent branch-local routed unitaries M_i^x and arbitrary hub phases e^(i alpha(o)); these are much more general than fixed cyclic translations. In particular, replacing C_i^x by any unitaries V_i^x on the local past carrier yields another valid process, for any process function w. A single U_i can still be inserted once using a controlled V_i^x followed by U_i.

The resulting process unitary has the form

    S |p,o> = e^(i alpha(o)) |o>_F tensor_i V_i^{w_i(o)}|p_i>.

This entire class has an explicit routed realization. Arbitrary phases depending jointly on p and o, and arbitrary entangling controlled unitaries on P, are not covered by this theorem without an additional decomposition argument.

### 8. Executable checks

Run `python3 work/check_classical_routes.py`. The script independently enumerates every tripartite binary nonself function, checks the fixed-point definition for all 64 local intervention tuples, compares it with (W), constructs the hub graph's forward and reverse influences, and verifies no non-green edge can be recurrent.

Results saved in `work/classical_routes_checks.json`:

* 4096 candidate nonself functions; 744 valid process functions.
* Zero fixed-point/pairwise-witness mismatches.
* 744 valid routed-graph certificates.
* One random local-unitary draw per process: largest entrywise unitarity error 1.8875e-15.
* 25 tests with independent two-dimensional ancillas, including Lugano: largest error 1.7764e-15.

The graph proof is dimension-independent and the finite enumeration is only a falsification check, not the basis of the proof.

### 9. Primary sources and prior-art boundaries

1. Vanrietvelde, Ormrod, Kristjansson, Barrett, *Consistent circuits for indefinite causal order*, arXiv:2206.10042v3 (26 November 2025), https://arxiv.org/html/2206.10042v3 . Definitions B.5-B.16 give precisely the external-index constraint, routes, strong parents, bi-univocality, and weak loops used here. Theorem B.1 gives the routed-superunitary implication. Section 4.3 constructs Lugano; Section 5 expects other known classically derived examples to be representable and states the full universality conjecture.

2. Baumeler, Costa, Ralph, Wolf, Zych, *Reversible time travel with freedom of choice*, Classical and Quantum Gravity 36, 224002 (2019), https://doi.org/10.1088/1361-6382/ab4973 . Theorem 2 proves classical reversible extendibility. Its final discussion says the general quantum connection remained open then; this is historical context, not a current open-problem claim.

3. Baumeler, Gilani, Rashid, *Unlimited non-causal correlations and their relation to non-locality*, Quantum 6, 673 (2022), https://quantum-journal.org/papers/q-2022-03-29-673/ , arXiv:2104.06234v3 https://arxiv.org/abs/2104.06234 . Around Theorem 4 it states that every process function and every mixture thereof has unitarily extensible behavior. Thus the generic quantum extension must not be advertised as newly discovered here.

4. Dourdent et al., *Paradox-free classical non-causality and unambiguous non-locality without entanglement are equivalent*, arXiv:2512.23599v1, https://arxiv.org/html/2512.23599v1 . Theorem 8 connects arbitrary process functions and complete product bases, consistent with the row-orthogonality argument. Equation (31) states the same pairwise exclusivity/witness pattern. This is prior art for the combinatorial and product-basis aspects, not evidence that the routed hub graph above already appears there.

The limited search did not locate this exact generic hub construction. That absence does not establish novelty.

<a id="rg-069"></a>

## RG-069 — Exact tripartite orthogonal-support routes

**Statement.** Exact tripartite orthogonal-support routes

**Status:** positive construction. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### Theorem

Let `I=I1 tensor I2 tensor I3` and let `O_i` have fixed finite computational bases. Suppose `E_i` are pairwise orthogonal projections, with `E_i` trivial on input factor `I_i`. For each basis label `a` of `O_i`, let `A_i(a)` be a unitary trivial on `I_i`, with

    A_i(a)-I = E_i [A_i(a)-I] E_i.

Then the unitary process

    S |p,o> = |o>_F V_o |p>_I,
    V_o = A_1(o_1) A_2(o_2) A_3(o_3),
    P=I1 tensor I2 tensor I3,  F=O1 tensor O2 tensor O3,

has an exact valid routed realization with unitary fixed fillings and one-use monopartite superunitary laboratory fillings. Its boundary spaces are exactly `P,F`; no extra final record is retained.

This includes the explicit `(3,3,2)` example in [RG-074: Higher-dimensional cube structure](higher-order.md#rg-074), and allows each active gate to act jointly and noncommutatively on the other two quantum payloads. It proves realizability of this class, not the full conjecture.

### 1. Reduce to local sector flags

Section 6 of [RG-074: Higher-dimensional cube structure](higher-order.md#rg-074) proves the following finite-dimensional fact. There exist local projections `Pi_i` such that, with cyclic indices,

    E_i <= Pi_(i+1) (I-Pi_(i+2)).                            (1)

One may take `Pi_1` to be the local support of `E_3` on `I1`, `Pi_2` the local support of `E_1` on `I2`, and `Pi_3` the local support of `E_2` on `I3`. Pairwise support separation follows by partially tracing `E_i E_j=0` over the two nonshared factors: the resulting positive reduced operators have product zero and hence orthogonal supports.

Write

    K_i^1 = ran Pi_i,      K_i^0 = ker Pi_i,
    B_i = {b in {0,1}: dim K_i^b > 0},
    B = B_1 times B_2 times B_3.

Only nonzero sector spaces are retained. Equation (1) implies that every `A_i(a)` preserves all three local flags `b_i`. Its only possible nonidentity action is on the other two payload spaces

    M_i = K_(i+1)^1 tensor K_(i+2)^0.

On a flag tuple `b`, the possible active gate is described by

    x_i = w_i(b) = b_(i+1)(1-b_(i+2)).                       (2)

The vector `x=w(b)` is either zero or has a single nonzero component. If `x_i=1`, the other two flags are fixed to `b_(i+1)=1,b_(i+2)=0`, while `b_i` is arbitrary. In particular changing `b_i` cannot change any component of `w(b)` in this active sector.

Define `X_i={w_i(b):b in B}`. Only branches `x_i in X_i` will be used; this handles rank-zero or full-rank `Pi_i` without zero-dimensional sectors.

### 2. Classical consistency of the control relation

The Boolean map (2) is a deterministic process function. Here is an elementary proof, also establishing the branch-stability property needed below.

For arbitrary local functions `f_i:{0,1}->{0,1}`, put `c_i=f_i(0)`. If `c=000` or `111`, its unique consistent assignment is `x=000,b=c`. Otherwise there is exactly one cyclic index `i` with `c_(i+1)=1,c_(i+2)=0`. Set `x_i=1`, all other `x_j=0`, `b_i=f_i(1)`, and `b_j=c_j` for `j!=i`. Because the two other flags are fixed to `1,0`, this satisfies `w(b)=x` regardless of `b_i`.

Uniqueness follows because an all-zero solution must have `b=c`, and a solution with active `i` must have the same two fixed other flags, hence must use that unique transition of `c`. Thus `b_i=f_i(w_i(b))` has exactly one solution.

Restricting the output flag alphabets to nonempty `B_i` preserves this property: extend any local function on `X_i` to `{0,1}` with values in `B_i`, and apply the full binary result. Every resulting `b` lies in `B`, and its `w_i(b)` lies in `X_i`, so the extension is never used outside the required input range.

Crucially, changing only the choice at branch `x_i=1` never changes the occurring laboratory branches `x`. If that branch occurs, only `b_i` can change; the other two flags and the whole active vector `x` stay fixed. If that branch does not occur, its choice has no effect.

### 3. Construct the reverse process first

It is convenient to realize `S^*` and then reverse the routed graph. The reversed laboratory `i` has input `O_i` and output `I_i`. Denote its unknown map by `L_i:O_i->I_i`. The reversed global past is `F=O1 tensor O2 tensor O3`, with one unsectorized factor `O_i` entering laboratory node `L_i`. The reversed global future is `P=I1 tensor I2 tensor I3`.

Besides the three laboratory nodes, use a purely classical hub `H`, three payload routers `R_j`, and a terminal assembly node `D`.

The design has two separate kinds of flow:

* all control wires entering or leaving `H` have one-dimensional sectors;
* each quantum payload from reversed laboratory `j` goes through `R_j`, then either straight to `D` or through the unique active *other* laboratory, and finally to `D`.

No quantum payload returns to `H`, and no processed payload returns to its router.

### 4. Arrows, sector dimensions, and routes

#### Laboratory nodes

At node `L_i`, branch `x in X_i` has:

* the unsectorized past input `O_i`;
* a one-dimensional control sector labelled `x` from `H`;
* an input edge from each `R_j`, `j!=i`, which is null and one-dimensional if `x=0`, and active with payload space `K_j^{beta_j(i)}` if `x=1`, where `beta_(i+1)(i)=1`, `beta_(i+2)(i)=0`.

The active input payload space is therefore `M_i` when `x=1`, and is scalar when `x=0`. Denote these spaces by `M_i^1=M_i`, `M_i^0=C`.

For each possible output flag `b_i in B_i`, the branch outputs:

* to `H`, a one-dimensional sector labelled `(x,b_i)`;
* to its own router `R_i`, a sector labelled `(x,b_i)` with quantum space `K_i^{b_i}`;
* to `D`, two processed-payload edges, null for `x=0`, and with respective spaces `K_(i+1)^1,K_(i+2)^0` for `x=1`.

Both processed-payload edge labels preserve `x`. Thus the input tuple of a branch is a single index tuple, while its output tuples are indexed by `b_i`. Different branches have disjoint input and output sets. The route is branched.

#### Classical hub

For each `b in B`, put one singleton-to-singleton branch `H^b`. Its input tuple is `((w_i(b),b_i))_i`, from the laboratory control-output wires. Its output tuple contains:

* `x_i=w_i(b)` on the control edge to laboratory `i`;
* one routing instruction `h_j(b)=(x_j,b_j,a_j)` to `R_j`, where `a_j=i` if there is an active index `i!=j`, and `a_j=direct` otherwise;
* the complete flag tuple `b` on an edge to `D`.

All these sectors are one-dimensional. The practical hub dimensions are both `|B|`, and its fixed filling is the basis bijection specified by these branches.

#### Payload router `R_j`

The router receives its payload sector `(x_j,b_j)` from laboratory `j` and a matching one-dimensional instruction `h_j=(x_j,b_j,a_j)` from `H`. Keep precisely the instruction values attained by some `b in B`.

If `a_j=direct`, the router sends its payload to `D` in a sector labelled `(x_j,b_j)`, and all edges to other laboratories are null.

If `a_j=i!=j`, it sends its payload to laboratory `i` in its active input sector, while its direct-to-`D` edge and its other laboratory edge are null. Necessarily

    x_j=0,     b_j=beta_j(i).                               (3)

Thus each non-direct instruction has a unique `(x_j,b_j)` and destination. Different instructions have disjoint output index tuples: direct outputs retain `(x_j,b_j)`, and non-direct outputs distinguish the active destination edge. Each instruction is a singleton-to-singleton route branch. The quantum dimension at its input and output is the same, and the fixed filling just transports that payload.

#### Terminal assembly

The node `D` has one branch. For every `b in B`, its allowed input index tuple consists of the flag label `b` from `H`, together with all direct and processed payload indices specified by `x=w(b)` and `a_j` above. This tuple contains exactly one quantum copy of each payload `K_j^{b_j}`.

Its practical input is consequently

    direct_sum_{b in B} tensor_j K_j^{b_j}.

The unique external output space is `P=I1 tensor I2 tensor I3`, with the same dimension. The fixed filling assembles the three possibly rerouted payloads, then uses the canonical direct-sum identification with `P`. It is unitary on its entire practical input space. The flag label is absorbed into the ordinary sector decomposition of `P`; no additional output register is retained.

All unused edge labels are one-dimensional null sectors. Empty active sectors are absent because `B_i,X_i` and the routing instructions were restricted to attainable values.

### 5. Exact monopartite laboratory fillings

On branch `x_i=0`, use the unknown reversed laboratory `L_i` and the scalar memory identity.

On branch `x_i=1`, first apply the unitary

    C_i = sum_{a in basis(O_i)} |a><a| tensor
          (A_i(a)^* restricted to M_i)

to the unsectorized past `O_i` and the two incoming payloads. Then apply `L_i` once to `O_i`, leaving those payloads untouched. Split its output `I_i=direct_sum_{b_i in B_i}K_i^{b_i}`, send the flag as the correlated one-dimensional hub label and the actual payload to `R_i`, and send the two processed payloads to `D`.

All splitting, relabelling, and recombination maps above are unitary identifications of direct sums. On each branch, the map is a unitary preprocessor, one call to `L_i` tensored with an identity, and a unitary postprocessor. The same unknown map occurs in the direct sum of both branches; it is not queried twice. Globally its private memory is `direct_sum_{x in X_i}M_i^x`.

For equal local input/output dimensions, every branch dimension balances directly. More generally, the input and output dimensions are `dim(O_i)dim(M_i^x)` and `dim(I_i)dim(M_i^x)`. The same private input/output ancillary correction that makes the original rectangular laboratory map unitary makes this wrapper unitary. Hence it is a monopartite superunitary under the ancillary-complete convention.

### 6. Bi-univocality

Forward bifurcation choices occur only at laboratory branches. They assign a flag `b_i=f_i(x_i)` for every branch `x_i in X_i`. The hub requires `x=w(b)`. Section 2 gives exactly one solution for every such collection of choices. This fixes all hub, router, and terminal indices, including where each quantum payload travels. Thus the forward choice relation is a total function.

In the adjoint graph, laboratory branches have no choices: their reversed output tuple is the single label tuple for `x_i`. Hub and router branches are still singleton-to-singleton. The only nontrivial reversed choice is at `D`, selecting one of its input tuples, equivalently `b in B`. This fixes `x=w(b)`, all router instructions, all laboratory branches, and all remaining indices uniquely. Thus the reverse choice relation is a total function. The graph is bi-univocal.

### 7. Weak loops, including arbitrary closed walks

The hub has no solid connections. Conditional on one of its singleton branches and any adjacent branch, the connecting index is a fixed one-dimensional value. Its branches also make no bifurcation choices.

All possible nontrivial solid connections elsewhere have the following forms (some disappear when the relevant payload is one-dimensional):

    L_j^x -> R_j^{(x,b,a)},
    R_j^{(0,b,i)} -> L_i^1       for i!=j,
    R_j^{(x,b,direct)} -> D,
    L_i^1 -> D.

Equation (3) is essential: a router sending to an active laboratory can only receive a payload from an inactive laboratory branch. A direct router leads only to `D`; a non-direct router leads only to an active laboratory branch.

Every forward weak arrow has a laboratory branch as source. By the active-branch stability established in Section 2, changing a choice at `L_i^1` can affect only its own output flag `b_i`, the corresponding hub branch, and its own **direct** router branch. It cannot affect any laboratory branch or any router that sends a payload to another laboratory. Thus all forward weak arrows leaving an active laboratory branch lead to terminal parts of the graph: hub branches or direct routers.

It follows that no active laboratory branch, hub branch, or direct router can lie on a directed cycle. A non-direct router cannot lie on a cycle either, because its only solid exit leads to an active laboratory branch and it has no forward choices. Therefore any forward-colored/solid closed walk lies entirely among the inactive laboratory branches `L_i^0`, where all arrows are weak and of the forward color. In particular no solid edge can lie in a recurrent strongly connected component.

The only nontrivial reversed choices occur at `D`. By the definition of the reverse-color arrows in the original branch graph, every reverse-colored arrow points **to** `D`. The node `D` is a sink and has no outgoing strong or forward weak arrows. Hence no reverse-colored arrow belongs to a closed walk.

Every closed walk is therefore monochromatic forward-weak. This proves the full weak-loops condition, including closed walks that traverse several simple cycles. Together with Section 6, the routed graph is valid under the original routed-graph definitions.

### 8. Contraction gives the desired process exactly

Fix computational basis values `o` of the reversed past and consider the reversed laboratory outputs in a sector tuple `q in tensor_j K_j^{b_j}`. The hub routes according to `x=w(b)`.

If `x=0`, no gate acts on any payload. If `x_i=1`, both other payloads reach `L_i^1`; its fixed preprocessor applies `A_i(o_i)^*` to those payloads. No other active preprocessor exists. Since every fixed gate preserves the flags, `D` assembles the result in the same `b` sector.

Because the nonidentity supports of all `A_i` are orthogonal, this payload transformation is precisely

    q -> V_o^* q.

The reversed past value `o_i` reaches its unknown laboratory as its input: the controlled preprocessor does not change that basis value. Thus the underlying fully open process tensor is exactly

    S^*: |o>_(reverse past) |q>_(reverse outputs)
          -> V_o^*|q>_(reverse future) tensor |o>_(reverse inputs).

Linearity gives the same identity on arbitrary quantum inputs and superpositions. Reversing all arrows/routes and taking adjoints of the fixed unitary fillings yields an exact routed realization of `S`. Bi-univocality and the weak-loops criterion are symmetric under this reversal; the colors interchange.

### Scope

This construction proves routed realizability of every tripartite orthogonal-support family, including noncommuting and entangling blocks in higher-dimensional sectors. Its mechanism uses one possible active laboratory branch and a purely classical hub, while all quantum payloads have terminal destinations. It does not require a flag to survive as an extra final register.

For four or more parties, pairwise orthogonal joint support projections need not admit the local two-flag envelope used in (1). The argument does not establish the corresponding all-N class theorem or the full routed-graph conjecture.

### Required proof qualifications

The branch-choice maps include dormant coordinates and degenerate local sectors. Weak-loop verification covers every closed walk, not only simple two-edge cycles; each laboratory filling is unitary on its full practical space.

<a id="rg-070"></a>

## RG-070 — Coded-cylinder routes

**Statement.** Coded-cylinder routes

**Status:** conditional positive construction. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### 1. The all-party theorem

Let `I=I1 tensor ... tensor IN`, with finite local dimensions d_i. Fix an orthonormal basis `B_i` of each input factor and an equally sized output label set. Let `C_i` be a subspace of `I_(bar i)` spanned by a subset `Y_i` of its computational product basis. Write f_i for its projector and

`F_i=I_i tensor f_i`.

Assume the F_i are pairwise orthogonal. They are *cylinders*: membership of a product-basis word in F_i is independent of its i-th coordinate. Put

`F_0=I-sum_i F_i`, `C_0=ran F_0`,

which is also computational-basis diagonal. Omit every zero-dimensional C_i or C_0 from the construction.

For each output label o_i, let a_i(o_i) be an arbitrary unitary on C_i. Extend it by the identity outside F_i and trivially on input i to obtain A_i(o_i). The unitary blocks

`V_o=F_0+sum_i [I_i tensor a_i(o_i)]F_i`                         (1)

define an ancillary-complete output-recording process

`S|p,o> = |o>_F V_o|p>_I`.

**Theorem.** Every process (1) has an explicit valid routed graph with full practical-space unitary fillings, the original boundaries, and each unknown laboratory operation used exactly once. The a_i may change individual local basis labels inside the code C_i; they need only preserve the joint code.

In particular the theorem applies whenever the actual nonidentity supports E_i admit pairwise orthogonal computational-diagonal cylinder envelopes `E_i<=F_i`. They need not themselves be diagonal or product projections.

### 2. Exact process equations

Orthogonality gives

`V_o V_o'^dagger = F_0+sum_i [I_i tensor a_i(o_i)a_i(o_i')^dagger]F_i`

`=I+sum_(i in D) ([I_i tensor a_i(o_i)a_i(o_i')^dagger]-I)F_i`,

where `D={i:o_i!=o_i'}`. Each summand is trivial on an input factor I_i with i in D. It is therefore annihilated by Q_D. This proves the exact output-recording PE criterion, including private ancillary extensions.

The graph below proves realizability independently of merely checking this criterion.

### 3. Construct the reversed process

For the reverse process, laboratory i takes the original output space O_i to the original input I_i. Denote its arbitrary unitary by W_i. The external past is the tensor product of the O_i, with quantum basis labels o_i; the external future is I.

There is one laboratory adapter A_i, one code hub H, and one final decoder D. The external past wire O_i enters A_i directly. The internal arrows are

`A_i -> H`, `H -> A_i`, `A_i -> D`, and `H -> D`.

Sector dimensions are as follows.

* `A_i -> H`: a one-dimensional null sector, and one one-dimensional sector for each basis label b_i in B_i.
* `H -> A_i`: a one-dimensional null sector and, if C_i is nonzero, one active sector of dimension r_i=dim C_i.
* `A_i -> D`: a one-dimensional null sector and, if C_i is nonzero, one active sector of dimension d_i r_i, identified with `I_i tensor C_i`.
* `H -> D`: a one-dimensional null sector and, if C_0 is nonzero, one active sector of dimension r_0=dim C_0.

The external output of D is the original unsectorized I. All assigned dimensions are positive.

#### Laboratory routes

The inactive branch `A_i^0` receives the null H input, sends one label b_i to H, and sends null to D. Its practical input has dimension d_i, and its practical output is the direct sum of d_i one-dimensional b_i sectors.

The active branch `A_i^1`, present only if C_i is nonzero, receives the active code sector from H, sends null to H, and sends the active `I_i tensor C_i` sector to D. Its practical input and output both have dimension d_i r_i. The whole own laboratory output on this branch stays quantum in the D-bound sector; it is not separately sectorized by b_i. Thus this branch has no forward bifurcation.

The two branches have disjoint input and output index sets.

#### Hub routes

For each nonzero C_i, hub branch `H_i` permits exactly these input tuples: its i-th input is null, while all other inputs have labels `b_(bar i) in Y_i`. Its unique output tuple activates the code sector on H->A_i and sets every other hub output to null.

Hub branch `H_0`, when C_0 is nonzero, permits input tuples with no null entries and full word `b in Y_0`, the computational basis support of F_0. Its unique output tuple activates H->D and sets every H->A_i to null.

Different H_i branches have their null entries at different positions; H_0 has none. Their input sets are disjoint. Their output tuples are also distinct, so these are branched relations.

#### Decoder route

D has one branch. Its input set consists of the tuples with exactly one active input: either the `I_i tensor C_i` sector from some active laboratory or the C_0 sector from H. Its output is the single external unsectorized label.

### 4. Bi-univocality

The only forward branch choices are the labels b_i at the inactive laboratory branches A_i^0. Prescribe all these choices, including those at branches that might not happen, to obtain a full word b.

If b belongs to a unique cylinder F_i, let H_i and A_i^1 happen and let every other laboratory use its inactive branch. This is consistent because membership of F_i is independent of b_i: the unused choice at A_i^0 does not affect the hub's test `b_(bar i) in Y_i`.

If b belongs to F_0, let H_0 happen and make all laboratories inactive. Since F_0,F_1,...,F_N are a partition, exactly one of these alternatives occurs.

Any global assignment must take one of these alternatives: a happening H_i forces exactly its i-th laboratory active and all others inactive, while H_0 forces all inactive. The hub's input restriction then gives exactly the membership test just described. Hence the augmented forward choice relation is total and single-valued.

For the reverse graph, the decoder's one branch chooses an active input i or 0. Choice i forces A_i^1 and H_i, and every other laboratory inactive. The prescribed reverse choice at H_i selects one word from Y_i and fixes all inactive laboratory output labels. Choice 0 forces H_0 and all laboratories inactive; its reverse choice selects one word from Y_0. All remaining routes have no reverse bifurcations. Thus the reverse choice relation is total and single-valued as well.

Consequently the graph is bi-univocal.

### 5. Weak loops

Every possible solid edge has one of the forms

`A_j^0 -> H_i`, `H_i -> A_i^1`, `A_i^1 -> D`,

or `A_j^0 -> H_0`, `H_0 -> D`.

Some displayed links may fail to be solid when their linking set is a single one-dimensional sector; allowing all of them only strengthens the argument. There is no solid edge from an active laboratory back to H: it sends the unique one-dimensional null value on that physical arrow. Likewise an inactive laboratory's D arrow and all inactive hub-to-laboratory arrows are null.

Only the branches A_j^0 have forward choices. All green arrows therefore start at an inactive laboratory branch.

In reverse, D's choice fixes every happening branch. The subsequent reverse choice of a basis word at H_i or H_0 only changes internal labels; it changes no happening branch. Thus the only reverse choices that influence branch happenings are those at D. Under the red-arrow convention every red arrow ends at D.

The vertices H_i can only lead through a solid arrow to A_i^1 and then D, or directly to D by a red arrow. Active laboratory branches have no forward choices and can only lead to D. H_0 and D cannot lie on directed loops. Therefore every recurrent branch component consists solely of inactive laboratory branches and green arrows. Every directed loop is weak and monochromatic, including loops with repeated vertices.

This proves weak loops. Together with bi-univocality, it proves validity of the routed skeleton.

### 6. Full practical-space unitaries

At H_i, map the direct sum of its one-dimensional input sectors `b_(bar i) in Y_i` to the corresponding computational basis of C_i. Both spaces have dimension r_i, so this is a full unitary. The analogous H_0 map is a full unitary on dimension r_0. Their direct sum fills H on its entire practical space.

At inactive A_i^0, apply W_i to the full external input O_i and identify its output I_i with the direct sum of basis-label sectors sent to H.

At active A_i^1, first apply

`sum_(o_i) |o_i><o_i| tensor a_i(o_i)^dagger`

on `O_i tensor C_i`, then apply `W_i tensor I_(C_i)`. Send the entire result in `I_i tensor C_i` to D. This is unitary on the full d_i r_i dimensional branch space. Combining both branches yields a one-slot superunitary on memory `C ⊕ C_i`, where the first summand is one-dimensional: it is a fixed controlled gate, one use of W_i, and fixed input/output identifications. No branch restricts W_i to a proper input subspace.

At D, use the orthogonal inclusion unitary

`C_0 direct_sum [direct_sum_i (I_i tensor C_i)] -> I`.

It is unitary on the entire practical input because its summands are exactly the ranges of F_0,F_1,...,F_N. The total dimension is dim I. Neither boundary contains an extra register or initialized ancilla.

Private ancillary extensions of W_i pass through these fixed branch identifications unchanged, establishing monopartite superunitarity of every laboratory wrapper.

### 7. The contraction is exactly the reversed process

Let `W=tensor_i W_i` and take a past basis word |o>. The H_0 branch contributes

`F_0 W|o>`.

For branch i, all inactive laboratories first supply the projection of their outputs onto C_i. The active adapter then applies a_i(o_i)^dagger on that code and W_i on its own input. Because F_i and a_i act trivially on input i, its contribution is

`[I_i tensor a_i(o_i)^dagger] F_i W|o>`.

The decoder sums these orthogonal sector contributions, giving

`[F_0+sum_i (I_i tensor a_i(o_i)^dagger)F_i] W|o>`

`=V_o^dagger W|o>`.

This is precisely the contraction of S^dagger with the arbitrary reversed laboratory operations W_i. Reversing the entire valid routed graph therefore realizes S. Reversing each one-slot wrapper gives fixed unitary adapters around one use of the original operation; no inverse-oracle access is assumed.

### 8. Finite graph checks

The separate checker check_coded_cylinder_routes.py examined 145 cylinder families with one through five laboratories, including unequal local dimensions, empty code sectors, residual sectors, and the four-GHZ partition. It checked 1,792 forward assignments and 1,103 reverse assignments. Every choice relation was single-valued and total, every decoder dimension matched the original input dimension, and no solid or reverse-colored edge belonged to a closed walk, even using a superset of possible solid edges.

For the four-GHZ example, the coded graph has 13 branches, a 20-edge solid superset, 36 forward-weak edges, and 12 reverse-weak edges. These are finite falsification checks with a fixed random seed; the proof establishes the arbitrary-N claim independently.

### 9. Scope

The construction works for any number of parties and arbitrary finite local dimensions, whenever pairwise orthogonal computational-diagonal cylinder envelopes exist. It allows arbitrary noncommuting and entangling gates within the joint code payloads, including gates that change every individual local basis flag.

Every three-party orthogonal-support family has such envelopes by the local-support lemma in [RG-074: Higher-dimensional cube structure](higher-order.md#rg-074). The four-GHZ family in [RG-071: Four-party orthogonal support geometry](positive-routes.md#rg-071) has parity-code envelopes and is therefore routed by this theorem too.

A common product-basis cylinder-envelope presentation is not automatic for general orthogonal supports: Section7 of [RG-071: Four-party orthogonal support geometry](positive-routes.md#rg-071) gives a five-party obstruction using three Bell sectors on a joint spectator pair. This is an obstruction to the present hypothesis, not to routing. The theorem also neither assumes nor establishes that every unitary process admits an orthogonal-support form.





**Reproduction limit:** supporting helpers were not supplied; the analytic argument remains available. See the [artifact map](../REPRODUCIBILITY.md#rg-070).

<a id="rg-071"></a>

## RG-071 — Four-party orthogonal support geometry

**Statement.** Four-party orthogonal support geometry

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### 1. Explicit four-qubit process

All four local input and output spaces are qubits. The global past and future each have dimension16, and the output-recording process unitary has dimension256:

`S|p,o> = |o>_F V_o|p>_I`, `o in {0,1}^4`.

For a three-bit word s define

`|g_s>=(|s>+|bar s>)/sqrt(2)`.

Set the four projections

`E_1=I1 tensor |g_000><g_000|_(234)`,

`E_2=I2 tensor |g_001><g_001|_(134)`,

`E_3=I3 tensor |g_010><g_010|_(124)`,

`E_4=I4 tensor |g_001><g_001|_(123)`.

Tensor factors in parentheses are ordered increasingly. Each E_i has rank2, is trivial on input i, and is nonzero.

For arbitrary real angles theta_i define

`A_i(o_i)=I+(exp(i theta_i o_i)-1)E_i`,

`V_o=product_i A_i(o_i)`.

The exact integer test case takes every theta_i=pi, so

`V_o=I-2 sum_i o_i E_i`.                                        (1)

### 2. Orthogonality certificate

A GHZ-pattern vector |g_s> is an eigenvector of each two-qubit parity Z_kZ_l, with sign `(-1)^(s_k+s_l)`. For every pair E_i,E_j, the following shared parity has opposite signs on their ranges:

| Supports | Shared parity | Sign on first | Sign on second |
|---|---|---:|---:|
| E1,E2 | Z3 Z4 | +1 | -1 |
| E1,E3 | Z2 Z4 | +1 | -1 |
| E1,E4 | Z2 Z3 | +1 | -1 |
| E2,E3 | Z1 Z4 | -1 | +1 |
| E2,E4 | Z1 Z3 | +1 | -1 |
| E3,E4 | Z1 Z2 | -1 | +1 |

Therefore E_iE_j=0 for every i!=j. They are orthogonal global supports of total rank8.

For any two output words, with `D={i:o_i!=o_i'}`, orthogonality gives

`V_o V_o'^dagger
 =I+sum_(i in D) (exp(i theta_i(o_i-o_i'))-1)E_i`.

Every summand is trivial on an input factor i belonging to D. Thus

`Q_D(V_o V_o'^dagger)=0`

for all distinct words. This proves exact ancillary-complete process validity for all real angles theta_i, not only the integer test case.

### 3. What fails beyond the three-party local-envelope lemma

Each three-qubit GHZ vector has full-rank one-qubit reduced states. Consequently none of its rank-one projections is contained in a nontrivial tensor-product projection across those three inputs. If

`|g_s><g_s| <= R_j tensor R_k tensor R_l`,

then every R must be the identity, by its full reduced support. Hence the four E_i cannot be separated using orthogonal *product projections* on individual inputs, as the three-party local-support proof did.

This is not absence of all classical envelopes. Define the larger parity-code projectors

`f_i=|s_i><s_i|+|bar s_i><bar s_i|` on the complementary triple,

`F_i=I_i tensor f_i`.

The same parity certificate makes the F_i pairwise orthogonal. Each has rank4 globally, so

`sum_i F_i=I16`.                                                 (2)

These are computational-basis diagonal cylinders, although they are not tensor products of individual-input projections. The E_i lie inside them.

For theta_i=pi, A_i acts on the two-dimensional code `C_i=span{|s_i>,|bar s_i>}` as the logical unitary -X: it swaps the two code words and adds a minus sign. Thus it changes all three individual local flags while preserving their joint parity code. A route that assumed each local flag remained fixed would not apply directly.

### 4. Complete influence and entanglement

When theta_i is nonzero modulo 2pi, output i changes every other input algebra: the GHZ projection on the other three qubits does not commute with the full matrix algebra of any one of them. The exact theta_i=pi test has all12 possible directed influence edges. There is no influence source or sink.

Its normalized blocks commute, because the E_i are orthogonal. Nevertheless they are not simultaneously diagonal in a product input basis. Otherwise each spectral projector E_i of the nontrivial block V_(e_i)=I-2E_i would be product-basis diagonal; after dropping the identity factor i, its rank-one GHZ projector would have to project onto a product basis vector, which is impossible.

In particular this family involves entangling controlled blocks and genuinely entangled support projectors. Its four nonzero supports avoid the simpler two-support example with the remaining parties terminal. These properties distinguish structural models; they do not imply a failure of routed realizability.

### 5. The coded-cylinder theorem routes this example

The explicit full graph is proved in [RG-070: Coded-cylinder routes](positive-routes.md#rg-070). It applies in any number of parties when the nonidentity supports have pairwise orthogonal computational-diagonal cylinder envelopes. Equations (2) provide exactly those envelopes here, with every code C_i two-dimensional and no residual sector.

In its reversed construction, inactive laboratory branches send output basis labels to a code hub. Hub branch i receives the three complementary output labels in the code pair `{s_i,bar s_i}`, coherently compresses that two-dimensional code, and sends it to the active laboratory i. The active branch applies the past-o_i-controlled logical phase gate on the code, then uses its own unknown operation once. Its own output and processed code go directly to the future decoder.

The decoder uses the exact orthogonal decomposition

`direct_sum_i (I_i tensor C_i) = I16`.

Every hub branch has dimension2 on both sides; each active laboratory branch has dimension4 on both sides; each inactive branch has dimension2 on both sides. The decoder is a full dimension16 unitary. No initialized boundary register or discarded future system occurs.

The unique active branch follows from the partition of basis words by the four cylinders. Only inactive laboratory branches have forward choices. All solid paths flow from inactive laboratories through a hub branch to an active laboratory and then the decoder; all reverse weak arrows end at the decoder. Hence any recurrent component consists only of inactive branches with green arrows. The coded-hub theorem supplies the complete bi-univocality, weak-loops, and exact-contraction proof.

Thus this four-party entangled-support family **is routed**. It is a positive extension of the construction, not a conjecture counterexample.

### 6. Exact verification

`check_four_party_orthogonal_support.py` builds all sixteen integer blocks of (1), checks their unitarity, and checks every one of the120 distinct relative-block PE equations using scaled integer erasure maps. Every resulting PE matrix is exactly zero.

It also verifies all12 actual influence edges using conjugated local Pauli generators, checks commutation of all normalized blocks, and verifies the rank4 parity-code envelopes partition the full16-dimensional input space. Twelve independent random local-unitary tuples give evaluated-unitarity error below `1.56e-15`. The certificate is saved in `four_party_orthogonal_support_checks.json`.

### 7. Remaining boundary

The three-party support theorem always supplies local cylinder envelopes. At four and more parties, orthogonality only separates supports on joint complementary systems. The present GHZ family still has the larger classical parity-code envelopes and is therefore covered by the new theorem.

The cylinder-envelope condition is a real restriction. For five qubit inputs, take three distinct Bell states beta_1,beta_2,beta_3 on inputs4,5 and set

`E_i=I_(123) tensor |beta_i><beta_i|_(45)` for i=1,2,3,

`E_4=E_5=0`.

These supports are orthogonal and each is trivial on its own input. In any product basis on inputs4,5, every Bell state has at least two nonzero coefficients because it is entangled. Three such support sets cannot be pairwise disjoint inside the four basis outcomes. The identity on inputs1,2,3 prevents using those factors to separate the supports. Hence no pairwise orthogonal computational-diagonal cylinder envelopes exist in any product basis. This is a strict obstruction to the new theorem's hypothesis, not to routing; these joint-spectator sectors can be handled by familiar controlled-order constructions with the spectator laboratories afterward.

The remaining problem is therefore to route general quantum orthogonal supports without assuming classical cylinder envelopes, and ultimately to extract a useful decomposition from processes lacking an orthogonal-support form. No non-realizability conclusion follows from the four-GHZ example or this five-party scope check.





**Reproduction limit:** supporting helpers were not supplied; the analytic argument remains available. See the [artifact map](../REPRODUCIBILITY.md#rg-071).

<a id="rg-072"></a>

## RG-072 — Quantum-support geometry and the envelope boundary

**Statement.** Quantum-support geometry and the envelope boundary

**Status:** source-level result. **Scope:** Full-local-rank GHZ-code route and the stated degenerate envelope obstruction; an envelope failure alone is not a universal no-host proof.

### 1. Full-local-rank pure complementary supports are forced into GHZ codes

Suppose

`E_i=I_i tensor |psi_i><psi_i|_(bar i)`

are pairwise orthogonal and every three-qubit vector psi_i has rank2 on each individual qubit. Thus each E_i has the smallest possible nonzero global rank2.

**Theorem.** There are local orthonormal input bases in which the four vectors have the forms

`psi_1 = alpha_1 |000>_(234)+beta_1 |111>_(234)`,

`psi_2 = alpha_2 |001>_(134)+beta_2 |110>_(134)`,

`psi_3 = alpha_3 |010>_(124)+beta_3 |101>_(124)`,

`psi_4 = alpha_4 |001>_(123)+beta_4 |110>_(123)`,                 (1)

with every alpha_i,beta_i nonzero. Phases and unequal coefficient magnitudes are allowed. The orthogonal parity-code cylinder envelopes of (1) partition the full input space. Consequently every supported phase-block process is routed by the coded-cylinder theorem.

The proof distinguishes generalized rank-two tensor decompositions from decompositions in orthonormal local bases. Orthogonality of those bases is a conclusion below, not an assumption.

### 2. A self-contained two-dimensional matrix-pencil dichotomy

For any pure three-qubit vector with rank2 on every qubit, its support on a pair of qubits is a two-dimensional subspace P of two-by-two matrices. A vector in P is product exactly when its matrix determinant vanishes.

Choose a basis A,B for P. The homogeneous quadratic `det(sA+tB)` is not identically zero. Otherwise every matrix in P would have rank1; two independent rank-one matrices with a rank-one sum must share a left or right factor, forcing one qubit's reduced state to have rank1, contrary to the hypothesis.

There are two possibilities.

* If the determinant polynomial has two distinct projective roots, P is spanned by two product vectors `a_k tensor a_l` and `b_k tensor b_l`. Both local pairs are linearly independent; otherwise one local reduced rank would be1. The full vector can therefore be written

  `psi=alpha a_j a_k a_l+beta b_j b_k b_l`,

  with all three local pairs linearly independent and alpha,beta nonzero. These pairs need not yet be orthogonal.

* If there is one double root, put its unique product vector into |00> using local orthonormal bases. Taking this as the first basis matrix, the other basis matrix M obeys

  `det(s|0><0|+tM)=s t M_11+t^2 det(M)`.

  A double root at t=0 forces M_11=0 and det(M)!=0, so both off-diagonal entries are nonzero. Subtracting the |00> term gives

  `P=span{|00>, u|01>+v|10>}`, `u v!=0`.

  Choosing the remaining qubit's orthonormal basis along the coefficient vector multiplying the second term puts the full state into the vacuum-plus-W form

  `psi=a|000>+b|100>+c|010>+d|001>`, `b c d!=0`.              (2)

This elementary pencil argument supplies all needed cases without invoking a classification under nonunitary local transformations.

### 3. The W case is incompatible with the other orthogonal supports

Apply the dichotomy to psi_1 on inputs234. Suppose it has form (2). Its pair34 support is

`span{|00>, c|10>+d|01>}`,

and its pair24 support is

`span{|00>, b|10>+d|01>}`.

For E_1E_2=0, the positive reduced support of psi_2 on34 must be orthogonal to the first of these spaces. Since psi_2 has local rank2 on input1, that support has dimension2 and is the exact orthogonal complement. Similarly for psi_3 on24. Thus write

`psi_2=v_1|11>_(34)+w_1(r|01>+s|10>)_(34)`,

`psi_3=v'_1|11>_(24)+w'_1(r'|01>+s'|10>)_(24)`,

where r,s,r',s' are all nonzero and v_1,w_1 are linearly independent. Also w'_1 is nonzero. These facts use exactly the stated full-local-rank assumptions.

The support of psi_2 on14 contains

`w_1 tensor |1>`, `v_1 tensor |1>+s w_1 tensor |0>`,

up to nonzero scalar factors. The support of psi_3 on14 contains `w'_1 tensor |1>`. Orthogonality E_2E_3=0 therefore forces

`<w_1,w'_1>=0`, `<v_1,w'_1>=0`.

Since v_1,w_1 span the two-dimensional input1, this gives w'_1=0, a contradiction. Hence the W case is excluded.

### 4. Orthogonality forces the generalized-GHZ local pairs to be orthogonal

We therefore have

`psi_1=alpha a_2 a_3 a_4+beta b_2 b_3 b_4`,

where each a_k,b_k is a linearly independent pair, not assumed orthogonal.

The orthogonal complement of

`span{a_k tensor a_l, b_k tensor b_l}`

is exactly

`span{a_k^perp tensor b_l^perp, b_k^perp tensor a_l^perp}`.

Both displayed product vectors are orthogonal to both original vectors and are linearly independent, proving this two-dimensional complement formula.

Consequently

`psi_2=c_1 a_3^perp b_4^perp+d_1 b_3^perp a_4^perp`,

`psi_3=e_1 a_2^perp b_4^perp+f_1 b_2^perp a_4^perp`,

with c_1,d_1 independent and e_1,f_1 independent. Their pair14 supports are

`span{c_1 tensor b_4^perp, d_1 tensor a_4^perp}`,

`span{e_1 tensor b_4^perp, f_1 tensor a_4^perp}`.

If `<a_4^perp,b_4^perp>` were nonzero, orthogonality of these subspaces would force e_1 orthogonal to both c_1 and d_1, impossible. Thus a_4 and b_4 are orthogonal. Applying the same argument to the pairs E_2,E_4 and E_3,E_4 makes a_3,b_3 and a_2,b_2 orthogonal as well.

Choose these orthonormal pairs as the local bases on234. Then

`psi_1=alpha_1|000>+beta_1|111>`.

The other three vectors have the forms

`psi_2=c_1|01>_(34)+d_1|10>_(34)`,

`psi_3=e_1|01>_(24)+f_1|10>_(24)`,

`psi_4=g_1|01>_(23)+h_1|10>_(23)`.

The remaining pairwise orthogonality conditions give

`c_1 perpendicular e_1`, `d_1 perpendicular f_1`,

`c_1 perpendicular h_1`, `d_1 perpendicular g_1`,

`e_1 perpendicular g_1`, `f_1 perpendicular h_1`.

In two dimensions these imply e_1 parallel h_1, f_1 parallel g_1, and e_1 perpendicular f_1. Hence c_1 perpendicular d_1, with c_1 parallel f_1,g_1 and d_1 parallel e_1,h_1. Choosing c_1,d_1 as the orthonormal directions on input1 yields exactly (1), after absorbing scalar coefficients.

This completes the full-local-rank theorem. Every degeneracy excluded in the argument was one of the explicitly assumed local rank2 conditions.

### 5. Exact coded route for the full-rank class

Replace each rank-one psi_i projector in (1) by the rank-two projector onto its two computational codewords. The resulting cylinder F_i=I_i tensor f_i has global rank4. The six opposite shared-parity signs are those already listed in [RG-071: Four-party orthogonal support geometry](positive-routes.md#rg-071), so the F_i are orthogonal and sum to I16.

Every phase gate on E_i preserves this code, even when alpha_i and beta_i are unequal. [RG-070: Coded-cylinder routes](positive-routes.md#rg-070) therefore gives a full-practical-space valid routed graph. This proves that the entire full-local-rank, rank2-support four-qubit sector is routed; the previously exhibited balanced GHZ quartet is only one instance.

### 6. Dropping full local rank produces a genuine envelope obstruction

Let `|+>=(|0>+|1>)/sqrt(2)`, `|->=(|0>-|1>)/sqrt(2)`, and `|Phi+>=(|00>+|11>)/sqrt(2)`. Define

`psi_1=|0>_2 tensor |Phi+>_(34)`,

`psi_2=(|0>_1|0>_3|1>_4 + |1>_1|->_3|+>_4)/sqrt(2)`,

`psi_3=|0>_1|1>_2|0>_4`,

`psi_4=|1>_1|1>_2|+>_3`,

and again `E_i=I_i tensor |psi_i><psi_i|`.

All four supports are nonzero and have global rank2. Their orthogonality can be verified without numerical calculation:

* E1,E2: the shared34 support of psi_2 is `C=span{|01>,|-+>}`, orthogonal to Phi+.
* E1,E3 and E1,E4: input2 has opposite fixed values0 and1.
* E2,E3: the shared14 support of psi_2 is `span{|0,1>,|1,+>}`, orthogonal to the fixed `|0,0>` of psi_3.
* E2,E4: the shared13 support of psi_2 is `span{|0,0>,|1,->}`, orthogonal to the fixed `|1,+>` of psi_4.
* E3,E4: input1 has opposite fixed values0 and1.

#### No common product-basis cylinder envelopes

Already E1 and E2 cannot be put inside orthogonal computational-diagonal cylinders in any product input basis. Because E1 is identity on input1 and E2 identity on input2, neither of those factors can separate their overlapping support. Such envelopes would require disjoint coordinate supports on34 for

`|Phi+>` and `C=span{|01>,|-+>}`.

In any product basis on34, the entangled Phi+ has at least two nonzero coordinates. The dimension-two space C also needs at least two coordinates. Disjoint supports among four coordinates would therefore require each support to have exactly two entries. Since Phi+ is entangled, its two entries occupy opposite corners of the two-by-two basis grid. The other two corners are then an orthogonal pair of product basis vectors spanning C.

But C has exactly two product rays, namely `|01>` and `|-+>`. Indeed its two spanning product vectors have linearly independent local factors, so the determinant of a general linear combination vanishes only when one coefficient is zero. Those two product rays have nonzero overlap of magnitude1/2. They cannot be an orthogonal product basis pair. This contradiction proves the absence of any common product-basis cylinder-envelope presentation.

This is stronger than failure of tensor-product projector envelopes: it excludes the full coded-cylinder hypothesis even after arbitrary local basis changes.

### 7. Exact valid process and present routing status

Taking theta_i=pi gives

`V_o=I-2 sum_i o_i E_i`.

Its matrix entries are rational. The verification script `check_degenerate_support_round4.py` uses a common integer scaling, verifies all120 relative-block PE equations exactly, and checks actual input-algebra influence. Every output influences all three other inputs, so the full graph has all12 possible directed edges and no source or sink.

Thus the degenerate quartet gives a finite, exact valid orthogonal-support process beyond the proven common-basis cylinder route. This envelope argument alone does not establish nonroutability. For the explicit quartet, the complete exact-host obstruction is [RG-001](obstruction.md#rg-001).

### 8. A normal form whenever one support is biseparable but not product

There is a further exact reduction of the degenerate case. Suppose all four
supports are nonzero and, after relabelling parties,

`psi_1=|0>_2 tensor chi_(34)`,

where chi has Schmidt rank2. No hypothesis is imposed on the other three
vectors' local ranks.

The reduced support of psi_1 on24 is `|0>_2 tensor I_4`. Orthogonality
E1E3=0 therefore forces psi_3 to factor as `|1>_2 tensor eta_(14)`.
Likewise E1E4=0 forces `psi_4=|1>_2 tensor zeta_(13)`.

Now E3E4=0 says that the reduced supports of eta and zeta on input1 are
orthogonal. Both are nonzero and input1 has dimension2, so both supports
have rank1 and are opposite directions. Choose these as the basis on1.
There are unit vectors d on4 and e on3 such that

`psi_3=|0>_1|1>_2|d>_4`,

`psi_4=|1>_1|1>_2|e>_3`.                                  (4)

Thus one genuinely biseparable support forces the two supports opposite
its entangled factors to be fully product.

Finally E2E3=0 kills the `|0>_1|d>_4` component of psi_2, while E2E4=0
kills its `|1>_1|e>_3` component. Hence

`psi_2=|0>_1|v>_3|d^perp>_4
       +|1>_1|e^perp>_3|w>_4`,                            (5)

where v and w may be unnormalized or zero. Orthogonality E1E2=0 is
exactly the two scalar conditions

`<chi|v,d^perp>=0`, `<chi|e^perp,w>=0`.                    (6)

Conversely, any normalized nonzero vectors of the forms (4)–(6), with
chi entangled, give pairwise orthogonal E_i. All six orthogonality
relations were used above or are immediate from the opposite input2
and input1 labels. Thus these formulas are a complete normal form under
the stated biseparable hypothesis.

For fixed entangled chi and fixed d,e, each of the two kernels in (6) is
one-dimensional, because the coefficient matrix of chi is invertible.
Consequently v and w are determined as rays, with only their relative
weight and phase still free. The explicit non-cylinder quartet in
Section6 is the case chi=Phi+, d=|0>, e=|+>, and equal weights.

This reduces the genuinely biseparable frontier to a controlled-basis
two-term family. It does not yet provide a routed construction for that
whole family, nor does it cover configurations with only full-rank and
fully product complementary vectors.

### 9. Exact boundary of the coded-envelope hypothesis in this normal form

Let C be the shared34 support of psi_2 in (5). Thus C is spanned by the
nonzero vectors among `v tensor d^perp` and `e^perp tensor w`.

**Proposition.** If dim C=2, this quartet admits common product-basis
orthogonal cylinder envelopes if and only if

`v parallel e`, `w parallel d`.                           (7)

If dim C=1, it always admits such envelopes.

For necessity when dim C=2, E1 is identity on1 and E2 is identity on2.
Any orthogonal diagonal-cylinder envelopes would therefore need disjoint
product-basis coordinate supports on34 for chi and C. The entangled chi
needs at least two coordinates, and C needs at least two. Both supports
must consequently use exactly two of the four coordinates. The two
coordinates of chi occupy opposite corners, so C is spanned by the two
remaining, opposite product-basis corners.

The two spanning product rays of C have linearly independent factors on
both3 and4. Indeed, if a factor pair were dependent while dim C=2, C
would be a fixed factor tensored with the entire other qubit; its
orthogonal complement could not contain the entangled chi. A
two-dimensional span of two product vectors with independent factors on
both sides has precisely those two product rays, by its determinant
pencil. Therefore those rays must be the two opposite product-basis
corners just found. Their factors must be orthogonal on each qubit,
which is exactly (7).

Conversely, under (7), conditions (6) place chi in

`span{e tensor d, e^perp tensor d^perp}`.

Use the bases e,e^perp on3 and d,d^perp on4. The following four cylinder
envelopes are computational-diagonal and pairwise orthogonal:

`F1=I1 tensor |0><0|2 tensor proj span{e d,e^perp d^perp}`,

`F2=I2 tensor proj span{|0>1 e3 d^perp4, |1>1 e^perp3 d4}`,

`F3=I3 tensor |0,1,d><0,1,d|_(124)`,

`F4=I4 tensor |1,1,e><1,1,e|_(123)`.

They have global ranks4,4,2,2 and contain E1,E2,E3,E4. The remaining
rank4 space is a valid residual sector. This gives the asserted coded
route when dim C=2 and (7) holds.

There are two cases with dim C=1. If both terms of (5) are nonzero,
their product vectors must be parallel; hence
`v parallel e^perp` and `w parallel d^perp`. Take

`F1=I1 tensor |0><0|2 tensor (I34-|e^perp,d^perp><e^perp,d^perp|)`,

`F2=I12 tensor |e^perp,d^perp><e^perp,d^perp|34`,

and retain F3,F4 above. Conditions (6) ensure E1<=F1. These envelopes
have ranks6,4,2,2 and are pairwise orthogonal in the displayed bases.

If only the first term of (5) is present, normalize v and instead take

`F1=I1 tensor |0><0|2 tensor (I34-|v,d^perp><v,d^perp|)`,

`F2=|0><0|1 tensor I2 tensor |v,d^perp><v,d^perp|34`,

`F3=|0><0|1 tensor |1><1|2 tensor I3 tensor |d><d|4`,

`F4=|1><1|1 tensor |1><1|2 tensor I34`.

Their ranks are6,2,2,4. Each contains the corresponding actual support,
and every pair is separated by an explicitly orthogonal local label or
by the excluded34 coordinate. The second-term-only case is symmetric.
This proves the proposition, including the degenerate weights.

Consequently the unresolved biseparable family has an exact description:
dim C=2 and its two product rays use incompatible local bases. The
existence of that incompatibility is an obstruction only to the coded
envelope construction. It is not an obstruction to all routed graphs.





**Reproduction limit:** supporting helpers were not supplied; the analytic argument remains available. See the [artifact map](../REPRODUCIBILITY.md#rg-072).

<a id="rg-073"></a>

## RG-073 — Complete native substitution on physical cylinders

**Statement.** Complete native substitution on physical cylinders

**Status:** source-level result. **Scope:** Orthogonal physical cylinders and their specified complete replacements; not arbitrary encoded carriers.

### 1. Cylinder data and the explicit process

Let H=tensor_i H_i, with dim H_i=d_i, and let S_i be pairwise orthogonal
projections satisfying

    [S_i, L(H_i) tensor I_bar_i]=0.

Thus S_i=I_i tensor s_i is a physical cylinder for its own query. Put
R=I-sum_i S_i. For nonzero S_i, the native input algebra at port i is

    B_i=L(S_i H) directsum L(H_i).

Write its independent entries as A_i directsum b_i, with A_i embedded as
S_i A_i S_i in L(H). Omit a zero active summand. Define

    G((A_i directsum b_i)_i)
       =sum_i [product_(j!=i) b_j] A_i
          +[product_j b_j] R.                         (1)

Every b_j acts on its original tensor factor. The full native A_i is an
arbitrary matrix on S_i H, not just an embedded original M_(d_i) family.
Then G is normalized, complex multilinear in the native algebra variables,
and independently completely unitary preserving on the SAME boundary H.

### 2. Direct proof, including independent ancillas

For passive unitary fillings put W=product_j b_j. Since the physical b_j
commute for different j, W* product_(j!=i)b_j=b_i*. Thus, on unitary tuples,

    W*G=R+sum_i b_i* A_i.                             (2)

Both b_i and A_i preserve S_i H. Each b_i* A_i is a unitary on that
carrier and vanishes on its orthogonal complement. Equation(2) is therefore
a unitary block diagonal operator for the FIXED orthogonal partition
R,S1,...,SN. Since W is unitary, so is G.

For independent private ancillary spaces K_i, enlarge each original local
factor H_i by its own K_i when evaluating passive b_i. The different b_i
still commute. Amplify each S_i by the identities on all K_j. It commutes
with the arbitrary local b_i because it is trivial on H_i and all private
spaces. The active A_i can be ANY unitary on S_i H tensor K_i and is
amplified by the other ancillary identities. It preserves the same S_i
carrier. Thus (2) is still a unitary direct sum, proving precisely the
independent complete native-filler quantifiers.

The polynomial (1), not the factorization (2), is the definition of G.
It contains each native variable once: a term indexed by i uses A_i and
the passive b_j at every other port, and the R term uses all b_j. The
adjoints b_i* in (2) are only a norm-proof device. No inverse unknown
query operation, additional query, or proposed implementation using W*
is inferred. At all native identities the polynomial is R+sum_i S_i=I.

### 3. Ordinary-query restrictions and a common moving output partition

For each i choose any unital representation
rho_i:L(H_i)->L(S_i H). Such representations are dimensionally possible
because rank S_i is a multiple of d_i. Substitution

    x_i -> rho_i(x_i) directsum x_i

gives an actual complete process on the original ports, explicitly

    F_rho(x)=sum_i [product_(j!=i)x_j]rho_i(x_i)
                    +[product_j x_j]R.              (3)

This is a restriction of the complete native theorem, not an additional
unitary-preserver assumption on the choices rho_i. In the aligned case
rho_i(x)=x_i S_i, (3) is the ordinary tensor product of all queries.
Nontrivial internal representations on the S_i give different processes.

For unitary passive fillings the output column projections in (1) are

    [product_(j!=i)b_j] S_i [product_(j!=i)b_j]*
       =W S_i W*,                                    (4)

because b_i preserves S_i. The residual output is W R W*. Thus all output
columns undergo the SAME product conjugation. Their joint orthogonality is
immediate from the input partition, and does not depend on the active A_i.

This common covariance is stronger information than separate isometry of
the columns. It is still not a fixed native output-sector partition: W
contains the arbitrary passive unknown queries. Uncomputing this movement
with W* would not supply a one-use routed realization.

There are two precise elementary constraints on such a realization. First,
the full coefficient span of G is all L(H): the aligned restriction above
is the ordinary product W, whose product matrix units span L(H). Hence
there is no nonzero proper pair of fixed input/output projections with
G(native) P_in=P_out G(native) for all native matrices. Indeed spanning
extends that identity to every operator, its identity instance gives
P_in=P_out, and commutation with all of L(H) makes that projection scalar.

Second, no nonzero proper active-column label can persist as a fixed
future sector for all passive fillings. The linear span of
{U_bar_i(b) S_i H: all passive unitary b} is all H. To see this, write
S_i=I_i tensor s_i with s_i nonzero. Product unitaries on the other factors
linearly span their full matrix algebra, whose orbit of any nonzero vector
in ran s_i spans H_bar_i. Tensoring with the complete H_i factor proves
the assertion. Thus any fixed future projection containing this entire
orbit would have to be I. This excludes precisely the proposed architecture
that keeps each active input label in its own fixed proper future sector;
it does not exclude intermediate branch changes or a genuinely cyclic host.

### 4. The concrete quartet specialization

The four projections in
[RG-015: Joint quartet column promotion](serial-interfaces.md#rg-015) are physical cylinders:

    S1=I1 P0_2 Cperp_34,                             rank4,
    S2=I2 proj span{|0,0,1>,|1,-,+>}_134,             rank4,
    S3=E3, S4=E4,                                   ranks2,2.

They are pairwise orthogonal and leave rank4. That source's explicit joint
native tensor is exactly (1), and the original quartet is exactly (3) with
rho_i(x)=R_i x_i R_i restricted to S_i. Therefore the same joint extension
has two independent complete proofs: direct orthogonal-cylinder validity
here, and replacement of the original actual process's serial columns.

The exact helper `check_quartet_joint_serial_promotion_round35.py` verifies
the cylinder commutations and supports and includes an independent-ancilla
example with all five output projections orthogonal. The source proof is
uniform in all dimensions and private ancillas; no finite sampling is used
to establish that uniformity.

### 5. The remaining geometric problem

A general route theorem for (1) would give a route for this quartet by the
specified original-query substitution, subject to checking the native
substitution/unfolding interface. Such a theorem is NOT proved here.
The geometric input is now explicit: orthogonal own-query cylinders S_i
and a residual R, with full native matrix freedom on each active cylinder.

The missing step is a finite routed mechanism that realizes the common
moving output partition (4), with each port used once and all native
fillers and internal edge insertions independently allowed. A fixed
ordinary serial path for each input label alone does not specify this
recombination. Neither a prepared classical copy of that label that is
left over at the boundary, nor an inverse use of W, is an allowed shortcut
to the original-boundary one-use problem.

The theorem provides complete process validity for a broad explicit class.
It does not make complete validity synonymous with routed-graph validity,
claim unrestricted universality, or exclude a genuinely cyclic host.





**Reproduction limit:** supporting helpers were not supplied; the analytic argument remains available. See the [artifact map](../REPRODUCIBILITY.md#rg-073).
