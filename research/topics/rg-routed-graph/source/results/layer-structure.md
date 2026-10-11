# Layer structure

[Topic index](../../README.md) · [Shared result index](../../../../RESULTS.md#rg--exact-native-routed-graph-universality)

Each result below has one owner. Exact scope and proof are updated here. Source-level mathematical arguments and finite certificates are distinguished from a new formal verification.

<a id="rg-018"></a>

## RG-018 — Reachable native branch capacity

**Statement.** Reachable branches remain represented at every native context; multiplicities are constant and obey the boundary capacity bound.

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### 1. Precise model

Let a finite routed tensor network have external input and output spaces
of the same dimension D>0. Each native node v has a branched route whose
b-th practical input and output spaces have equal positive dimension
n_(v,b). Choose a fixed unitary identification between them. Its full
allowed filler algebra is

    A_v=direct_sum_b M_(n_(v,b)).                        (1)

The skeletal contraction F of the network is complex multilinear in all
native fillers. Assume it sends every tuple of full native unitaries to
a unitary between the external spaces, also after independent private
matrix-ancilla amplifications. No auxiliary filling is fixed when imposing
this universal premise. Bi-univocal weak-loop graphs have this property by
the original routed superunitary theorem. The result below also applies
whenever this complete-unitarity premise is established in another way.

A branch is reachable if a globally consistent assignment of wire sector
indices selects it and all sectors on that assignment have positive
dimension. Reachability is a property of the full skeleton, before any
native auxiliary unitaries are specialized. External boundary legs are
part of the consistency assignment; we do not trace out an unspecified
additional environment or postselect an external state.

### 2. Multiplicity at every context

Fix a node v and a tuple u of full unitaries at all other native nodes.
After identifying the external spaces, right-normalize by

    pi_u(a)=F(a,u) F(1,u)*.                              (2)

Then pi_u is a unital *-homomorphism. For every branch b there is an integer
m_(v,b)>=0, independent of u, such that

    rank pi_u(e_b)=n_(v,b) m_(v,b),
    sum_b n_(v,b) m_(v,b)=D.                             (3)

This is the audited general native multiplicity theorem
[RG-018: Reachable native branch capacity](layer-structure.md#rg-018). For completeness, a
unital map preserving unitaries and their private M2 amplifications is
multiplicative by the square identity on [[0,a],[a',0]]. Its central
idempotents therefore map to orthogonal projections. Their ranks are
constant on the connected product of all other native unitary groups.
The rank of a represented M_n central summand is n times its multiplicity.

If m_(v,b)=0, then F(a,u)=0 for every a in that summand and every unitary
tuple u. Unitaries linearly span each finite direct sum of matrices, so
multilinearity makes the entire corresponding tensor coefficient family
zero, including at arbitrary nonunitary matrices at every other node.

### 3. Reachability cannot cancel coefficientwise

Every reachable branch has m_(v,b)>=1.

Proof. Choose one globally consistent sector assignment selecting b.
Choose one basis vector in each selected nonzero wire sector. At each
native node choose the single matrix unit which maps the tensor product
of these selected incoming basis vectors to the tensor product of the
selected outgoing basis vectors, in the selected branch; set all other
native branch blocks to zero. These are allowed matrix-algebra inputs for
a coefficient test, although generally not unitary fillers.

Every node matrix unit fixes all basis labels on its incident wires.
Thus the contraction has one compatible quantum basis assignment on every
wire incident to a node, of amplitude one. It has a nonzero external
matrix element. A direct external wire containing no node contributes an
identity matrix element, which can also be chosen to be one. Closed
components cause no cancellation: each of their wire basis labels is
likewise fixed, and the product/trace of the matching matrix units is one.
A self-wire is covered by the same calculation.

Hence the contraction with this branch matrix unit is nonzero at one
tuple of matrix-algebra inputs. This contradicts the coefficientwise
vanishing conclusion of Section2 if m_(v,b)=0. Equivalently, expanding each
of these matrices as a finite complex linear combination of native
unitaries shows that at least one tuple of other unitary fillings has a
nonzero branch map. Constancy of (3) then makes it nonzero at every such
context.

The witness uses a bare routed skeleton: its tensor coefficients are the
ordinary wire contractions and the selected node matrix units. No fixed
extra complex-valued tensor is secretly retained at another node while
claiming that arbitrary full native matrix units are available there.
When auxiliaries are part of the host, they too are varied in this witness
and only afterward specialized to their desired unitary fillings.

### 4. Graph-wide consequences

At every native node, summing only reachable branches,

    sum_(b reachable) n_(v,b) <= D.                     (4)

Indeed all their multiplicities in (3) are positive integers. In
particular every reachable branch has n_(v,b)<=D and every node has at
most D reachable branches. This is not merely a bound on the branches
that happen to be visible at one chosen auxiliary filling: reachability
forces their represented supports to remain nonzero at every full
unitary auxiliary filling and every unitary original-query context.

There is also a local edge-alphabet consequence. For an original wire e,
let K_e be the set of sector values that occur in a global consistent
assignment, with positive dimensions d_(e,k). Then

    sum_(k in K_e) d_(e,k) <= D.                        (5)

If e meets a native node, use that node's practical input or output space.
For each k choose one globally reachable incident sector tuple containing
k. Different k give orthogonal tuple spaces; each selected tuple space
has dimension at least d_(e,k). Their sum is contained in the direct sum
of the reachable practical branch spaces, whose dimension is bounded by
(4). If e connects only external boundaries, its dimension is at most D
directly. Formula(5) counts only globally reachable sector values; arbitrary
unreachable decorations of the skeleton are not bounded by this proof.

For the sixteen-dimensional quartet, every native node therefore has at
most sixteen reachable branches, total reachable practical dimension at
most sixteen, and every wire has at most sixteen reachable sector labels
and total reachable sector dimension at most sixteen. The number of nodes
and wires can still be unbounded.

### 5. What auxiliary specialization does and does not preserve

Fix arbitrary full unitary fillers at every auxiliary node. Every
reachable branch of a remaining native node still has positive represented
multiplicity: this follows from Section3 before specialization and the
constancy over the full context space. A reachable branch at an auxiliary
node likewise has a nonzero partial contribution if its own branch filler
is varied while all other nodes remain fixed. No reachable full branch
can become an identically zero operation merely because the other
auxiliaries were assigned special unitaries.

This does not make every branch-graph dependence operationally faithful
at the specialized tensor. Different occurrence-pattern terms can still
combine, supports can rotate, and a specific choice dependence can become
invisible after fixed encodings. Positive branch rank is weaker than
faithfulness of all graph paths or of every pattern intersection.

The theorem also does not bound a distributed original query by the
capacity of a single native node unless a precise whole-query unital
embedding into that node has been supplied. Its valid graph-independent
content is (3)–(5) for the actual complete native host.

### 6. Finite profiles for a whole-first-query quartet node

Suppose additionally that one native node carries the entire quartet's
first M2 query through unital component inclusions, and specializing the
other nodes/embedded original queries recovers the exact original quartet.
Apply the audited first-node classification
[RG-012: Native capacity and analytic carrier methods](native-interfaces.md#rg-012). It allows at
most one used M4 summand, with represented multiplicity one and carrier S1;
every other used summand is M2. Section3 now removes the qualifier
"used" from every globally reachable branch of this actual host.

Consequently the reachable native algebra of that node has one of the
following forms, with strictly positive represented multiplicities:

    direct_sum_(b=1)^k M2,       sum_b m_b=8,  k<=8;
    M4 directsum direct_sum_(b=1)^k M2,
                                sum_b m_b=6,  k<=6.       (6)

Up to relabeling the M2 branches, the multiplicity lists are the integer
partitions of eight or six, respectively. This is a finite necessary
list, not a claim that every listed profile is realizable. The M4 carrier
is fixed by the original-query theorem; no such fixed-support assertion
is made for the separate M2 summands.

This corollary applies only where the entire original query has the
specified native-node inclusion. It does not silently replace a
distributed query or a multi-node one-query wrapper by such a node.

Dependencies: the contextual multiplicity theorem and the same
matrix-unit coefficient method as [RG-003: Branch faithfulness under complete extensions](foundations.md#rg-003). For the
sufficient graph-to-complete-unitarity implication, see
[Consistent circuits for indefinite causal order, Theorem3.1](https://arxiv.org/html/2206.10042v3).

<a id="rg-019"></a>

## RG-019 — Weak-loop layer slice structure

**Statement.** Weak-loop layer slice structure

**Status:** source-level result. **Scope:** Scalar internal wires and exact cut-tensor form do not identify a coherent physical fragment with one arbitrary quantum node.

### 1. The precise graph input

We use the branch graph of [Consistent circuits for indefinite causal
order, Definitions3.6–3.7 and AppendixB.4.1](https://arxiv.org/html/2206.10042v3).
A solid branch edge is absent between two co-occurring branches exactly
when every original wire between them has one fixed compatible index value,
whose sector has dimension one. In a valid weak-loop graph every strongly
connected branch component has only one dashed color internally; its
condensation is acyclic. The latter is already part of the published proof,
not a new theorem of this note.

Fix a strongly connected component L of the branch graph. An occurrence
pattern q selects one branch at each original node and occurs in at least
one globally consistent index assignment. Only the selected branches that
belong to L are called the q-slice of L. Different branches of the same
original node are never selected simultaneously.

### 2. Scalar internal-wire lemma

For any two selected branches b,c in the q-slice and any original wire
from the node of b to the node of c, that wire has a unique index value
compatible with the joint occurrence of b,c, and its sector is one
-dimensional. In particular this value is fixed throughout every global
index assignment with occurrence pattern q.

Proof. The branches co-occur by the definition of q. If their wire did not
have the stated property, Definition3.6 would create a solid edge b->c.
Since b,c lie in one strongly connected component, there is a directed
return path c->b. The solid edge would belong to a forbidden closed walk.
The same proof covers parallel wires separately and a self-wire. Hence
there is no such solid edge, which is precisely the stated alternative.

The assertion is stronger than saying that an internal sector happens to
have dimension one in one assignment. Multiple possible one-dimensional
sector labels for the same co-occurring pair would also create a solid
edge and are excluded.

### 3. Exact cut-tensor form

Choose unit vectors for all one-dimensional sectors. Fix q and open every
wire joining a selected L-branch to anything outside the selected L-slice.
For each selected branch b, restrict its full native filling U_b to the
fixed sectors of its internal incoming and outgoing wires. Leave all its
opened external wires as tensor legs, extending forbidden external sector
tuples by zero in their ambient tensor product. Call this rectangular
tensor U_b[q]. Then the q-slice contraction is exactly

    T_L[q] = tensor_product_(b in q intersect L) U_b[q],       (1)

up to the fixed permutations that order its external tensor legs.

Indeed every internal contraction pairs two fixed one-dimensional unit
vectors, so contributes the scalar one. All remaining legs belong to just
one local branch slice. No quantum summation index remains between two
selected branches of L. An arbitrary choice of sector basis changes only
fixed scalar conventions on the branch slices and not this conclusion.

For the full graph, first expand the finite sum over consistent index
assignments and group it by q. Insert (1) into each summand and contract
its external legs with the complementary graph. This is an exact finite
tensor identity, valid for all local matrices, and hence for all native
unitaries and their private-ancilla extensions. It is legitimate even
when one original node has different branches in different layers:
each q selects only one of them before the cut is taken.

There can remain sums over the external sectors of (1), and different q
terms can interfere coherently after the rest of the graph is contracted.
Equation (1) is not a claim that the full effective channel is separable,
that the q terms are orthogonal, or that L is a standalone unitary process.
In particular one must not combine these q-dependent cuts into one fixed
physical cut without a separate argument.

### 4. Why this does not yield a single quantum node

The original quantum inputs and outputs of each U_b[q] may have arbitrarily
large dimensions on the opened wires. Their local slices can each act on
independent quantum systems, entangled beforehand by earlier auxiliary
operations and recombined later. Formula (1) removes internal quantum
communication; it does not remove those quantum systems or their distinct
unknown queries.

Combining two independent fillers U and V into U tensor V only specifies
a product subgroup of U(dim U times dim V). Replacing that product by an
arbitrary full unitary is an enlargement of the allowed fillings and
requires a new validity proof. Likewise, summing q does not make different
occurrence patterns into the rectangular input/output support of one full
matrix branch. The retained [RG-003: Branch faithfulness under complete extensions](foundations.md#rg-003) supplies a
necessary test: every input/output corner of a reachable full branch must
extend to a consistent assignment. Incompatible occurrence patterns often
fail this test.

Thus neither layer condensation nor dimension multiplication alone lets us
apply the quartet's native-M6 exclusion to a collection of auxiliary nodes
or to several original-query locations. The branch dimensions in that
exclusion refer to one actual unrestricted native matrix summand carrying
a whole original-query inclusion.

### 5. Exact constraint on a proposed coherent decoder

Suppose a construction exposes inside one strongly connected branch
component an encoder-to-decoder quantum wire which, for a co-occurring
branch pair, can occupy more than one sector label or a sector of dimension
at least two. The scalar internal-wire lemma immediately rejects that
weak-loop certificate. Equivalently, quantum decoding inside a recurrent
component cannot be introduced while retaining a return dependency to its
entry. This includes the retained entry/choice expansion lemma,
but does not require an entry-to-choice path to be identified in advance:
any resulting same-component solid edge is enough.

A candidate can escape this test by placing the quantum operation across
layers, altering the occurrence dependencies, keeping it inside a native
monopartite filling rather than exposing it as graph nodes, or using a
completely different graph. Every such escape still needs its own full
native-filler and original-query implementation checks.

### 6. Consequence for the present search

The useful finite search variables are not just active histories or
quantum dimensions. A candidate needs occurrence predicates, shared
forward and reverse choice coordinates, the scalar internal sectors for
each co-occurring pair, and quantum adapters across layers. The quartet's
entangled serial cylinders rule out some simple product-code interfaces,
but this note supplies no theorem converting every layer adapter into
such an interface. That conversion is an explicit remaining gap.

<a id="rg-020"></a>

## RG-020 — Node-closed fixed-index collapse

**Statement.** Node-closed fixed-index collapse

**Status:** source-level result. **Scope:** Requires node closure and fixed interface indices; does not authorize collapse of an arbitrary whole branch SCC.

### 1. Hypotheses and statement

Let a finite routed graph satisfy bi-univocality and weak loops in the
sense of [Consistent circuits for indefinite causal order, Definitions3.4--3.7
and Theorem3.1](https://arxiv.org/html/2206.10042v3). The external boundary
indices are singleton. Every practical native branch has equal positive
input and output dimension and permits its whole unitary group. Remove
globally unreachable branches and sectors if desired; the reduction is
justified in Section2.

Take the strongly connected components of the branch graph. Assume:

1. **Whole vertices.** All surviving branches of each original graph
   vertex belong to one component. Thus the components partition the
   graph vertices, not merely their branch names.
2. **Fixed interface indices.** Every original wire joining distinct
   components has exactly one globally reachable index value. Its quantum
   sector may have arbitrary positive dimension.
3. **One unknown per component.** Each original unknown balanced matrix
   query M_(d_i) is inserted once, at one graph vertex, through a specified
   complete monopartite unitary filling. Every component contains at most
   one such original-query location. All other vertex fillers are fixed
   full native unitaries. Distributed implementations that place one
   original unknown at several graph vertices are outside this hypothesis.

**Theorem.** The resulting process on the original queries has an ordinary
fixed-order unitary circuit realization, with one use of each query and
the unchanged original boundary. In particular it is a QC-QC.

The theorem applies to arbitrary numbers and dimensions of auxiliary
vertices. The components themselves can contain genuine dashed cycles.
Their internal graph need not be an ordinary directed acyclic graph.

For the retained quartet, and for its joint cylinder extension if restricted
along the original query embeddings, the audited QC-QC obstruction excludes
this normal form. Hence a successful host must have at least one of:
multiple original-query locations in a component; an original vertex whose
branches belong to different components; or a genuinely varying sector
index crossing components. No one of these alternatives is asserted to be
sufficient for a construction.

### 2. Removing unreachable decorations does not enlarge a filler

The native capacity theorem [RG-018: Reachable native branch capacity](layer-structure.md#rg-018)
shows that every reachable branch is represented with positive multiplicity
at every full unitary context. Its matrix-unit images are therefore all
nonzero. Consequently every input/output matrix-unit corner of a reachable
branch extends to some consistent wire-sector assignment. Otherwise that
corner's contraction would be structurally zero at every filling, contrary
to its positive represented multiplicity.

If a wire has only one globally reachable index, every practical incident
tuple in a reachable branch must use that index. A tuple using another
value would give such a structurally zero corner. Thus, after discarding
unreachable branches, its other sector values are absent from all practical
spaces. Removing them changes neither a surviving branch's dimension nor
any allowed matrix entry. It does not project a reachable full branch onto
a proper subspace.

Unreachable branches occur in no consistent assignment. Their forward and
reverse choice coordinates never affect the contraction or the status of
any occurring branch. Discarding them preserves the complete tensor and
the two choice functions on the remaining coordinates. Co-occurrence and
possible linking values between remaining branches are unchanged. Hence
the surviving branch graph is the corresponding induced graph, with its
same reachable components. These remarks also permit the simpler literal
hypothesis that each interface wire has a singleton index set from the
outset; no reduction is then necessary.

### 3. Consistent assignments factor across the opened components

After Section2, all intercomponent indices are fixed singleton values.
Open those wires at the component boundaries, retaining their full quantum
sector dimensions. Write Gamma_C for the resulting fragment on the vertices
of a component C. Its exterior indices are singleton, including any
original exterior wires incident to it.

The local branched routes impose only the internal index constraints of
their own component. There is no variable index left to match between two
components. Therefore there is an exact Cartesian factorization

    ConsistentSections(Gamma)
       = product_C ConsistentSections(Gamma_C).       (1)

The same statement holds after prescribing forward choices at every branch:
the full compatible-section set is the product of the compatible-section
sets of the individual fragments. The original choice coordinates are
partitioned by components because of the whole-vertex hypothesis.

For any specified fragment choices, extend them arbitrarily to all other
components. Global forward univocality supplies exactly one global section,
so the chosen fragment has at least one section. If it had two, combining
them separately with the same sections of the other components would give
two global sections. Thus every fragment is forward univocal. Applying the
identical argument to reversed choices proves reverse univocality too.

This argument supplies totality as well as uniqueness. It does not assume
that arbitrary opened quantum inputs had been reachable in the original
host; those are not index choices and are dealt with by the validity theorem
after the fragment has received its own graph certificate.

### 4. Each fragment inherits a genuine weak-loop certificate

Every consistent index section of one fragment extends to a full section
by (1), since the other factors are nonempty. Thus two branches inside it
co-occur under exactly the same possibilities before and after opening,
and the possible tuples on their internal linking wires are unchanged.
Their solid edges are consequently unchanged.

The fragment's forward choice function is the corresponding component
factor of the full choice function. Its internal functional dependencies
therefore are exactly the original internal green edges. Reversal proves
the same for red edges. The fragment branch graph is the induced branch
graph on C. Every loop in it is a loop of the original graph, so it is weak.

The original routed-superunitary theorem now applies directly to Gamma_C.
It gives a completely unitary supermap from all its full native fillers to
its whole quantum boundary, including independent private ancillas. In
particular its total input and output Hilbert spaces have the same dimension.
No arbitrary-input isometry property of an old restricted fragment has
been postulated. It follows from bi-univocality and weak loops of this
newly opened graph.

### 5. The components have an ordinary quantum order

Consider an intercomponent wire of quantum dimension at least two. Choose
any global section; its source and target branches co-occur. Their fixed
linking sector on this wire has dimension at least two, so the primary
solid-edge definition supplies a solid branch edge from the source
component to the target component. Such an edge follows the directed
acyclic condensation graph of the branch graph.

Wires whose unique sector has dimension one carry no quantum system and
can be suppressed using fixed scalar identifications. Their fixed indices
enforce no additional variable constraints. Thus every nonscalar quantum
wire between opened fragments follows the same condensation DAG. The
fragments form an ordinary acyclic circuit of completely unitary boxes,
with the original past and future and no extra boundary register.

### 6. A one-query fragment is a one-slot comb

Fix all auxiliary fillers in Gamma_C. If there is no unknown query there,
the fragment is just a fixed unitary. If its one unknown is x in M_d, the
specified monopartite insertion and Section4 make its contraction L_C(x)
a linear, independently completely unitary-preserving map between equally
sized fragment boundaries. Normalize by L_C(I) to obtain a unital map.
The retained private-M2 unitary-preserver theorem makes it a *-homomorphism.

Finite-dimensional representation theory therefore gives a memory size m
and fixed unitaries U_C,V_C such that

    L_C(x)=U_C (x tensor I_m) V_C.                    (2)

The normalization convention can be left or right; it only changes the
two fixed unitaries. Equation(2) is a full coefficient identity and retains
all private ancillary amplifications. In particular it introduces one
ordinary use of x, not an inverse or an additional call.

Replace each opened component by its fixed unitary or the comb(2), and
compose along the condensation DAG from Section5. A topological ordering
of this finite circuit gives a fixed order of all original queries; parallel
independent calls can be serialized with the other registers carried as
memory. This proves the theorem on the unchanged original boundary.

### 7. Exact remaining gap

If an interface sector index can vary, consistent sections need not factor
as in(1). Opening then releases constraints that the surrounding graph had
enforced. Neither fragment univocality nor fragment complete unitarity
follows by the present argument. Similarly, if a vertex has branches in
different components, a component is not a subnetwork of whole native
vertices and cannot be opened as above.

The layer-slice theorem correctly handles those cases only after
conditioning on an occurrence pattern. Such slices may be rectangular and
may interfere after external contraction; they cannot be substituted for
the valid fragments constructed here. Extending the collapse beyond the
explicit fixed-index, whole-vertex hypotheses remains open.

<a id="rg-021"></a>

## RG-021 — Coherent fragment theorem and its exact boundary

**Statement.** Coherent fragment theorem and its exact boundary

**Status:** source-level result. **Scope:** Conditional coherent-boundary theorem; correlated host-occurring caps are not the unrestricted product boundary.

### 1. Open fragment and the two total-domain hypotheses

Let Gamma be a finite directed graph fragment with indexed internal and
boundary wires and a branched route at each internal vertex. Every sector
has positive finite quantum dimension. Every native branch has equal
positive practical input/output dimension and admits its full unitary
group. Keep all branches and their independent choice coordinates.

Write I_in and I_out for the products of the input and output boundary
index sets. Let nonempty sets

    Rin subset I_in,             Rout subset I_out

be fixed. They need not be Cartesian products over the boundary wires.
For a forward choice tuple f, specify one full outgoing index tuple at
EVERY internal branch, including nonoccurring branches. A section extending
(r,f) is an assignment of all wire indices that has boundary input r,
satisfies all routes, and follows f at every occurring branch. Define
reverse choices analogously using full incoming tuples at every branch.

Assume:

**F.** The exact domain of the forward section relation is
Rin times ALL forward choice tuples. At each point in that domain there
is exactly one section. There are no such sections at inputs outside Rin.

**R.** The exact domain of the reverse section relation is
Rout times ALL reverse choice tuples. At each point in that domain there
is exactly one section. There are no such sections at outputs outside Rout.

These are independent statements. In particular F alone need not prove R,
and merely knowing which boundary tuples occur somewhere is insufficient.
Every consistent section extends some full forward and reverse choices:
prescribe the tuples at occurring branches and arbitrarily fill unused
coordinates. Consequently every consistent section has input in Rin and
output in Rout, and conversely every permitted boundary input/output has
at least one section.

The unique sections define the forward and reverse branch-status maps.
In each map retain the boundary tuple as a separate input coordinate.

### 2. Internal weak-loop condition

Define a graph on the internal branches as follows.

* A solid arrow b to c is defined exactly as in primary Definition3.6,
  using all consistent sections of Gamma: the branches must co-occur and
  some wire from their vertices must have either more than one compatible
  index value or a compatible quantum sector of dimension greater than one.
* A green arrow b to c means that changing f_b can change the forward
  status of c while keeping the boundary input r and every other forward
  choice fixed. Existence of such a change for any r in Rin suffices.
* A red arrow b to c means that changing the reverse choice at c can change
  the reverse status of b while keeping the boundary output and all other
  reverse choices fixed. This is the primary reversed orientation.

Assume every closed walk of this internal graph is entirely dashed of a
single color. The condition includes closed walks with repeated vertices,
not only simple cycles. This definition is meaningful because F and R
already supply total functions on their specified product domains.

### 3. The coherent practical-boundary theorem

Define the coherent practical boundary spaces by

    H_Rin  = direct_sum_(r in Rin) tensor_product_(e input) H_(e,r_e),
    H_Rout = direct_sum_(s in Rout) tensor_product_(e output) H_(e,s_e).

No measurement or independent clamping of the individual boundary indices
is part of these spaces. They are subspaces of the ambient boundary tensor
products, and preserve coherence between distinct permitted tuples.

**Theorem.** Under F, R, and the internal weak-loop condition, contraction
of Gamma is a completely unitary supermap between H_Rin and H_Rout, for
all independent full native branch fillers and all their private ancillary
amplifications. In particular dim H_Rin = dim H_Rout. The equality and the
unitarity are conclusions; neither is an extra assumption about a cut of
an old host.

If Gamma has been cut out of another tensor network, the theorem gives the
same contraction on its specified practical boundary. It makes no claim
about unitarity on the larger product of independently opened edge spaces.

### 4. Coherent capping gives a literal valid graph

Add an encoder vertex E before every input boundary wire. Give E a single
unsectorized external input wire of dimension dim H_Rin. Its one branch
has one input index value and precisely the output tuples Rin. Its entire
practical output is H_Rin; hence it is a square full-unitary native slot.

Add a decoder D after every output boundary wire, with one branch whose
input tuples are Rout and whose only output index value has quantum
dimension dim H_Rout. Its practical input is H_Rout. The new external
indices are singleton, as required by the primary theorem.

For a forward choice assignment in the capped graph, E's choice selects
one r in Rin. D's forward choice is singleton. By F there is exactly one
fragment section for r and all the internal choices, and by R its output
belongs to Rout. It therefore extends uniquely through D. Thus the capped
graph is forward univocal. Reversing this reasoning, D's reverse choice
selects s in Rout and E's reverse choice is singleton; R supplies the
unique section and F ensures its input is accepted by E. This establishes
reverse univocality as well.

One can equivalently phrase primary univocality as uniqueness of branch
statuses: with the prescribed forward choices and singleton external
indices, those statuses determine all wire indices. The stronger section
formulation F/R above therefore entails exactly the required property.

Every fragment section extends through the caps, and every capped section
restricts to a fragment section. Thus internal co-occurrence and possible
linking values are unchanged. Internal solid edges are unchanged too.
E's choice is exactly the old boundary input coordinate; holding it fixed
is exactly the condition in the definition of an internal green arrow.
The corresponding statement for D's reverse choice gives the same red
arrows. Consequently the internal branch graph is precisely the graph in
Section2, not an inferred subgraph of a previous host.

The cap statuses E and D are constant: both occur in every section.
Moreover E has a singleton reverse choice, while D has a singleton forward
choice. It follows directly from primary Definition3.7 that:

    E has only possible solid and green outgoing arrows;
    D has only possible solid and red incoming arrows.

For clarity, an arrow into E cannot be green because its status is
constant, cannot be red because its reverse choice is singleton, and
cannot be solid because no internal wire enters E. An arrow out of D is
excluded by the dual three reasons. The other possible dashed cap arrows
also vanish when they would depend on the cap's constant status. Hence
neither cap lies on a closed walk. All closed walks of the capped graph
are internal and weak. The capped graph therefore satisfies the exact
primary bi-univocality and weak-loop hypotheses.

### 5. Full native and private-ancilla validity

Apply the primary theorem to the capped graph with all its native slots,
including E and D unrestricted. It gives a routed superunitary. Fix E and
D to any coordinate unitaries identifying their unsectorized spaces with
H_Rin and H_Rout. Its contraction is precisely the fragment contraction
between those coherent spaces. Removing these two fixed coordinate changes
proves the theorem.

The theorem applies equally when each internal filler carries its own
independent private ancilla. The caps then act as their fixed coordinate
unitaries tensored with the corresponding bypassed identity spaces. This
is the ordinary complete-superunitary conclusion of the graph theorem;
it does not assume that these input vectors were reachable in an old
external context. No arbitrary joint replacement of independent native
fillers has been made. Every internal branch retains its full original
matrix freedom, including off-diagonal corners between its practical
index sectors.

### 6. Example and immediate one-query consequence

The open diagonal-code decoder of
[RG-021: Coherent fragment theorem and its exact boundary](layer-structure.md#rg-021) has

    Rin={(0,0),(1,1)},       Rout={the single output index}.

It satisfies both domains and has a trivial internal branch graph. Its
old matrix L is unitary from span{|00>,|11>} to the qubit. The theorem
recovers exactly that assertion and does not declare L trace preserving
on the four-dimensional ambient input. Coherence between 00 and 11 is
retained by the full encoder branch.

If a fragment satisfying the theorem contains exactly one original M_d
query, inserted once through a complete monopartite filling at a whole
vertex, and all other fillers are fixed, its map L(x) is linear and
completely unitary preserving. Normalize at x=I. The private-M2
homomorphism theorem and finite-dimensional representation theory then
give fixed unitaries U,V with

    L(x)=U (x tensor I_k) V.

This is a one-use ordinary comb on the coherent practical boundary. It
does not by itself prove that several such coherent boundary codes compose
as an ordinary DAG: their intercomponent matching and possible shared
correlations must still be established.

### 7. What is not inherited automatically

For an arbitrary whole-vertex strongly connected component of a valid
host, one may form the sets of boundary tuples that occur somewhere in
the host. This alone does not prove that its standalone section relation
has domain Rin times ALL choices, or the reverse product-domain property.
Opening the component can change which assignments extend externally;
its internal solid and functional-dependence relations must also be
checked on the newly allowed sections. No arbitrary cut-unitarity or
partial-choice superunitarity theorem is being assumed.

The fixed-index collapse proves these hypotheses by a Cartesian
factorization of complete sections. Section4 supplies a replacement proof
of validity once the more general correlated product-domain hypotheses
are established. The further inheritance and composition problems with
variable component interfaces remain separate research targets.

### Correlated-interface boundary qualification

### 1. A two-node valid graph

Take a qubit past and future, with singleton external indices. Join two
vertices P and V by two parallel wires. Each wire has two sector indices
0,1, each of quantum dimension one. The practical output tuples at P and
practical input tuples at V are exactly

    (0,0), (1,1).

Each vertex has one branch. Its practical input and output dimensions are
both two, so its filler is the entire U(2). The first vertex maps the past
qubit into the two-dimensional diagonal code

    C=span{|00>,|11>} subset C^2 tensor C^2,

and the second maps this same practical space to the future qubit. Their
contraction is a unitary for all independent fillers and private ancillas.
The forward choice at P selects one of the two tuples; the reverse choice
at V does the same. In either direction the consistent section is unique.
The graph is acyclic, so its branch graph has no forbidden loop.

For coordinate-identity fillers the two actual matrices are

    J=|00><0|+|11><1|,
    L=|0><00|+|1><11|,
    L J=I_2,       L*L=P_C.

All of these identities are exact. In particular, P_C is a proper
projection of rank two in the four-dimensional ambient wire space.

### 2. Why the unrestricted opened cut is not trace preserving

Open the two incoming wires of V and independently allow all their index
values. The ambient cut space is C^2 tensor C^2. The old V filler,
zero-extended off its practical tuples, is L rather than an isometry on
this full space. Its completely positive map is

    rho -> L rho L*,

and is not trace preserving there: the input |01><01| has trace one and
is sent to zero. The same holds for |10><10|. The correct practical input
is the correlated space C, on which L is unitary onto the future qubit.

Thus validity of a host does not establish trace preservation on all
independently opened edge-index combinations. This example does not
contradict the conditional collapse theorem: it violates that theorem's
fixed intercomponent-index hypothesis. It also does not refute a future
cut theorem using a suitably defined correlated practical boundary.

### 3. Why measured flags lose the original contraction

The two index values must remain coherent. The input |+> is encoded as

    J|+>=(|00>+|11>)/sqrt(2),

and L returns |+>. If one treats the matched tuples as measured classical
instrument outcomes, the intermediate off-diagonal terms |00><11| and
|11><00| are removed. Recombination then yields I_2/2 instead of |+><+|.
Equivalently, the outcome Kraus operators of the measured version are
|0><0| and |1><1|, whose outcome-forgetting channel dephases the qubit.

Consequently a proposed instrument-DAG reduction must preserve these
off-diagonal coherences, or prove a separate reason that they are absent.
Merely summing matched classical outcomes is not the old tensor
contraction. This statement does not exclude a coherent dilation or a
fresh-memory completion under additional established hypotheses.

### Remaining conditional boundary question

A possible extension is a partial-fragment theorem with fixed correlated
practical boundary index sets. Its forward and reverse choice-relation
domains would have to factor as the prescribed practical boundary times
all internal choices, independently of the chosen internal branch
fillers. One would also retain the weak-loop condition and show complete
unitarity on that coherent practical boundary, including private ancillas.
The diagonal-code fragment above fits the intended boundary geometry.

Neither the existing layer-slice identity nor the published total-choice
graph theorem by itself proves this proposed extension. In particular,
an arbitrary partial choice relation need not have a filler-independent
domain. Establishing the correct theorem, and then a coherent effective
interface completion for whole-vertex, one-query components, is a target. No such general partial-fragment or QC-QC-collapse result is
claimed in this note.

<a id="rg-023"></a>

## RG-023 — Lossless coherent-code DAG composition

**Statement.** Lossless coherent-code DAG composition

**Status:** source-level result. **Scope:** Requires a physical DAG and the stated code supports; not a consequence of branch-SCC condensation alone.

### Statement

Consider a finite tensor network whose boxes and physical wires form an ordinary directed acyclic graph. At each box v fix coherent practical input and output subspaces

\[
C_v^{\rm in}\subseteq H_v^{\rm in},\qquad
C_v^{\rm out}\subseteq H_v^{\rm out}.
\]

Assume its box map is a unitary \(L_v:C_v^{\rm in}\to C_v^{\rm out}\), extended by zero on \((C_v^{\rm in})^\perp\). The codes can correlate several input or output wire indices. No tensor-factorization of a code is required. Assume the whole contracted map is a unitary from the designated global input to output, for every allowed tuple of unknown queries.

Then every reachable intermediate state lies in the practical input code of the next box. This holds coherently, including when that input is entangled with all wires not currently acted upon. There is no physical projection, measurement, or postselection in the conclusion.

If each variable box is independently a complete one-query comb on its code, contains at most one original query, and every original query occurs at one such box, the complete network has an ordinary fixed-order one-use unitary circuit realization on the original logical boundary, with clean auxiliary memory.

### Proof of the support assertion

Choose any topological ordering of boxes. At step t let \(K_{t-1}\) and \(K_t\) be the ambient tensor-product spaces on the current wire cuts. Pad the next zero-extended box by identities on untouched wires, and apply the required fixed wire permutation. This gives

\[
A_t:K_{t-1}\to K_t,
\qquad A_t^\dagger A_t=P_t,
\]

where P_t is the projector onto the next practical input code tensored with the untouched wires. Thus \(\|A_t\|\le1\). Let \(W_t=A_t\cdots A_1\).

For each input vector \(\psi\), global unitarity gives

\[
\|\psi\|\ge\|W_1\psi\|\ge\cdots\ge\|W_m\psi\|
=\|\psi\|.
\]

Every inequality is an equality. In particular

\[
0=\|W_{t-1}\psi\|^2-\|A_tW_{t-1}\psi\|^2
=\|(I-P_t)W_{t-1}\psi\|^2.
\]

Hence \(P_tW_{t-1}=W_{t-1}\). The state before every box lies in its input code, for every input vector and every allowed query context. The same proof with spectator identities covers arbitrary external entanglement and private ancillary inputs.

The union, or linear span, of the reachable states across query contexts is still contained in the same fixed practical input support. Thus a subsequent completion of each box can be chosen independently of unknown query values.

### Proof of the one-query circuit assertion

For a variable box, complete one-query preservation on its code gives fixed coordinate unitaries

\[
L_v(x)=U_v(x\otimes I_{r_v})V_v
\]

between its coherent code spaces. All untouched wires simply enlarge the memory multiplicity. Constant boxes are fixed code unitaries.

Put every cut space into a sufficiently large common workspace H. Choose its dimension to be divisible by every query dimension and by the original boundary dimension, and large enough for every ambient cut space. Fixed isometric embeddings \(J_t:K_t\hookrightarrow H\) can be chosen so the original initial and final boundaries are embedded with a clean memory state.

At each variable step, the support \(J_{t-1}(\operatorname{ran}P_t)\) has dimension \(d_v r'_v\). Extend its fixed decoding coordinate map to a unitary on H, putting that support into the tensor product of the query's d_v-dimensional subsystem and an r'_v-dimensional memory subspace. Apply the original query once. Then use a fixed unitary extension of the output coding coordinate map to put the result into \(J_t(\operatorname{ran}A_t)\). Both completions exist because the prescribed maps are isometries between equally dimensional subspaces; their arbitrary complements do not depend on x. A constant box is completed in the same manner without a query.

By the support assertion, the actual circuit trajectory never encounters any arbitrary complementary action. Induction through the topological order therefore reproduces exactly \(J_tW_t\) at every stage. At the end it yields the original global unitary and returns the extra memory to the chosen clean output embedding. This is a fixed-order one-call-per-query circuit. Complete coefficient identities preserve private ancillary extensions.

### Application boundary

The lemma closes only the **composition** issue after three facts have been independently established:

1. Every proposed component map is unitary between its fixed coherent practical spaces for all independent allowed fillings
2. Inserting those practical-code projections into the old contraction leaves the global contraction unchanged
3. The component wiring is a physical DAG after any rigorously justified wire simplifications

The global unitarity of a routed host alone establishes none of the first or third facts. A branch-condensation DAG is not automatically a physical DAG. Backward scalar sector wires may still enforce matching constraints, and turning them around can destroy branch separation. The local whole-SCC counterexample in [RG-022: Whole-SCC coherent-boundary counterexample](construction-boundaries.md#rg-022) also fails the first premise for the proposed host-occurring boundary spaces.

The norm proof does show that, once these premises are established, correlated coherent interface codes require no extra separability assumption and no measurement of their indices.

<a id="rg-024"></a>

## RG-024 — Partial endpoint extraction

**Statement.** Past/future endpoint extraction holds for reachable proper branch subsets with pinned siblings; whole-layer extraction is a special case.

**Status:** source-level result. **Scope:** Requires the specified extremal placement and reachable reduction; does not infer arbitrary coherent-SCC collapse.

### 1. Partial version of the extraction statement

**Reachability convention.** Work in the reachable-reduced routed graph: all branch SCCs, minimal/maximal query-bearing layers, and original-query branch sets below are taken after removing globally unreachable branches and sectors. Every branch b quantified below is globally reachable. This removal preserves the surviving full native branch freedoms and the represented process.

Let L be a minimal SCC among the SCCs that contain branches of original-query vertices. Choose a topological order in which L is the first such SCC. Suppose L is green and every original-query branch in L belongs to the **same** original query i. The vertex carrying i can have additional branches in later SCCs.

Write B for the branches of query vertex i belonging to L, and let d_b be the practical native matrix dimension of branch b. Then there are mutually orthogonal, nonzero, query-independent projections E_b on the original past such that

\[
E_b\le S_i,\qquad \operatorname{rank}E_b=m_b d_b,\quad m_b\in\mathbb N_{>0}.
\]

Consequently

\[
\sum_{b\in B}d_b\le\operatorname{rank}\Bigl(\sum_{b\in B}E_b\Bigr)
\le\operatorname{rank}S_i.
\]

Here S_i is the canonical maximal first-query column projection of the normalized original process. If B contains every branch of that native vertex, its projections sum to I, recovering full first-use extraction.

Dually, if L is maximal among query-bearing SCCs, is red, and all query branches in L belong to a single original query i, then

\[
0\ne E_b\le T_i,\qquad
\sum_{b\in B}d_b\le\operatorname{rank}T_i,
\]

where T_i is the canonical maximal last-query row projection. No whole-vertex assumption is needed for this partial conclusion.

### 2. What changes in the proof

Fill earlier auxiliary branches and every auxiliary branch of L. All branches in B remain exchanged. The other branches of query vertex i remain exchanged in later SCCs. At the resulting induction boundary, H2–H4 make the occurrence projector for b in B act on the original past alone: later siblings are not in b's past, while siblings in L are removed from its support by their orthogonality and H3.

Unlike the full-vertex theorem, one does **not** assert that the B projectors sum to I. Put \(E_b=\zeta_b^{\rm out}\) and \(E=\sum_{b\in B}E_b\).

For an arbitrary matrix a on branch b's native practical input, define

\[
\mu_b(a)=T^\dagger\bigl(\zeta_b^{\rm in}a_{b,\rm anc,in}\bigr)T.
\]

H2 gives commutation of \(\zeta_b^{\rm in}\) with b's entire input matrix algebra, and H6 places the pullback on the original past. Therefore \(\mu_b:M_{d_b}\to\mathcal L(P)\) is a *-homomorphism with unit E_b. The maps for distinct b have orthogonal units. Nonzero units give the stated positive integer multiplicities.

Normalize the prescribed original query filling branchwise,

\[
F_i(x)^b=F_i(I)^b\pi_b(x).
\]

The pattern-resolved recovery from the whole-layer proof, restricted to E_b, gives

\[
F(x,\mathbf y)E_b
=F(I,\mathbf y)\mu_b(\pi_b(x)).
\]

The shared use of x in later sibling branches is harmless: the restriction E_b selects branch b at this native vertex, so every sibling is inactive. In the resolved recovery its bypass trace is divided out; equivalently that inactive sibling filler can first be replaced by its value at identity without affecting the restricted native contraction. Thus this is a statement about the original single-use query, not independent substitutes for its sibling occurrences.

At the all-identity outside context, normalization gives

\[
\alpha_i(x)E_b=\mu_b(\pi_b(x)).
\]

The right side acts within E_b. Applying this identity to x and x* shows E_b reduces \(\alpha_i(M_{d_i})\). Substitution into the previous display gives the canonical first-column identity on E_b for every other-query context. Hence E_b≤S_i. The time-reversed proof gives E_b≤T_i.

### 3. Why reachability gives a nonzero projector after fixed refilling

One may invoke the audited reachable-native-branch faithfulness result. There is also a direct exchange formulation.

At the all-exchange context, a globally reachable branch b has a nonzero occurrence projector: a witnessing complete forward choice tuple selects nonzero sector spaces, so the corresponding basis sector lies in its support. Pad every subsequently removed exchange ancilla back in by a fixed bypass unitary. The all-exchange fillers and any target partially refilled fillers now act on the same spaces. At every vertex their route-preserving unitary family is a product of connected full unitary groups on native branches.

For each such context, varying only the native phase of branch b gives a one-parameter unitary polynomial, whose normalized b coefficient is an orthogonal projection. That projection depends continuously on the other full routed unitary fillers. Its rank is an integer and hence constant on the connected context space. It was positive at all exchanges, so remains positive at the target context. Removing the spectator bypass padding preserves positivity. This proves E_b≠0 for every globally reachable b used above.

This reasoning varies only actual route-preserving native unitary operations and their local ancillary amplifications. It does not replace independent vertices by an unrestricted joint operation.

### 4. Quartet host restrictions in the reachable-reduced graph

For the retained quartet, the audited canonical endpoint data are

\[
(\operatorname{rank}S_1,\operatorname{rank}S_2,
\operatorname{rank}S_3,\operatorname{rank}S_4)=(4,4,2,2),
\qquad T_i=0\quad\text{for every }i.
\]

Every realizing host, after the stated reachable reduction, must satisfy the following:

- A maximal query-bearing SCC that is red cannot contain branches of just one original query. It must contain branches from at least two original-query vertices
- In particular no maximal query-bearing SCC can be a singleton: a singleton may be colored red and contains one query branch
- Thus every maximal query-bearing SCC is genuinely recurrent. If it is single-query, it must be green
- In a minimal green single-query SCC, the sum of its practical native branch dimensions is at most 4 for query 1 or 2, and at most 2 for query 3 or 4
- Since complete original-qubit inclusion forces every nonzero native simple branch dimension to be a multiple of 2, a minimal green SCC for query 3 or 4 can contain exactly one M2 branch and no M4 branch. For query 1 or 2 it can contain one M4, one M2, or two M2 branches, with the appropriate representation multiplicities fitting the rank bound

If **every original-query vertex is whole within an SCC** and **each query-bearing SCC contains only one original query**, every minimal query-bearing SCC must instead be red: a green one would give S_i=I, contradicting the proper quartet S_i. Every maximal query-bearing SCC must be green: a red one would give T_i=I, contradicting T_i=0. All these extremal SCCs are nontrivial. There must be at least two query-bearing SCCs, and a directed condensation path from a red minimal one to a green maximal one. No query-bearing SCC may be isolated in the query-bearing partial order.

These are necessary structural restrictions, not a nonroutability theorem. Multi-query endpoint SCCs and split-query vertices remain possible, and the red-before-green pattern itself is realizable.

### 5. Why four queries do not eliminate the color pattern by counting

Let H(x) be the exact controlled-Lugano host of [RG-022: Whole-SCC coherent-boundary counterexample](construction-boundaries.md#rg-022), with B and C fixed and only A carrying an original query x through the same complete U2 inclusion in both native branches. Its one query-bearing SCC is the green six-branch component. It contains the entire query vertex and only one original query. Its other vertices and fixed auxiliary branch fillers retain the original full native graph certificate.

Reverse a copy, obtaining H♯(x), whose query-bearing component is red. Compose H♯(x) followed by H(y), using a fixed unsectorized 32-dimensional boundary identification. Validity is preserved; no cross-copy return dependency is introduced. This is an exact **two-query** host with a red first query SCC and a green last query SCC. Both SCCs contain whole original-query vertices and one original query each.

The resulting process is an ordinary fixed-order two-query process. It does not have the quartet's canonical endpoint defects. Its deterministic hubs remain split among singleton SCCs, so it does not settle the globally whole-vertex conjecture. Four serial copies with colors R,R,G,G similarly give an exact four-query host with the same color pattern and one original query per recurrent query-bearing SCC.

Thus neither the red-before-green orientation nor an original-query count ≤4 is an obstruction by itself. The theorem that a stand-alone complete process with at most two unknown queries is QC-QC cannot be applied to an arbitrary SCC without first proving that SCC's complete input/output boundary theorem. The exact local boundary counterexample shows why such a step needs proof. An explicitly serial construction does supply that theorem for its whole factors; an arbitrary condensation does not.

### Whole-layer exchange proof underlying the partial extension

### 1. Use of the published partial-exchange induction

Use the exchange construction and established invariants H1–H6 in Appendix B.4 of [Vanrietvelde et al., arXiv:2206.10042v3](https://arxiv.org/html/2206.10042v3). Fill every branch in earlier SCCs, and every auxiliary branch of the selected green SCC, with its fixed native filler. Within the SCC choose the induction order so these auxiliary branches precede every branch of N. Leave all original-query branches exchanged.

At this induction boundary the partially filled skeletal map T is unitary. Write \(\zeta_b^{\rm out}\) and \(\zeta_b^{\rm in}\) for the occurrence projectors of the still-exchanged branches b of N. They satisfy

\[
\zeta_b^{\rm in}=T\zeta_b^{\rm out}T^\dagger.
\]

The exchange output ports form part of the input boundary of T; exchange input ports form part of its output boundary. P denotes the original global past.

Only branches of N remain unfilled in its layer or any earlier layer. By H2, an out-projector of this green layer can therefore act only on P and N's exchange output factors. It does not act on its own branch factor. For a distinct sibling c, H4 gives \(\zeta_b^{\rm out}\zeta_c^{\rm out}=0\), and H3 then says

\[
\zeta_b^{\rm out}
=\zeta_b^{\rm out}(I-\zeta_c^{\rm out})
\]

acts trivially on c's exchange output factor. Thus every \(\zeta_b^{\rm out}\) is supported on P alone.

By H5, applying T to \(\zeta_b^{\rm out}\) is the contraction with N restricted to its b summand. Summing over **all** branches of N reconstructs the original partially exchanged N filler. Since T is unitary,

\[
\sum_{b\in\operatorname{Br}(N)}\zeta_b^{\rm out}=I,
\qquad
\sum_b\zeta_b^{\rm in}=I.
\]

The completeness of this sum is exactly where whole-vertex containment matters.

### 2. A full input matrix algebra pulled back to P

Let x range over the original query algebra M_d. Normalize its native monopartite filling at x=I. Complete unitary preservation gives a unital *-representation on the practical native input,

\[
F_N(x)=F_N(I)\,\pi_N(x),\qquad
\pi_N(x)=\bigoplus_b\pi_b(x).
\]

The block decomposition follows because both \(F_N(x)\) and \(F_N(I)\) preserve the native branch partition. Each \(\pi_b\) is a unital *-representation on b's practical input. The usual private-ancilla unitary-preserver theorem justifies this normalization for a complete monopartite filling.

Place \(\pi_b(x)\) on b's exchange input port at the output of T and define

\[
\widehat\pi(x)=\sum_b\zeta_b^{\rm in}\,\pi_b(x)_{\rm anc,in}.
\]

For a green layer, H2 puts every \(\zeta_b^{\rm in}\) on the strict future, which contains no branch of N. Therefore these projectors commute with every N exchange-input matrix. Orthogonality and the complete sum imply that \(\widehat\pi\) is a unital *-representation.

Define its pullback

\[
K_{\rm total}(x)=T^\dagger\widehat\pi(x)T
=\sum_b T^\dagger\pi_b(x)_{\rm anc,in}T\,\zeta_b^{\rm out}.
\]

H6 says each summand acts only on P and remaining strict-past exchange outputs, after multiplication by its branch projector. There are no remaining strict-past branches. The branch projectors themselves act only on P, as proved above. Hence

\[
K_{\rm total}(x)=K_P(x)\otimes I_{\rm remaining\ exchange\ outputs}.
\]

It follows that \(K_P:M_d\to\mathcal L(P)\) is a unital *-representation. Consequently \(\dim P=dm\) and \(K_P(x)=V^\dagger(x\otimes I_m)V\) for a fixed coordinate unitary V.

### 3. Branch-resolved recovery from the exchange identity

A naive contraction with future fillers is **not** adequate: an inactive exchange branch contributes a bypass trace. The following recovery removes that problem explicitly.

First observe that K commutes with every remaining occurrence projector. For any unfilled branch c at a vertex other than N, its SCC is later than N's SCC. H2 therefore puts \(\zeta_c^{\rm in}\) on factors excluding **all** N exchange-input ports. It commutes with every \(\pi_b(x)_{\rm anc,in}\); and H2 gives commutation with the projectors \(\zeta_b^{\rm in}\). The same commutation holds for siblings in N. Hence

\[
[\widehat\pi(x),\zeta_c^{\rm in}]=0,
\qquad [K_P(x)\otimes I,\zeta_c^{\rm out}]=0
\]

for every remaining c.

At every vertex v let \(B_v\) denote its unfilled branches. Use the alternatives

\[
\{\zeta_c^{\rm out}:c\in B_v\}
\quad\text{and}\quad
\chi_{v,*}=I-\sum_{c\in B_v}\zeta_c^{\rm out}.
\]

The last alternative selects the sum of its already filled branch summands. The alternatives are orthogonal and complete, by H4 and H5. At N, where every branch is unfilled, the last alternative is zero. Taking products over vertices yields complete orthogonal pattern projectors \(\chi_q\). H5, multilinearity, and inclusion-exclusion identify \(T\chi_q\) with the network in which q specifies the occurring unfilled branch, or the sum of already filled summands, at each vertex. Every \(\chi_q\) commutes with K.

For each unfilled branch c, let \(\Theta_c:H_c^{\rm out}\to H_c^{\rm in}\) be its exchange bypass, and let \(U_c:H_c^{\rm in}\to H_c^{\rm out}\) be the filler to be recovered. Put

\[
\tau_c=\operatorname{Tr}(U_c\Theta_c).
\]

Assume temporarily that all \(\tau_c\ne0\). On the q-resolved summand, close each exchange input/output pair using U_c. An active branch's swap gives precisely U_c on the native wires. An inactive branch contributes precisely \(\tau_c\). Therefore

\[
\mathcal R_{\mathbf U}(T)
=\sum_q\Bigl(\prod_{c\text{ inactive in }q}\tau_c^{-1}\Bigr)
\operatorname{Contr}_{\mathbf U}[T\chi_q]
\]

is exactly the original skeletal contraction with those unfilled native branches filled by U_c. For fixed U and fixed pattern projectors this is a linear recovery operation on its matrix argument. No arbitrary joint filler is introduced.

The exchange identity at N is

\[
T_\pi=\widehat\pi(x)T
=T(K_P(x)\otimes I),
\]

where \(T_\pi\) is the native network with \(\pi_N(x)\) applied to N's input before its exchange. On a q-resolved term, N has one specified active branch b. Thus

\[
T_\pi\chi_q
=\widehat\pi(x)T\chi_q
=\pi_b(x)_{\rm anc,in}T\chi_q.
\]

Closing its exchange pair using \(F_N(I)^b\) gives exactly \(F_N(I)^b\pi_b(x)=F_N(x)^b\), while every inactive trace remains unchanged. Consequently the same recovery formula applied to \(T_\pi\) yields the desired original process with x at N.

On the other hand, since \([K_P\otimes I,\chi_q]=0\) and K acts on P alone, it passes to the right through every term of the recovery formula. Hence

\[
G(x,\mathbf y)=\mathcal R_{\mathbf U}(T_\pi)
=\mathcal R_{\mathbf U}(T)K_P(x)
=G(I,\mathbf y)K_P(x).
\]

The fixed bypasses can be chosen with nonzero \(\tau_c\) at one baseline context, for example \(\Theta_c=U_c(I)^\dagger\). For arbitrary full native unitary fillers, nonvanishing traces give a dense set. For the prescribed original-query embeddings, the baseline nonvanishing makes each trace a nonzero real-analytic function on the connected product of query unitary groups; their simultaneous nonvanishing again is dense. Continuity extends the coefficient identity to the zero-trace contexts. Multilinearity then gives the full coefficient identity and its independent private-ancilla amplifications.

K was obtained with every later original-query port still exchanged, and its bypasses were fixed once at the baseline. Thus K is independent of every later original query. This resolves the inactive-trace and central-branch noninjectivity issues; no generic injectivity of exchange encoding is assumed.

### Trace-zero recovery and private systems

### 5. Zero traces, fixed bypasses, and ancillas

Choose each bypass once using the adjoint of its baseline native branch filler. At the common baseline all tau_c equal their positive branch dimensions. Each trace is therefore a nonzero real-analytic function of the remaining original unitary queries, and the simultaneous nonzero set is dense in their connected product group. This works even when different branch fillers are tied to the same original query: the same baseline makes every trace nonzero. Continuity extends the recovered identity to the zero-trace locus.

The occurrence projectors and K_P were constructed before any later query branch was filled. They may depend on the already fixed auxiliary fillers and the fixed bypass choices, but not on later unknown queries. The dense-set continuation is therefore of one fixed identity, not of context-dependent factorizations.

Finally, a multilinear map is determined by its values on products of unitaries, because unitaries linearly span each matrix algebra. The equality thus holds coefficientwise. Separate private-ancilla amplifications follow from that coefficient identity, so no new context-dependent K or exchange construction is needed for each ancillary dimension.

### Required proof qualifications

Reachability is needed before auxiliary specialization: a selected branch has a nonzero complete matrix-unit coefficient, and its normalized support has context-independent rank. A zero at a chosen original baseline cannot be treated as graph absence without this native support argument.

<a id="rg-025"></a>

## RG-025 — Green whole-query group extraction

**Statement.** Green whole-query group extraction

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### 1. Statement

Let a valid routed graph have balanced native branch dimensions. Original matrix queries are inserted once through complete monopartite fillings at native vertices. Let L be a minimal SCC among those containing original-query branches, and choose a topological ordering making it first among such SCCs. Assume:

- L is green
- Every original-query vertex with a branch in L has **all** its branches in L

Fix all auxiliary native fillers. Let z be the original queries in L and y the other original queries. Then there is a memory space M of dimension equal to the original past P, and independently ancillary-complete unitary processes

\[
A(\mathbf z):P\to M,\qquad B(\mathbf y):M\to F,
\]

with the exact coefficient factorization

\[
G(\mathbf z,\mathbf y)=B(\mathbf y)A(\mathbf z).
\]

Each original query belongs to only one factor and is used through its original single-use coefficient dependence. No physical edge-cut domain or coherent code is assumed to be unitary. Auxiliary vertices may have branches in multiple SCCs.

The time-reversed theorem extracts a genuine last block from a maximal **red** query SCC containing whole original-query vertices.

### 2. The partial-exchange boundary

Use Appendix B.4 of [Vanrietvelde et al., arXiv:2206.10042v3](https://arxiv.org/html/2206.10042v3). Fill every earlier branch and every auxiliary branch of L, placing these first in L's internal induction order. Let C be the set of all remaining branches in L; these are precisely the branches of its original-query vertices. Let R be the other unfilled branches.

Use notation

\[
C_o=\bigotimes_{b\in C}H_b^{\rm out},\quad
C_i=\bigotimes_{b\in C}H_b^{\rm in},
\qquad R_o,R_i\text{ analogously}.
\]

At this induction boundary H1 gives a unitary

\[
T:P\otimes C_o\otimes R_o\to C_i\otimes F\otimes R_i.
\]

No earlier original query was fixed: there are none. Every later original-query port remains exchanged. Because L is green, all occurrence projectors in H2–H7 are defined at this step, without the partial-red-layer exception.

### 3. All C-input observables have no dependence on R-output ports

Fix b in C and any matrix f on its exchange input factor \(H_b^{\rm in}\). Write \(Z_b=\zeta_b^{\rm out}\). H2 places Z_b on \(P\otimes C_o\): all strict-past branches have already been filled and no later branch belongs to b's past.

For its active part, H6 gives a matrix f'_P such that

\[
T^\dagger f_{b,i}T\,Z_b=f'_P Z_b.
\]

For its inactive part, the local exchange has the fixed bypass \(\Theta_b:H_b^{\rm out}\to H_b^{\rm in}\). H5, summed over all the other branches at that whole query vertex, gives

\[
T^\dagger f_{b,i}T\,(I-Z_b)
=(\Theta_b^\dagger f\Theta_b)_{b,o}(I-Z_b).
\]

This is a literal inactive-wire identity: whenever another branch of that vertex occurs, the b ancilla follows its bypass. H2 excludes b's own factor from Z_b, so the right-hand factors commute. Summing the two identities shows that

\[
T^\dagger f_{b,i}T\in\mathcal L(P\otimes C_o)\otimes I_{R_o}.
\]

The local matrix algebras on all b in C generate the full matrix algebra \(\mathcal L(C_i)\). Therefore

\[
T^\dagger\bigl(\mathcal L(C_i)\otimes I_{F R_i}\bigr)T
\subseteq\mathcal L(P\otimes C_o)\otimes I_{R_o}.       \tag{1}
\]

This is a complete quantum no-signalling statement, including arbitrary off-diagonal native matrix units. It is stronger than independence of the sector status functions.

### 4. Finite-dimensional factorization of the exchange unitary

The left side of (1) is a unital representation of the full matrix algebra \(\mathcal L(C_i)\) on \(P\otimes C_o\). Representation theory supplies a unitary

\[
U:P\otimes C_o\to C_i\otimes M
\]

with \(\dim M=\dim P\), since all native branches are dimension-balanced and \(\dim C_o=\dim C_i\). Choose U so this representation is conjugation by U.

Then \(T(U^\dagger\otimes I_{R_o})\) intertwines every matrix on C_i with the identical matrix at its output. The commutant of a full matrix algebra is the matrix algebra on its multiplicity space. Consequently there is a unitary

\[
V:M\otimes R_o\to F\otimes R_i
\]

such that

\[
T=(I_{C_i}\otimes V)(U\otimes I_{R_o}).             \tag{2}
\]

At this point U and V are fixed matrices, not assumed native graph fragments.

### 5. Recover future fillers entirely inside V

Branch exchange encodings have inactive bypass traces and are not generically injective on central branch directions. The following explicit recovery avoids either assumption.

For any c in R, H2 places \(\zeta_c^{\rm in}\) on \(F\otimes R_i\), with **no C_i factor**. Indeed C belongs to an earlier SCC, whereas an in-projector can only involve the branch's future (strict future for green c). At each vertex with at least one R branch, use the alternatives consisting of its unfilled R-branch projectors and the complementary projector selecting its already filled summands. Whole C-query vertices have no R branches and remain unrestricted during this future-pattern recovery; they are not included in these alternatives. All C-query vertices are whole in C, so no vertex has both C and R query branches. Products of these commuting alternatives give future occurrence-pattern projectors \(Q_q\) on \(F\otimes R_i\).

H5 and inclusion-exclusion identify

\[
(I_{C_i}\otimes Q_q)T
\]

with the network restricted to that future occurrence pattern. If the desired native filler at c is \(W_c:H_c^{\rm in}\to H_c^{\rm out}\), set \(\tau_c=\operatorname{Tr}(W_c\Theta_c)\). Closing c's exchange ports gives W_c if c is active and \(\tau_c\) if it is inactive. Therefore, when every \(\tau_c\ne0\), the exact recovered future map is

\[
V_{\mathbf y}
=\sum_q\Bigl(\prod_{c\text{ inactive in }q}\tau_c^{-1}\Bigr)
\operatorname{Contr}_{R,\mathbf W}\![Q_q V].
\]

Using (2), this recovery gives the actual original graph with every R port filled and C still exchanged:

\[
T_{\mathbf y}=(I_{C_i}\otimes V_{\mathbf y})U.       \tag{3}
\]

All future contractions and pattern projectors act entirely inside V. The bypasses may be fixed at an identity-query baseline so all traces are nonzero there. Nonzero traces hold on a dense set of future unitary contexts; continuity extends (3) to every context.

For every y, \(T_{\mathbf y}\) is unitary by the routed-superunitary theorem: its actual local operations are routed unitaries, with the remaining exchanges using separate local ancillas. Thus \(V_{\mathbf y}\) is unitary. It is multilinear in the original future queries: from (3), it is a fixed linear extraction of \(T_{\mathbf y}\), for example a normalized C_i partial trace of \(T_{\mathbf y}U^\dagger\). No inverse query appears in its definition. The same coefficient statement gives independent ancillary completeness.

### 6. Recover layer fillers entirely inside U

For b in C, its input occurrence projector Z_b acts only on \(P\otimes C_o\). Since every relevant query vertex is whole in C, its branch projectors sum to I by H5. Their products form complete layer pattern projectors \(P_p\) on \(P\otimes C_o\).

These projectors remain valid after the future recovery: they pass through all R contractions and select the same native C branches. Apply the branch-resolved exchange recovery to the C ports in (3). With the same active-swap/inactive-trace rule,

\[
A_{\mathbf z}
=\sum_p\Bigl(\prod_{b\text{ inactive in }p}
\operatorname{Tr}(F_b(\mathbf z)\Theta_b)^{-1}\Bigr)
\operatorname{Contr}_{C,\mathbf F(\mathbf z)}[U P_p]
\]

on the dense nonzero-trace set. The resulting exact graph contraction is

\[
G(\mathbf z,\mathbf y)=V_{\mathbf y}A_{\mathbf z}.
\]

Continuity removes the temporary trace restrictions. Taking one fixed future baseline \(\mathbf y_0\) gives

\[
A_{\mathbf z}=V_{\mathbf y_0}^\dagger G(\mathbf z,\mathbf y_0),
\]

so A is a multilinear independently complete superunitary in the layer's original queries. This also proves that the recovery expression introduces no nonlinear query dependence. Put B(y)=V_y to obtain the claimed factorization.

Whole containment of the query vertices ensures no original x was used in both recovered factors. No independent-branch replacements of an original query are performed in the final statement.

### 7. The ≤2-query consequence and the actual remaining gap

If L contains at most two original queries, A is an actual stand-alone complete one-/two-query process on the full original-size boundary M. Thus the one-query comb theorem, or the established bipartite QC-QC characterization, legitimately applies to A. No SCC physical-boundary inheritance is used.

This theorem only extracts an **earliest green** block. Its dual extracts a **latest red** block. It does not extract an earliest red or latest green block. A red-before-green arrangement can therefore remain blocked even when each component carries at most two original queries.

For the quartet, first-column ranks are (4,4,2,2), their total is 12<16, and all last-row projections vanish. Under whole-original-query containment, an extracted stand-alone one-/two-query first block would provide a first-query cover of the 16-dimensional past using its original queries, contradicting these rank bounds. An extracted one-/two-query last block would provide a nonzero last row, contradicting T_i=0. Likewise a first block containing exactly three of the four queries leaves a one-query last block and is impossible; a last block containing exactly three leaves a one-query first block and is impossible.

Consequently, if this theorem passes audit, a quartet host in which every original-query vertex is whole and the queries occupy at least two SCCs must have only red minimal query SCCs and only green maximal query SCCs, even when a component can contain several original queries. The case where all four original queries occupy one SCC is not excluded. Nor is the red-first/green-last multi-component case: no unproved grouping into two unrestricted meta-queries is allowed.

### Audit clarifications

In the future-recovery patterns, take products only over vertices with remaining-future branches; whole current-layer vertices remain unrestricted and are not classified as already filled via an empty future sum. The factorization can be normalized canonically as G(z,y)=G(z₀,y)G(z₀,y₀)*G(z,y₀). At identity origins the residual is G(I_z,y), obtained by fixing extracted queries in the same valid host, not by replacing a grouped layer with a new unrestricted native node.

### 8. Canonical baseline identity and iteration

The audited factorization implies, for any fixed unitary baselines z0,y0,

    G(z,y)=G(z0,y) G(z0,y0)† G(z,y0).

At normalized identity origins this is G(z,y)=G(I_z,y)G(z,I_y). Both residual factors are the original valid routed host with the complementary original queries fixed to identity. Thus iteration uses an actual residual host rather than promoting either factor to an unrestricted native group node.

<a id="rg-026"></a>

## RG-026 — One-SCC fixed occurrence markers

**Statement.** A green SCC has fixed future occurrence projections, and a red SCC has their past time dual, with exact pinned-sibling recovery.

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### Result and scope

Let L be one green SCC of the branch graph of a finite valid, dimension-
balanced routed host. Fix every native branch outside L at its specified
unitary baseline. The actual native fillers on any branches in L may vary
independently; all other fillers in L may be pinned as well. Let G(u) be the
resulting unitary boundary map. For b in L, let G_b(u) be the exact occurrence-
marked contraction, meaning that only branch b is retained at its vertex,
with its actual filler unchanged. Then there is a fixed future projection

    K_b = G_b(u0) G(u0)†

such that, coefficientwise,

    G_b(u) = K_b G(u).                                  (1)

The projection is independent of every varied filler in L. This is an
identity of the actual native tensor, including independent private-ancilla
amplifications. It is not necessary for a vertex to have all its branches
in L. Pinned siblings outside L remain in their original native direct sum;
the resulting dependence may be affine in an individual branch variable.

In particular, for a hypothetical quartet host, **a green SCC containing a
passive original-query branch contains no branch of a different original
query**. Thus any green SCC involving several original queries contains
only their active branches. Auxiliary branches are unrestricted by this
conclusion. No corresponding passive-branch exclusion is obtained for red
SCCs, and no host nonexistence or graph deletion is asserted.

### 1. Exact pattern recovery without inverse traces

We use the partially filled exchanges and H1--H6 from Appendix B.4 of
[Vanrietvelde et al., arXiv:2206.10042v3](https://arxiv.org/html/2206.10042v3),
especially equations (50), (53), (56)--(58). The following bookkeeping is
also the precise improvement over the stated inverse-trace argument.

Suppose a set S of native branch exchanges is to be closed. At each vertex
v having at least one S branch, use the alternatives

    { zeta_b : b in S at v } together with
    zeta_(v,*) = I - sum_(b in S at v) zeta_b.

The star alternative means *all other branches at that actual vertex*,
including pinned branches and still-exchanged branches not in S. There is
no whole-vertex insertion in place of this complement. H2 and H4 make these
alternatives commuting orthogonal projections summing to I. Products over
the relevant vertices give complete occurrence-pattern projections Pi_p.
H5, expanded by inclusion--exclusion for each star alternative, identifies
T Pi_p (or Pi_p T on the output side) with the exact native contraction
restricted to this pattern. Products asking for two distinct branches of
one vertex are zero by H4; the H5 hypothesis of distinct vertices is never
violated.

Write Theta_b : H_b,out -> H_b,in for the fixed inactive bypass and d_b for
its dimension. To recover a desired filler u_b : H_b,in -> H_b,out, close
its exchange factors in pattern p with

    u_b                 if b is active in p;
    Theta_b† / d_b      if b is inactive in p.            (2)

In the active case the swap closure inserts u_b. In the inactive case the
literal bypass in (50) closes to

    Tr[(Theta_b† / d_b) Theta_b] = 1.

Consequently summing these pattern-restricted contractions is exactly the
native map with S filled. This recovery is linear in the partially exchanged
map and polynomial in the desired fillers. It is valid at every matrix
value. No inverse trace, analyticity, generic context, or continuity limit
is needed. Formula (2) is the pattern-resolved form of the active/inactive
kappa recovery used in the published induction.

The rule remains exact if a branch b elsewhere is marked first: multiply
the same patterns by its occurrence projector, use H4 for incompatible
same-vertex alternatives, and H5 for the compatible restrictions. In
particular no pattern partition has to be changed for the marked map.

### 2. Exchange boundary and complete no-signalling inclusion

Choose an SCC topological ordering with L at its specified location. Fill
all earlier branches at their fixed baselines. Leave C = all branches of L
and R = all later branches exchanged. Keeping *all* of L here avoids an
unnecessary assumption about current auxiliary siblings. We are not in a
partially filled red layer, so every relevant H2--H6 projector is defined.
H1 supplies a unitary

    T : P tensor C_out tensor R_out -> C_in tensor F tensor R_in.

For c in C, write Z_c = zeta_c,out. H2 puts Z_c on P tensor C_out, excluding
c's own output factor. There is no still-exchanged strict past of c. H6
therefore gives, for every matrix f on H_c,in,

    T† f_(c,in) T Z_c = f'_P Z_c.                       (3)

On the complementary occurrence sector, (50) and H5 give

    T(I-Z_c) = W tensor Theta_c.

This statement uses the sum of *every* sibling other than c, whether pinned
or in C or R. Its validity is not restricted to an unfilled whole vertex.
Moving f through the displayed bypass and multiplying by T† yields

    T† f_(c,in) T (I-Z_c)
      = (Theta_c† f Theta_c)_(c,out) (I-Z_c).            (4)

The rightmost projector commutes with the c-output matrix by H2. Equations
(3)--(4) imply that the pullback of each C-input local matrix algebra is
contained in L(P tensor C_out) tensor I_Rout. These algebras generate the
*full* matrix algebra L(C_in), so

    T†[ L(C_in) tensor I_(F Rin) ]T
      is contained in L(P tensor C_out) tensor I_Rout.  (5)

Thus (5) includes off-diagonal matrix units; classical branch-status
independence alone would be insufficient.

### 3. Algebra factorization and future recovery

The inclusion (5) is a unital representation of the full matrix algebra
L(C_in) on P tensor C_out. Finite-dimensional representation theory gives
unitaries

    U : P tensor C_out -> C_in tensor M,
    V : M tensor R_out -> F tensor R_in,
    T = (I_Cin tensor V)(U tensor I_Rout),              (6)

with dim M = dim P, since every branch is balanced and dim C_in=dim C_out.
This is a factorization of the exchange unitary, not a presumed physical
edge-cut unitary.

For r in R, H2 puts zeta_r,in on F tensor R_in, with no C_in support. Even
when r belongs to a red layer, its possibly non-strict future cannot reach
the earlier L. Build the R-pattern projections Q_q on F tensor R_in using
Section 1. At a vertex with both C and R branches, the star alternative
includes its C branches as well as all previously pinned siblings.

Apply the recovery (2) with the fixed R fillers. All its projectors and
closures act inside V in (6). It follows that

    T_0 = (I_Cin tensor V_0) U,                        (7)

where T_0 is the actual routed map with C exchanged and all other branches
filled. It is unitary by routed validity with the exchange ancillas. Since
U is unitary, (7) makes V_0 a unitary M -> F.

For b in C, H2 puts B_b = zeta_b,in on F tensor R_in, because b is green and
its input-side marker only involves its *strict* future. By H2 it commutes
with every Q_q. Apply exactly the same R-pattern recovery to B_b T. H4
kills patterns selecting an incompatible R sibling of b; the star pattern
retains b. H5 identifies all other terms. The result is exactly the b-marked
partially exchanged native network and has the form

    T_(0,b) = (I_Cin tensor V_b) U,                    (8)

where V_b is fixed and need not be unitary.

### 4. Identical current-pattern recovery is the decisive step

For each vertex having C branches, form the right-domain C alternatives

    Z_c, c in C at that vertex;   I-sum_c Z_c.

Their products P_p act only on P tensor C_out. The complementary alternative
now represents all siblings outside C, including the R siblings just
recovered. H5 and inclusion--exclusion identify these same P_p as the exact
current occurrence restrictions both before and after the R contractions:
right multiplication by P_p acts on neither of the contracted R factors.

Apply rule (2) with the desired C fillers to both T_0 P_p and T_(0,b) P_p.
In (7)--(8) this means applying the *same* contractions to U P_p. Neither
V_0 nor V_b acts on a C exchange factor, so each factors outside every term.
Writing the resulting common map P -> M as A(u), one obtains

    G(u)   = V_0 A(u),
    G_b(u) = V_b A(u).                                (9)

No assertion that b+I is a unital matrix-query insertion occurs in this
argument. The contribution of b in (8) may vanish on some P_p; that is
already encoded by (8) and uses the same recovery, not a new partition.
Equation (9) immediately gives (1) with K_b=V_b V_0†.

Fix any unitary u. The actual native branch phase z gives

    G(u;z)=G(u)+(z-1)G_b(u).

It is unitary for every modulus-one z. Its normalized left phase curve is
I+(z-1)K_b; comparison of the constant and first Fourier coefficients gives
K_b=K_b†=K_b². Thus K_b is an orthogonal projection. At u0 this is exactly
the baseline formula in the statement.

The proof above yields a coefficient identity in the native matrix entries,
not just on a finite collection of unitary contexts. An independent private
ancilla at a native vertex amplifies those entries to operators, and entries
at different vertices act on distinct ancillas. Each native vertex is used
once; different branch summands at the same vertex are added, not multiplied.
Accordingly the same coefficient identity gives (1) with K_b tensor identity
on all private ancillas. This preserves a shared private ancilla across the
siblings of one actual vertex, and does not replace it by unrelated native
branches.

As a useful corollary, all the K_b for b in L commute. Add independent phase
variables at two branches in L and apply (1) before extracting the other
phase coefficient: G_bc=K_b K_c G=K_c K_b G. For distinct branches of one
vertex this coefficient is zero, giving K_b K_c=0. This observation describes
fixed future records for this restricted family; it does not make an
unavailable graph record into an actual new native vertex.

### 5. Quartet passive-branch consequence

At fixed auxiliary baselines, the audited complete joint original-native
interface is

    G((a_i directsum b_i)_i)
      = sum_i U_bar_i A_i + F(b)(I-sum_i Q_i),

with mutually orthogonal Q_i<=S_i and all Q_i nonzero. A central identity
P_b of an active native branch at vertex j obeys 0<P_b<=Q_j<=S_j. Its passive
branch has unit P_b=I-Q_j. Directly from the displayed formula, for every
actual original-native filler tuple, the exact b-marked coefficient is

    G_b(u)=G(u)P_b.                                   (10)

For active b, the represented A_j commutes with its branch-central P_b and
all other columns annihilate P_b. For passive b, multiply by I-Q_j and
remove exactly the active-j column. Thus (10) holds also when only individual
branches are free and their siblings are pinned. It is not an assumption
about an arbitrary complete auxiliary extension.

Suppose the passive branch c of original i and a branch b of a different
original j are in the same green L. Pin all other branches at baseline and
vary c's actual M2 filler h. With the common normalized baseline G(I)=I,

    G(h)=Q_i+alpha_i(h)(I-Q_i).

Equations (1) and (10), first at h=I and then at arbitrary h, give

    K_b=P_b,    [P_b,alpha_i(h)(I-Q_i)]=0.              (11)

If b is active, put T_b=P_b. If b is passive, put T_b=I-P_b=Q_j. In either
case T_b is a nonzero projection <=S_j and T_b Q_i=0. Since Q_i reduces
alpha_i, equation (11) is exactly

    [T_b,alpha_i(h)]=0 for every h in M2.

The twelve independently certified cross-cylinder tests prove that no such
nonzero T_b exists for i!=j. Concretely, R_i fixes S_j and the partial trace
Tr_i(I-S_j) is positive definite; a commuting nonzero projection would become
an impossible physical-i cylinder inside S_j. This proves the stated green
SCC exclusion. The proof applies to every allowed active subalgebra and
multiplicity at ports 1 and 2; no maximal native promotion was assumed.

Time reversal of the graph theorem gives fixed *past* markers for a red
layer with all outside branches pinned. The quartet markers in (10) are
already past markers, so this gives no red analogue of (11). The green/red
asymmetry is essential.

### 6. Exact cyclic calibration and checker

[green_layer_future_marker_independent_check.py](../green_layer_future_marker_independent_check.py) reconstructs the literal
binary Lugano host with three native M2+M2 laboratories, an eight-branch
scalar hub, and an M8 future decoder. With

    w(o)=(o2(1-o3), (1-o1)o3, o1(1-o2)),

its contraction is

    G(o,p)=product_i U_i^(w_i(o))[o_i,p_i].

All 64 complete forward choices, including dormant coordinates, have unique
consistent sections. The eight reverse choices are also unique. The only
recurrent SCC is the three losing branches (i,0), and all its internal
edges are green. All wire sectors at fixed co-occurring branch pairs are
one-dimensional, so there are no solid edges.

The three losing fillers contain 12 independent symbolic matrix entries;
winner siblings are pinned, including a calibration with distinct rational
nonidentity winner baselines. The exact losing marker is the fixed future
row projection onto w_i(o)=0, of rank six. All polynomial identities are
verified, also after a dense rational future decoder and source rotation.

The checker additionally reconstructs a 512-dimensional partial-exchange
permutation with all six lab branches exchanged, recovers the winner R
siblings using (2), and obtains the 64-dimensional C-exchanged permutation.
It then recovers the losing fillers symbolically. Both recoveries use the
proper same-vertex sibling complements; the identical C patterns give all
three marked and the unmarked final contractions exactly. This directly
tests the critical bookkeeping in Sections 3--4.

A separate exact 64-by-64 test gives each native vertex its own private
qubit and uses rational four-dimensional unitaries with noncommuting
operator blocks. Both unitarity and all fixed future-marker identities
hold. Arithmetic is integral with denominator 15625. The worst quartic
int64 dot-product bound is

    64 * 15625^4 = 3814697265625000000 < 2^63;

all earlier bounds are smaller and explicitly checked. The private-qubit
test is a calibration; arbitrary private dimensions follow from the
coefficient proof, not from its finite size.

Finally, the literal time reverse has a fixed past marker but fails a fixed
future-marker identity: vary losing vertex 1 by X and mark either of the
other losing branches. The exact squared Hilbert--Schmidt defect is 4.
This guards against silently reversing the conclusion.

<a id="rg-027"></a>

## RG-027 — Joint status faithfulness within one SCC

**Statement.** Joint positive/negative occurrence patterns in one branch SCC are projections with constant rank and exact structural reachability.

**Status:** source-level result. **Scope:** The same-SCC restriction is essential; see RG-048 for the failure of arbitrary cross-SCC baseline inference.

### 1. Same-layer joint markers are projections at every native context

Let L be one SCC of a valid, reachable-reduced routed graph, and let G(u)
be its complete native contraction. For b in L let G_b(u) retain just branch
b at its vertex. Fix every filler outside L, temporarily. The green-layer
marker theorem gives

    G_b(u)=K_b G(u),

where K_b is a future projection independent of all fillers in L. Add a
phase at a second branch c in L and extract its coefficient from this same
identity. If b,c belong to different vertices, multilinearity gives

    G_bc(u)=K_b G_c(u)=K_b K_c G(u).

Repeating with b,c interchanged shows [K_b,K_c]=0. If they are different
branches of one vertex, the mixed coefficient is zero and K_b K_c=0.
Induction gives, for any compatible finite list B of branches in L,

    G_B(u)G(u)†=product_(b in B) K_b,                 (1)

an orthogonal projection. For a red layer, the time-dual theorem instead
gives G_b=G P_b, with fixed past projections for the temporarily pinned
outside context. The same coefficient argument gives

    G(u)†G_B(u)=product_(b in B) P_b,                 (2)

also an orthogonal projection.

These are statements at **every** full native unitary context: the outside
fillers were arbitrary before being temporarily pinned. They do not claim
that a green K_b stays constant as those outside fillers vary. Rather,
K_b(u)=G_b(u)G(u)† is continuous there, and at every such context it is part
of the commuting same-layer family.

One may also use complete layer-status patterns. At every vertex v having
branches in L, take its L-branch projections together with

    K_(v,*)=I-sum_(b in L at v) K_b

(or the past versions in the red case). The star alternative says that v
uses a branch outside L. Products over these complete commuting alternatives
are projections, and coefficient extraction/inclusion--exclusion identifies
them with the corresponding exact occurrence-pattern restrictions of G.
Thus (1)--(2) apply to these patterns as well.

### 2. Constant rank upgrades a baseline zero to structural absence

The full native unitary parameter space is a product of U(d_b), including
every independently adjustable native branch. It is connected. The rank of
the projection in (1) or (2), or of a complete pattern projection, is a
continuous integer-valued function. It is therefore constant over the
entire native parameter space.

Consequently, if G_B(u0)=0 at one unitary baseline, then G_B(u)=0 at every
native unitary context. Unitaries span each actual native direct-sum algebra,
so multilinearity makes the entire marked coefficient tensor zero.

Conversely, suppose a consistent route section containing B exists. At
every vertex select the matrix unit that uses the incoming and outgoing
index tuples of that section, and choose a basis vector in each positive-
dimensional edge sector. At every vertex retain only that branch matrix
unit. All internal indices and basis vectors are then fixed consistently;
one boundary matrix entry of the marked contraction is 1. Hence its tensor
is not zero. The same argument handles a complete layer-status pattern,
choosing one outside branch wherever the pattern says star.

We obtain the exact criterion:

    A joint branch pattern confined to one SCC is reachable
    iff its marked coefficient is nonzero at any unitary baseline.

Equivalently, the normalized same-layer pattern projection has positive,
context-independent rank precisely for the reachable patterns. In
particular there are at most D nonzero complete patterns on a D-dimensional
boundary.

The special projection identities (1)--(2) are essential. A general pair of
branches in different SCCs need not have a normalized joint marker that is
a projection. The baseline-zero DAG counterexample remains valid: its
A0/B1 joint coefficient can be zero at one context and nonzero at another.
No generic joint-zero inference is used here.

### 3. Quartet consequences

At the common quartet baseline, every actual original-query native branch
has the fixed past marker from the audited joint-native tensor. Active
branch units at different original vertices satisfy

    0<P_b<=Q_i<=S_i,   0<P_c<=Q_j<=S_j,   P_b P_c=0

because S_i S_j=0 for i!=j. Therefore their jointly marked baseline
coefficient is zero. If b,c lie in the same SCC, Section 2 implies that
**they never co-occur in any globally consistent section**, for either SCC
color. This applies to arbitrary allowed active summands and multiplicities,
not merely Q_i=E_i or maximal supports.

Combined with the green passive-branch exclusion, a green SCC involving
several original queries contains only active original branches, and every
consistent section meets at most one of those original vertices inside the
SCC. Red SCCs may contain passive branches from several original queries;
only their cross-original active-active co-occurrences are excluded here.

### 4. No direct edges between the excluded branch pair

A useful elementary branch-graph fact makes this combinatorial restriction
more explicit. If two complete forward choices differ only in a branch a's
output coordinate and a is inactive in either corresponding section, that
section remains consistent after the coordinate change: the dormant choice
is unused. Forward univocality therefore makes both sections identical.
Hence any actual change of another status b requires a active on both
sides, and b active on one side. A green edge a->b therefore witnesses a
section where a and b co-occur. The reverse-choice argument proves the same
for a red edge (with the reversed arrow convention). A solid edge already
requires an actually co-occurring endpoint pair by its definition.

It follows that the cross-original active branches excluded in Section 3
cannot have any direct branch-graph edge between them. A path through other
branches need not have a single common section, so this does **not** exclude
an SCC connected through auxiliaries or other original passive branches.
No transitivity of co-occurrence is assumed.

### 5. Exact calibration

The green-Lugano checker [green_layer_future_marker_independent_check.py](../green_layer_future_marker_independent_check.py)
provides the required fixed-future family with losing-marker ranks 6,6,6.
Their pairwise joint ranks are 4 and their triple joint rank is 2; all are
nonzero and the corresponding sections exist. The literal reversed host
has the same joint pattern ranks from fixed-past markers. The companion
[branch_layer_joint_occurrence_checks.py](../branch_layer_joint_occurrence_checks.py) verifies all complete native
status patterns in that SCC, all direct-edge co-occurrence witnesses, and
the quartet active-active zero products from the exact physical fixtures.
These are calibrations of the proof, not a finite-context replacement for
the continuous constant-rank argument.

<a id="rg-028"></a>

## RG-028 — Product-dimension SCC capacity

**Statement.** The product of dimensions of jointly occurring branches divides the nonzero row-module dimension and is at most the external dimension.

**Status:** source-level result. **Scope:** Does not imply that the joint-marker rank is divisible by that product.

### Theorem

Let B be a set of branches that co-occur in a consistent section of one
SCC L of a valid finite dimension-balanced routed graph. If their actual
native dimensions are d_b, and the original past/future dimension is D,
then

    product_(b in B) d_b <= D.                         (1)

More precisely, there is a nonzero subspace W of the original past (for a
green L) or original future (for a red L) for which

    product_(b in B) d_b divides dim W <= D.            (2)

The rank of the jointly marked boundary coefficient need not be divisible
by this product. W is an auxiliary algebraic row-span subspace arising from
the partially exchanged map, not a presumed physical cut or a promoted
native interface. Only the actual co-occurring branch dimensions enter.

### 1. Reverse induction for a red layer

We prove the red case; time reversal gives the green case. Use the published
exchange induction on the time-reversed graph. The chosen red L becomes
green there, and all of its original strict-future branches can be filled
first at fixed native unitary values. Translate back to the original time
direction. Leave C=all branches of L and R=all original earlier branches
exchanged, where a fixed SCC topological order puts R before L. Any branches
incomparable to L may be placed in either group and fixed or recovered
accordingly.

The resulting partial exchange is a unitary

    T : P tensor C_out tensor R_out -> F tensor C_in tensor R_in.

The dual H2--H6 statements are the original-direction H2--H7 statements
appropriate to this reverse filling order. For b in C, the output-side
occurrence projector Z_b is supported on P tensor R_out: a red branch's
output projector has only strict-past support. In particular, Z_b commutes
with every C-output operator, not just its own.

All strict-future exchanges have been removed. H7 therefore states that
for every f in L(H_b,out) there exists a matrix K_b(f) on the original F
alone such that

    T f_(b,out) T† zeta_b,in = K_b(f)_F zeta_b,in.

H2 gives zeta_b,in T = T Z_b. Multiplying the last identity by T on the
right, and using that Z_b commutes with f, yields

    T Z_b f_(b,out) = K_b(f)_F T Z_b.                  (3)

No algebraic properties of the chosen ambient matrices K_b(f) are assumed.
They may be nonunique away from the subspace actually used below.

For co-occurring B, its branches lie at distinct vertices. Their commuting
occurrence projectors give Z_B=product_(b in B) Z_b and the exactly marked
map T_B=T Z_B by H5. Every C-output matrix commutes with every factor of
Z_B. Multiplying (3) by the other factors gives, for each b in B,

    T_B f_(b,out) = K_b(f)_F T_B.                       (4)

This step neither requires different K_b to commute on all of F nor uses
any whole-vertex substitution for a partially free branch family.

### 2. Recover the old past without losing the intertwiner

For r in R, its output-side occurrence projector is supported on P tensor
R_out, with no C_out factor. For a green r its non-strict past can include
its own earlier SCC, and for a red r only its strict past is needed; neither
can include the later L. At each vertex with R branches, build the
right-domain occurrence alternatives from its R projectors together with
I minus their sum. The latter includes the current C siblings and already
filled strict-future siblings. Their products Pi_q form the complete
right-domain R patterns.

Use the exact recovery from [RG-026: One-SCC fixed occurrence markers](layer-structure.md#rg-026):
close an active R branch with its desired fixed filler, and an inactive
branch with Theta_r†/d_r. H4/H5 and inclusion--exclusion make this the exact
partial native contraction, also with B marked. Incompatible R siblings of
marked C branches contribute zero; the complementary pattern retains them.

Every Pi_q commutes with each f_(b,out), because it has no C_out support.
The closures of R exchange ports also commute with f, and K_b(f) acts only
on F and so passes outside every contraction. Thus (4) survives unchanged:

    S_B f_(b,out) = (K_b(f)_F tensor I_Cin) S_B,        (5)

where S_B : P tensor C_out -> F tensor C_in is the actual jointly marked
partially exchanged map with all branches outside C filled. This is the
only required recovery invariance. No factorization into a parallel comb,
no product-domain physical cut, and no positivity of K_b(f) was assumed.

### 3. A nonzero jointly marked exchange exists

A co-occurring route section makes the fully marked native coefficient
tensor nonzero: select the compatible branch/index/quantum-basis matrix
unit at every vertex; one boundary entry of the contraction is 1. Native
unitaries span every actual direct-sum algebra, so there is a tuple of
native unitary fillers where the fully marked map is nonzero. Fix the
outside fillers to their values in that tuple. Recovering the current C
fillers from S_B by the exact branch-pattern rule gives that nonzero fully
marked map. Hence S_B itself is nonzero.

This argument is sufficient on its own. The stronger same-SCC joint-rank
faithfulness in [RG-027: Joint status faithfulness within one SCC](layer-structure.md#rg-027) also shows that a
reachable same-layer pattern has nonzero fully marked coefficient at
*every* unitary baseline. Neither assertion is a generic rule for branches
in different SCCs.

### 4. The partial-row span is a matrix-algebra module

Let W be the span in F of all vectors

    (I_F tensor <c|) S_B |x>,

where c ranges over a basis of C_in and x over P tensor C_out. Since S_B is
nonzero, W is nonzero. Equation (5) shows that every K_b(f) preserves W.
Moreover its restriction to W is uniquely determined by f: two choices
with the same intertwining action agree on this spanning set.

Write rho_b(f)=K_b(f)|_W. Applying (5) to arbitrary x and c proves directly:

    rho_b(f+g)=rho_b(f)+rho_b(g),
    rho_b(lambda f)=lambda rho_b(f),
    rho_b(I)=I_W,
    rho_b(f)rho_b(g)=rho_b(fg).

For different b,c the C-output matrices commute. Equation (5) then gives

    [rho_b(f),rho_c(g)]=0 on W.

Therefore multiplication defines a unital complex algebra representation

    rho : tensor_(b in B) M_(d_b) -> End(W).

The source is the simple algebra M_n with n=product d_b. The representation
is nonzero and unital. Using its matrix units E_aa, W is the direct sum of
the subspaces rho(E_aa)W, and rho(E_ab) gives isomorphisms between them.
Consequently dim W=n m for a positive integer m. Since W is a subspace of
F, this proves (1)--(2). No adjoint preservation or *-unitarization is needed.

Reversing the entire argument places W in the original past for a green L.
If private ancillas are included, their boundary factors and the applicable
native branch dimensions are included consistently; no private multiplicity
is silently turned into an independent branch.

### 5. Quartet consequences and limits

At D=16, four co-occurring passive original branches already contribute
2^4=16. Thus no additional native branch of dimension greater than one can
co-occur with those four passive branches **inside the same SCC**. The
statement also applies to a mixed active/passive selected pattern, with
its actual branch dimensions, whenever that pattern is reachable.

If one SCC contains all four passive originals, their jointly marked
quartet baseline is I-sum_i Q_i and has rank at least four. They therefore
co-occur. In a red SCC this is not excluded by the green-marker theorem,
but it leaves only dimension-one co-occurring auxiliary branches in that
SCC on these all-passive sections. In particular, such a red SCC cannot
contain every branch of another native vertex if all those branches have
dimension greater than one: a section using all four passive originals
must use one branch of that additional vertex as well.

Auxiliary branches outside the SCC are not counted. Nor does this bound
exclude auxiliary quantum branches elsewhere in the same SCC on different
sections. Same-SCC co-occurrence is essential; a serial circuit may of
course use arbitrarily many quantum vertices in different SCCs.

### 6. Exact calibration

[branch_layer_product_dimension_checks.py](../branch_layer_product_dimension_checks.py) uses the actual Lugano host
already fully checked for both choice directions and weak loops. It
constructs the 512-dimensional all-laboratory exchange permutation and
marks the three losing branches, then time reverses it. All 12 matrix-unit
intertwiners of the three M2 factors hold before recovery. It also checks
them after exact recovery of the winning sibling branches, obtaining the
64-dimensional marked exchange. Its partial-current-input row span W has
dimension eight, so the product 2*2*2=8 saturates the bound on D=8.

After finally closing current fillers at the identity, the normalized joint
marked boundary projection has rank only two. This explicitly rules out
the tempting but false strengthening that the boundary marker rank must
be divisible by the product. The same W computation for each one- and
two-branch subset gives the required divisible module dimensions.

The proof depends only on the published exchange invariants, exact
pattern-resolved recovery, and native skeletal coefficient faithfulness.
It does not require a graph realization of a complete auxiliary tensor.

<a id="rg-029"></a>

## RG-029 — No-path marked operational order

**Statement.** No-path marked operational order

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### Statement

Let a finite dimension-balanced routed host be bi-univocal and satisfy the weak-loops condition. Use its globally reachable-reduced branch graph, with all solid, forward-green, and reverse-red arrows. Fix arbitrary unitary native fillers at every reachable branch as a common baseline. Let b and c be branches of distinct native vertices. Assume there is no directed path b ->* c in this branch graph.

Vary only the actual native filler x on c; all its sibling fillers remain at their baseline values. Fix b at baseline when defining its exact occurrence-marked contraction. Normalize the global baseline to identity by fixed boundary unitaries. Write:

- G(x) for the actual affine native contraction;
- G_b(x) for the same contraction restricted to occurrence of b;
- rho_c(x) for the contraction restricted to occurrence of c, linear in its actual matrix x;
- G_bc(x) for the contraction restricted jointly to b and c;
- P_b = G_b(x_0), with x_0 the baseline filler of c.

Then the following identities hold for every x in the full actual matrix space of branch c:

    G_b(x) = P_b G(x),
    G_bc(x) = P_b rho_c(x).

Here P_b is an orthogonal projection. The identities concern actual branch insertion, not an artificial whole-vertex matrix query c ⊕ I. More generally, the proof gives a fixed future marker while any subset of the branches left exchanged at the chosen boundary varies independently; branches already filled there stay at their specified baselines.

### 1. Choose one reverse-induction boundary

Let L(b) and L(c) denote the SCCs of b and c. Absence of b ->* c implies these are distinct and the SCC condensation has no path from L(b) to L(c). Therefore a topological total ordering can place L(c) strictly before L(b). Reverse this order and apply the published exchange induction to the time-reversed routed graph. Original green layers become reverse red layers, and original red layers become reverse green layers.

The exact H2 output-side support rule used in the reverse graph is:

    Z_rev,out(a) acts on P_rev tensor (past_rev(a) ∩ E)_out,rev
        if a is reverse green;
    Z_rev,out(a) acts on P_rev tensor (strict_past_rev(a) ∩ E)_out,rev
        if a is reverse red.

Here P_rev=F, reverse output exchange factors are original input exchange factors, past_rev is original future, and strict_past_rev is original strict future. These are precisely the two cases of H2 preceding equation (53) in Appendix B.4.2. H2 defines all remaining projectors except at a special step, which is explicitly the condition that the just-filled and next-to-fill branches belong to the same reverse-red layer.

Use adjoints of the fixed original baseline fillers in this reverse induction. Translating its partially filled exchange back to the original direction leaves an original unitary

    T : P tensor E_out -> F tensor E_in,

where E is the set of branches still exchanged. The original fillers already inserted are their prescribed baselines. In particular c remains exchanged at either boundary below.

Case A: b is in an original green layer. Stop immediately before filling any branch of L(b). All original layers after L(b) have been filled. This is the start of a reverse-red layer, not a special step. Thus H2--H5 are available for every branch in E. The reverse output-side occurrence projector for b is supported on the reverse global past and the still-exchanged strict reverse past. This is original F plus the still-exchanged original strict future of b. The latter set is empty. Hence, after translating orientation, the b input-side marker is a projection K on F alone.

Case B: b is in an original red layer. Within its reverse-green layer, choose b last, and fill all its other branches first at baseline. Stop immediately before filling b. A reverse-green layer has no special-step exception; H2--H5 are available for all remaining branches. The reverse output-side marker of b can involve only the reverse global past and the still-exchanged reverse past. Equivalently, its original input-side marker can involve F and the still-exchanged original future of b, including its own SCC. All those other branches have already been filled. A marker never acts on its own branch's exchange factor. Thus this marker is again a projection K on F alone.

Singleton SCCs may be colored either way; either allowed choice gives the same conclusion. The relevant endpoint is always a non-special reverse-induction step. No property of a temporarily undefined projector is used.

The reverse H5 identity, after taking its adjoint, now says exactly

    T_b = (K_F tensor I_Ein) T,                         (1)

where T_b retains b's actual exchange summand and removes every other summand at b's native vertex. This K can depend on the already filled baseline branches, but cannot depend on x at c, which is still exchanged.

### 2. Exact simultaneous recovery with pinned siblings

For each actual native vertex v, let E_v be its still-exchanged branches. On T's right-hand domain use the mutually orthogonal alternatives

    Z_a = zeta_a,out, a in E_v;
    Z_(v,*) = I - sum_(a in E_v) Z_a.

The star alternative is the sum of all already filled branch summands at that same native vertex. It is not a whole-vertex substitution. If no branch at v has been filled, the star alternative is zero. Products over vertices form a complete commuting pattern partition Pi_p. H4 kills incompatible siblings, and H5 plus inclusion--exclusion identifies T Pi_p with the exact native exchange contraction restricted to that pattern. H5 is only applied to sets with at most one branch per actual vertex.

For each a in E, choose its desired actual filler u_a, taking u_c=x and all other fillers at baseline. In pattern p close a's exchange ports by

    u_a                  if p selects a;
    Theta_a^dagger / d_a  if p does not select a.

The active swap closes to u_a. The inactive bypass closes to

    Tr[(Theta_a^dagger / d_a) Theta_a] = 1.

Sum the resulting pattern-restricted contractions. This is a linear recovery map R_u on exchange tensors and gives exactly the actual native contraction:

    R_u(T) = G_raw(u).                                (2)

There is no inverse trace, restriction to generic unitaries, limit argument, or changed native algebra.

The identical patterns and identical closures also recover the b-marked map. To see this explicitly, (1) is also T_b=T Z_b. At b's vertex a pattern either selects b, in which case Z_b Pi_p=Pi_p, or selects a sibling/star, in which case Z_b Pi_p=0. Thus recovery of T_b retains precisely the b-occurrence terms. This includes the case that other siblings of b were filled before the chosen boundary. All other vertices keep exactly the same alternatives. Hence

    R_u(T_b) = G_raw,b(u).                            (3)

Since K acts only on the uncontracted original F factor, it factors through right multiplication by every Pi_p and through every exchange-port closure. Applying the same recovery to (1) proves

    G_raw,b(u) = K G_raw(u).                          (4)

In particular, even if a right-side pattern projector involves c_out, it occurs identically in (2) and (3) and cannot prevent factoring K. This is why pinned-sibling recovery introduces no unproved dependence on c.

### 3. Normalize and extract the joint coefficient

Let the fixed baseline boundary map be G_raw,0. For example normalize by G=G_raw,0^dagger G_raw. Equation (4) becomes

    G_b(u) = P_b G(u),
    P_b = G_raw,0^dagger K G_raw,0 = G_b(u_0).

This P_b is a projection because K is. Other fixed unitary input/output baseline normalizations give the same statement in their corresponding coordinates.

With all siblings of c pinned, the exact native contraction is affine in c's matrix, with its linear part equal to rho_c. The b-marked contraction has linear part G_bc. Taking linear parts of the preceding identity yields

    G_bc(x) = P_b rho_c(x)

for every native matrix x. Equivalently, subtract the identity at x=0 from the identity at arbitrary x. No promotion of the affine c insertion to a unital matrix query is involved.

### 4. Sufficient path criterion in the question

Use local baseline coordinates so c's baseline is I, and put Q_c=rho_c(I). Suppose the actual two-variable native family is

    G(x,z) = [I-Q_c+rho_c(x)] [I+(z-1)P_b]

for every full native matrix x and scalar phase z, with siblings fixed. Its joint marked coefficient is

    G_bc(x) = rho_c(x) P_b.

If there were no path b ->* c, Section 3 would instead give G_bc(x)=P_b rho_c(x). Thus the assumed static order and no-path condition force

    [P_b,rho_c(x)] = 0 for all x.

Consequently, if [P_b,rho_c(M_dc)] is nonzero, the actual full branch graph contains a directed path b ->* c.

The same implication follows if the displayed family is initially known only for all native unitary x and unit-modulus z: coefficient extraction and the linear span of native unitaries extend it to every matrix. Distinct native vertices ensure the two marks are genuine independent multilinear slots.

### 5. Scope and primary dependencies

The proof uses only the time-reversed published exchange induction at one non-special step, H2 support and projector commutation, H4 sibling orthogonality, H5 exact occurrence restriction, and the literal active/inactive exchange formula. It does not invoke H6 on an arbitrary red branch, a global algebraic cut, SCC fragment unitarity, or presumed operational DAG causality.

Primary source: Vanrietvelde et al., arXiv:2206.10042v3, Appendix B.4, especially the branch path convention, the special-step qualification of H2, equations (50), (53), (56)--(57), and the active/inactive refill equations (88a)--(88b):
https://arxiv.org/html/2206.10042v3

### 6. Exact cyclic calibration

[check_no_path_lugano.py](../branch_path_causality/check_no_path_lugano.py) reconstructs the literal binary Lugano host with three M2+M2 laboratories, one eight-branch scalar hub, and one M8 decoder. Its branch graph is computed on all 64 forward choice assignments, including dormant choices, and all eight reverse choices. All 15 branches are reachable. It has 36 green arrows, 14 red arrows, and no solid arrows. Its only recurrent SCC is the three losing laboratory branches; it is green in the forward host and red in the reverse host.

The baseline uses distinct nonidentity rational rotations on both siblings at every laboratory, nontrivial scalar hub signs, and a dense rational decoder. Global baseline unitarity is checked exactly. For every pair of distinct native vertices with no directed b-to-c path, and every matrix unit in c's full actual matrix algebra, the checker verifies the normalized identity G_bc(x)=P_b rho_c(x). It checks 92 no-path pairs in each direction: 290 native matrix-unit identities forward and 1,064 in reverse. Baseline identities then also give the full affine G_b(x)=P_b G(x) statement.

The path condition is independently guarded by negative controls on reachable pairs. A forward losing-branch/decoder example has squared Hilbert--Schmidt defect 784/15625. A reverse pair within the red recurrent losing SCC has defect 3872/15625. Thus the test would reject dropping the graph-path hypothesis or indiscriminately applying a fixed future marker within a red SCC.

<a id="rg-036"></a>

## RG-036 — Full-matrix downset factorization

**Statement.** Every branch-graph downset has exact recovered D-dimensional tensor factors, including red layers and split native vertices.

**Status:** source-level result. **Scope:** An algebraic factorization with shared original variables, not physical graph compression.

### Claim

Let a finite dimension-balanced, bi-univocal, weak-loops routed host be globally reachable-reduced. Fix arbitrary unitary baselines at its actual native branches. Let A be any downset of its full branch graph: if c has a directed path to a branch of A, then c belongs to A. Put R=Bran\\A. The graph uses all solid, forward-green, and reverse-red arrows.

There are fixed-size memory spaces and separately recoverable unitary families W(u_A), V(u_R) such that the actual native contraction obeys

    G_raw(u_A,u_R) = V(u_R) W(u_A).

Here different branches of an auxiliary native vertex may lie on different sides. The identities concern its actual direct-sum branch fillers with every sibling present, not artificial unital whole-vertex matrix queries. Parameter sharing across the two sides is permitted as an algebraic identity, although it does not make them independent original-query processes.

In particular, if no original-query branch has a path to the auxiliary branch b, take A=Anc(b) union {b}. Every original-query branch belongs to R. Fix all other auxiliary fillers. At a normalized baseline F(I)=I, let G_b(a,U) be the actual b-marked contraction, with b's filler u_b,0 a, and beta_b(a)=G_b(a,I). Then

    G_b(a,U)=F(U) beta_b(a),
    G(U;a)=F(U)[I-Q+beta_b(a)],  Q=beta_b(I).

No assumption rank(Q)=d_b is used.

### 1. The missing red input-algebra lemma at the all-exchange context

Let T be the all-exchange unitary of Appendix B.4, and Z_b its output-side occurrence projector (a projector on T's domain). Write Ad_T for conjugation by T. For a green branch b, published H6 gives

    Ad_T^*(f_b,in) Z_b = f'_strict-past Z_b.

For a RED branch b the same base-case computation, equations (76)–(86), proves the weaker but sufficient identity

    Ad_T^*(f_b,in) Z_b = f'_past Z_b,                 (R6)

where f'_past acts on the global past and the exchange outputs of ALL branches in P(b), including b's red SCC but excluding b itself.

This is not an application of published H6 to red b. It is a new lemma obtained from its explicit all-exchange calculation. The substitutions are justified as follows. Set K=P(b). The base calculation needs precisely these graph exclusions:

1. No red arrow c->b for c outside K. This follows from the definition of past; the own-branch status cannot depend on its own reverse choice by reverse univocality.
2. No solid arrow c->d with c outside K and d in K union {b}. For c != b, such an edge followed by d->*b would put c in K. For c=b and d in K, it would be a solid edge in b's SCC, forbidden by weak loops. A solid self-loop is forbidden as well.
3. No green arrow c->d with c outside K and d in K. Again transitivity settles c != b. If c=b, d must be in b's SCC and a green edge there contradicts that the SCC is red.

A sector-embedding point in the last independence step deserves an explicit lemma. Suppose c outside K co-occurs with b and a physical wire runs from c's vertex to b's vertex. Absence of a solid c->b arrow says that, conditioned on the endpoint branch pair, this wire has one compatible index k and its sector is one-dimensional. Fix a complete reverse-choice context witnessing the pair. Change only b's reverse choice to ANY of its allowed full native input tuples. Own-branch reverse univocality keeps b active. Absence of a red c->b arrow keeps c active. The pair condition therefore forces that new tuple's wire coordinate to be the SAME k. Hence every allowed input tuple of b uses the same scalar sector on this physical wire. Its contribution to the embedding p_b in (85) is fixed across all outside choices. This rules out a hidden dependence of the off-diagonal f matrix entry on which outside branch happened. The identical lemma holds for any cross-edge from a branch outside a downset into a branch inside it. It uses complete inverse choices, including dormant coordinates, and does not resolve a quantum sector into a new center.

For incoming scalar embeddings at other inside branches d in K, the same observation applies to outside c != b, since a red c->d would put c in K. The exceptional outside label c=b can have a red edge into K and must be handled separately: b is fixed active in the marked sandwich, no solid edge b->d makes its scalar index fixed for each selected d, and that d selection depends only on K choices by the no-green exclusion. Thus no nonexistent no-red b->K premise is used.

The first exclusion gives equality of bra/ket statuses for all branches outside K, exactly as in (77)–(78). The second makes every nontrivial physical wire leaving such an outside branch untouched by f and the inside contractions, giving the outside diagonal projectors of (81). The third makes the remaining coefficient in (85) independent of outside forward choices, as used in the paragraph after (85). Bi-univocality gives the same zero extension in (83)–(86). Thus replacing every P^str(b) in the base H6 calculation by K=P(b) proves (R6), with no other use of the color of b. Native multiplicity and off-diagonal matrix units are retained in this calculation.

Singleton b can be designated green. Only genuinely recurrent red layers need (R6).

### 2. The all-exchange unitary is quantum causal across any downset

Use tensor products A_o, A_i, R_o, R_i of the corresponding branch exchange factors. The all-exchange map is

    T: P tensor A_o tensor R_o -> A_i tensor F tensor R_i.

For every b in A, H2 gives Z_b supported on P tensor A_o, since all of b's past is in A. The active part of T^* f_b,in T is supported on P tensor A_o by published H6 if b is green and by (R6) if b is red.

For the inactive part, the literal b exchange wire is the bypass Theta_b, so

    T^* f_b,in T (I-Z_b)
      = (Theta_b^* f Theta_b)_b,out (I-Z_b).

This follows from H5 and summing all other native summands at b's vertex. It includes siblings at that vertex on either side of the partition. Adding active and inactive parts proves

    T^* [L(A_i) tensor I] T
       is contained in L(P tensor A_o) tensor I_Ro.   (1)

Indeed the individual b input algebras generate the full matrix algebra L(A_i). This is a complete full-matrix no-signalling statement, not a phase or diagonal-sector assertion.

Finite-dimensional representation theory applied to (1) supplies unitaries

    W: P tensor A_o -> A_i tensor M,
    V: M tensor R_o -> F tensor R_i,
    T=(I_Ai tensor V)(W tensor I_Ro).                 (2)

Because native branches are balanced, dim(A_o)=dim(A_i), hence dim(M)=dim(P). W and V are algebraic factors of T, not purported physical graph fragments.

### 3. Exact future recovery, including split native vertices

For each native vertex v that has R branches, the commuting output-side alternatives are

    K_c=zeta_c,in, c in R at v;
    K_v,*=I-sum_(c in R at v) K_c.

Every K_c acts on F tensor R_i: H2 allows only c's future (strict future if c is green), and a future of c in A would contradict downclosure. Therefore their commuting pattern products K_q act entirely inside V in (2). H4 gives sibling orthogonality. H5 and inclusion-exclusion identify (I_Ai tensor K_q)T with the exact exchange contraction restricted to that native pattern. The star alternative at a split vertex is exactly the sum of all its A summands. Vertices with no R branch are not restricted in this recovery.

In each pattern close each R branch c using

    u_c                      if c is selected;
    Theta_c^*/d_c             otherwise.

The active swap recovers the actual filler u_c. The inactive bypass yields Tr(Theta_c^* Theta_c)/d_c=1. Summing all patterns is an exact linear recovery; no trace denominator depending on u_c, generic context, or limit is required. Because the patterns and closures lie entirely in V, the recovered unitary has the form

    T_R(u_R)=(I_Ai tensor V(u_R))W.                   (3)

It is the actual routed host with R fillers inserted and A exchanges still present. Each local partially exchanged operation is a routed unitary on its branchwise direct sum, even at a vertex with both A and R branches. The superunitary theorem therefore makes T_R(u_R) unitary for every native unitary context. Equation (3) implies V(u_R) is unitary.

### 4. Exact ancestral recovery

For each vertex with A branches use domain-side alternatives

    Z_a=zeta_a,out, a in A at v;
    Z_v,*=I-sum_(a in A at v) Z_a.

They act on P tensor A_o. Their pattern projectors Pi_p commute with R closures. Also, (I_Ai tensor K_q)T Pi_p is the exact jointly restricted native contraction: incompatible A/R siblings vanish by H4; compatible conditions are precisely H5 plus inclusion-exclusion. Thus the same Pi_p still select the exact A occurrences in T_R(u_R).

Applying the same active-u/inactive-Theta^*/d closure to A factors in (3) therefore gives

    G_raw(u_A,u_R)=V(u_R) W(u_A).                    (4)

The star term at a split vertex selects its already filled R summands. It does not insert a new native matrix freedom or use a query twice. For any fixed u_R baseline, global unitarity and unitarity of V imply that W(u_A) is unitary for every unitary u_A.

Using the same patterns but retaining only the b occurrence gives

    G_raw,b(a,u_R)=V(u_R) W_b(a).                    (5)

Here a can be any actual matrix, by linearity; all siblings remain pinned to their specified values.

### 5. Normalize and obtain the requested identity

Set W_0=W(u_A,0) and V_0=V(u_R,0), and normalize on the left by (V_0 W_0)^*. With all A fillers fixed except b's u_b,0 a,

    F(U)=W_0^* V_0^* V(U) W_0,
    beta_b(a)=W_0^* W_b(a).

Equation (5) gives exactly G_b(a,U)=F(U)beta_b(a). The unmarked complement is unchanged when b varies, so G(U;a)=F(U)[I-Q+beta_b(a)]. Actual one-port ancillary completeness identifies beta_b as the supported *-homomorphism with unit Q, but that identification is not needed for the factorization itself and no multiplicity-one hypothesis enters.

Private ancillas can be carried throughout as external input/output systems at each native vertex. Equivalently apply the same proof to the locally amplified routed host; trivial external index sets introduce no internal branch edge and all native branches remain balanced. A common original-query ancilla can act on all its R branches, since they are all on the R side. Branch-private ancillas embed in the tensor product ancilla at their actual native vertex. Thus (4)–(5) hold coefficientwise with arbitrary independent local ancillary extensions, without granting an unrestricted joint operation to several vertices.

### 6. Time dual

If there is no path b->*c for any original-query branch c, apply the theorem to the reversed routed graph, whose colors interchange. The resulting exact future form is

    G_b(a,U)=beta_b(a)F(U),
    G(U;a)=[I-Q+beta_b(a)]F(U),

with the input/output baseline coordinates correspondingly identified. If both no-path conditions hold, beta_b(M_d) commutes with every F(U).

### Primary dependency and audit target

Primary source: Vanrietvelde et al., arXiv:2206.10042v3, Appendix B.4, equations (50), (53), (56)–(59), (76)–(86), and (88a)–(88b): https://arxiv.org/html/2206.10042v3

The only new source-level lemma is (R6), the past-supported all-exchange red input algebra. The independent audit checked the three stated graph exclusions against every use of P^str in (76)–(86), including scalar-sector embeddings, and checked the two-sided pattern recovery when one auxiliary native vertex has branches on both sides. The proof never invokes the special red induction step or H6 for an already partially filled red layer.

### 7. Exact calibrations

The independent standard-library all-exchange checker [check_downset_exchange_permutation.py](../upstream_matrix_causality/check_downset_exchange_permutation.py) verifies 14 minimal ancestral downsets/orientations in the literal binary Lugano exchange permutation, including 176 full matrix units and 163,840 exact actions. It separately checks (R6) for all three reverse red losing branches, and rejects an illegal singleton cut through that SCC.

The actual native recovery calibration [RG-037: Red split-vertex calibration](layer-structure.md#rg-037) and its checker use a 48-branch routed host with a six-branch red SCC, five native vertices split across the ancestral cut, and a marked M2 branch of rank 20 (multiplicity 10). All 16 joint native matrix-unit identities pass at nonidentity rational baselines. Dropping no-path inside the red SCC gives an exact squared Hilbert--Schmidt defect of 3. The scalar sibling at the marked vertex is pinned outside the cut.

The additional `lugano_probe.py` verifies 5,008 exact joint native coefficient identities across all 184 allowed no-path pairs in ordinary Lugano and its reverse. These finite tests calibrate the proof; they do not replace its general argument.

### Required proof qualifications

At a red active branch the incoming tuple is fixed by the branch itself; the input algebra remains the full practical matrix algebra after direct-sum sector bookkeeping. Recover each native branch with the same complementary sibling pattern in both factors. This covers split vertices without replacing them by independent original queries.





**Reproduction limit:** supporting helpers were not supplied; the analytic argument remains available. See the [artifact map](../REPRODUCIBILITY.md#rg-036).

<a id="rg-037"></a>

## RG-037 — Red split-vertex calibration

**Statement.** Red split-vertex calibration

**Status:** exact calibration. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### Literal routed construction

Start with the controlled Lugano host described and certified in `routed_graph_new/fragment_audit.md`: selector S has M4, each of three laboratories has M2+M2, hub H has 32 scalar branches H^(s,o), decoder D has M32. Its boundary dimension is 32 and its six laboratory branches form one green SCC. With o=(a,b,c), use w(o)=(b(1-c),(1-a)c,a(1-b)) and the four selector shifts 000,100,010,001.

Take a coherent direct sum of this whole host (mode 1) and a 32-dimensional bypass (mode 0), then add full M64 source and sink caps E and Z. Their two practical sector tuples are m=0,1, each of total dimension 32. Their native branches each have full M64 freedom. All outside boundary indices are singleton.

The sum is an actual route, not an assumption about a fragment:

- E's mode-1 tuple sends dimensions 4,2,2,2 to S and the three labs. Its mode-0 tuple sends dimension 32 to H. Unused payload sectors are scalar. E sends the same scalar mode label to every other vertex
- S and each lab keep their original mode-1 branches and get one scalar mode-0 bypass branch. The existing hub/lab index wires get a special scalar mode-0 label
- H keeps all 32 original scalar mode-1 branches. It also has one mode-0 M32 branch taking E's bypass payload and sending it to Z; every other input/output at that branch is fixed scalar
- D keeps its mode-1 M32 branch and gets a scalar mode-0 branch
- Z's mode-1 tuple receives the 32D D payload, and its mode-0 tuple receives the 32D H payload, all unused inputs being scalar

Every branch is a disjoint rectangular route of balanced dimension. Source/sink native matrices can coherently mix modes. Every stated branch is reachable.

The 512 complete forward choices are source mode m, the selector's four choices, and all six laboratory bits (including dormant mode-0 choices). The 64 complete reverse choices are sink mode m and D's 32 reverse choices. Each gives one section: if m=0, the fixed bypass; if m=1, the unique controlled-Lugano section. This establishes bi-univocality on complete choices, not only on active choices.

All extra solid edges are E->S_active, E->L_i^x, E->H_bypass, D_active->Z, and H_bypass->Z. The old active links through the scalar hub still have fixed 1D indices for every co-occurring endpoint pair. Extra forward dependence comes only from E's mode choice; extra reverse dependence points only to Z. Thus weak loops are preserved, and the only recurrent SCC is the original six-branch green laboratory SCC.

Now reverse the full graph. The six laboratory branches form a genuine RED SCC. For b=L_0^0, let A be its full ancestral downset in this reverse graph. The exact certificate gives |A|=40 out of 48 reachable branches. A contains every active lab branch, every active hub branch, D_active, and Z. It excludes E, both S branches, every lab's scalar sibling, H_bypass, and D_bypass. Hence FIVE actual native vertices straddle A and its complement: all three labs, H, and D. In particular b belongs to a branched vertex whose scalar sibling is pinned outside A.

The original query is the complete unital M2 inclusion U -> U tensor I32 in native M64 cap E, which lies outside A and has no reverse path to b. This query mixes the two coherent global modes. All auxiliary siblings retain full native matrix spaces; their particular baselines are merely fixed.

### Exact matrix test

Use nonidentity rational rotations at all six M2 branches and at selector S, nontrivial scalar hub signs, and a nonidentity permutation at the M32 bypass sibling. Baseline caps are identities. The literal forward map is diag(H_bypass,M_controlled), and the reverse is its adjoint.

For every matrix unit a in b's full M2 and every matrix unit U in the original M2 query, the checker verifies

    G_b(a,U)=F(U) beta_b(a).

All 16 exact rational coefficient identities pass. Q=beta_b(I) is explicitly checked to be an orthogonal projection, with

    rank Q = 20,   d_b = 2,   rank Q / d_b = 10.

Thus the test has repeated multiplicity, an actual red SCC, and pinned siblings on the other side of the ancestral cut. It does not split the represented center into rank-two pieces.

A negative control makes another lab branch in the same red SCC the varying query and drops the no-path hypothesis. An actual pair of matrix units then has squared Hilbert--Schmidt defect 3. The test would reject an unqualified full-matrix orientation assertion inside a red SCC.

Files: [red_split_vertex_calibration.py](../upstream_matrix_causality/red_split_vertex_calibration.py), [red_split_vertex_checks.json](../upstream_matrix_causality/red_split_vertex_checks.json), and `red_split_vertex_calibration.log` under `source/`.
