# Core obstruction

[Topic index](../../README.md) · [Shared result index](../../../../RESULTS.md#rg--exact-native-routed-graph-universality)

Each result below has one owner. Exact scope and proof are updated here. Source-level mathematical arguments and finite certificates are distinguished from a new formal verification.

<a id="rg-030"></a>

## RG-030 — Single-branch centrality and all four active ideals

**Statement.** An actual unbranched query forces branch-central comparison. In the quartet all four Q_i are nonzero, hence at least eight original-query branches.

**Status:** source-level result. **Scope:** The former three-port cover lower bound is subsumed; the general nonseriality-graph cover criterion remains a corollary.

### Main statements

**Branch-centrality theorem.** In a valid reachable-reduced routed host,
suppose one original matrix query i occupies a native vertex having a single
reachable branch. Fix all other vertices except one native vertex j. Use a
common normalized baseline, and write the resulting complete pair as

    G(x,a),  G(I,1)=I,
    alpha(x)=G(x,1),  rho(a)=G(I,a).

Here a ranges over the ENTIRE actual native direct-sum algebra at j. There
is a sum e of central native branch identities at j such that P=rho(e)
commutes with alpha(M_d), and

    G(x,a)=alpha(x) rho(a) P + rho(a) alpha(x) (I−P).       (1)

Thus the two order sectors are branch-central at j, not arbitrary sectors
of a hidden representation multiplicity. No uniqueness of P is claimed.

**Quartet consequence.** If the branch-centrality theorem holds, every
original quartet query must have a nonzero classified active ideal:

    Q1 != 0, Q2 != 0, Q3=E3, Q4=E4.

In particular every original query vertex has at least two reachable native
branches, giving at least eight such branches in total and total active
physical rank at least eight. This is still only a host necessity. The
complete all-Q_i=E_i orthogonal-column tensor remains compatible with these
bounds and does not itself supply or exclude a routed graph.

The key proof point is the following branch-free-variable endpoint lemma.
It is proved directly from the audited exchange argument, rather than
misapplying its old original-query statement to an affine insertion.

### 1. Endpoint extraction with pinned siblings and free native branches

Fix a topological ordering of the branch SCCs. Let N be a native vertex
having one globally reachable branch n, whose SCC is a singleton. Put an
original matrix query x at N through its complete monopartite filling.

**First-end version.** Pin every branch strictly before n to a specified
unitary baseline. Branches strictly after n may have arbitrary independent
native unitary fillers, with any subset instead pinned to baseline. A
vertex other than N may have both pinned and free branches. Then

    H(x,u)=H(I,u) K(x),                                  (2)

where K is a fixed unital *-representation independent of all free branch
fillers u. For any common baseline u0,

    K(x)=H(I,u0)† H(x,u0).

**Last-end version.** Pin every branch strictly after n. Arbitrary native
branches before n may remain free. Then

    H(x,u)=L(x) H(I,u),                                  (3)
    L(x)=H(x,u0) H(I,u0)†.

These statements do NOT assert that a map b↦b⊕I is a unital linear matrix
query. The free variables are simply actual independently adjustable native
branch fillers elsewhere in the graph.

#### Proof of the first-end version from H1–H6

A constant-status branch belongs to no directed cycle: no green edge enters
it and no red edge leaves it. Weak loops therefore place n in a singleton
SCC without a self-loop. Declare this singleton green.

Use the published partial-exchange induction after every branch before n
has been filled at its pinned baseline. Leave n and all later branches
exchanged; later pinned branches will also be recovered at their fixed
values. H1 makes the resulting exchange map T unitary.

Because N has only one reachable branch, the sum in H5 at N consists of
that branch alone. Hence its input and output occurrence projectors are
both I. This conclusion is valid after partial filling and does not assert
that any other branch status is constant.

Normalize N's native query as F_N(x)=F_N(I) pi(x), where pi is a unital
*-representation on the practical native input. On n's exchange-input
factor, pi(x) is an ordinary full-support matrix. H6, with the occurrence
projector I and no remaining strict-past exchange ports, gives

    T† pi(x)_(n,input) T = K(x)_P tensor I.               (4)

Conjugation by T shows multiplicativity, adjoint preservation and unitality
of K. Thus K is supported on the original past alone and is independent of
all still-exchanged later fillers.

For every later branch c, H2 puts its exchange-input-side occurrence
projector on its allowed future factors, excluding n's exchange input.
It therefore commutes with pi(x). Pulling back with T shows its output-side
occurrence projector commutes with K. This statement includes red later
layers; n lies strictly earlier and is not in their allowed future support.

At every other native vertex v, form the alternatives consisting of its
remaining exchange-branch projectors together with

    chi_(v,*)=I−sum_(c still exchanged at v) zeta_c.

The complementary alternative represents the SUM of its already pinned
branch summands. H4–H5 and inclusion-exclusion provide orthogonal complete
occurrence-pattern projectors chi_q. This step is precisely what permits
one vertex's siblings to be split between pinned and free locations.

For a later branch c with recovered filler U_c and fixed exchange bypass
Theta_c, put tau_c=Tr(U_c Theta_c). In a pattern q, closing an active swap
returns U_c; closing an inactive bypass returns the scalar tau_c. Dividing
out the inactive factors and summing q is the exact linear branch-resolved
recovery from the audited whole-layer proof. All chi_q commute with K, and
K acts only on the original past, so (4) passes through every recovery term:

    Recovery(T pi-pullback) = Recovery(T) K(x).

Closing n with F_N(I) turns its inserted pi(x) into precisely F_N(x).
Every other free or pinned native branch is recovered at its chosen value.
This proves (2) on the dense set where all tau_c are nonzero. Fixed
bypasses may be chosen as baseline adjoints; every tau_c is nonzero at
baseline. The product of full native branch unitary groups is connected,
so the nonzero-trace set is dense. Continuity extends the identity to all
native unitary branch fillers.

The recovery preserves coherent sums of occurrence patterns; it does not
measure their labels or require a product practical code. No physical SCC
cut, local fragment unitarity, or injectivity of a central exchange encoding
is used. The dependence on selected native branch matrices can be affine
when their siblings are pinned. That causes no difficulty in the recovery,
which works on the actual native contraction before any query relabeling.
Coefficient differences extend the resulting identity to arbitrary matrices
on the free branch slots. Independent ancillary versions then follow from
the coefficient identity; different branch ancillas can equivalently be
included in their native vertex's tensor-product private ancilla.

Finally, time reversal exchanges green first ends with red last ends and
H6 with H7. Applying exactly the same argument with all branches after n
pinned proves (3). The singleton is allowed either color. This does not
extend the theorem to an earliest red recurrent SCC or a latest green
recurrent SCC.

### 2. Apply the lemma to a second native vertex

Choose one topological ordering of the full branch condensation with n at
its fixed position. Every branch of j is strictly before or strictly after
n, since n's SCC is a singleton containing no other branch. Let B_− and B_+
be these two sets. Incomparable SCCs are put on either side by the chosen
topological ordering; no extra graph relation is inferred from this choice.

Write the actual native algebra as the direct sum over its branches and
write a=a_−⊕a_+. Fix all other native vertices at their baseline fillers.
The pair G(x,a) is linear in a, with coefficient maps G_b(x,a_b). At x=I,
normalization and complete one-port preservation give the representation
rho(a)=sum_b rho_b(a_b), with Q_b=rho_b(I_b) orthogonal central branch units.

Pin the B_+ branches to their baseline identities and vary B_− arbitrarily.
In the last-end lemma, all branches after n are now pinned; variable
branches remain only before it. Equation (3), evaluated at the same all-
identity baseline, gives

    G(x,a_−⊕1_+)=alpha(x) rho(a_−⊕1_+).                (5)

Pin B_− instead and apply the first-end lemma:

    G(x,1_−⊕a_+)=rho(1_−⊕a_+) alpha(x).                (6)

Neither (5) nor (6) is obtained by calling a_−⊕1_+ a whole-vertex matrix
query. They follow from the branch-free-variable proof above.

For b in B_−, compare (5) with a_b at an arbitrary unitary and at identity,
all other branch values fixed. This gives

    G_b(x,a_b−I_b)=alpha(x) rho_b(a_b−I_b).

Differences of unitaries from I linearly span every matrix algebra: −I
supplies I and ordinary unitaries span the algebra. Hence

    G_b(x,a_b)=alpha(x) rho_b(a_b),  b in B_−.

Likewise (6) gives G_b(x,a_b)=rho_b(a_b) alpha(x) for b in B_+.

Put e=sum_(b in B_−) 1_b and P=rho(e). Summing all branch coefficients and
then setting a=1 gives

    alpha(x)=alpha(x)P+(I−P)alpha(x),

so [P,alpha(x)]=0. Since e is central in the actual native algebra, P is
central in rho(A_j), not merely in its commutant. The summed coefficient
identity is exactly (1). An alternative placement of an incomparable
branch may yield another P when orders coincide; no uniqueness is used.

### 3. Why the quartet admits no such unbranched port

Suppose original query i had Q_i=0. Reachable native faithfulness and the
exhaustive original-query interface classification leave it with the sole
passive M2 branch. Apply (1) to any different actual native query vertex j,
fixing the other originals at identity and auxiliary fillers at the common
baseline.

The classified native algebra at j has one passive M2 summand, represented
with identity I−Q_j, and an active ideal supported on Q_j<=S_j. A central
projection P has scalar value zero or one on this simple passive summand,
regardless of its representation multiplicity. Consequently either

    P<=Q_j<=S_j,   or   I−P<=Q_j<=S_j.                 (7)

Restrict j's native input to its actual original embedding. With beta_j its
single-query representation, equation (1) becomes

    F_ij(x,y)=alpha_i(x) beta_j(y) P
             +beta_j(y) alpha_i(x)(I−P).

If P<=S_j, the exact right defect must vanish:

    `[F_ij−beta_j alpha_i](I−S_j)=0.                   (8)`

If I−P<=S_j, the other right defect must vanish:

    `[F_ij−alpha_i beta_j](I−S_j)=0.                   (9)`

This uses centrality, not the unjustified assumption that a general
commuting projection is scalar on a multiplicity space.

The independent checker constructs each S_j from the proved exact carrier
vectors, reconstructs F by both the normalized and raw-normalizer formulas,
and finds a nonzero exact Pauli witness to BOTH (8) and (9) for every i!=j.
All 24 defects, including an explicit entry and squared Hilbert–Schmidt norm,
are saved. Thus every proposed unbranched original query i contradicts the
actual quartet pair coefficients.

It follows that all four Q_i are nonzero. Since Q3<=E3 and Q4<=E4 reduce
their original irreducible rank-two factor actions, Q3=E3 and Q4=E4. If a
separate host-compatibility condition gives Q1<=E1, it now forces Q1=E1.
The possible native multiplicities at ports 1 and 2 remain intact; no full
M4 promotion has been assumed.

### Positive calibration and scope

The explicitly routed switch in [RG-030: Single-branch centrality and all four active ideals](core-obstruction.md#rg-030) has one
unbranched original A and two B branches, one before A and one after A.
At identity auxiliaries its full native pair is

    G(A,B0⊕B1)=diag(A B0, B1 A).

Here rho(B)=diag(B0,B1), alpha(A)=diag(A,A), and the comparison is exactly
the native branch-central projection P=diag(I2,0). The checker verifies (1)
symbolically for arbitrary matrix entries. Thus the centrality theorem
agrees with a genuinely nonserial valid host having one unbranched query;
its quartet obstruction comes from the specific complementary defects.

All four original active supports may still equal E_i, with every native
filler direction in the common curvature radical. That complete interface
tensor is already known and is not ruled out by this theorem. Any attempt
to force Q1 beyond E1, expose an additional record, or remove the remaining
red/green recurrent structure still needs a further graph argument or an
actual construction.

### General nonseriality graph cover criterion

### Theorem: the pair nonseriality graph needs a native branch cover

Work in a finite, valid bi-univocal weak-loop routed host after the already
audited reachable reduction. Let each original matrix query occur once via
its complete monopartite native insertion. Fix all auxiliary fillers at one
baseline. Join original queries i,j by an edge when their two-query
restriction, with every other original query fixed at baseline, is neither
strict serial order on the original boundary.

Then the original-query vertices having **more than one reachable native
branch** form a vertex cover of this graph.

For the retained quartet this graph is K4. Consequently at least three of
its four original query vertices have multiple reachable native branches.
By the exhaustive faithful native interface classification, this is
precisely the assertion that at least three of Q1,Q2,Q3,Q4 are nonzero.
Thus their total active physical rank is at least six, and at least seven
reachable original-query branches are required (four passive branches and
at least three active branches).

No maximal native promotion, chosen scalar flag, or static-control claim is
used. Auxiliary vertices, coherent multiplicities and practical index
correlations are unrestricted within the original host assumptions.

### 1. A constant-status branch is in a singleton branch SCC

A vertex with exactly one globally reachable branch has that branch active
in every consistent global section. Its branch-status function is therefore
constant in both complete forward and complete reverse choices.

By the branch-graph definitions:

- A green arrow points from an output-choice branch to a branch whose status
  changes. Hence no green edge can enter a constant-status branch
- A red arrow points from a branch whose status changes to an input-choice
  branch. Hence no red edge can leave a constant-status branch

Every directed cycle in a weak-loop branch graph must be wholly green or
wholly red, with no solid edge. A cycle through a constant-status branch
would require respectively a green incoming or red outgoing edge. Both
are impossible. A nontrivial SCC contains a directed cycle through each
of its branches, so this branch lies in a singleton SCC, without a self-loop.

This argument concerns status dependence only, not independence of scalar
wire indices or a separable practical edge space. A constant-status branch
can still have solid incoming and outgoing quantum edges.

### 2. Two unbranched originals give a strict serial pair

Suppose original vertices i and j each have one reachable branch. Fix every
other original query at identity and all auxiliary fillers at their given
baseline. The underlying native graph and its full routes remain the same;
only the designation of which two fillings are unknown changes.

Both remaining query SCCs are singletons by Section 1. Choose a topological
ordering and take the earlier of the two query SCCs. A singleton without a
self-loop can be declared green. It contains the entire native vertex of
its original query and no branch of the other original query. The audited
whole-layer first-use theorem therefore applies, regardless of auxiliary
vertices split across other SCCs.

At the normalized identity baseline, if i is earlier it gives exactly

    F_ij(U_i,U_j)=F_ij(I,U_j) F_ij(U_i,I)
                =alpha_j(U_j) alpha_i(U_i).

If j is earlier it gives the opposite product. This is an equality on the
original boundary, with all independent private-ancilla extensions. No
physical unitary SCC cut is asserted.

Thus a pair that excludes both products cannot have both vertices
unbranched, proving the vertex-cover theorem. More generally, any chosen
collection of unbranched original vertices becomes a fixed-order process
when all other originals are fixed: repeatedly apply this same singleton
first-use extraction in a topological ordering.

### One-unbranched-query calibration

### 4. Calibration: one unbranched query can genuinely survive

The general result cannot be strengthened to say every query in every
nonserial process must branch. Here is an explicit quantum-switch host with
one unbranched original A (native M2) and one branched original B (native
M2+M2). Its boundary dimension is four.

There are auxiliary source S and decoder D with full M4 freedom, and two
routing vertices M,N with two full M2 branches each. A single scalar control
c is relayed S→M→N→D. Each potential data wire has a one-dimensional vacuum
sector and a two-dimensional occupied sector, except M→A and A→N, which
are unsectorized qubit wires.

For c=0 the occupied data path is

    S → B0 → M0 → A → N0 → D.

For c=1 it is

    S → M1 → A → N1 → B1 → D.

The six conditional data wires are S→B, S→M, B→M, N→B, N→D, B→D. Their
inactive sectors are vacuum; the source, mergers and splitter impose the
correlated tuples, rather than independent choices for the two possible
paths. B0 and B1 are branches of the SAME native vertex B.

The checker gives every local route as a disjoint union of rectangles,
verifies the practical branch dimensions, and enumerates all global sector
assignments. There are exactly two consistent sections. Only S has a
nontrivial forward choice (c), and only D a nontrivial reverse choice (c).
Thus there are two complete choices in either direction and each selects
one unique section.

Green arrows leave S; red arrows enter D. Solid edges are computed directly
from the sector dimensions and conditional endpoint-branch pairs. The full
branch graph is acyclic: B0 is before A and B1 is after A. It therefore
satisfies weak loops with all independent native fillers intact. The physical
vertex graph does have the cycle B→M→A→N→B, illustrating why the distinction
between vertex and branch graphs matters.

At identity auxiliary fillers, the tensor is

    |0><0| tensor U_A U_B + |1><1| tensor U_B U_A.

The exact test uses rational noncommuting unitaries to distinguish it from
both uniform orders. Its completeness is supplied by the actual route
certificate, not by scalar numerical tests. More generally arbitrary native
fillers give the two blocks N0 A M0 B0 and B1 N1 A M1 between the full M4
source and decoder, with independent private ancillas permitted.

This calibration is separate from the quartet. It also shows why a lone
unbranched query may be interposed between different branches of another
query and cannot simply be extracted as a global first or last query.

<a id="rg-031"></a>

## RG-031 — Forced red passive core and uniform capacity

**Statement.** All four passive originals lie in one red SCC; active originals lie in or before it and are globally exclusive. The core has at most ten M2 branches.

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### 1. The four passive branches are mutually reachable

Let p_i be the unique passive native branch of original query i. The audited
native classification gives its represented unit I−Q_i and its normalized
M2 representation

    rho_i(x)=alpha_i(x)(I−Q_i),

where 0<Q_i<=S_i, the S_i are mutually orthogonal, and Q_i reduces alpha_i.
Pin all other native branches at their common unitary baseline. Varying
only this passive branch gives L_i(x)=Q_i+rho_i(x).

Every original native branch has a fixed past marker in the exact joint
native quartet tensor. Hence the mixed marked coefficient for passive p_j
and the full passive i matrix x is

    G_(p_j,p_i)(x)=rho_i(x)(I−Q_j).

If there were no branch-graph path p_j->*p_i, the audited no-path phase
causality lemma would instead give

    G_(p_j,p_i)(x)=(I−Q_j)rho_i(x).

Their difference cannot vanish for every x. Indeed Q_i Q_j=0 and Q_i
reduces alpha_i, so

    [Q_j,rho_i(x)]=[Q_j,alpha_i(x)].

The cross-serial-cylinder theorem excludes a nonzero projection <=S_j
commuting with alpha_i(M2) for i!=j. Thus p_j->*p_i for every distinct i,j.
All four passive branches lie in one recurrent SCC L.

The independently audited green-layer future-marker theorem forbids a
passive original branch sharing a green SCC with any other original branch.
Consequently L is RED.

### 2. Every other original branch lies in or strictly before the core

Let a be any active branch of original i, with nonzero unit P_a<=S_i. For
j!=i, its mixed coefficient with passive j is

    G_(a,p_j)(x)=rho_j(x)P_a.

No path a->*p_j would force P_a rho_j(x) instead. Since Q_j P_a=0, the
same cross-cylinder argument makes their commutator nonzero for some x.
Thus every active branch reaches L. An active branch outside L is therefore
in its STRICT GRAPH PAST, not merely earlier in one arbitrary SCC order.
There are no original query branches strictly after L or incomparable with it.

### 3. Uniform core restrictions are now unconditional

The earlier common-passive-core hypotheses are established by Section1, so
[RG-031: Forced red passive core and uniform capacity](core-obstruction.md#rg-031) and
[RG-032: Saturated passive-core rigidity](core-obstruction.md#rg-032) apply to EVERY quartet
host. They give:

- Both active branches 3 and4 lie strictly before L, by the subsequently
  audited full-input record argument in [RG-034: Exact full-input gathering and final Gram contradiction](core-obstruction.md#rg-034)
- All original active branches are globally mutually exclusive, including
  active branches outside L
- Every native branch in L is M2; there are at most ten such branches,
  including the four passive originals
- The total active supports are exactly
  Q1 in {E1,S1}, Q2 in {E2,S2}, Q3=E3, Q4=E4
- The four passive output algebra factors are the physical four qubit factors
- Each auxiliary branch in L has one unique assigned original i, co-occurs
  only when that original is active OUTSIDE L, has unit P_b<=Q_i, and its
  full M2 output image is physical_i(M2). Its represented multiplicity may
  still be two; no hidden multiplicity is promoted to branches
- An original active branch in L has represented unit E_i or S_i−E_i and
  represented rank two. For i=3,4 only E_i is available
- If all original vertices are whole inside L, then L contains no auxiliary
  branches at all. Every auxiliary branch lies outside the core

Independently of this distinguished core, every recurrent SCC of any
D16 host has at most32 reachable branches by the operator trace-capacity
bound. The total number of auxiliary-only components is not bounded here.

### Scope of the core reduction

The remaining host architecture consists of this small red core together
with an arbitrary fixed auxiliary network, and mutually exclusive original
active calls lying in its strict past or in the core. A core scalar-status
record can be exposed by the separately checked graph rewrite in
[RG-044: One-SCC scalar status record](phase-records.md#rg-044).

What is NOT established is a valid compression of the external network into
a controlled single-call encoder, a one-term product hub, or a unitary
physical SCC fragment. A correlated practical boundary can have more labels
than its quantum code dimension, so it cannot simply be capped as a full
product domain. No arbitrary-host impossibility or quartet routed host is
claimed by these restrictions.

### Uniform recurrent-layer capacity and core count

### 1. Scalar branches cannot lie in a recurrent SCC

A native branch with practical dimension1 has a single input tuple and a
single output tuple, and all its sectors have dimension1. Its complete
forward and reverse choice coordinates are singletons. Hence it has no
outgoing green dependence edge and no incoming red dependence edge.
A nontrivial SCC has only one dashed color and every branch has both an
incoming and an outgoing internal edge. Thus every branch in a recurrent
SCC has d_b>=2. The same reasoning excludes a one-vertex self-loop at a
scalar branch. Solid internal edges are already forbidden by weak loops.

### 2. Operator and trace capacity

Fix a recurrent SCC L of a D-dimensional unitary host, after globally
unreachable branches are removed. At any common full-native unitary context,
its occurrence projections P_b commute. At each vertex include the extra
alternative I−sum_(b in L at that vertex)P_b for choosing a branch outside L.
Their joint products form an orthogonal resolution of I.

Every nonzero joint pattern occurs in a consistent section by same-SCC
joint-marker faithfulness. Its active native dimensions obey

    product_(b in pattern) d_b <= D.

Taking logarithms and resolving I gives the OPERATOR inequality

    sum_(b in L) log2(d_b) P_b <= log2(D) I.              (1)

In particular

    sum_(b in L) rank(P_b) log2(d_b) <= D log2(D).         (2)

Each reachable native branch has rank(P_b)=m_b d_b with m_b>=1. Since d_b>=2,
each summand on the left of (2) is at least2. Consequently

    number of branches in L <= floor(D log2(D)/2).

At D=16 this gives at most32 reachable branches in EVERY recurrent SCC,
uniformly over the total number of native vertices elsewhere in the host.
It does not bound the number of auxiliary-only SCCs or singleton vertices.
It does not say rank(P_pattern) is divisible by the product of dimensions.

If k whole native vertices lie in L, all their branch projections sum to I
and all their dimensions are at least2. Equation(2) gives k<=log2(D). In
particular no recurrent layer of a16-dimensional host contains more than
four whole native vertices.

### 3. A core containing all four passive original branches

Suppose L contains the unique passive native branch p_i of each of the four
original quartet vertices. It is recurrent and, by the green passive-branch
exclusion, RED. Write Q_i for the active original carrier, with

    rank Q_i in {2,4} for i=1,2,
    Q_3=E_3, Q_4=E_4,
    Q_i<=S_i, Q_i Q_j=0 for i!=j,
    rank Q_total=sum_i rank Q_i <=12.

At the normalized quartet baseline the four passive markers are I−Q_i.
The same-SCC joint-marker theorem applies to their complementary events as
well as their positive occurrences. Since

    (I−P_(p_i))(I−P_(p_j))=Q_i Q_j=0,

rank constancy forces that negative-pattern marker to vanish at every full
native context. A global section with both original i and original j active
would witness that marked coefficient, so is impossible.

Thus ALL original active branches are globally mutually exclusive under this
COMMON-PASSIVE-SCC hypothesis, even when the active branches themselves lie
outside L. Every global section has at least three passive originals in L.

### 4. The only possible additional branches in that core

Let b be an auxiliary branch in L. It is reachable and has d_b>=2. Choose a
section containing b. If all four originals were passive, its capacity
would be at least2^4 d_b>16. Therefore exactly one original i is active.
If that active original branch also belonged to L, capacity would again be
at least2^4 d_b. Thus that original active branch lies outside L.

The other three passive qubits lie in L. Hence8 d_b<=16 and d_b=2. No two
auxiliary branches in L can co-occur: together with those three passive
qubits they would have product dimension at least32.

Likewise every original active branch lying in L must have dimension2:
it co-occurs with the other three passive originals there. An M4 original
active branch in L would already violate the product bound.

Consequently all native branches of this common-passive core are M2, and
a section selects one of the following layer patterns:

- Four passive originals, with no auxiliary branch in L
- Three passive originals and the unique active original branch in L,
  with no auxiliary branch in L
- Three passive originals, whose unique active original lies outside L,
  and at most one auxiliary branch in L

There may be no auxiliary branch in the third case.

### 5. At most ten branches in the common-passive core

Call the branches of L other than its four passive originals deviations.
These are original active branches in L or auxiliary M2 branches in L.
Two deviations can never co-occur, by the preceding capacity and exclusivity
arguments. Their commuting represented units therefore are pairwise
orthogonal. Each deviation occurs only when some original is active, so
its represented unit is contained in Q_total at the quartet baseline.

Every deviation has represented rank at least2. Therefore

    number of deviations <= rank(Q_total)/2 <=6,
    number of branches in L <=4+6=10.

More precisely, auxiliary units are supported on the sum of carriers of
original active branches OUTSIDE L. Thus all4 rank-two minimal active
supports give at most8 total branches in the common-passive core; the10
bound allows rank-four supports at both first ports.

### 6. When all original vertices are whole in one SCC

If L contains all branches of all four original vertices, every section
contains four original branches there. Their native dimensions are at least2,
so the capacity is exhausted and each selected original branch has dimension2.
Any co-occurring auxiliary branch would have to be scalar, but scalar
branches cannot belong to a recurrent SCC. Reachability then excludes all
auxiliary branches in L.

The green passive exclusion makes L red. Thus such a hypothetical host has
one red original-query SCC consisting ONLY of the actual original native
M2 branches; every auxiliary branch lies outside that SCC. This does not
mean that its external fixed network is a one-term product hub. Contracting
that network while preserving route validity and correlated practical codes
remains an open normalization step.

### Exact quantitative sharpening

### Further exact sharpening

[RG-032: Saturated passive-core rigidity](core-obstruction.md#rg-032) proves that in this
common-passive-core case Q1 and Q2 are each Ei or Si, Q3=E3, and Q4=E4.
Thus the possible Q_total ranks are 8,10,10,12; the previously stated bounds
remain correct. That additional result also assigns every core auxiliary
branch to a unique missing original and restricts core original-active
branch units to Ei or Si-Ei. Those conclusions use saturation and the
specific quartet coefficient formula, not the trace capacity alone.

<a id="rg-032"></a>

## RG-032 — Saturated passive-core rigidity

**Statement.** Saturation fixes the total original carriers, passive output factors and unique assignments of core auxiliaries, preserving multiplicities.

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### Conclusions

Suppose one actual red SCC L contains all four passive original-query
branches of a quartet host. At the common normalized quartet baseline:

- Q1 is E1 or S1; Q2 is E2 or S2; Q3=E3 and Q4=E4
- The four passive output algebra actions obtained from H7 are exactly the
  physical four qubit factors, when parameterized by the original Ui
- Every auxiliary branch in L is a native M2 branch assigned to one unique
  original i. It occurs only when that original is active outside L. Its
  baseline unit P_b satisfies P_b<=Q_i and commutes with physical_i(M2)
- Every original active branch a in L has unit E_i or S_i-E_i and represented
  rank two. The latter alternative is available only for i=1,2

An auxiliary M2 branch may still have representation multiplicity two on a
rank-four support; this proof does not split it into independent branches.
Nor are auxiliaries outside L normalized, removed, or classified.

### 1. Keep the H7 representatives fixed before choosing a pattern

Use the reverse-induction setup of [RG-028: Product-dimension SCC capacity](layer-structure.md#rg-028).
Fix all outside native fillers at the common baseline and exchange all
current branches C of L. Before choosing any marked pattern, H7 supplies,
for every branch b and every output matrix f, a matrix K_b(f) on the original
future F alone. The argument in that note recovers the strict past using
right-domain patterns with no C_out support and obtains

    S_B f_(b,out) = (K_b(f) tensor I_Cin) S_B           (1)

for each b in any jointly marked subset B of C. The same originally chosen
K_b(f) works for every B containing b. Its restrictions to the partial-row
span W_B form commuting algebra representations.

A reachable same-SCC pattern is nonzero at the common unitary baseline by
[RG-027: Joint status faithfulness within one SCC](layer-structure.md#rg-027), not merely at some pattern-dependent
outside context. Its marked partial exchange S_B is therefore also nonzero.
If product_(b in B) d_b=16, the module dimension theorem forces W_B=F.
Consequently K_b(f) is unique as a matrix on F and defines a unital complex
algebra representation there. In particular two saturated patterns are
using the same K_b, not separately chosen or conjugated representations.
This common-baseline point is necessary for the comparisons below.

### 2. Recover the four passive fillers as the original Ui

Let B be the four passive originals. Its fully marked coefficient at the
quartet baseline is

    R = I-sum_i Q_i,

of rank at least four. Thus B is reachable and its native dimensions give
2^4=16. All four partial-row representations are globally defined on F and
their images commute. Their tensor product is a unital representation of
M2 tensor M2 tensor M2 tensor M2 = M16 on F=C16.

There is a minor basis issue in applying (1) to actual original fillers.
At passive branch i write its native filler as

    u_i(Ui)=u_i,0 pi_i(Ui),

where pi_i is the unital original M2 embedding in that native M2 input
algebra. It is a *-isomorphism. Define the corresponding output operator

    f_i(Ui)=u_i,0 pi_i(Ui) u_i,0†.

Then u_i(Ui)=f_i(Ui)u_i,0. Closing an exchange after right multiplication
by f_i inserts exactly this output-left-composed native filler. Define
rho_i(Ui)=K_i(f_i(Ui)); its image is the same as K_i's image.

This manipulation survives current-layer recovery. In the red-layer
exchange, every current output-side occurrence projector has strict-past
support and thus no C_out factor. It commutes with all f_i. On a marked
passive branch the active recovery closes with its desired u_i; incompatible
patterns vanish. Every other branch closes with its prescribed active
filler or normalized inactive bypass. The factors rho_i therefore pull
outside the identical pattern contractions in (1).

It follows that the exact jointly marked boundary map is

    G_B(U)=product_i rho_i(Ui) R = rho(tensor_i Ui) R.  (2)

By the independently audited joint-original-native formula the same map is
F(U)R. Dependence on an individual passive branch is not treated as a whole
unital matrix query: (2) is obtained from the actual marked coefficient and
exchange recovery. The original Ui parameterization is reinstated only via
the explicit pi_i above.

A unital representation of M16 on a 16-dimensional complex space is an
algebra automorphism in some basis. Matrix units give an invertible S with

    rho(A)=S A S^-1,
    F(U)R=S(tensor_i Ui)S^-1 R.                       (3)

No adjoint or metric claim about S is required.

### 3. General exact parallel-column lemma for the quartet

The following coefficient fact is useful beyond the passive core.

**Lemma.** Let P be any nonzero projection. If an invertible S satisfies

    F(U)P=S(tensor_i Ui)S^-1 P                         (4)

for all original matrices, then P is contained in one of the five mutually
orthogonal spaces E1,E2,E3,E4,R_E, where R_E=I-sum_i E_i. Moreover S is a
nonzero scalar multiple of Z_i in the E_i case, or of I in the R_E case.
Here Z_i is the physical Pauli Z on qubit i. These alternatives also suffice.

**Proof.** In the physical computational basis, write o,a in {0,1}^4 and

    V_o=I-2 sum_(i:o_i=1) E_i,
    D0=I+sum_i (Z_i-I)E_i.

The exact normalized quartet coefficient is

    F_(o,a)=|o><a| V_o D0.

Comparing matrix-unit coefficients in (4) gives

    |o><a| V_o D0 P = S|o><a|S^-1 P.                  (5)

Since S^-1P is nonzero, some row <a|S^-1P is nonzero. For that row, the
right side of (5) is nonzero for every o. Its range is span(S|o>); the left
side has range contained in span(|o>). Thus every S|o> is a nonzero multiple
s_o|o>, and S is diagonal. Combining all a in (5) gives

    V_o D0 P = s_o S^-1 P.

Taking o=0000, where V_0=I, yields

    V_o D0 P = (s_o/s_0) D0 P.                        (6)

The V_o are commuting involutions. Their joint eigenspaces are exactly the
four rank-two E_i and the rank-eight R_E: on E_i the eigencharacter is
(-1)^(o_i), and on R_E it is 1. Every other sign pattern has zero joint
space. Since D0P is nonzero, (6) places its range inside one of these five
spaces. D0 preserves each E_i and is the identity on R_E, so P itself is
contained in the same space. Equation (6) then determines every s_o,
giving S proportional to Z_i or I respectively. Conversely, on E_i the
quartet equals Z_i(tensor Ui)Z_i, and on R_E it equals tensor Ui. This proves
the coefficient identity in both cases. ∎

The argument does not assume rank P is large, that P is a physical cylinder,
or that S is unitary. The distinct fixed future coefficient rows force the
similarity to have the stated form.

### 4. Passive saturation forces Ei<=Qi

Apply the lemma to (3) with P=R. Its rank is at least four, excluding every
rank-two E_i sector. Therefore

    R<=R_E,   S is scalar,   rho(tensor Ui)=tensor Ui.

In particular rho_i(Ui)=physical_i(Ui) for each original qubit.

Since E_i R=0, E_i is contained in sum_j Q_j. For j!=i, E_i Q_j=0 because
Q_j<=S_j and the canonical carriers are orthogonal. Hence E_i<=Q_i. The
actual-native classification gives Q_i<=S_i and ranks in {2,4} at the first
two ports, while S3=E3 and S4=E4. Thus

    Q1 in {E1,S1}, Q2 in {E2,S2}, Q3=E3, Q4=E4.

This removes tilted rank-two *total active supports* only under the stated
common-passive-core hypothesis. It is not a general interface theorem for
all hosts or all isolated native vertices.

### 5. Each core auxiliary branch has a unique original assignment

The independently audited quantitative corollaries show that a reachable
auxiliary branch b in L has native dimension two. Every section containing
it has exactly three passive originals in L; the missing original i is
active outside L. For such a section, B={b} union {p_j:j!=i} is a reachable
same-SCC pattern with product dimension 16. It is nonzero at the common
baseline, so W_B=F.

The K_b from Section 1 is therefore a global unital M2 representation and
commutes with the three passive images physical_j(M2), j!=i. Their joint
commutant is exactly physical_i(M2). Injectivity of a unital homomorphism
from the simple M2 and equality of dimensions imply

    K_b(M2)=physical_i(M2).

If another section containing b omitted a different passive k, its saturated
pattern at the *same* baseline would force the *same* K_b image into
physical_k(M2). Distinct physical single-qubit factors intersect only in
scalars, which cannot contain an injective M2 image. Thus the missing i is
unique across all sections containing b.

Let P_b be the origin unit of this native auxiliary summand. Since b never
co-occurs with passive i, their commuting same-layer units obey
P_b(I-Q_i)=0, so P_b<=Q_i. Recovering just the b filler in (1) at all other
baseline fillers gives its origin one-port branch representation in the
form

    beta_b(h)=K_b(f_b(h)) P_b.

The one-port representation has unit P_b, so its image maps ran P_b into
itself. As K_b(f_b(M2)) is the entire *-closed physical_i(M2), ran P_b is
invariant under this factor and its adjoints. Consequently

    [P_b,physical_i(M2)]=0.

This is valid for either represented rank two or four. It does not resolve
a rank-four multiplicity-two M2 branch as two native branches. In fact the
same formula plus * preservation of beta_b makes K_b, in the normalized
native h coordinate, a *-representation: the physical_i factor acts
faithfully on every nonzero reducing P_b. This optional strengthening is
not needed for the assignment or support conclusions.

### 6. Original active branches inside the core are canonical sectors

Let a be an original active branch of query i that lies in L, with unit
P_a. Quantitative capacity makes its actual native dimension two. It
co-occurs with the other three passive originals and with no auxiliary
branch of L, so the pattern again saturates dimension 16 at the common
baseline. Its original M2 embedding into this native M2 branch is an
isomorphism, and the recovery argument of Section 2 gives

    F(U)P_a=S(tensor Ui)S^-1 P_a

for some invertible S. The equality on the left is the exact original
restriction of the actual branch-marked native tensor.

The parallel-column lemma places P_a inside E_l for some l, or inside R_E.
But P_a<=Q_i<=S_i is orthogonal to every E_l with l!=i. Its represented rank
is a positive multiple of two. Since E_i has rank two and S_i intersect R_E
is S_i-E_i of rank two for i=1,2 and zero for i=3,4, it follows that

    P_a=E_i or P_a=S_i-E_i.

In particular its represented rank is exactly two, and an original active
M2 branch of multiplicity two cannot lie inside this core. Total Q_i=S_i
remains possible through two distinct native M2 summands in the core, or
through active branches partly or entirely outside it. No restriction of
this form is asserted for an original active branch outside L.

### Exact certificate and scope

`branch_layer_saturated_passive_checks.py/_checks.json/.log` verifies the
physical matrix-unit row formula, all sixteen joint reflection characters,
D0's sector actions, every sufficient parallel-column identity, the four
allowed total support tuples, the relevant intersections with S_i, and the
commutants of the three physical spectator factors. It also checks explicit
tilted rank-two total supports that the new common-core theorem excludes.

[RG-031: Forced red passive core and uniform capacity](core-obstruction.md#rg-031) separately audits the
32-branch recurrent-layer bound, the ten-branch common-passive-core bound,
and global active exclusivity. Neither audit proves that the four passive
originals must occupy one SCC, constructs a host, or compresses the arbitrary
outside auxiliary network.

<a id="rg-033"></a>

## RG-033 — Rank-two branch acyclicity

**Statement.** An actual native M2 branch of represented rank two cannot belong to a recurrent weak-loop SCC.

**Status:** source-level result. **Scope:** Only this branch has multiplicity one; all other native multiplicities remain arbitrary.

### 1. Exact hypothesis transfer to the whole-vertex pair

For two distinct actual vertices B,C, hold every other native vertex at its
specified unitary baseline. Identify the practical input/output spaces at each
branch by that branch's baseline unitary, and right-normalize the boundary by
the common baseline. The resulting bilinear map is defined on

    A_B = directsum_(b at B) M_(d_b),
    A_C = directsum_(c at C) M_(d_c).

These are the **entire** native algebras. Arbitrary branch matrices and arbitrary
independent private ancillas at the two vertices are admitted by the routed
superunitary theorem. A shared private ancilla across branches of one vertex
gives A_B tensor M_m; it does not create operations mixing distinct native
central summands. Pinning other vertices at unitaries and multiplying by the
fixed boundary normalization preserves complete unitarity.

The retained source
explicitly covers exactly this model, including nonfaithful representations.
Its conclusion is a single orthogonal projection K in the joint commutant with

    H(a,x)=rho_B(a)rho_C(x)K+rho_C(x)rho_B(a)(I-K).

I checked the actual source proof: normalized amplified slices are
homomorphisms; differentiation yields the two represented Leibniz rules;
the factor-free cross-commutator Gram reconstruction gives the strict-support
coefficient commuting with both images; the reflection calculation kills the
commuting-support correction and makes the strict coefficient a projection.
None of these steps assumes that the native algebra is a matrix factor.
The cited [RG-075: Support of mixed biderivations](higher-order.md#rg-075), Sections 1--3, really is
factor free. There is no use here of its factor-specific Section 4.

K need not be unique or vary continuously with any context. One arbitrary
valid K at the one common baseline is all the rank-two proof uses.

### 2. Same-layer coefficient extraction, with siblings pinned

For a green SCC L the audited marker theorem says G_c(u)=P_c G(u) while only
L-branches vary and every other filler is pinned. Here the normalized
baseline is I and P_c is the represented c-branch unit at that baseline.

To extract b's coefficient, vary only b, pinning every sibling, including
siblings outside L. Subtract the identity value:

    G_(b,c)(a-I_b,I_c)=P_c beta_b(a-I_b).

Differences of unitaries from identity span M_(d_b): -I supplies the identity
direction, and unitaries span the algebra. Hence the displayed identity
extends to all matrices and gives

    G_(b,c)(a,I_c)=P_c beta_b(a).

Interchanging b,c gives G_(b,c)(I_b,x)=P_b beta_c(x). At the identity these
two extractions also give [P_b,P_c]=0. Alternatively this commutation follows
directly by extracting the two independent branch phases.

This derivation does not vary a sibling outside L. The full native pair is
introduced only for its complete comparison theorem and then restricted to
the b,c summands. The affine map a -> a directsum I is never asserted to be
a unital linear full-matrix query. For siblings at the same actual vertex,
direct-sum orthogonality already gives P_bP_c=0, and no bipartite theorem is
applied to them.

I also checked the marker proof against the retained primary paper text,
`upstream_matrix_causality/arxiv2206v3.txt`, Appendix B.4.2:
H2 has precisely the strict-future support used for a green input marker;
H6 uses only strict-past ports on the active sector; the inactive exchange
is the fixed bypass. The proof begins at a whole-layer boundary, avoiding
the partially filled-red-layer exception. Its two recovery stages preserve
the same current-pattern projectors, including the full complement of any
split vertex. This is the necessary reason the marker identity survives
arbitrary pinned siblings. I found no additional whole-vertex assumption.

### 3. The rank dichotomy, including orientation

Restrict the whole-native pair comparison to b,c and compare the two
coefficient identities in Section 2. With the source's convention the
identities are exactly

    [beta_b(a),P_c]K=0,
    `[beta_c(x),P_b](I-K)=0.`

Since K commutes with P_b and beta_b(M2), and rank P_b=2, the supported M2
representation is irreducible. Therefore KP_b is either P_b or 0.

If KP_b=P_b, the first commutator is supported on P_b because P_b commutes
with P_c. It therefore vanishes outright. The projection P_bP_c belongs to
the commutant of the irreducible M2 on P_bH, and is 0 or P_b.

If KP_b=0, joint commutation of K with beta_c gives

    K[beta_c(x),P_b]=[beta_c(x),P_b]K=0.

The second displayed identity again makes that commutator zero outright.
Thus beta_c restricts to a possibly zero *-representation on P_bH. Its
supported unit is P_bP_c. A nonzero representation of M_(d_c) has dimension
a positive multiple of d_c. Provided d_c>=2, the only possible nonzero rank
within the two-dimensional carrier is 2. Hence again P_bP_c is 0 or P_b.
This restriction does not require c to have multiplicity one globally.

For a red SCC, fixed past markers replace the two marked coefficients by
beta_b(a)P_c and beta_c(x)P_b. The factors K and I-K exchange roles and the
same dichotomy follows. No orientation reversal was omitted.

### 4. Why d_c>=2 holds on a recurrent SCC

Every internal edge of a recurrent SCC belongs to a directed loop. Weak
loops consequently makes every internal edge dashed and of its SCC's one
color. Each vertex of a recurrent green SCC has an internal outgoing green
edge; each vertex of a recurrent red SCC has an internal incoming red edge.

By primary Definition 3.7, the former requires at least two values of that
branch's forward output-choice coordinate. The latter requires at least two
values of that branch's reverse input-choice coordinate. With positive sector
dimensions, native practical dimension is at least the cardinality of either
choice domain. Hence d_c>=2. A scalar branch has singleton choice domains
and cannot lie in a recurrent weak-loop SCC. Dimension balance is required
when exchanging the two directions and is part of the stated host model.

Unreachable zero-dimensional or unused labels are not covert exceptions:
the theorem is applied to reachable native branches with positive sectors,
as in the source host class. If a formulation permits zero-dimensional
labels, they must first be discarded.

### 5. Negative-pattern faithfulness at all auxiliary contexts

The needed event is exactly b AND NOT c. For a green L, at any full native
unitary context u, temporarily pin the outside-L tuple and apply the marker
theorem. The normalized marked map is

    (G_b(u)-G_(b,c)(u))G(u)^dagger = K_b(u)(I-K_c(u)).

The same-SCC marker projections commute, so this is a projection. It is
continuous in **every** native filler, including every auxiliary outside L.
The full native unitary parameter space is a finite product of connected
unitary groups. Thus its integer rank is globally constant. If P_b(I-P_c)=0
at the common baseline, the entire negative-pattern map vanishes at every
native unitary tuple. The identical reasoning treats b AND c and, with
left normalization, a red L.

At every actual vertex, native unitaries span its entire direct-sum algebra.
Multilinearity therefore upgrades this all-unitary vanishing to vanishing of
the whole skeletal pattern tensor. If a consistent section realizing the
pattern existed, choose at every vertex its actual active-branch matrix unit
for that section's incoming/outgoing index tuples and fixed positive-sector
quantum basis vectors. One boundary coefficient is then 1. This contradicts
tensor vanishing. For NOT c, select the section's actual other sibling;
there is no cancellation or subtraction left at that matrix-unit tuple.

Consequently P_bP_c=0 says b,c never co-occur in any section, and
P_bP_c=P_b says c always occurs whenever b occurs. This implication is
structural, not merely a statement about one set of pinned auxiliary values.
It is valid because b,c are in the SAME SCC; no different-SCC zero inference
is used.

### 6. Dormant choices close the graph contradiction

Take two complete forward choice vectors differing only at b's output
coordinate. If b is inactive in either corresponding section, that entire
section is still compatible with the other vector because this coordinate
is unused there. Forward univocality makes the two sections equal. Thus any
change forces b active on both sides; it also proves that b cannot change
its own status, excluding a green self-loop.

Every other c in L has constant status conditional on b, by Section 5.
Therefore the changed coordinate cannot change any status in L. In the
exact primary Definition 3.7 this says that b has no internal outgoing
green edge, contradicting recurrence. Same-vertex siblings cannot change
while b is active either.

Repeat on the full reverse-choice domain. Any change caused by b's input
coordinate requires b active on both sides and changes no L status. The
primary red convention therefore gives no internal red edge c -> b,
contradicting recurrence in a red L. All dormant coordinates are retained
throughout; no choice domain is conditioned or shortened.

### 7. Independent exact calibration and scope

[check_lugano_rank_two.py](../rank_two_recurrence_audit/check_lugano_rank_two.py) independently reconstructs the eight-section
binary Lugano host, exhausts all 64 full forward choice vectors and all
eight reverse vectors, and checks the dormant/own-choice assertions. Its
only recurrent SCC consists of the three native M2 losing branches; each
has represented rank 6. Its three winning M2 branches have represented
rank 2 and are acyclic. Literal time reversal gives the corresponding red
SCC with the same ranks, again with every rank-two branch acyclic.

The checker also verifies the whole M2+M2 native comparison for all three
laboratory pairs, on all 64 matrix-unit coefficient pairs per pair. It
checks the correctly complemented comparison after time reversal. The
recurrent losing pairs have joint rank 4 and negative-pattern rank 2:
their multiplicity-three supports correctly evade the rank-two dichotomy.
Outputs are [lugano_rank_two_checks.json](../rank_two_recurrence_audit/lugano_rank_two_checks.json) and `lugano_rank_two_checks.log`.

These are exact finite calibrations, not substitutes for the argument.
The proof establishes acyclicity of an ACTUAL native M2 branch represented
on rank two. It neither treats a proper coefficient of a larger simple
native factor as a branch nor extends the rank-two conclusion to arbitrary
higher ranks. No distributed original-query encoding or enlarged boundary
has been excluded by this argument.

<a id="rg-034"></a>

## RG-034 — Exact full-input gathering and final Gram contradiction

**Statement.** A whole vertex with no recurrent green branch admits the stated actual input record; the joint passive-1/passive-3 record contradicts the exact positive-definite Pauli Gram.

**Status:** source-level result. **Scope:** Quantum acyclic input tuples and split vertices are included; whole-red-vertex gathering is the special case. With RG-033 this closes the quartet contradiction.

### 1. Precise hypotheses and conclusion

Start with a finite, bi-univocal, weak-loop routed graph, reduced to globally
reachable native branches, with positive sector dimensions and the actual
native rectangular branch routes. Let J be one whole native vertex. Assume:

1. No reachable branch of J belongs to a recurrent green SCC
2. Every full practical input tuple h in a recurrent red branch of J has
   quantum dimension d_h=1

A branch of J outside recurrent SCCs is allowed to have d_h>1. Its sibling
branches may occupy different SCCs. The rewrite gathers **all** inputs of J at
one actual new native vertex A and passes the bundled input label h to J. Each
A_h has one input tuple, one output tuple, and full native matrix algebra M_(d_h).
J retains its entire original direct-sum native algebra and all coherent matrix
entries between input tuples in each old branch.

The rewritten graph is bi-univocal and weak-loop. It permits independent native
fillers and independent private ancillas, and inserting the tensor-product
identity at every A_h recovers the original tensor exactly.

For the normalized quartet, use the already audited universal host hypotheses
in [RG-031: Forced red passive core and uniform capacity](core-obstruction.md#rg-031): original boundary dimension 16; each original
query used once at its own native vertex; arbitrary fixed auxiliaries allowed;
common red passive SCC L; saturated supports Q1 in {E1,S1}, Q3=E3, Q4=E4;
global exclusivity of original active events; and the strict-past placement of
active3/4. Then the new conclusion is unconditional within that host class:

**The unique active branch of original 3, and separately the unique active
branch of original 4, lies in a recurrent GREEN SCC strictly before L.**

The two green SCCs may coincide. No entire physical cut, surrounding auxiliary
network, or green SCC is compressed into an independent quantum interface.

### 2. Complete choice functions and native branches

A full practical input tuple h belongs to a unique J branch b because the
native input subsets are disjoint. Redirect every old incoming wire of J to A.
Use one bundled A→J wire with a sector for every h, of dimension d_h, and the
canonical identification of that sector with the old tensor product of h's
sectors. A_h's local route is the singleton rectangle {h}×{h}.

Every old consistent assignment extends uniquely: its old J input tuple fixes
A_h and the bundle label. Conversely the new assignments restrict to old ones.
Old forward choice coordinates are unchanged. At every old J branch its reverse
input coordinate is renamed bijectively h↔bundle(h); all other old reverse
coordinates are unchanged. Every new A branch has singleton choice domains in
both directions, including when d_h>1. Thus the *complete* choice functions,
with every dormant coordinate retained, correspond exactly. No currently active
coordinate is selected in advance, and no old M2 branch is split into queries.

The same argument works with scalar status wires. At an old branch, their labels
are fixed by that branch, so they introduce no old bifurcation choices. At A the
refined branch label includes h and the status. Unreachable joint alternatives
can be retained while checking choices, then deleted; their new choice domains
are singleton anyway.

### 3. Fine-event dependencies, including source changes

Let E_h be the event that J's full input is h, and b its unique old branch.
A branch's status cannot change when only its *own* forward or reverse choice
changes: if inactive on either side, its dormant choice was unused and the
same assignment solves the changed choice vector, contradicting uniqueness.

Suppose one forward coordinate c changes E_h. Work on the side where h occurs.
If b's status changes, there is an old green c→b. Otherwise b stays selected
and some incoming wire index changes.

If that wire's source branch a stays selected, its output tuple can change
only if c=a. The two co-occurring a,b assignments have different wire labels,
so Definition 3.6 gives an old solid c→b, even when both labels are scalar.

If the source branch changes, there is an old green c→a. To obtain the remaining
edge, make a **different reverse-choice comparison**, starting at the assignment
with input h: change only b's reverse input choice to an admissible h' having
the other wire label. Own-choice stability keeps b active. Either a disappears,
giving old red a→b, or a remains and two wire labels occur with a,b, giving
old solid a→b. Hence the original forward dependency supplies a path

    c --green--> a --red-or-solid--> b.

This is not assuming that the forward comparison itself supplies a red witness.
All comparisons use full choice vectors with dormant values present.

If b is in red SCC L_b, any such c must be a *strict* predecessor of L_b:
a green edge or solid edge cannot be internal to a red SCC, and the displayed
path inside L_b would contain a forbidden green edge. If b is acyclic, c is a
strict predecessor of b. This also excludes c=b.

For reverse dependence, if c changes E_h by changing b's status, there is old
red b→c. If b stays active but its actual input tuple changes, then necessarily
c=b, because that tuple is the selected reverse coordinate at b. Thus every
reverse target of E_h lies in L_b or its successors (or at/after acyclic b).

### 4. Every solid/dashed edge and simultaneous placement

The old-to-old dashed dependencies are unchanged by the complete choice
bijections. Some old solid edges are removed by redirecting physical wires;
none is added between two old branches.

For any old source a co-occurring with A_h, the redirected edge has the fixed
label specified by h. It is solid exactly when its sector dimension is >1.
In that case the same sector occurred at the old co-occurring a,b pair, so
there was old solid a→b. In particular a is strictly before b's SCC. The bundle
contributes solid A_h→b exactly when d_h>1, and to no other old branch.

Under the stated scalar-red hypothesis, there are no new solid edges
incident to an A_h associated with a red b. For acyclic b the possible quantum
solids are the strictly forward subdivisions just described. Scalar flag wires
also have fixed labels at every co-occurring endpoint pair and add no solids.

A branches have no outgoing green or incoming red edges because their choice
domains are singleton. Their only new dashed arrows are green c→A_h from the
strict predecessor region of b's SCC, and red A_h→c into that SCC or later.
There are no physical A→A wires or dashed arrows between different A branches.

Choose one topological ordering of the *old condensation DAG* and insert each
A_h immediately before its associated old SCC. All incident arrows advance
this augmented order. This works simultaneously for A branches associated with
different, even incomparable, old SCCs. It is not an iteration that assumes
some partially gathered old vertex remains unchanged. A new path through
several A branches cannot evade the ordering. No SCC merges and no new directed
cycle occurs. Old recurrent SCCs retain their old internal dashed edges and
colors. Thus the complete weak-loop condition is preserved.

Definitions 3.5–3.7 and Theorem 3.1 of the
[primary framework](https://arxiv.org/html/2206.10042v3) are precisely the
consistent-assignment, choice-dependence, and conditional-sector definitions
used here. Appendix B's ancilla-padding lemma adds private input/output wires
without altering the choice relation or branch graph. Accordingly, the new
native freedoms have the full independent ancillary completeness of the graph
theorem, not merely scalar-phase validity at one coefficient tensor.

### 5. The passive-1 flag is legal at the split original vertex

Fix j=3 or j=4, and suppose its active branch a_j is not recurrent green.
The unique passive branch p_j is in L, while a_j is strictly before L.
Both are native M2. A recurrent red branch has a nontrivial incoming red edge;
therefore its own reverse input-choice domain has at least two elements.
Native dimension two then forces exactly two scalar input tuples. The proposed
whole-vertex gather therefore satisfies Sections 1–4, irrespective of a_j's
red/acyclic location and irrespective of its scalar/quantum input partition.

Append one bidirectional scalar flag pair between original vertex 1 and A.
At every branch of original 1 its fixed flag is its passive-versus-active
status. No assumption that original vertex 1 is whole in L is made.

For input h in p_j, E_h's dependencies lie strictly before L forward and
in/after L reverse. The passive-1 status has the same bounds because p_1∈L.
Each joint h/status event has dependencies contained in the union of those
of its factors, so the refined A branches retain their allowed placement.

For input h in a_j, global exclusivity of all original active events says
that original 1 is passive in **every consistent assignment where E_h holds**.
Thus its sole reachable joint event is literally E_h. This is stronger than a
baseline-zero mixed coefficient. It includes all choice contexts and dormant
coordinates. The status flag creates no new dependence at any upstream A_h.

Consequently one actual, valid native A slot jointly records passive-1 and
all of original j's input tuples. This is not an inference that two separately
available phase extensions commute.

### 6. Exact quartet coefficient and Pauli Gram contradiction

Normalize the common native baseline so its boundary contraction is I_16 and
set every new A_h filler to its tensor identity. The new contraction is then
literally the old contraction. For all independent central phases z_h at A,
its normalized map is sum_h z_h P_h. Unitarity for every phase vector, together
with sum_h P_h=I, makes the P_h mutually orthogonal projections. This conclusion
holds for an algebra ⊕_h M_(d_h), even if some d_h=2; no full C^k or quantum M_k
interface is being assumed.

The coarse event passive-1 is I−Q1. The coarse event 'j passive, input tuple t'
is D_(j,t). Both are sums of the *same actual slot's* branch-unit projections,
so

    [I−Q1, D_(j,t)] = 0.

Keep the original parameterization exact. In the native passive M2 branch
write the original query as

    u_j(U_j)=u_(j,0) pi_j(U_j),

where pi_j is a unital *-isomorphism on native input matrices. For its scalar
tuple vector e_t define p=pi_j^−1(|e_t><e_t|). This is an arbitrary rank-one
orthogonal physical-qubit projector. Restricting the native input tuple inserts
u_(j,0) pi_j(p) at this one passive branch, with all other native branches at
the common baseline. The already audited passive coefficient identity gives

    D_(j,t)=physical_j(p)(I−Q_j).

Equivalently, one may use the saturated passive output factor with
f_j(p)=u_(j,0)pi_j(p)u_(j,0)†. These two descriptions agree; there is no unstated
computational input basis or dropped native baseline unitary.

The original U_j is still shared across its native branches through its
original fixed embeddings. The gather does not change those embeddings.
Identifying the above single-branch *marked coefficient* does not replace
that one use of U_j by two independent original calls. Independent native
fillers are legal test variables supplied by the actual routed host, and the
old shared-original restriction is recovered exactly at the new identities.

Since Q1 Q_j=0 and Q_j=E_j reduces physical_j(M2),

    [Q1,D_(j,t)] = [Q1,physical_j(p)].

The left side vanishes by the common record. For either j=3 or j=4, the exact
Pauli-commutator Gram matrix is

    G(E1,j)=4 I_3,
    G(S1,j)=[[32/9, 0, −8/9],
             [0, 16/3, 0],
             [−8/9, 0, 32/9]].

Their leading principal minors are respectively (4,16,64) and
(32/9,512/27,5120/81). Both are strictly positive. More explicitly the minimum
eigenvalues are 4 and 8/3. For p=(I+n·sigma)/2, ||n||=1,

    ||[Q1,physical_j(p)]||_HS² = (1/4)n^T G(Q1,j)n,

which is at least 1 for Q1=E1 and at least 2/3 for Q1=S1. It cannot vanish.
This exact positive-definite witness excludes every native input basis.

Apply the contradiction **separately** first at j=3 and then at j=4 in the
same hypothetical host. No simultaneous gather of both vertices is needed.
Each active branch must therefore be recurrent green. The previously proved
strict-past conclusion puts both green SCCs strictly before the same red L.
There is no remaining new conditional graph premise in this conclusion;
its dependencies are the previously audited quartet host classification,
forced passive core, global active exclusivity, and the now-audited rewrite.

### 7. Independent finite calibration and exact reruns

[non_green_input_gather_quantum_audit.py](../non_green_input_gather_quantum_audit.py) constructs literal local rectangular
routes rather than assuming the intended global section map. It merges each
winning pair of reverse-Lugano scalar hub branches into one native M2 hub:
its two scalar P-input tuples coherently feed a single quantum M2 sector at
the winning lab. Every lab is now genuinely split between a red losing M2
branch with two scalar input tuples and an acyclic winning M2 branch with
one quantum input tuple.

It enumerates every internal edge assignment, verifies native input/output
dimension balance and local branch partition disjointness, then independently
evaluates both complete choice functions. Before and after gathering lab 2
and lab 0's losing-status flag it finds:

- 8 consistent assignments; 8 forward and 64 reverse complete choices
- Exact section/choice bijections with every dormant coordinate retained
- The same recurrent red losing SCC and only acyclic new record branches
- The quantum solid H_winner2→L2_winner replaced exactly by
  H_winner2→A_(2,0)→L2_winner
- Four reachable A branches with native algebra C+C+C+M2 and baseline
  represented ranks 1,2,2,3
- Joint branch-unit orthogonality and passive-status/input-tuple commutation
- Exact 16×16 amplified unitarity with a private qubit at A, independent
  noncommuting scalar-branch and quantum-branch fillers, and independent
  nontrivial native lab, hub, and source fillers

The general completeness proof is Sections 2–4. The finite amplified
certificate is [non_green_input_gather_quantum_audit_checks.json](../non_green_input_gather_quantum_audit_checks.json).
The calibration scripts also cover the all-scalar split-layer example,
the excluded recurrent-green negative control, all four exact E1/S1,
j=3/4 Grams, and the complementary-passive commutator reduction.

The negative control is essential: gathering a quantum input at a recurrent
GREEN losing branch of forward Lugano creates a solid-plus-green cycle.
Thus the green exclusion is substantive, rather than a color convention.

### 8. Optional stronger lemma: quantum input tuples in red SCCs

The scalar-red condition in Section 1 is sufficient but is actually unnecessary
for the unflagged whole-vertex input gather. Keep the exclusion of all recurrent
green branches, but allow arbitrary positive d_h also when b is recurrent red.

A quantum redirected edge a→A_h implies old solid a→b. A solid cannot be
internal to red L_b, so a is a strict predecessor of L_b. The quantum bundle's
only new solid is A_h→b. The green parents remain strict predecessors by
Section 3, and all red targets remain in/after L_b. Thus *all* incident edges
still admit placement immediately before L_b, exactly as for the acyclic case.
The same complete-choice and tensor arguments apply without change.

This proves the stronger unflagged statement. A status co-record still needs
its own joint-event dependency bounds; arbitrary cross-SCC flags are not
licensed by this relaxation. The quartet uses precisely the bounded passive-1
flag established in Section 5 and already satisfies the conservative scalar
condition, so this optional strengthening is not a hidden prerequisite.

### Literal full-red-input route construction

### 3. Literal gather-and-record route

For every selected whole vertex J, replace all its old incoming wires by
one bundled scalar-sector wire whose labels h are its complete practical
input tuples. Redirect those old incoming wires to a new vertex A. For
one tuple h, the tensor product of its old sectors is one-dimensional by
hypothesis; identify it with the one-dimensional bundled sector h.

At J, replace each branch input set I_b by the same set of labels h in I_b.
Its direct-sum practical input Hilbert space, including all coherent matrix
entries between different h, is unchanged. Its old outputs and full native
matrix algebra remain intact. This does not split J's original branch into
smaller matrix queries.

A has one scalar branch for every joint selected tuple (h_J)_J. That branch
has the corresponding fixed tuple on all redirected incoming wires and
fixed bundled outputs h_J. Input and output dimensions are both one. Its
independent scalar filler supplies the phase for that full input pattern.
This single gather-and-record vertex is equivalent to scalar splitters,
a central record, and scalar mergers; no unrestricted quantum splitter is
inserted into a recurrent branch.

For an additional status flag from another vertex N, append two scalar
wires N->A and A->N. At every N branch fix their value to the specified
status label of that branch, as in the proved SCC scalar-record lift. The
A label includes that flag. In particular a binary passive-1 flag remains
well-defined on all of vertex 1's siblings, including those outside L.

### 4. Exact choice maps, solid edges, and weak loops

Old consistent sections have a unique extension: A's label is exactly the
old input-tuple vector and any selected status flags. Forgetting A reverses
this correspondence. Old forward choices are unchanged; old reverse choices
at a selected J are simply renamed from tuple h to the bundled label h.
Every A branch has one input and one output tuple, so contributes no actual
choice coordinate. Thus both complete choice functions, including dormant
coordinates, are in bijection with the old ones.

Every new incoming wire at a co-occurring source/A pair has its index fixed
by A's branch label, and its sector has dimension one. Every A->J bundle
wire likewise has its fixed one-dimensional label. Added status wires have
fixed one-dimensional labels at their co-occurring endpoint pairs. Hence
there are no new solid edges. Removed incoming old edges may remove old
solid edges; the remaining old edges and their dependencies are unchanged.

The only new dashed edges are green c->A_pattern and red A_pattern->c.
Section 2 puts every green parent strictly before L and every red target
in L or later. Selected status flags obey the same bounds, because their
statuses belong to a red L. Joint-pattern changes always change at least
one such coordinate. The new A branches have no outgoing green or incoming
red edges. They may therefore be placed immediately before L without
merging any old SCC or creating a new cycle. Weak loops are preserved.

The proof deals with all whole recipient vertices simultaneously. It does
not apply the rewrite successively after moving an arbitrary subset of one
vertex's branches, and does not conditionally tap a quantum input sector.

### 5. Exact tensor and phase projections

At baseline all new scalar fillers are 1, so the coherent tensor contraction
is exactly the old one. At general phases z_s it is

    G_new(u,z)=sum_s z_s G_s(u),

where G_s is the old contraction restricted to the recorded full input
pattern and status flags. Actual graph validity gives independent ancillary
completeness with the original native matrices unchanged.

At the normalized common baseline, the G_s are the orthogonal projections
of one actual native C^k slot. In particular all coarse recorded events
commute. With a passive-1 flag and a whole original j input tuple recorded,
this includes commutation of Q1 with every passive-j input-tuple projector.
This is the property used in [RG-034: Exact full-input gathering and final Gram contradiction](core-obstruction.md#rg-034).

<a id="rg-035"></a>

## RG-035 — No native branch can realize the K12 cut phase

**Statement.** No native branch can realize the K12 cut phase

**Status:** scoped negative result. **Scope:** The exact prescribed group-cut occurrence coefficient is excluded for every actual auxiliary multiplicity, not all abstract auxiliary cuts.

### Result

Write

    K12=I12 tensor |minus,1><minus,1|34,
    F12=F(U1,U2,I,I),    F34=F(I,I,U3,U4).

There is no reachable actual auxiliary branch b with nonzero origin unit
Q<=K12 and occurrence/phase coefficient

    C_b(U)=F34 Q F12.                                 (1)

This statement allows every possible native dimension and representation
multiplicity at b; the proof uses only its central branch phase. In
particular, combining it with the independently audited multiplicity-one
cut theorem and the exact supported cut spaces removes the {1,2} option
from every actual multiplicity-one auxiliary branch. Its remaining
necessary cut types are the two boundary cuts and the four singleton-before
cuts. This is neither graph deletion nor a classification of repeated
multiplicities with other marker formulas.

### 1. Fixed pair comparison convention

Fix all other original/native fillers at the common quartet baseline.
Restrict the auxiliary vertex to the two-dimensional central phase algebra
that distinguishes b from its complement. Its origin image is

    beta(z,w)=zQ+w(I-Q).

At original vertex i retain its ENTIRE actual native algebra A_i, with
origin representation rho_i. The finite-C*-algebra bipartite theorem gives
a projection P commuting with both Q and rho_i(A_i), such that the b-phase
coefficient is

    C_i(a)=Q rho_i(a)P + rho_i(a)Q(I-P).               (2)

Thus P is the sector where the b phase is AFTER the original native
operation; I-P is the BEFORE sector. No uniqueness of P is claimed or used.
On the original embedding rho_i is alpha_i, and on its passive summand it is

    rho_(p_i)(x)=alpha_i(x)(I-Q_i).

Since P commutes with the full native image, it commutes with alpha_i(x)
and Q_i as well as Q. This includes arbitrary allowed active subalgebras.
All formulas are identities on the actual complete native tensor, so the
passive affine insertion is not promoted to an artificial whole query.

### 2. Recover the true passive-3/4 order from the original restriction

For j=3,4 the native active carrier is Q_j=E_j. The exact geometry gives
Q E_j=E_j Q=0. Every active native element has origin image supported on
E_j; both orders in (2) therefore vanish on the ENTIRE active ideal:

    C_j(a_active)=0.

On the other hand, (1), restricted to original j alone, gives

    C_j(original x)=alpha_j(x)Q.

Decomposing this original insertion into its actual active and passive
components now legitimately yields

    C_(b,p_j)(x)=alpha_j(x)Q=rho_(p_j)(x)Q.            (3)

The inactive active-j sibling, pinned at its baseline, also has zero b-marked
coefficient. Hence the whole affine passive-j slice has b marker G(x)Q.
This is the exact original-to-passive bridge; (3) is not inferred merely
from a whole-query ordering statement.

For j=3, use the physical Z3; for j=4 use X4. Each maps the K12 carrier
orthogonally to itself. Since Q<=K12 is nonzero, it cannot commute with
either indicated matrix. As E_j is a physical j-cylinder and Q E_j=0,

    [Q,rho_(p_3)(Z)]=[Q,Z3] !=0,
    [Q,rho_(p_4)(X)]=[Q,X4] !=0.

The audited actual-branch no-path theorem applied to (3) therefore forces

    b -> p_3,   b -> p_4

in the full branch graph. In particular b has a path to the passive core.

### 3. The branch is strictly before the passive core

All four passive originals lie in one red SCC L. Every reachable auxiliary
branch in L is native M2 and has origin unit supported on one particular
Q_i<=S_i, by the audited saturated-core assignment theorem. Scalar native
branches cannot belong to a recurrent SCC. The exact intersections

    K12 intersect S_i = {0}, for all i,

therefore exclude b from L. This argument also preserves possible repeated
multiplicity of an M2 branch; only its represented unit is used.

Since b has a path to L and is not in it, b lies in the strict graph past
of L. There is consequently no directed path p_i->b for i=1,2. Apply the
TIME-DUAL of the no-path marker theorem, with the actual passive branch
p_i left variable. It gives the fixed-past b marker and therefore

    C_(b,p_i)(x)=rho_(p_i)(x)Q,    i=1,2.              (4)

This is a branch-specific coefficient conclusion with every active sibling
pinned. It requires neither all branches of the auxiliary vertex to be
before L nor a physical unitary cut.

### 4. Two known orders force a comparison-independent linear equation

For i=1,2, (1) restricted to the whole original i gives the opposite order:

    C_i(original x)=Q alpha_i(x).

Comparing this with (2) gives

    `[Q,alpha_i(x)](I-P)=0.                            (5)`

Equation (4), compared with (2) on the actual passive summand, gives

    [Q,alpha_i(x)(I-Q_i)]P=0.                         (6)

At x=I, (6) also gives [Q,I-Q_i]P=0. Expand the commutator in (6) and
subtract alpha_i(x)[Q,I-Q_i]P. The result is

    `[Q,alpha_i(x)](I-Q_i)P=0.                         (7)`

Since P commutes with Q_i, multiplying (5) by I-Q_i gives the same expression
on I-P. Adding to (7) yields the necessary equation

    `[Q,alpha_i(x)](I-Q_i)=0,  for all x in M2,`
    i=1,2.                                          (8)

No scalar orientation is selected on a commuting sector. A single arbitrary
valid P at the common pair baseline suffices for the calculation; it may be
nonunique and may differ between i=1 and i=2.

### 5. Exact complex-linear contradiction

The now unconditional canonical total supports are

    Q1 in {E1,S1},   Q2 in {E2,S2}.

Use the rational frame

    B=I12 tensor (|0>-|1>)3 tensor |1>4,   B†B=2I4.

Every operator supported on K12 has a unique form B H B† for H in M4(C).
Build the coefficient matrix of (8), using only x=X,Z at each of i=1,2.
There are sixteen complex unknown entries of H. This proves a stronger
linear assertion than needed: no Hermiticity, positivity, or projection
constraint is imposed on H.

For either choice Q1=E1 or S1, the i=1 system has exact rank fourteen and
kernel

    H = I1 tensor |1><v|2,   v arbitrary in C2.

For either choice Q2=E2 or S2, the i=2 system has exact rank fourteen and
kernel

    H = |minus><w|1 tensor I2,   w arbitrary in C2.

These two two-dimensional complex spaces have zero intersection. The
checker verifies the displayed kernel vectors coefficientwise and supplies
nonzero rational 14-by-14 minors for the upper-rank identities. It also
constructs a direct 16-by-16 row minor of each combined system. Their
determinants in the stated unnormalised frame are

    (E1,E2): 1/128       (E1,S2): 1/128
    (S1,E2): 1/2187      (S1,S2): 1/2187.

All selected row labels, column labels, rational matrices, determinants,
and kernel bases are saved in the JSON certificate. Thus every combined
system has exact rank sixteen over Q, and over C, forcing H=0 and Q=0.
This contradicts the hypothesized reachable branch.

The same checker verifies K12's orthogonality to E3,E4, the orthogonal
carrier displacement by Z3/X4, and positive-definite matrices
B†(I-S_i)B certifying every K12/S_i intersection is zero.

### 6. Consequence for actual multiplicity-one auxiliary branches

The supported-cut theorem gives any actual multiplicity-one auxiliary
summand a fixed before-set and a phase coefficient of the form F_R Q F_L.
The exact proper cut spaces are S1,S2,E3,E4 for the four singleton-before
sets, K12 for before={1,2}, and zero for the other nine proper sets. The
present proof eliminates the K12 option as an ACTUAL native branch,
regardless of what abstract complete extension realizes that formula.

Accordingly its only remaining necessary cut types are

- before-set empty or all originals: a boundary multiplication
- before-set {i}: a supported singleton/one-query cut with Q<=S_i

These are necessary possibilities only. This does not prove that every
remaining coefficient type is graph-realizable, that a surviving branch
can be removed from the graph, or that repeated-multiplicity branches have
a multiplicity-one cut form.

### Dependencies and exact files

- Actual pinned-sibling no-path theorem and its time dual:
  `/workspace/shared/conjectures/branch_path_phase_causality.md`
- [RG-031: Forced red passive core and uniform capacity](core-obstruction.md#rg-031)
- [RG-032: Saturated passive-core rigidity](core-obstruction.md#rg-032)
- finite-C*-algebra bipartite comparison theorem at the actual native pair
- audited multiplicity-one supported-cut theorem and all-context cut spaces
- Independent certificate:
  [core_group_cut_branch_independent_check.py](../core_group_cut_branch_independent_check.py),
  [core_group_cut_branch_independent_checks.json](../core_group_cut_branch_independent_checks.json),
  `core_group_cut_branch_independent_check.log`

The scout was not imported by the independent checker. All carriers,
comparison equations, kernels, and row minors were reconstructed exactly.

<a id="rg-038"></a>

## RG-038 — Controlled ancestral factor and optional completion

**Statement.** The strict predecessor factor is an exact controlled active-native sum with a complete optional residual tensor.

**Status:** source-level result. **Scope:** The same original variables remain in both factors; not automatically a one-query circuit factorization.

### 1. Partition and the square memory

The union A of all strict predecessor SCCs of the distinguished SCC L is a
downset. If a branch reaches any component strictly before L, it also
reaches L; it cannot belong to L or its future without creating an SCC
identification. The complement B may include auxiliary branches in L,
strictly after L, or incomparable with L. It must not silently be replaced
by L alone.

The forced-core result puts every original branch outside L in A. Those
branches are active. It also puts the active branches of originals 3 and 4
in A. Thus the selected upstream original inputs contain no passive native
branch and contain the complete active supports E3 and E4.

The downset factorization is on the original D=16 coefficient space. Its
memory dimension is exactly

    dim M = dim P · dim A_out / dim A_in = dim P = 16.

This uses actual native dimension balance, not a cap on physical cut labels
or a choice of a full product domain at a graph cut. The factors are square
unitaries after exact native recovery. Their tensor coefficients retain a
16-dimensional boundary even when evaluated with private ancillas.

### 2. An explicit common normalization

Write the initially recovered families as W_raw, V_raw, with baseline
W0=W_raw(1), V0=V_raw(1). Identify the recovered memory with the original
past using W0 and normalize the whole boundary on the left by (V0 W0)*.
Then set

    W(a) = W0* W_raw(a),
    V(b) = W0* V0* V_raw(b) W0,
    G(a,b) = (V0 W0)* G_raw(a,b) = V(b) W(a).

Both factors equal I at their respective baselines. In particular,

    W(a)=G(a,1),       V(b)=G(1,b).

This establishes the claimed agreement of a branch's normalized origin
unit and supported representation between W and the normalized full host.
No independent branch-dependent gauge is allowed or needed.

### 3. Literal coefficient proof of the controlled ancestral formula

Fix every auxiliary filler at its specified baseline. Let T be all actual
original active branches in A. The exact recovered W is a polynomial that
is affine in the selected branch tuple at each actual original vertex.

Every monomial containing two different selected branches is zero:

* For siblings at one actual vertex, native direct-sum linearity permits
  at most one selected branch in a literal section
* For branches at different original vertices, audited global active
  exclusivity forbids a literal section containing them both

The second premise is genuinely global section incompatibility. Merely
knowing that two origin projections multiply to zero at a single context
would not justify the vanishing of all mixed coefficients.

Consequently, for branch matrices a_b in right-relative baseline
coordinates,

    W(a)=C+Σ_(b in T) L_b(a_b).

The b-marked one-port coefficient is L_b=β_b by the normalized baseline
slice in Section 2. The actual complete one-port theorem identifies β_b
as the supported faithful representation with unit P_b. Evaluating at all
a_b=I gives C=I−Σ_b P_b. Thus

    W(a)=I−P_A+Σ_(b in T) β_b(a_b),   P_A=Σ_b P_b.

At one original vertex the units are orthogonal central summand units in
its represented native algebra. At distinct originals they are contained
in the already orthogonal total carriers Q_i. Thus their sum is a
projection and the formula is a direct controlled sum on the original
16-dimensional space, with all represented multiplicities retained.

For the original embedding π_(i,b), the native classification gives
β_b(π_(i,b)(x))=α_i(x)P_b. Summing over upstream branches of original i
proves the draft's equation (2), including P_3^A=E3 and P_4^A=E4.

This substitution shares the SAME U_i, and the SAME private ancilla, with
any passive or active sibling belonging to B. It does not produce two
independent original calls. No direct-sum summand is promoted to a new
actual vertex.

### 4. Private completeness, including a split vertex

All private systems are indexed by actual native vertices. Branches of
one vertex are independent direct-sum alternatives on a common private
system E_v, not independent laboratories.

The draft can invoke the audited amplified recovery. There is also a
direct coefficient justification that avoids any new amplified memory
gauge. Lift the fixed D-dimensional coefficient tensors of G, V, W to
arbitrary private E_v. Since V and W are the baseline slices G(1,b) and
G(a,1), each lifted slice is unitary for all allowed private-amplified
branch unitaries by complete unitarity of the full host.

The scalar polynomial identity G=VW lifts coefficientwise. A coefficient
of VW containing both an A branch and a B branch at the same actual vertex
is zero, because G has total degree one in that vertex's full native
direct-sum tuple. Fixing the native matrix-entry indices first makes this
an equality of boundary coefficient matrices. Multiplying such a zero
coefficient by the two possibly noncommuting private matrix entries still
gives zero. In every remaining monomial, there is at most one private
matrix entry for each vertex, and entries from distinct private systems
commute. Its amplified coefficient therefore agrees with G's canonical
amplification.

Thus the lifted factorization uses the original D-dimensional coefficient
tensors and the same private systems at a split vertex; it does not rely
on identifying separately chosen amplified memories. Pinning all A
fillers at their baseline tensored with I_E leaves W(1)=I on the full
boundary and all private systems. This proves the needed complete
unitarity premise for V with the absent alternative I_Ev.

### 5. Exact optional-algebra homogenization

List only actual vertices having at least one B branch as residual inputs.
For a wholly B vertex retain its actual direct-sum algebra. For a split
vertex v use

    (⊕_(b in B at v) M_(d_b)) ⊕ C.

Omit wholly A vertices. This is the natural precise reading of the draft;
adding unused dummy scalar inputs would be unnecessary. There is ONE new
scalar summand for the whole absent event, even if v has many A branches.
Its represented support may have arbitrary allowed rank: the rank is not
the number of scalar summands.

For one selected vertex v write the coefficient polynomial as

    K = K_abs + Σ_b K_b(a_b).

After private amplification, write U_b=Σ_pq E_pq⊗U_(b,pq). For a unitary
Z on E_v, the blocks of U_b(I_(d_b)⊗Z*) are U_(b,pq) Z*. In every term
where v is present, right multiplication of the whole output by Z gives

    [coefficient] U_(b,pq) Z* Z = [coefficient] U_(b,pq).

The moved Z commutes with boundary coefficient matrices and every other
vertex's private matrix entries. It is never commuted through U_(b,pq).
In an absent term it remains as the unique scalar input Z. Hence exactly

    K_hat((U_b),Z)
      = K((U_b(I_(d_b)⊗Z*))_b) (I_boundary⊗Z).

Both factors on the right are unitary. With several split vertices,
replace every selected U_b at v by U_b(I⊗Z_v*) and multiply on the right
by the product of all Z_v. The Z_v act on distinct private systems and
commute. The term-by-term identity simultaneously proves separate
linearity on the completed direct-sum algebras and arbitrary independent
private-ancilla unitarity. The new scalar coordinate has identity baseline
1, so the completed V remains normalized.

This proves the lemma without treating Z as a scalar complex phase at
ancillary levels, without commuting it through U_b, and without inserting
one scalar option for each absent A branch.

### 6. Exact reproducible calibrations

Run, using only Python's standard library:

    python core_ancestral_controlled_factor_independent_check.py

The generated `_checks.json` records:

* 100 exact optional-completion/unitarity identities on D=16 with two
  private qubits and two branches at each tested vertex
* The incorrect left substitution (I⊗Z*)U_b fails in 98 of these trials
* Incorrect final left multiplication by Z also fails in 98 trials
* 50 independent-branch and 50 shared-original-parameter split-vertex
  identities, using one common private qubit at the split vertex
* 3,840 exact incompatible amplified matrix-unit products vanish
* Three ancestral alternatives combine into one absent event of rank six

The tests use exact signed permutation unitaries, including noncommuting
local/private actions. They calibrate the ordering, shared-index, and
absent-multiplicity issues. They do not replace the general coefficient
proof or construct a routed host.

### 7. Permitted conclusion and remaining boundary

The strict ancestral original dependence, at fixed auxiliary baselines,
is exactly the displayed controlled native sum. The residual has a
well-defined normalized ancillary-complete optional-algebra tensor on the
original D-dimensional coefficient boundary. Its unrestricted B-native
inputs, including the core native M2 inputs, are retained.

Nothing here realizes either tensor as a new valid routed graph, removes
auxiliary vertices in B, makes the core a standalone physical SCC
fragment, bounds a physical cut's correlated labels by D, or supplies an
independent arbitrary M16 gate at the memory. In particular any subsequent
construction must restore the actual shared original vertices and all
split-vertex zero coefficients. On that expressly algebraic scope, no
remaining proof gap was found.

<a id="rg-039"></a>

## RG-039 — Bounded necessary layer-tensor form

**Statement.** The necessary reduction has at most seven retained layer tensors, 32 branches per recurrent layer and 36 aggregate carrier patterns.

**Status:** source-level result. **Scope:** Only a necessary coefficient relaxation; it gives neither a graph realization nor a sufficiency theorem.

### 1. Simultaneous gauges really are full-host slices

An initial union A_j=C_1 union ... union C_j of any topological SCC order is
a downset of the full branch graph. The audited theorem gives a square
D-dimensional recovered factorization for every such cut. If G(1)=I and
G(X,Y)=V_raw(Y) W_raw(X), the baseline matrices satisfy V_0 W_0=I. Therefore

    G(1,Y) G(X,1)
       = V_raw(Y) W_0 V_0 W_raw(X)
       = G(X,Y).

No independent factor gauges are being identified by fiat. For the cut
A_(j-1) against its complement, fix every component after C_j at baseline.
The two factors are then respectively the slice with C_j free and the
slice with A_(j-1) free. Induction gives exactly

    G(u)=L_m(u_Cm) ... L_1(u_C1),
    L_j(u_Cj)=G(1,...,u_Cj,...,1).

All matrices act on the same normalized original D=16 coefficient boundary.
The dimension follows from dim M=D dim A_out/dim A_in=D, using actual native
balance. It is unrelated to the cardinality of a physical cut's labels.

The cut theorem initially gives unitary-input identities. Each side is a
polynomial in disjoint native branch entries and separately affine in each
individual branch matrix, since that branch occurs in only one factor. The
blocks of a native direct-sum unitary vary independently. Their unitary
affine spanning therefore extends the identity to arbitrary matrices. There is no use of inverses of
variable fillers.

### 2. Native query use and private completeness survive composition

Every actual branch occurs in one and only one C_j. Even when one actual
vertex appears in several factors, each factor contains disjoint branch
variables at that vertex. At fixed native-entry indices, a monomial in the
product has a unique assignment of its variables to layers. The full host
has degree at most one in that vertex's direct-sum tuple. Hence every
product coefficient that selects two distinct branches at that vertex is
zero as a boundary matrix. This is stronger than a cancellation only after
sharing original parameters.

On private amplification, the potentially repeated entries at that vertex
would appear in the fixed layer order. Their boundary coefficient is
already zero before multiplication by those possibly noncommuting entries.
Every surviving term contains at most one entry from that vertex. Entries
at different actual vertices act on independent private systems and
commute. The factor identity consequently lifts using one private system
per actual vertex, including vertices split across several layers.

Each L_j is literally a full-host baseline slice. Its independent private
completeness follows by putting the baseline tensored with the private
identity in all other branches. At a selected vertex v it is affine in the
branches in C_j. If any sibling is outside C_j, homogenize the single
absent alternative using one scalar summand:

    A_(j,v)=(direct sum_(b at v in C_j) M_(d_b)) direct sum C.

If the whole vertex lies in C_j, no scalar is added. The proved completion
identity uses U_b(I tensor Z_v*) on the right of each active branch and a
final right multiplication by Z_v. It is valid for noncommuting private
entries. A large number of absent siblings contributes one scalar
alternative, not one source or one scalar summand per sibling.

**Encoding clarification:** these artificial scalar coordinates are set to
1 when recovering the original native product and imposing its shared-query
or native-linearity equations. Their arbitrary independently completed
values are used to test each layer's completeness, not to claim that the
product of completed layers is a new single-use native process for arbitrary
new scalar inputs. With this reading, the stated query accounting is
correct.

### 3. Omitting auxiliary-only components is exact at the stated baseline

After fixing every auxiliary filler to its prescribed native baseline, a
component without an original branch has L_j=G(1)=I. This remains true when
the same auxiliary vertex has a different branch in a retained component:
the omitted component has no free branch of its own, and the slices have
disjoint branch variable lists. Its matrix disappears from the product.

For each retained layer, keep its native branch freedoms while all other
layers are pinned. Optional source completion depends only on its selected
branches and the yes/no fact that some sibling is absent. The arbitrarily
large algebras and branch lists belonging wholly to omitted components are
absorbed into finite coefficient matrices. Their independent freedoms are
not preserved. This is exactly the permitted tensor restriction and does
not silently contract a physical routed fragment.

### 4. Branch, source, and exchange-dimension bounds

The four passive original branches belong to the same forced red SCC.
The active carrier ranks of originals 1 and 2 are at most four. Every
nonzero original active simple summand has native dimension at least two,
because it admits the original unital M2 embedding; its faithful supported
representation has rank a positive multiple of that native dimension.
Thus each of originals 1 and 2 has at most two active branches. Originals
3 and 4 each have one. There are at most six active branches outside the
passive core, hence at most seven retained SCCs. This does not resolve a
multiplicity-two M2 or an M4 as two different branches.

In a recurrent SCC, the reviewed trace-capacity inequality is

    sum_b rank(P_b) log2(d_b) <= D log2(D)=64.

Every such branch has d_b>=2 and rank(P_b)>=d_b, so there are at most32.
The same inequality gives sum_b log2(d_b)<=32 and therefore

    D product_b d_b <=16*2^32=2^36.

This is the all-exchange dimension of the corresponding virtual layer
factor, not a physical cut dimension. No rank divisibility by a joint
native-dimension product is asserted. An acyclic SCC is one branch. At any
reachable branch, the faithful one-port representation also gives d_b<=16.
The distinguished core has its already proved stronger bound of ten M2
branches. All stated bounds are consequently valid; using32 for every
retained layer is simply loose.

### 5. The36 aggregate (Q,T) patterns and F=B A

Let C_i denote the active original support inside the core. Every such core
branch has unit E_i or S_i-E_i. With Q_i in {E_i,S_i} for i=1,2 and
T_i=Q_i-C_i, exactly the six listed pairs remain as a necessary list.
For i=3,4 the independent full-input audit puts their active branches
strictly upstream, so Q_i=T_i=E_i. Upstream individual summands can retain
hidden multiplicity or tilted supports when their aggregate is S_i. The
36-pair list does not select an unsupported basis for them.

Global section incompatibility, not just orthogonality of baseline
projections, kills all coefficients using two upstream active branches.
The normalized original-only ancestral factor is therefore exactly

    A_T(U)=I-sum_i T_i+sum_i alpha_i(U_i)T_i.

The same formula holds for each upstream SCC's selected subset. Their
supports are orthogonal reducing projections for the corresponding origin
representations. All these factors commute, and their product is A_T.
This justifies the loss of upstream original-only ordering data.

The core's baseline slice is the joint native quartet formula with
upstream active fillers pinned at identity. It is

    B(U)=W_phys(U) R
          +sum_i U_bar_i [T_i+alpha_i(U_i) C_i],
    R=I-sum_i Q_i.

Here U_bar_i denotes the product of physical original actions at the three
other ports. The key identities are

    B(U) T_i=U_bar_i T_i,
    B(U)(I-sum_i T_i)
       =W_phys(U)R+sum_i U_bar_i alpha_i(U_i)C_i.

Because T_i reduces alpha_i, multiplication gives

    B(U) A_T(U)
       =W_phys(U)R+sum_i U_bar_i alpha_i(U_i)Q_i
       =F(U).

The proof is polynomial for arbitrary matrices. On unitaries A_T is a
direct controlled unitary, and B=F A_T* is unitary. Their stronger separate
private completeness on their actual optional sources follows from the
baseline-slice construction; it is not inferred solely from ordinary
unitarity of the displayed shared-parameter formula.

All incompatible repeated-query terms vanish as boundary matrix
coefficients, before any private entries are multiplied. The argument
therefore also preserves a common, possibly noncommuting private system at
each original query. No second independent original query is introduced.

### 6. An explicit finite number of real coefficient variables

The stated finite relaxation has a genuine uniform variable bound.
Here is a deliberately very loose one. There are at most7*32=224 retained
branch incidences and at most224 layer-source incidences. In one layer,
let k_v>=1 be the number of selected branches at source v. The complex
vector-space dimension of its completed input algebra is

    a_v=sum_(b at v) d_b^2+epsilon_v,
    epsilon_v in {0,1}.

Since d_b<=16,

    a_v<=256 k_v+1<=257^(k_v).

A separately linear optional layer tensor to M16 has at most

    256 product_v a_v <=256*257^32

complex coefficients. Across seven layers this gives at most

    3584*257^32

real coefficient variables. Smaller cases can be treated as a finite
union rather than padding with sources that do not exist.

The discrete data are finite as well: branch dimensions1,...,16; their
layer assignments; their partitions into actual vertices; original-query
labels; and absent-summand indicators. In particular the same-vertex
identifications across layers are a partition of at most224 source
incidences. The original M2 inclusions can be parameterized by finitely
many bounded-size matrix units subject to polynomial homomorphism and
adjoint equations; alternatively use unitary conjugacies for their fixed
finite multiplicity types. No data about the unbounded omitted native
algebras have to be retained. Baselines can be identities in relative
native coordinates; allowing bounded-size baseline matrices instead also
keeps the variable count finite.

For each fixed discrete type, coefficients of the product, its target
restriction, the native repeated-vertex zero identities, normalization,
and canonical origin identities are finite polynomial equations in real
and imaginary parts. Ordinary layer-unitarity is a finite first-order
real formula: universally quantify the finitely many local block entries,
assume their unitary equations, and require L*L=I. Quantifier elimination
over real closed fields produces a semialgebraic condition on the layer
coefficients. Existential feasibility of the resulting finite union is
therefore a bounded-variable necessary relaxation.

A prescribed finite set of private-ancilla dimensions adds another finite
collection of polynomial tests. The proof does not turn unrestricted
private completeness into finitely many tests and does not state an
ancilla cutoff. Nor does a solution of the relaxation establish routed
topology, bi-univocality, weak loops, or realizability of any virtual layer.

### 7. Reproducible exact calibration

Run:

    python bounded_layer_tensor_normal_form_independent_check.py

The checker uses the portable exact quartet fixtures but reconstructs the
candidate supports and factors independently. It checks all36 carrier
patterns against the direct physical normalized quartet on two tuples of
arbitrary nonunitary matrices, including singular and zero inputs. It also
checks all36 patterns on an exact private-qubit extension whose matrix
entry blocks do not commute, testing F=B A and unitarity of F,A,B. All
calculations are rational or Gaussian-rational. The resulting JSON and log
are adjacent to the checker. The run completed with PASS:72 ordinary
nonunitary identities and36 private-qubit identities/unitarity checks.
These finite tests calibrate the formulas;
the general validity and boundedness are the proofs above.

### 8. Scope of the green-placement addendum

The stated Section5 is explicitly conditional on the separate
non-green input-gather graph audit. Nothing in Sections1-6 relies on it.
Once that premise is independently established, the four relations
(same SCC,3 before4,4 before3,incomparable) exhaust the partial-order
possibilities for their two recurrent green SCCs. Both remain strict
predecessors of the passive core by the already audited branch result.
The graph-color premise should be cited to its own final audit rather
than inferred from this tensor calculation.
