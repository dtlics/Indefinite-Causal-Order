# Obstruction

[Topic index](../../README.md) · [Shared result index](../../../../RESULTS.md#rg--exact-native-routed-graph-universality)

Each result below has one owner. Exact scope and proof are updated here. Source-level mathematical arguments and finite certificates are distinguished from a new formal verification.

<a id="rg-001"></a>

## RG-001 — Exact four-qubit routed-host obstruction

**Statement.** The explicit independently private-complete M2^4 -> M16 process has no finite bi-univocal weak-loop host with one whole complete monopartite insertion per original query.

**Status:** source-level proof with exact certificates. **Scope:** Original dimension-16 past/future; exact equality; arbitrary finite fixed auxiliaries and multiplicities. Excludes no approximation, enlarged boundary, distributed-query or extra-query model.

### 1. Claim and realization model

Let H=(C2)^tensor4, with identical sixteen-dimensional global past and
future. We exhibit a complex multilinear map

    F:M2 × M2 × M2 × M2 -> M16

which maps independently private-ancilla-amplified unitary inputs to a
unitary output at every finite private dimension, but has no realization
of the following form:

1. A finite dimension-balanced routed graph, with its full forward and
   reverse bifurcation-choice maps univocal and with weak loops
2. Arbitrary fixed routed unitary fillers at any finite number of
   auxiliary vertices
3. Each original M2 input used exactly once, at its own actual native
   vertex, through a linear independently complete monopartite unitary
   insertion
4. Equality of the full multilinear tensor on the original H boundary,
   including its canonical independent private-ancilla amplifications

No bound on auxiliary count, internal multiplicity or sector dimensions
is assumed. Branches at the same native vertex can belong to different
strongly connected components. Nothing in the proof contracts a physical
SCC fragment as a unitary or enlarges a native original query by fiat.

The model is the finite skeletal realization in Corollary3.1 of
[Vanrietvelde, Ormrod, Kristjansson and Barrett, arXiv2206.10042v3](https://arxiv.org/html/2206.10042v3),
with exact boundary and whole one-use monopartite insertions as stipulated
in the problem. Theorem3.1 expressly uses bi-univocality and weak loops as
the definition of a valid graph; validity here does not mean an arbitrary
cyclic tensor network that happens to be unitary at selected fillers.
Corollary3.1 specifies the fixed-unitary and complete monopartite fillings,
and Conjecture1 asks for such a fleshing-out of a valid graph. The theorem
concerns that precise formulation of routed universality; see also
[Exact model](../FINAL_MODEL_AND_SCOPE.md).

#### Native algebras and graph conventions

A native branch b is one rectangular component of a vertex's routed
relation. Its practical input and output spaces have the same dimension
d_b, and its freely fillable matrix block is M_(d_b), after fixing input/
output baseline identifications. The entire vertex has algebra
direct_sum_b M_(d_b). Positive-dimensional edge sectors and all dormant
choice coordinates are retained. Unreachable branches are removed.

A solid b->c arrow means an actual physical edge has, conditional on
co-occurring b,c, either more than one allowed index value or a sector of
dimension greater than one. A green b->c arrow means changing only b's
forward output choice can change c's occurrence. A red b->c arrow means
changing only c's reverse input choice can change b's occurrence. Weak
loops say every recurrent strongly connected component (SCC) is entirely
green or entirely red, with no internal solid arrow.

At a unitary baseline normalize the global map to I. A one-port native
slice is a unital *-representation rho of its full finite C*-algebra.
Write beta_b for its branch summand and P_b=beta_b(I_b). Reachability makes
beta_b faithful, so rank(P_b)=m_b d_b with integer m_b>=1.

For clarity, a complete monopartite insertion falls within this algebra
model automatically. If T:M2->direct_sum_b M_(d_b) is such an insertion,
then T(I) is branchwise unitary. The normalized map T(I)†T(x) is unital.
Expanding at exp(it h) gives a Jordan *-homomorphism. Applying the same
argument to its actual private-M2 amplification and polarizing an
off-diagonal 2-by-2 Hermitian matrix gives associative multiplication.
Thus it is a unital *-homomorphism. This uses no operation mixing distinct
central native branches. Its fixed T(I) is absorbed in the local baseline.

### 2. The explicit completely unitary quartet

Let plus=(|0>+|1>)/sqrt2, minus=(|0>-|1>)/sqrt2 and
Bell+=(|00>+|11>)/sqrt2. Define

    E1=I1 tensor |0,Bell+><0,Bell+|_(234),
    E2=I2 tensor |eta><eta|_(134),
    eta=(|0,0,1>+|1,minus,plus>)/sqrt2,
    E3=I3 tensor |0,1,0><0,1,0|_(124),
    E4=I4 tensor |1,1,plus><1,1,plus|_(123).

These are mutually orthogonal rank-two projections, each trivial on its
own query qubit. All their matrix entries are rational. Put

    V_o=I-2 sum_i o_i E_i,                 o in {0,1}^4,
    F_raw(U)=sum_o |o><o| (tensor_i U_i) V_o,
    D0=I+sum_i (Z_i-I)E_i,
    F(U)=F_raw(U)D0.                                   (2.1)

The map is linear in each Ui and F(I)=I. Its single representations are

    alpha_i(x)=R_i x_i R_i,
    R_i=I+(Z_i-I)E_i.                                  (2.2)

An equivalent formula useful below is

    F(U)=tensor_i U_i
          +sum_i U_bar_i (Z_i U_i Z_i-U_i) E_i,         (2.3)

where U_bar_i is the product of the other three physical inputs.

#### Complete unitarity proof

Let Ui be an arbitrary unitary on its qubit and private system K_i; all
E_i act trivially on the private systems. Set

    P_o=(tensor Ui)† (|o><o| tensor I_private) (tensor Ui),
    A_i=sum_o o_i P_o=Ui†(|1><1|_i tensor I_Ki)Ui.

The different A_i commute, A_i commutes with E_i, and for i!=j,
sum_o o_i o_j P_o=A_i A_j. Direct expansion yields

    F_raw†F_raw
     =I-2 sum_i(E_i A_i+A_i E_i)
        +4 sum_i E_i A_i E_i
        +4 sum_(i!=j) E_i A_i A_j E_j.

The one-index terms cancel. Each cross term is
A_i E_i E_j A_j=0. Therefore F_raw†F_raw=I at arbitrary private dimensions.
The map is square, hence unitary. At identity its value is the unitary D0,
which proves the same assertion for F. No two entries of a single private
unitary were commuted. This is a parameter proof, not a finite test.

### 3. Two finite-C*-algebra facts

We use the following complete bipartite classification. If a normalized
bilinear map G:A×B->M_D is independently completely unitary preserving,
where A,B are finite C*-algebras, its single maps alpha,beta are unital
*-representations and there is an orthogonal projection K commuting with
both represented algebras such that

    G(a,b)=alpha(a)beta(b)K+beta(b)alpha(a)(I-K).        (3.1)

No simplicity, faithfulness or uniqueness of K is required. This is
applied to entire native vertices, before restricting their branch blocks.

For reproducibility, the attached proof
[RG-002: Complete finite-algebra bipartite comparison](foundations.md#rg-002) establishes (3.1) as follows.
The normalized one-variable slices are homomorphisms. Differentiating
their multiplication laws gives the two represented Leibniz identities
for the mixed correction h=G-alpha beta. Comparing the two expansions
gives C(a,b)h(a',b')=h(a,b)C(a',b'), where C is the cross commutator. The
common kernel of all C is reducing. On its complement a finite Gram
inverse constructs one multiplier commuting with both endpoint algebras.
On the common kernel, the signed-reflection unitarity equations force
h†h=0. On the complement the same equations make the multiplier
self-adjoint and idempotent, giving K. This proof retains central direct
sums and all private-M2 multiplications. Its three independent derivations
and the exact hypotheses are included with the dependency manifest.

We also use commuting-origin rigidity: a normalized multilinear unitary
preserver whose single maps are commuting representations is their product.
A direct induction on Hermitian reflections proves it. After subtracting
the product, the difference vanishes on proper identity faces. The full
sign Fourier coefficient in unitarity makes the remaining correction
skew-adjoint; the all-but-one coefficients make it anticommute with every
single reflection. The constant coefficient is then its positive square,
so it vanishes. Reflections span each finite C*-algebra. In particular this
applies to commutative phase inputs without ancillary assumptions.

### 4. Computer-assisted finite native-interface lemma

Define four mutually orthogonal serial supports

    S1=I1 tensor |0><0|_2 tensor
          Proj span{|plus,0>,|1,minus>}_(34),
    S2=I2 tensor Proj span{|0,0,1>,|1,minus,plus>}_(134),
    S3=E3, S4=E4.                                     (4.1)

Their ranks are4,4,2,2, and E_i<=S_i. The exact finite lemma needed in the
proof is the following.

**Native-interface lemma.** For every complete native replacement of the
four whole original queries, with arbitrary other vertices fixed at a
unitary baseline, each native algebra has one passive M2 quotient and an
active ideal. Its represented active unit Q_i obeys

    0<=Q_i<=S_i,    [Q_i,alpha_i(M2)]=0.

At ports3/4 the represented algebra is either the original M2, or exactly
M2+M2 on E_i and I-E_i, with multiplicities1 and7. At ports1/2 the active
rank is0,2 or4. If A_i denotes a represented active matrix and b_i its
passive qubit input, the entire joint native tensor is

    G((a_i+b_i)_i)=sum_i U_bar_i(b) A_i + F(b) R_Q,
    R_Q=I-sum_i Q_i.                                  (4.2)

The result does not grant any larger native freedom than the actual host.

#### Why the finite calculation is exhaustive

Untwist a native origin algebra by R_i. Since it contains the original
M2 factor, it is M2 tensor B_i for a unital B_i subset M8. Restricting a
whole native/original pair invokes (3.1). Five original pair comparison
families are finite two-element families; only pair34 has a continuous
projection family. For a finite family, real-analytic finite-disjunction
locking gives one comparison satisfying the native commutation condition
at every spectator origin. This does not choose a continuous projection
from a multivalued family. Each locked comparison and its unitary transport
therefore gives an exact linear commutator constraint on B_i.

For port2 the three incident conditions are intersected. The Gaussian-
rational spectator set is I,X,Y,Z and (3I+4iX)/5,(3I+4iY)/5,(3I+4iZ)/5.
The sixteen first-stage candidates reduce to four distinct algebras of
dimensions6,5,7,9; the second stage leaves dimensions5 and6; the third
leaves exactly M2(J)+C(I-J), with J the relative rank-two carrier in S2.
These are exact subspace intersections, not dimension-only comparisons.

At port1 the eight locked bit rows have relative dimensions5,5,5,5,2,2,2,2.
The first four lie in M2 on S1 plus the scalar complement; the latter four
lie in the two-dimensional algebra generated by E1. The corresponding
comparisons annihilate the indicated serial support.

For ports3/4 retain the full continuous family as a relaxation. Write its
relative projection p=h+q, with q supported on c. For an arbitrary native
relative coefficient X introduce Y=pX. The necessary linear equations are

    (I-c)Y=hX,       Y(I-c)=Xh.                        (4.3)

The same Y is used for every original-factor matrix coefficient t. In the
physical frame A=R_i(t tensor X)R_i and B=R_i(t tensor Y)R_i, transport
through the continuous pair at its identity origin is

    u_j† [B+alpha_j(u_j)(A-B)alpha_j(u_j)†]u_j.        (4.4)

The two finite locked transports follow. Complex linearity of the actual
native tensor in every spectator supplies rational linear constraints on
(X,Y). Eliminating Y existentially in each of the four finite bit cases,
for each port, leaves precisely span{I,e_i} as the projected X-space.
All eight exact dimensions are2. This relaxation imposes neither positivity
nor a projection equation on Y; it can only enlarge the actual possibilities.
It therefore covers every continuous comparison and every actual native
algebra. The displayed two-dimensional space is explicitly verified to be
the final projected space, not merely a sampled upper bound.

The reproducible programs are context_closure.py, locked_contexts.py,
verify_first_port_serial_ideals.py and verify_last_port_maximality.py,
with an independent last-port reconstruction. They use rational/Gaussian-
rational matrices only. Their inputs, row spaces, kernels and exact
outputs are included. Full mathematical reductions are appended in
[RG-007: Exact second-port algebra containment](native-interfaces.md#rg-007), [RG-008: Exact third/fourth-port algebra containment](native-interfaces.md#rg-008) and
[RG-009: Passive quotients and unique active serial ideals](native-interfaces.md#rg-009). The finite lemma is the only
nontrivial computational elimination in the contradiction.

#### Passive quotient and tensor formula

Restriction of B_i to the large scalar complement defines a character.
Its kernel is the active ideal, and tensoring the character with M2 gives
the passive quotient. Origin-kernel simple summands vanish at every
context: their normalized support projections vary continuously over a
connected product of unitary groups, so zero rank stays zero; unitary
spanning then kills the whole coefficient tensor. Reachability excludes
such unused summands in an actual host.

Every comparison annihilates Q_i. In the exact transport of an active
matrix A_i, the other E_j annihilate it, and the relative transports act
as identity on it. Thus its one-port coefficient is U_bar_i A_i. Subtracting
the original insertion gives the passive coefficient F(b)(I-Q_i).

To obtain the simultaneous formula rather than just marginal ones, put
independent phases on the active ideals. With original active fillers,
commuting-origin rigidity gives all-passive coefficient F(b)R_Q. At
arbitrary active unitaries let C_S be the phase coefficient indexed by
the set S of active ports. Unitarity and phase Parseval give

    sum_S ||C_S||²=D,
    sum_S |S| ||C_S||²=sum_i rank Q_i,
    ||C_empty||²=D-sum_i rank Q_i.

Subtracting forces sum_(|S|>=2)(|S|-1)||C_S||²=0. Every multi-active
coefficient vanishes, and the remaining coefficients are the one-port
ones. This proves (4.2) coefficientwise, also with private ancillas.

### 5. Graph/exchange facts with pinned siblings

The following facts follow from the routed exchange induction in
AppendixB.4 of the primary paper. We give the recovery details that matter
for actual partial branches.

For any set of branches still exchanged, at each native vertex use their
occurrence alternatives together with I minus their sum. The complement
is the sum of all pinned or otherwise omitted siblings. H2/H4 make these
a commuting orthogonal pattern partition; H5 and inclusion--exclusion
identify exact restricted native contractions. In a pattern close an
active exchange with its desired filler u_b, and an inactive exchange with
Theta_b†/d_b. The inactive bypass has trace1, since
Tr(Theta_b†Theta_b)/d_b=1. Summing patterns is exact linear recovery,
including when a marked branch has already been closed. It requires no
inverse filler-dependent trace, generic limit or whole-vertex substitution.

#### 5.1 Fixed one-SCC occurrence markers

For a green SCC L, fix all outside fillers. Its marked coefficients obey

    G_b(u)=P_b G(u),                 b in L,           (5.1)

with fixed future projections independent of every filler in L. For a red
SCC the exact time dual is G_b(u)=G(u)P_b.

For a green L fill its strict past, leaving L and the future exchanged.
H6 and the inactive bypass put the pullback of the full L-input algebra
on the past and L-output factors. Representation theory factors this
exchange unitary across a D-dimensional memory. H2 puts the future
occurrence patterns and the marked b projector entirely on the future
factor. Recover the future identically in marked and unmarked tensors,
then recover the current layer with the same right-domain patterns. The
two contractions have forms V_b A(u) and V_0 A(u), with V_0 unitary. Thus
P_b=V_b V_0† is independent of u. Branch-phase unitarity makes it a
projection. This proves (5.1) without requiring whole vertices in L.

Extracting further phase coefficients shows all these projections commute
and joint marks are their products. Include negative/complementary status
events at each vertex. At every outside unitary context each joint product
is a projection. Its rank is constant over the connected full native
unitary domain. A zero at one baseline therefore makes the corresponding
tensor zero everywhere. Conversely a consistent section gives a nonzero
matrix-unit coefficient by selecting its branch, index and quantum-basis
tuple at every vertex. Consequently a same-SCC status pattern is globally
reachable if and only if its baseline projection is nonzero. This step
must not be used for arbitrary patterns in different SCCs.

#### 5.2 No directed path fixes the opposite operational order

For distinct native vertices, if no branch-graph path b->*c exists, then

    G_(b,c)(x)=P_b beta_c(x).                          (5.2)

Choose an SCC order with c before b and use the exchange induction on the
reversed graph. If original b is green, stop before filling its reversed
red layer; if original b is red, put it last in its reversed green layer
and stop before it. Both are non-special induction boundaries. All allowed
future factors of b's original input marker have been filled, so H2 puts
that marker on the global future alone. H5 gives T_b=P_F T. Apply the same
right-pattern recovery just described to both sides; P_F factors out.
Normalizing and taking c's actual linear coefficient gives (5.2). The
time dual gives beta_c(x)P_b when no c->*b path exists.

#### 5.3 Same-layer product capacity

For branches B that co-occur inside a red SCC, H7 at the reverse-induction
boundary supplies output intertwiners

    S_B f_(b,out)=(K_b(f) tensor I)S_B.

Recover the strict past using right patterns with no current output
support; the same intertwiners survive. The span W of all partial-current-
input rows of S_B is nonzero. On W, each K_b gives a unital algebra
representation of M_(d_b), and different factors commute. Hence
tensor_(b in B) M_(d_b) acts on W, so

    product_(b in B) d_b divides dim W <=D.            (5.3)

No *-representation or physical-cut isometry is assumed in constructing
W. In particular (5.3) does not assert a corresponding divisibility of the
joint occurrence-marker rank. The green statement is time dual.

### 6. All originals have active branches

Suppose Q_i=0. The native-interface lemma leaves a single reachable M2
branch at original i. A constant-status branch has no incoming green or
outgoing red edge and cannot be recurrent. Place all other native branches
before or after it in an SCC topological order. The exchange first/last
endpoint identities imply that its comparison with any whole native
vertex j is a sum of the actual branch identities before that singleton.
Thus the comparison is central at native j, not an arbitrary hidden
multiplicity projection.

The passive M2 summand at j is simple. A central comparison P therefore
has either P<=Q_j<=S_j or I-P<=Q_j<=S_j. One of the two pair order defects
must vanish on I-S_j. It does not. Taking both original pair inputs X,
the exact squared Hilbert--Schmidt norms of the two right-complement
defects are as follows:

    proposed i   tested j     first order   reverse order
        1            2            6             16
        2            1            8             12
        3            1           16/3           16
        4            1           16/3           16.

Each entry is obtained directly from (2.1), (2.2) and (4.1); explicit
nonzero matrix entries are in native_single_branch_centrality_checks.json.
All four Q_i are therefore nonzero. In particular Q3=E3 and Q4=E4, and
their active branches are native M2 with represented rank2.

### 7. A forced red passive core

We first record a simple exact geometric fact. For i!=j no nonzero
projection P<=S_i commutes with alpha_j(M2). Since E_j S_i=0, conjugating
by R_j leaves P fixed. Such a commuting projection would therefore be an
ordinary physical-j cylinder I_j tensor q. But each exact matrix
Tr_j(I-S_i) is positive definite, excluding such a nonzero cylinder. The
twelve Gaussian-rational positive-definiteness checks are in the cross-
serial-cylinder certificate; the spaces in (4.1) define them completely.

Let p_i be the passive original branch with unit I-Q_i and representation
rho_i(x)=alpha_i(x)(I-Q_i). Formula (4.2) gives

    G_(p_j,p_i)(x)=rho_i(x)(I-Q_j).

If no p_j->*p_i path existed, (5.2) would give the opposite order. Their
difference is [Q_j,alpha_i(x)] because Q_iQ_j=0, and cannot vanish for all
x by the preceding geometry. Thus all four passive branches are mutually
reachable in a recurrent SCC L. This SCC cannot be green: (5.1) would
give the same forbidden opposite-order identity. It is red.

For any active branch a of original i with unit P_a<=S_i, the mixed
coefficient with passive j!=i is rho_j(x)P_a. The same argument gives
a->*p_j. Thus every original active branch lies in L or strictly before it.

The negative passive-status events belong to the same red L. At baseline
their pair projections are Q_iQ_j=0. Same-SCC pattern faithfulness therefore
proves that original active events are globally mutually exclusive, even
when their actual branches lie outside L. This is a global route statement,
not an inference from an arbitrary cross-SCC zero coefficient.

### 8. Saturation fixes the total carriers

The all-passive joint unit is R_Q=I-sum Q_i, of rank at least4. Its four
native M2 dimensions saturate (5.3): their row module is all of H. The
common H7 output actions form a representation of M2 tensor M2 tensor
M2 tensor M2=M16 on H. Hence for an invertible S,

    F(U)R_Q=S(tensor Ui)S^-1 R_Q.                     (8.1)

The S need not initially be unitary. It is forced by coefficients.

More generally, let P!=0 satisfy F(U)P=S(tensor Ui)S^-1P. For the physical
matrix-unit coefficient indexed by output o and input a, (2.1) gives

    |o><a|V_oD0P=S|o><a|S^-1P.

Some row of S^-1P is nonzero. Its coefficient then forces every S|o> to
be proportional to |o>; S is diagonal, with diagonal s_o. Taking o=0000
and comparing the other rows yields

    V_o D0P=(s_o/s_0)D0P.

The simultaneous eigenspaces of the V_o are exactly E1,E2,E3,E4 and
R_E=I-sum E_i. D0 preserves these spaces. Thus P is contained in one of
them; S is proportional to Z_i on the E_i alternative or to I on R_E.

Apply this to P=R_Q. Its rank>=4 excludes the rank-two alternatives,
so R_Q<=R_E and S is scalar. Orthogonality S_iS_j=0 now gives E_i<=Q_i.
Together with the interface ranks this yields

    Q1=E1 or S1,    Q2=E2 or S2,    Q3=E3, Q4=E4.     (8.2)

It also identifies each passive output factor with the corresponding
physical qubit. The argument retains arbitrary auxiliary multiplicities;
it does not assume a product physical cut at L.

### 9. Rank-two branches cannot lie in a weak loop

This is the decisive general lemma.

**Lemma.** If an actual reachable native M2 branch b has rank(P_b)=2,
then it belongs to no recurrent SCC.

**Proof.** Suppose first that its SCC L is green. Let c be another branch
of L at a different native vertex. Necessarily d_c>=2: a scalar branch
has no outgoing green or incoming red choice dependence and cannot be
recurrent. Same-layer markers imply [P_b,P_c]=0 and

    G_(b,c)(a,I_c)=P_c beta_b(a),
    G_(b,c)(I_b,x)=P_b beta_c(x).                      (9.1)

Apply (3.1) to the entire two native vertices, keeping every sibling.
Restrict its coefficient afterward to the b,c summands:

    G_(b,c)(a,x)=beta_b(a)beta_c(x)K
                 +beta_c(x)beta_b(a)(I-K).

Here K commutes with both full origin algebras. Combining with (9.1),

    [beta_b(a),P_c]K=0,
    `[beta_c(x),P_b](I-K)=0.                           (9.2)`

On the rank-two carrier P_b, beta_b is irreducible. Therefore KP_b is
either P_b or0; no unique orientation is assumed.

If KP_b=P_b, the first commutator of (9.2) is supported on P_b, since
[P_b,P_c]=0. Multiplication by K leaves it unchanged, so it vanishes.
Irreducibility gives P_bP_c=0 orP_b.

If KP_b=0, the second commutator is entirely supported on I-K because
K commutes with beta_c. It vanishes, so P_b reduces beta_c(M_(d_c)).
The supported restriction has unit P_bP_c; its nonzero rank is a positive
multiple of d_c>=2. Since rank P_b=2, that unit again is0 orP_b.

For c at the same vertex, P_bP_c=0 by native direct-sum orthogonality.
Thus every L status is either always absent or always present whenever b
occurs: the alternatives follow from same-SCC faithfulness applied to
P_bP_c or P_b(I-P_c).

Changing b's forward output choice cannot change its own occurrence.
If b were inactive, the dormant coordinate would be unused, so univocality
would leave the whole section unchanged. Whenever any change occurs, b
is active on both sides. Every other same-layer status is then constant,
so b has no internal outgoing green edge. This contradicts recurrence.

For a red SCC use the past-marker versions of (9.1). The roles of K and
I-K swap, giving the identical extremal joint-unit conclusion. Changing
b's reverse input choice can then alter no other L status, so there is
no internal incoming red arrow c->b. This again contradicts recurrence.
The proof covers every possible recurrent weak-loop color. QED.

### 10. A legal input record gives the contradiction

Original3 has precisely an active M2 branch a3 with unit E3 of rank2 and
a passive M2 branch p3 in the red core L. By Section9, a3 is acyclic.
Section7 makes it a strict predecessor of L.

Gather all physical inputs of original vertex3 at a new native vertex A.
For each original full input tuple h introduce A_h with that input tuple
and one bundled output sector h of the same quantum dimension d_h. Put
the tensor identity in A_h. The original vertex retains its whole native
matrix algebra, including coherence between its input tuples. Every old
section extends uniquely, and both full choice maps are merely relabelled:
the new A_h have one input tuple and one output tuple, so no new choices.

We verify weak loops rather than assume it. If changing a forward choice
c changes the fine event 'input h at branch b', either b's status changes,
giving green c->b, or b stays fixed and an incoming wire index changes.
If the old source branch stays fixed this gives solid c->b. If its source
a changes, there is green c->a. A separate reverse-choice change of b's
input tuple keeps b active; it either removes a, giving red a->b, or keeps
a with two wire values, giving solid a->b. Thus in every case the forward
dependency lies strictly before b's red or acyclic SCC. A reverse change
either gives red b->c or is b's own input coordinate, so its target is in
that SCC or later.

At p3 the two native input tuples are scalar: a recurrent red M2 branch
has a nontrivial reverse-choice domain, hence at least two tuples. At the
acyclic a3, a quantum tuple is allowed. Any new incoming solid arrow
a->A_h was already a solid a->a3; it is strictly earlier. The new outgoing
solid A_h->a3 is likewise strictly forward. All record branches can be
placed immediately before their corresponding old SCC. None creates a
cycle, even though the same new vertex has branches at different levels.

Also record the passive-1 status, using fixed bidirectional scalar flag
wires. On an active3 tuple, global active exclusivity makes that status
always true, so there is no extra dependence. On a passive3 tuple, both
events have forward dependencies strictly before L and reverse dependencies
in L or later. Their conjunction retains those bounds. This is one actual
joint record, not a presumed compatibility of two abstract phase slots.

At identity record fillers the full tensor is unchanged. Its branch-unit
projections are orthogonal, also when an A_h block is M2 rather than C.
The coarse passive-1 unit I-Q1 must therefore commute with every marked
passive3 input-tuple projection D_(3,t).

Write the original passive insertion as u_3(U)=u_30 pi_3(U), where pi_3
is an M2 *-isomorphism on native input coordinates. If e_t is a native
scalar input-tuple vector, p=pi_3^-1(|e_t><e_t|) is an arbitrary rank-one
physical-qubit projector. The exact passive coefficient gives

    D_(3,t)=alpha_3(p)(I-E3)=p_3(I-E3).

Since Q1E3=0 and E3 commutes with p_3, the joint record forces

    [Q1,p_3]=0.                                      (10.1)

This is impossible for both alternatives (8.2). For Pauli indices a,b,
let G_ab=Tr([Q1,sigma_a^(3)]†[Q1,sigma_b^(3)]). Direct rational calculation
from the displayed vectors gives

    G(E1)=4 I3,
    G(S1)=[[32/9,0,-8/9],[0,16/3,0],[-8/9,0,32/9]].

For p=(I+n.sigma)/2 with real |n|=1,
||[Q1,p_3]||²=(n^T G n)/4. The minimum eigenvalues of these Grams are4
and8/3, respectively. The squared norm is at least1 or2/3, contradicting
(10.1). This completes the stated no-host proof. The complete shortest chain
has independently passed the source-level review included with this manuscript.

### 11. Reproducibility and limits of the claim

The dependency manifest identifies the exact proof and certificate for
each finite step and its file hash. Matrix calculations use exact rational
or Gaussian-rational arithmetic. Finite unitary samples appear only in
positive/negative calibrations of general identities; they do not replace
the complete-unitarity or graph arguments. The native-interface result is
a finite exhaustive necessary-condition elimination, with the continuous
comparison relaxed rather than discretized.

The proof specifically allows arbitrary fixed entangling auxiliaries and
arbitrary native representation multiplicities. The rank-two lemma concerns
one actual M2 branch of multiplicity one, which the exhaustive original3
classification forces. It does not promote hidden multiplicity spaces or
assert every auxiliary is classical. No unrestricted additional memory gate,
ordinary DAG causality premise, product-domain cut, or repeated oracle use
is introduced.

No assertion is made here about formulations allowing a different external
boundary, approximate equality, original queries distributed over several
native vertices, non-monopartite insertions, or extra calls. Those are
different realization questions and require separate statements.
