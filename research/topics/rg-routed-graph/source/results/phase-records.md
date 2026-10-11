# Phase records

[Topic index](../../README.md) · [Shared result index](../../../../RESULTS.md#rg--exact-native-routed-graph-universality)

Each result below has one owner. Exact scope and proof are updated here. Source-level mathematical arguments and finite certificates are distinguished from a new formal verification.

<a id="rg-040"></a>

## RG-040 — Separated and branched-recipient flag refinement

**Statement.** An actual separated flag rewrite preserves bi-univocality, weak loops and complete equality under full-choice independence, including branched recipients.

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### 1. Statement and graph hypotheses

Let a finite branched routed graph be bi-univocal and satisfy weak loops.
Work after global reachable reduction. Let A be a native vertex with one
reachable branch, of practical matrix dimension d. Its branch status is
constant, so it lies in a singleton branch SCC: no green edge enters it and
no red edge leaves it, while every directed cycle must be monochromatic
and dashed.

Choose one topological ordering of the branch SCCs. Let J be any other
native vertex. Partition its branches into B_- before A and B_+ after A in
that ordering. They cannot share A's singleton SCC. Incomparable components
are placed by the chosen ordering; no physical time order of SCC fragments
is assumed.

There is a valid routed graph on the SAME external boundary and the SAME
native vertices, obtained by adding a two-wire binary scalar flag loop
between J and A and replacing A's one M_d branch by two M_d branches.
Every old native branch at J and elsewhere retains exactly its old full
matrix freedom. The diagonal insertion a -> a⊕a at A recovers the old
coefficient tensor exactly. The new two branch fillers are independently
arbitrary, with complete private-ancilla validity.

The construction extends simultaneously to any finite collection J_1,...,J_k
of distinct other vertices, using a k-bit flag pattern and 2^k copies of A's branch.
Unreachable pattern branches may afterward be removed by the established
global reachable reduction.

This is conditional on a genuine single-branch separator A and actual
before/after branch sums. It is not a rewrite for an arbitrary commuting
projection or an arbitrary scalar flag known only from a tensor formula.

### 2. The local route construction

Write A's old rectangular branch as I_A -> O_A, where I_A and O_A are
sets of complete correlated index tuples. They need not be Cartesian
products of wire-index sets. Define t(b)=1 for b in B_- and0 for b in B_+.

Add wires J->A and A->J, each with two one-dimensional sectors labeled0,1.
For every old branch b at J, replace its rectangle I_b -> O_b by

    I_b × {t(b)} -> O_b × {t(b)}.

The added factors denote its incoming and outgoing flag-wire labels. They
are one-dimensional, so both practical branch spaces keep their old
dimensions. Distinct old branch domains and ranges remain disjoint.

Replace A by branches A_0,A_1 with rectangles

    I_A × {t} -> O_A × {t},  t=0,1.

Each retains dimension d and full U(d) freedom. The two rectangles have
disjoint domains and ranges. If a flag-direction wire already exists, the
new flag may be bundled with it by a product sector index; the proof below
is unchanged.

This creates the actual record wires. It does not presume the event was
already available on an edge. The physical two-cycle consists of explicit
scalar-sector wires with matching local branch constraints.

A consistent old section selects exactly one J branch b. It has exactly
one extension to the new graph, with both new flag wires equal t(b) and A_t
selected. Conversely forgetting the flags and the subscript of A_t turns
every new consistent section into an old one. Thus the section sets are in
bijection. The same statement holds componentwise for multiple flags.

### 3. Selector independence in BOTH complete choice domains

Let Phi be the old complete forward-choice function and Psi the old
complete reverse-choice function. These are functions on the full products
of branch choice coordinates, including all dormant/unused coordinates.

Let g be the status of the event 'J lies in B_-'. In forward choices,

    g=sum_(b in B_-) status_b.

No status_b in this sum depends on A's old output-choice coordinate:
otherwise there would be a green edge A->b, contrary to b preceding A.
Therefore g depends only on the OTHER forward choices.

In reverse choices use instead

    g=1−sum_(b in B_+) status_b.

No status_b in this sum depends on A's old input-choice coordinate:
otherwise there would be a red edge b->A, contrary to b following A.
Therefore g depends only on the OTHER reverse choices as well.

The complement identity uses the fact that exactly one J branch occurs in
each section. Neither forward independence alone nor an informal claim
that a classical event is 'known before A' would suffice.

### 4. Exact bi-univocality with dormant new choices

A new forward choice consists of two independently specified A output
coordinates o_0,o_1 and all old non-A coordinates w. The selector is already
determined as g(w), independent of any old A coordinate. Define its section
by

    Phi_new(o_0,o_1,w)=lift(Phi(o_(g(w)),w)).

The old section still has selector g(w), so it satisfies both flag-wire
constraints and the selected A branch's output choice. The other A choice
is dormant. Every compatible new section must reduce to this old section,
proving existence AND uniqueness for every complete new forward tuple.

Similarly, for independent input coordinates i_0,i_1 and reverse choices v,

    Psi_new(i_0,i_1,v)=lift(Psi(i_(g(v)),v)).

The reverse selector independence proves totality and uniqueness separately.
All non-A branch choice domains correspond bijectively to their old domains;
adding a fixed flag to each local branch adds no extra choice there.

For k flags, replace the two choices by independently supplied coordinates
(o_s) and (i_s) for every s in {0,1}^k and select s=g(w) or g(v). Each
component of g is independent of the old A coordinate. Thus this argument
retains ALL dormant copies, not only the branch that happens to occur.

### 5. Functional-dependence lemma for the new dashed edges

Place all new A-pattern branches at A's old singleton level. Every other
branch retains its old SCC level. We prove that new dependency edges either
inherit an old edge of the same color, or run strictly forward across this
singleton level. Hence no new SCC can cross that level.

#### Forward/green case

Changing only a new output coordinate at A_s leaves the selector fixed. If
s is dormant, nothing changes. Otherwise the old section changes only its
A output choice. Thus a changed old status b gives an old green edge A->b,
so b is strictly after A. No other A-pattern status changes.

Now change a non-A output choice v. If g is unchanged, the selected A
coordinate is unchanged, and any changed old status b gives an old green
edge v->b.

If g changes, at least one before-event changes. Holding ANY fixed old A
choice gives two valid old complete choices, so some before-J status changes
and an old green edge v->j_- exists. Consequently v is strictly before A.
For an old target b, compare the effective old choices in two steps:

    change v while holding the old A choice fixed;
    then change the old A choice to the newly selected coordinate.

A net change of b must occur in at least one step. It therefore gives either
an old v->b edge or an old A->b edge. In the second case b is after A, so
the new edge v->b crosses strictly from before A to after A. A changed
A-pattern status only gives v->A_s, again from strictly before A.

The intermediate old choice is legitimate even if its A coordinate would
be dormant in the new graph. The proof is explicitly about the full old
choice product; it does not condition away unused coordinates.

#### Reverse/red case

Changing only the new input choice at A_s either is dormant or changes only
A's old reverse input. A changed old status b gives an old red edge b->A,
so b is strictly before A. The new edge is b->A_s.

Change a non-A reverse input choice v. If the selector stays fixed, changed
old status b gives an old red edge b->v. If the selector changes, its
complementary AFTER-event changes; an old edge j_+->v exists, so v is
strictly after A. Splitting the effective old choice change into a v change
and an A change shows that a changed b gives either old b->v or old b->A.
The latter has b before A and yields a new before-to-after edge b->v. A
changed A-pattern status gives A_s->v, also towards strictly after A.

These arguments work for several flags: if their vector changes, choose
one changing component to locate v before A in the forward case or after A
in the reverse case. No new dashed edge connects two A-pattern branches.

### 6. Solid edges and weak loops

For every old physical wire, the sections co-occurring at a new endpoint
pair are either unchanged or a subset of the sections at its old endpoint
pair. An old unique one-dimensional conditional wire sector therefore
cannot become a non-unique or higher-dimensional one. New solid edges on
old wires can only restrict/duplicate pre-existing solid edges.

Each added flag wire has a unique one-dimensional index whenever its two
endpoint branches co-occur: J_b fixes t(b), and A_s fixes its flag pattern.
It creates no solid branch edge. The same argument applies when bundling a
flag with an existing wire.

Thus every newly exposed edge between distinct old SCC levels respects the
old condensation order, including all selector-induced edges from Section5.
Within an old non-A SCC, new edges are only inherited edges of its old
color. The A-pattern nodes have no edges among themselves and no route
back across their singleton level. Old SCCs may split; distinct old SCCs
cannot merge. Every remaining directed cycle is therefore contained in an
old monochromatic dashed SCC. Weak loops are preserved.

This establishes the actual routed certificate, not only unitarity of the
intended new tensor. In particular it does not use the false rule that
serial quantum subdivision always preserves weak loops.

### 7. Exact marked contraction and complete equality

Expand the old skeletal contraction into native J branch summands. In the
new contraction the two new one-dimensional flag loops contribute1 for
the unique matching flag and0 otherwise. Hence

    G_new((a_t),B,others)=sum_b G_b(a_(t(b)), B_b, others).

There is no extra trace dimension, no measurement of the branch label, and
no discarded interference between summands. Diagonal a_t=a gives the old
coefficient tensor exactly. The primary routed-superunitary theorem gives
independent complete freedom at every new native branch and preserves the
original query embeddings branchwise via the canonical one-dimensional
flag factors.

For a quartet auxiliary whose actual marked J event has coefficient F(U)P,
the normalized new direct-sum representation at fixed U has central branch
projections P and I−P. Indeed the sum of the new branch identities on either
flag value is literally the corresponding old marked native contraction.
Its diagonal restriction is the old G. Multiplicativity of that normalized
representation gives the stronger identity

    G_new(a0⊕a1,U)=G(a0,U)(I−P)+G(a1,U)P,

with flag1 chosen for the marked event. Relabeling the two flags gives the
other conventional ordering. This proves the exact desired refinement,
rather than merely inferring it from forward-choice independence.

### 8. Simultaneous flags and a new structural exclusion

Apply the graph rewrite simultaneously to every selected original vertex
that straddles the SAME unbranched auxiliary. A small actual active event
may be the before sum or its complement; relabel its flag so value1 means
the active event. Both independence proofs survive this relabeling.

At the quartet baseline these marked events have input projections
P_j<=S_j. Let Q_s be the origin central projection of the single new native
A-pattern branch s. The direct-sum representation gives orthogonal Q_s
summing to I. Exact marked contractions give

    sum_(s:s_j=1) Q_s=P_j.

Therefore, by multiplication in this ONE direct-sum representation,

    Q_s=product_(j:s_j=1) P_j
        product_(j:s_j=0) (I−P_j).                    (4)

This establishes the joint-pattern formula from the actual graph and its
native representation. It is not inferred merely from individual marker
commutation with G or from separately valid flag interfaces.

The quartet carriers S_j are mutually orthogonal. Every pattern with two
active values therefore has Q_s=0 at baseline. But this pattern is now the
central identity of ONE native refined branch. Reachable native faithfulness
(and constant rank as all other native unitary fillers vary on the same boundary) implies
that this branch is globally unreachable. The section bijection then proves
that the corresponding selected original branch events NEVER co-occur in
any old graph section either.

After reachable reduction, at most the all-zero pattern and the single-
active patterns survive. On the quartet tensor the refined coefficients are
exactly

    sum_j G(a_j,U)P_j + G(a_0,U)(I−sum_j P_j).

This is the special situation where a baseline zero DOES imply structural
non-cooccurrence: the zero has become one actual central native branch
projection through a separately proved graph rewrite. The earlier DAG
counterexample does not meet these before/after-selector hypotheses and
remains valid.

### 9. Nontrivial cyclic calibration

[branch_flag_loop_cyclic_calibration.py](../branch_flag_loop_cyclic_calibration.py) gives every native rectangular
route and all full choice domains for a concrete test. A genuine Lugano
feedback component has three laboratory vertices with two M2 branches each
and scalar hub branches indexed by o. Its output bit g=o1 controls whether
a further native query B occurs before or after the single M2 auxiliary A.
Scalar encoder/decoder branches preserve the full coherent data qubit; a
full M16 future decoder may mix all record sectors.

Unlike a purely DAG switch test, g depends on choices in a recurrent green
SCC. A itself has a two-valued forward output coordinate AND a two-valued
reverse input coordinate. The refinement duplicates both, including the
dormant copies.

Exact exhaustive results:

-64 consistent sections before and after, with a forgetting bijection
-2048 old and4096 new complete forward choices, all uniquely solvable
-128 old and256 new complete reverse choices, all uniquely solvable
-28 old and29 new native branches, all dimensions balanced
-92/100 green edges,32/34 red edges, and2/2 solid edges
-The same nontrivial three-branch green SCC survives; no mixed-color or
 solid cycle appears

The checker also contracts exact nontrivial rational native fillers, with a
future decoder mixing record sectors. It verifies unitarity and the exact
marked refinement formula, with the selector's input projection of rank8.
The literal time-reversed calibration is also checked: forward/reverse
counts exchange, and the same nontrivial SCC is wholly red before and after
the rewrite. The calibration labels g=0 as the before event, the harmless
opposite convention from the theorem’s flag1. These are valid cyclic hosts
of their own, not quartet hosts.

### Scope

The theorem supplies a genuine routed realization of the previously derived
commuting-event refinement WHEN the event is an actual before/after branch
sum relative to one unbranched separator. It does not expose arbitrary
laboratory-input flags, refine arbitrary repeated multiplicities, remove
auxiliary vertices, or construct the retained quartet. Proper-support and
branched auxiliary residuals remain the next open cases.

### 10. Quartet normal form for previously unbranched auxiliaries

Combine the rewrite with the audited strict-oriented full-matrix theorem
and graph-centrality. At a fixed quartet baseline, every genuinely interior
unbranched quantum auxiliary has at least one nontrivial before/after
original-query event. M8 and M16 auxiliaries cannot have one and are already
boundary multiplication; M1 is a scalar phase. The remaining sizes are M2
and M4.

For one M2 separator, apply all its nontrivial original-query comparison
flags simultaneously. There are at most four. For M4, nontrivial flags are
possible only on S1,S2, so there are at most two. Relabel every flag so value1
is the small active event P_j<=S_j. Formula(4) and global faithfulness leave
EXACTLY the all-zero branch and one branch for each selected event:

- Each P_j is nonzero, so its single-active pattern is reachable
- Their sum has rank at most12, so the all-zero projection has rank at least4
  and is also reachable
- All patterns with two active flags are globally unreachable

The new actual native algebra therefore has at most five M2 summands or
at most three M4 summands, respectively. Its repeated residual block is not
removed or resolved into a smaller native matrix algebra.

This may be iterated over the finitely many originally unbranched interior
quantum auxiliaries. Each step keeps every other old native branch and its
full freedom. In particular a different one-branch auxiliary remains a
constant-status singleton and the theorem applies to it afterward. Setting
all copies of each refined filler to the old baseline recovers the original
quartet tensor at every stage. The relevant definition of 'interior' is its
coefficient map with all OTHER auxiliaries fixed at that baseline; the map
of an as-yet-unrefined vertex is unchanged there.

Consequently existence of a quartet host implies existence of an equivalent
valid host in which every genuinely interior quantum auxiliary is branched.
The newly introduced branches at a refined M2/M4 vertex have the bounded
form just stated; originally branched auxiliary vertices remain arbitrary.
Unbranched boundary-only vertices may remain in the graph and can still be
structurally important. This is not a deletion or absorption theorem.

The refinement does not bound the number of auxiliary vertices, classify
proper-support repeated blocks, or imply a quartet host exists. It makes
the remaining branched-auxiliary/repeated-complement problem an actual
routed normal-form problem rather than only an algebraic tensor proposal.

### Branched-recipient extension with dormant choices

### 1. Hypothesis and construction

Let A have any finite set C of native branches, with possibly different
practical matrix dimensions. Choose a topological ordering of the old
branch SCCs. For a distinct vertex J, assume EVERY J branch is either
strictly before EVERY A branch, or strictly after EVERY A branch. Let these
two sets be B_- and B_+. In particular no J branch lies within A's full span
or shares an SCC with an A branch. Both sets may be nonempty.

Use exactly the two scalar flag wires J->A and A->J from the unbranched
construction. The J branch b emits and accepts the fixed flag t(b). Split
EACH old A branch c into (c,0) and(c,1), with the same old rectangle and a
fixed matching flag on both sides. Its practical dimension stays d_c.
Thus the actual native algebra changes from

    A_A=direct_sum_c M_(d_c)

to two independently fillable copies of A_A. This does not split a hidden
representation multiplicity. The old branches themselves are duplicated
using new routed sector labels, and every old filler is recovered by the
diagonal embedding.

The hypotheses can hold with A branches inside a genuinely recurrent SCC,
as the calibration in Section6 demonstrates.

### 2. Bi-univocality uses the ENTIRE old branch-choice vector

In forward choices the before-event g is independent of every output-choice
coordinate of every old A branch: a dependence would give a forbidden
backwards edge A_c->J_b with J_b before all A. In reverse choices use the
complementary after-event; a dependence on any A_c input coordinate would
give J_b->A_c with J_b after all A. Componentwise invariance on the full
Cartesian choice product implies invariance under changing the entire
A choice vector.

The new complete forward input supplies o_(c,0),o_(c,1) for EVERY c, including
all dormant coordinates. First compute g from the non-A choices. Then use

    old output-choice vector (o_(c,g))_(c in C)

in the old forward choice function. Lift its resulting old section by the
unique consistent flag. The resulting selected old A branch c may itself
depend on these choices; that causes no problem because the whole vector,
not only a presumed active coordinate, was supplied. Section-forgetting
and old uniqueness prove new existence and uniqueness. The reverse proof
uses the whole vector (i_(c,g)) in exactly the same way.

The proof works for multiple distinct J vertices satisfying the same strict
outside-span hypothesis. Their selector vector is independent of every old
A coordinate, and each entire old choice vector is selected by that pattern.

### 3. Dashed-edge proof without constant recipient status

Changing a copied A_c coordinate while the selector is fixed reproduces a
change of the single old A_c coordinate. A change of another A_d status is
allowed here: it yields an inherited edge between copies of c and d with
the same flag. No argument assumes the statuses at A are constant.

If a non-A FORWARD choice v changes the selector, a before-J status changes,
so v is strictly before EVERY A branch. Compare the two effective old choices
by first changing v and then changing the coordinates of the old A vector
ONE AT A TIME. A changed old target b therefore gives either an inherited
v->b edge or an inherited A_c->b edge for some c. In the latter case the new
v->b edge is strict in the old SCC order, because

    v < every A branch, and SCC(A_c) <= SCC(b).

A change of the copied flag on an A_d status gives v->A_(d,g), again strict.

There is a useful precision here: b need not lie after ALL A branches. It
may lie inside A's span, after or in the SCC of the particular influencing
A_c. Strict old-order progress from v is all that is required.

The REVERSE argument is dual. If changing non-A input choice v changes the
selector, an after-J status changes, so v is after EVERY A branch. Telescoping
the old A input coordinates gives an inherited b->v edge or b->A_c for some
c. The latter yields a new strict-order b->v edge, since

    SCC(b) <= SCC(A_c), and every A branch < v.

Copied A_d flag changes give A_(d,g)->v. Again the source can lie inside A's
span; it need not lie before every A branch.

When the selector stays fixed, all dependencies are inherited directly.
For several flags, choose any changing component to locate v outside the
entire A span. Dormant coordinates remain present throughout every
intermediate old choice vector.

### 4. Weak loops, complete tensors, and capacities

Section-forgetting is a bijection. Old physical-wire conditional value sets
at copied endpoints are restrictions of their former sets. Added flag
wires have one fixed dimension-one label at each co-occurring endpoint pair.
Thus no new solid edge can appear unless it is a copy/restriction of an old
solid edge.

Every new dashed edge not inherited from the old graph strictly advances
its SCC order by Section3. Therefore a new SCC can only project inside one
old SCC. Copies of A branches can rejoin via unchanged nodes within that old
SCC, but all inherited internal edges have the same old dashed color and
there are no internal solids. The old monochromatic weak-loop condition is
preserved. There is no need for A to have a singleton SCC.

The local balanced rectangles and exact section bijection give the same
marked-contraction identity as before, preserving coherent sums and all
full native freedoms. At a fixed original-query context the normalized
new one-port representation is a representation of

    direct_sum_(c,pattern) M_(d_c).

The flag-pattern identities are actual CENTRAL elements of this ONE native
algebra. Their marked marginal contractions are the actual J events. This
proves complete commutation and the direct-sum coefficient refinement,
without inferring it by amplifying a scalar-only identity.

For a quartet baseline with small selected P_j<=S_j, the joint pattern
projection equals the product of its marginals, as in the unbranched theorem.
Two active events give zero, so global native faithfulness forces the
corresponding copied branches to be unreachable. This is structural old-
section non-cooccurrence via the forgetting bijection.

There is also a branchwise capacity statement. In a surviving flag pattern
s, each reachable copied A branch(c,s) has represented rank m_(c,s)d_c with
positive integer m_(c,s). Thus

    sum_(c reachable in pattern s) d_c <= rank(P_s).

In a single-active quartet pattern the right side is at most four. An old
A branch of dimension greater than four therefore cannot co-occur with any
selected active event. Branch dimensions greater than two are similarly
excluded from a selected rank-two event. No finer split of a rank-four
representation multiplicity is inferred.

### 5. Exact cross-carrier geometry and whole-query gap exclusion

[cross_serial_cylinder_independent_audit.py](../cross_serial_cylinder_independent_audit.py) independently reconstructs all
four S_j from their explicit proved carrier vectors. For every i!=j it checks

    S_j E_i=0,  R_i S_j R_i=S_j,

and computes the physical partial trace

    K_(i,j)=Tr_i(I−S_j).

All eight leading principal minors of every K_(i,j) are positive rationals.
The determinants agree with the author's twelve certificates. Hence K is
positive definite, not merely of numerically estimated full rank.

Suppose a nonzero projection P<=S_j commuted with alpha_i(M2). Conjugation
by R_i fixes P, so it commutes with the physical i-th matrix factor and must
be I_i tensor p. Inclusion in S_j would imply

    0=Tr[(I−S_j)P]=Tr[K_(i,j) p],

contradicting positive definiteness and p!=0. Thus NO nonzero projection in
S_j commutes with the different original factor alpha_i.

Now let A be the entire ACTUAL native vertex of original query i. Suppose
all its branches lie strictly inside a gap of original query j's branch
SCCs: every j branch is before all i branches or after all i branches,
with nonempty sets on both sides. The branched flag-loop theorem applies.
Its nontrivial central flag event commutes with the entire native image at
i, hence with alpha_i. Reachable faithfulness and the original j native
classification make that event or its complement a nonzero P<=S_j. The
preceding exact geometry contradicts this.

Consequently no whole original-query vertex can occupy such a strict gap
between branches of another original query. At j=3,4 the actual native
vertex has exactly two branches; strict nesting of another whole query
span between those two branch SCCs is therefore impossible. Shared SCCs,
SCC-internal orders, and interleaved branch spans are expressly outside the
hypothesis and remain possible.

<a id="rg-041"></a>

## RG-041 — Same-SCC flag refinement

**Statement.** Same-SCC flag refinement

**Status:** source-level result. **Scope:** Requires explicit one-sided coarse-event independence; arbitrary hidden labels cannot be exposed.

### 1. Green-SCC statement

Let a valid routed host have a green branch SCC L. Let A and J be distinct
native vertices, with EVERY branch of A lying in L. Let B be any selected
set of J branches lying in L, not necessarily all branches of J. In each
complete forward or reverse section put

    g=sum_(b in B) status_b.

Because exactly one J branch occurs, g is a bit. Assume g is independent
of every old A output-choice coordinate on the FULL complete forward-choice
product. Then adding the two scalar flag wires J->A and A->J and copying
each A branch according to g preserves native dimensions, bi-univocality,
weak loops, and the exact diagonally restricted tensor.

A sufficient graph-only hypothesis is the stated one:

    no green edge A_c -> J_b for any A branch c and selected b in B.

It makes each selected status independent, hence makes their sum independent.
The sum condition is strictly weaker: individual statuses may change while
the selected total remains fixed. The positive calibration below uses this
more general possibility.

The RED dual assumes every A branch and every selected J branch lies in one
red SCC, and g is independent of every A reverse-input choice. Absence of
all red edges J_b -> A_c is sufficient. Its forward independence is automatic.

### 2. The opposite choice direction is automatic

Inside a green SCC there is no red edge, since each internal edge belongs
to a directed cycle and weak loops permits only the one dashed color. Thus
no selected J_b status depends on any A_c REVERSE input choice. Their sum g
is independent of the whole A input-choice vector. The assumed forward
independence similarly gives invariance under the whole output vector.

Unselected J branches may lie anywhere. No assertion about their separate
statuses is used, and no complement is silently required to lie outside L.
The selected set B itself is what supplies the support localization below.

In the red case there is no internal green edge, giving automatic forward
independence; the reverse independence is the stated hypothesis.

### 3. Exact choice functions, including dormant branches

The local route modification is exactly the branched-recipient construction:
every old J branch receives and returns a fixed bit,1 on B and0 elsewhere;
every A branch c becomes two branches (c,0),(c,1) with its old rectangle and
that fixed bit at both ends. All added sectors are one-dimensional.

The section-forgetting map is a bijection. For new forward choices, determine
g from the non-A choices and feed the ENTIRE selected old vector
(o_(c,g))_c into the old choice function. The active A branch can change;
no constant-status assumption is made. All dormant old coordinates are
still supplied. Do the same with the input vector for reverse choices.
The two independence facts prove unique compatible sections in both
directions exactly as in the branched-gap proof.

### 4. Every new edge is safe

Write SCC inequalities in the old condensation order.

#### Green SCC

If changing a non-A FORWARD coordinate v changes g, some selected J_b
status changes, giving an old green v->J_b edge. Therefore SCC(v)<=L.
When the effective old A output vector switches, change its coordinates
one at a time. A changed old target t gives either an inherited v->t edge
or an old green A_c->t for some c, so SCC(t)>=L. In the latter case the
new v->t edge is strict in the old SCC order unless both endpoints lie in
L, in which case its color is green. A copied A status changing only through
g gives a green v->A_(c,g) edge with the same safe localization.

If changing a non-A REVERSE input coordinate v changes g, an old red
J_b->v edge exists. Since J_b lies in green L and no red edge is internal,
SCC(v)>L strictly. Telescoping the old A input coordinates gives inherited
red t->v or old red t->A_c. The latter has SCC(t)<L strictly, so any newly
exposed t->v edge advances strictly across L. A copied A flag-status change
gives red A_(c,g)->v, also strict. No new red edge lies inside L.

Changes of a copied A coordinate with fixed selector reproduce a single
old A_c coordinate change. Dependencies can be inherited between different
A branch copies; they retain their old colors. The proof never assumes a
fixed active A branch.

#### Red SCC

Exchange forward/green with reverse/red and reverse all dependency
orientations. A forward selector-changing source v is strictly before L,
and any target influenced through A is strictly after L. A reverse
selector-changing target v has SCC(v)>=L, while statuses changed through
an A input have SCC(t)<=L. Equality is possible only for new RED edges
inside L. No new green internal edge appears.

#### Solid edges and SCCs

Old-wire conditional sector sets at copied endpoints are restrictions of
the old sets. Added flag wires have one fixed dimension-one label at every
co-occurring endpoint pair. Hence no new solid edge can occur except an
inherited one. The only new edges that can stay within an old SCC have its
permitted color. Other genuinely new edges strictly advance the old SCC
order. SCCs cannot merge across old levels, although copies can rejoin
inside L. Weak loops therefore remains valid.

### 5. Exact marker and complete interpretation

The added flag contraction is1 on its unique matching branch pattern and0
otherwise. Thus the new tensor is the coherent sum of old J branch
coefficients with the appropriate independently chosen A copy. Diagonal
restriction recovers the old tensor, with no measurement or dimension
factor.

At a fixed normalized baseline, the new direct-sum native representation
makes the copy flag a central projection commuting with the diagonal old
A algebra. Its coefficient is exactly the old selected-J marked
contraction. This remains true with arbitrary independent private wires,
by the actual new routed graph. In particular a scalar-only polynomial
commutation identity is not being amplified by assumption.

The same proof works for several selected events in the SAME monochromatic
SCC, provided each event has the required one-sided independence. Their
pattern vertex is one actual native direct-sum representation. The fixed-
vertex multiplicity potential decreases on every genuine split just as for
gap refinements, so the termination lemma extends to these additional
admissible steps.

### 6. Quartet direct-influence and transition consequences

Assume every branch of original query i lies in one green SCC L. Let b be
ANY branch of a different original query j that lies in L. If no A_i branch
has a direct green edge to b, apply the theorem with selected set {b}.
The resulting native-central event commutes with alpha_i(M2).

The actual j native algebra is its active ideal plus its one passive M2
branch. Every branch is reachable and the all-four-active theorem applies,
so the selected branch projection is proper and nonzero. Either it, or its
complement when b is passive, gives a nonzero P<=S_j. The independently
verified cross-carrier geometry forbids [P,alpha_i(M2)]=0. Therefore

    for each such b, some branch c of original i has a green edge c->b.

The source branch c may depend on b. This does not say EVERY i branch
influences every j branch.

For red L the exact dual is: each other original branch b in L has a red
edge b->c to SOME branch c of the whole original i. It is reverse input
influence from i to b, with the red edge oriented as stated.

The coarse-event version gives a stronger, precise form when BOTH original
i and j are whole inside L. Construct an undirected transition graph on
j's native branch labels: connect b,b' if two complete forward choices
differing in one i output coordinate make j switch between b and b'. A
union of transition components is exactly a selected event insensitive to
all those coordinates. The quartet geometry forbids every nonempty proper
such event, so this transition graph is connected. For red L, use reverse
i input-coordinate changes instead.

If j is only partially in green L, the same argument excludes any nonempty
proper transition component contained entirely among its L branches.
Moreover j must have at least one branch in the STRICT GRAPH FUTURE of L.
Otherwise no outside-j status could depend on an i output choice: a green
edge from i in L to such a branch would itself put that branch in the strict
future. The complementary event 'j is in L' would then be independent,
contradicting the same-SCC refinement and cross-carrier geometry. Incomparable
outside branches cannot substitute for a genuine future branch.

More precisely, every i-induced transition component containing an L branch
must reach a future-j branch, unless j is wholly in L and that component is
all of j. The red statement requires a strict GRAPH PAST branch and uses
reverse input transitions. These are intrinsic condensation-reachability
claims; no arbitrary ordering of incomparable SCCs is substituted.

Shared-SCC and interleaved configurations are not excluded wholesale. The
result supplies necessary direct influence and, when appropriate, connected
branch-transition behavior inside a surviving component.

### 7. Positive same-SCC coarse-event calibration

`branch_flag_loop_same_scc_calibration.py/_checks.json/.log` starts with the
controlled Lugano host using four input relabelings, whose three whole
laboratory vertices lie in one green SCC. A separate coherent control/data
vertex B supplies a bit c through the already proved gap refinement to
laboratory J=L1. Its four branches are labeled(x,c). Recipient A=L0 still
has its two old branches; all A branches and the two selected J branches
with c=0 are in the same green SCC.

The selected SUM event is c=0 and is independent of A's entire output-choice
vector. Individual selected J statuses still have green influences from A;
this calibrates the strictly weaker event-level theorem honestly.

Copying c from J to A inside the SCC gives:

-64 consistent sections before and after
-2048/8192 complete forward choices, including all dormant copied coordinates
-64/64 complete reverse choices
-An8-node green SCC becoming a10-node green SCC with no red or solid cycle
-All four recipient copies reachable, with their full M2 freedoms intact

The checker verifies projection of the entire selected old A choice vector
for every new forward tuple and the absence of internal red edges. Its
literal time reverse is the red-SCC calibration with exchanged choice
counts. The boundary dimension is128. This is a valid generic routed host,
not a quartet host; its independent coarse flag therefore does not conflict
with the quartet-specific cross-carrier obstruction.

### Scope

All recipient branches must lie in the selected monochromatic SCC. Every
selected J branch must lie there too, and the indicated one-sided event
independence must hold on the full choice domain. These conditions cannot
be inferred solely from a complete tensor, the absence of a quantum
commutator at one context, or a path-level sketch. The theorem supplies an
actual flag refinement under those conditions and leaves the remaining
shared-SCC/interleaved search open.

<a id="rg-042"></a>

## RG-042 — Finite flag-refinement saturation

**Statement.** Finite flag-refinement saturation

**Status:** source-level result. **Scope:** Integer multiplicity potential bounds effective splits for the fixed vertex set, not the number of auxiliary vertices.

### Statement

Fix any normalized complete process on a D-dimensional boundary realized
by a finite valid routed host with N native vertices. Fix the full native
filler baseline. Repeatedly apply an admissible separated flag-loop
refinement to an EXISTING recipient vertex whenever it genuinely splits
at least one reachable native branch. Remove globally unreachable copies
and retain the diagonal baseline at every refined vertex.

Every such sequence has at most

    P_initial = sum_v sum_(reachable b at v) (m_b−1)
              <= N(D−1)

genuine steps, where the origin represented rank of branch b is d_b m_b
and d_b is its full practical native matrix dimension. Thus the procedure
can be continued to a terminal valid host in which every admissible
before/after selector of J around A is already central in the represented
actual native algebra of A. Equivalently, that selector is a function of
A's existing native branch label in every global route section.

This is a finite, host-dependent normal form. It does not bound N across
all possible hosts or classify selectors whose vertices have interleaved
branches or shared SCCs.

### 1. Integer potential and its bound

At the common baseline, complete one-port normalization gives a unital
*-representation of every native algebra. Global reachable faithfulness
makes each reachable branch representation nonzero. A simple branch M_(d_b)
therefore has positive integer multiplicity m_b, and

    sum_b d_b m_b = D

at each native vertex. Since d_b>=1 and there is at least one reachable
branch at each vertex,

    0 <= sum_b(m_b−1) <= D−1.

Summing over the fixed N vertices proves the stated finite bound. No
assumption is made that the representations are multiplicity-free.

### 2. Exact change under a flag split

A separated flag refinement copies an old recipient branch b into branches
(b,s), all of the SAME practical dimension d_b. At the diagonal embedding,
the old branch unit is the sum of these mutually orthogonal new branch
units. Therefore

    d_b m_b = sum_s d_b m_(b,s),
    m_b = sum_s m_(b,s).

Discard multiplicity-zero copies, which are globally unreachable by the
faithfulness theorem. Let k_b>=1 be the number of remaining copies; k_b
cannot vanish because every old witnessing section lifts uniquely. Then

    (m_b−1)−sum_s(m_(b,s)−1)=k_b−1.

The total potential drop is exactly sum_b(k_b−1). A genuine split lowers it
by at least one.

Every other vertex retains its old native branches and full matrix
freedoms. With all new recipient copies at the diagonal old baseline, the
entire coefficient map of each such other vertex is unchanged. Hence all
its origin branch ranks and multiplicities are unchanged. Section-forgetting
also preserves reachability of every other old branch. The only contribution
to the potential change is therefore the stated recipient contribution.

### 3. Why zero-drop steps may be skipped

Suppose every old branch has exactly one reachable copied pattern. After
removing unreachable copies, the copied branch is canonically identified
with the old branch. Its additional input/output flag tuple is then fixed
by that branch label, so its complete forward and reverse choice domains
correspond bijectively to the old ones.

The section-forgetting bijection consequently identifies all old and new
branch-status functions. Green and red dependencies are identical after
relabeling. Old physical-wire conditional sectors are identical as well,
and each added flag wire has a unique dimension-one label at a co-occurring
endpoint pair. Thus no new solid edge appears and the effective branch
graph is unchanged.

Such a step does not change the effective native algebra or the possible
SCC-order separation hypotheses for subsequent refinements. It can be
skipped rather than used to generate an artificial infinite sequence of
additional scalar wires.

### 4. Terminal centrality and global record semantics

An admissible separated J selector gives, by the graph rewrite, a projection
P in the commutant of the origin represented native algebra pi_A(A_A).
The copied branch projections split each old unit pi_A(1_b) into its P and
I−P portions (or their multi-flag analogues).

If P were not CENTRAL in pi_A(A_A), it would be non-scalar on the multiplicity
space of at least one old simple block. Both its selected and complementary
portions in that block would then be nonzero, producing two reachable copies
and lowering the potential. Therefore, at a terminal host every admissible
P is central: it is a sum of old native branch units.

Conversely, when P is central, every old simple block has exactly one
nonzero flag copy. Consider the valid flag refinement hypothetically, even
if the zero-drop step is not performed. Every mismatched copy has zero
represented unit at baseline and is globally unreachable. The exact section
bijection then proves that the original selector value is determined by the
old A branch label in EVERY consistent section, not just at the fixed
quantum filler baseline.

This is the precise sense in which terminal selectors are already native
records. It is stronger than a fixed-context operator commutation but does
not assert an arbitrary record is present on a pre-existing physical edge.

### 5. Termination and preserved scope

If any admissible selector is not yet native-central, choose it and apply
the proven graph refinement. Every such step lowers a nonnegative integer.
After at most P_initial steps none remains. New admissible separations can
appear when old SCCs split; the same potential controls them. No uniform
choice of a topological ordering across the whole procedure is required.

The external boundary, full query tensors and independent ancillary
validity remain unchanged at each diagonal baseline. No original query is
split across vertices or called again. The procedure adds only scalar flag
wires and native branch copies at EXISTING vertices.

Introducing fresh M1 pivot vertices can itself increase the potential and
vertex count, so such additions are explicitly outside this termination
claim. They may be studied separately as cut-record constructions. Shared-
SCC and interleaved events, and the remaining repeated native blocks, are
not classified by this normal form.

<a id="rg-043"></a>

## RG-043 — Branch-condensation cut records

**Statement.** Branch-condensation cut records

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### 1. A scalar pivot does not change the tensor

Adjoin a disconnected one-branch M1 native vertex A with empty practical
input and output tuples. Both spaces have dimension one; its filler is a
scalar phase. It contributes that phase multiplicatively to the global
skeletal contraction. At filler1 the original tensor and external boundary
are exactly unchanged.

This vertex has no nontrivial forward or reverse choice coordinate, no wire
edge and no branch-graph loop. It can be placed at any selected cut in a
topological ordering of the old branch SCCs. This is a legitimate elementary
routed extension, not an enlarged quantum external boundary.

The framework permits this directly: Definition B.5 allows arbitrary finite
nodes and head/tail functions without requiring incidence at every node;
B.7 then permits the singleton route on its empty products. Definition B.12
makes its scalar filler a multiplicative tensor factor. No fallback source/
sink component is needed. [Primary definitions B.5, B.7 and B.12](https://arxiv.org/html/2206.10042v3).

### 2. The actual original-query event at a cut

Fix a quartet host and a cut between old branch SCCs. For each original
query vertex j that has branches on both sides, let b_j^pass be its unique
passive native branch. Select the sum e_j of active branches on the side
OPPOSITE b_j^pass. This is either the before-pivot sum or its complement,
with nonempty selected and complementary sets.

At the quartet baseline its represented projection satisfies

    0<P_j<=Q_j<=S_j.

The exact native marker is F(U)P_j. It is a sum of actual native branch
identities, not an arbitrary laboratory-input flag. Different selected j
have orthogonal P_j because the S_j are orthogonal.

Apply the simultaneous flag-loop rewrite between the scalar pivot and all
these original vertices. The pivot becomes a genuine routed scalar record
vertex, initially with one branch per binary pattern. Its pattern projections
are the products of the P_j and I−P_j inside its actual direct-sum native
representation. Every pattern with two selected active events is zero at
baseline and hence globally unreachable.

After reachable reduction its native algebra is C^(k+1): one all-zero branch
and one single-active branch for each of the k straddling original vertices.
Each single-active projection is P_j, and the all-zero projection is

    R=I−sum_j P_j.

All are nonzero; rank R>=4. The record's exact coefficient map is

    G_record((z_0,z_1,...,z_k),U)
       =F(U)[z_0 R+sum_j z_j P_j].

This is also independently complete when the scalar branches carry arbitrary
unitaries on the record's private ancillary system. Its routed availability
comes from the explicit flag-loop graph, not merely from this tensor formula.

### 3. A structural interval-overlap exclusion

Choose any one topological ordering of the branch SCCs. For a global route
section sigma and query j, let t_j(sigma) be the SCC position of its selected
branch, and p_j the SCC position of its passive branch. Define I_j(sigma)
as the set of cuts strictly separating those two positions. It is empty
when the selected branch is passive or shares its SCC with the passive
branch.

At a cut c, the selected small event e_j occurs in sigma exactly when
c lies in I_j(sigma): its selected active branch and passive anchor are on
opposite sides. The actual cut-record theorem forbids two such events from
co-occurring. Therefore

    I_i(sigma) intersect I_j(sigma) is empty for i!=j.

Thus the intervals are edge-disjoint along the chosen SCC ordering. They
may share an endpoint SCC; no order inside an SCC is asserted. The statement
holds for every global section and every chosen topological ordering, not
only for nonzero amplitudes at the original fixed auxiliary fillers.

This is a graph necessity genuinely stronger than a baseline zero mixed
coefficient. The zero became the represented identity of one actual native
record branch before reachable faithfulness was applied.

### 4. Scope and calibrations

The earlier routed DAG with orthogonal baseline A0/B1 flags remains a
counterexample to unrestricted baseline non-cooccurrence inference. Its
two selected branch/passive-anchor intervals occupy separate parts of the
DAG and need not overlap a common cut. The present argument does not combine
arbitrary events from different graph locations into one record.

The reversed Lugano example also remains intact. Branches in one recurrent
SCC are never separated by a condensation cut, so the construction does not
resolve SCC-internal records or collapse static query flags to an ordinary
circuit.

These cut records concern actual native original-query branch sums. They do
not establish joint accessibility of the four different seven-sector
laboratory-input record contexts, nor promote an arbitrary mathematical
multiplicity to native flags. New pivot vertices increase the vertex count,
so their addition is expressly outside the decreasing-potential saturation
bound for a fixed vertex set.

### 5. Intrinsic order-ideal and endpoint formulation

Every order ideal of the branch-condensation poset is an initial segment of
some topological ordering. Thus the cut theorem equivalently says: in any
global section, the membership vectors of the selected query branches and
of their passive anchors differ in at most ONE coordinate at every order
ideal.

There is a useful exact four-endpoint test. Take two co-occurring selected
branches with SCC endpoints (a,p) and(b,q), where p,q are their passive
anchors. Choose one endpoint u from {a,p} and one v from {b,q} to include,
with the other endpoints u',v' excluded. Such a separating ideal exists if
and only if neither excluded endpoint is below either included endpoint.
Indeed the downward closure of {u,v} is the minimal candidate ideal.
Consequently all four such choices must fail this separability test.
Reflexive order automatically handles any same-SCC identification.

An even cleaner equivalent follows when both pairs are nondegenerate
(a!=p and b!=q): the TWO ENDPOINT SETS must be completely ordered,

    every element of {a,p} <= every element of {b,q},

or the reverse set of four inequalities. Thus every global section's
non-SCC-internal selected/passive endpoint pairs form a chain of disjoint
cut intervals in the condensation PARTIAL order itself, not merely in one
arbitrarily chosen linear extension.

Proof of the equivalence: fix an allowed orientation u included, u' excluded
of the first pair. Ideals between down(u) and the complement of up(u') all
split that pair. A maximal chain between those ideals adds one SCC at a
time. Since the second pair's endpoints are distinct, its membership cannot
change from both outside to both inside without an intermediate split,
which is forbidden. Therefore either both second endpoints are <=u or
u' is <=both. If the first pair is ordered, this gives the desired complete
ordering immediately. If its two endpoints are incomparable, apply the
argument to both orientations. The two mixed possibilities would force
the distinct second endpoints to equal the same first endpoint; those are
impossible. The remaining two possibilities are the two complete orderings.
The converse is immediate: an ideal cannot split two completely ordered
nondegenerate endpoint sets at once.

In particular, if two passive anchors share an SCC T and both selected
branches lie outside T, co-occurrence forces one selected SCC strictly
before T and the other strictly after T. Two on the same side cannot
co-occur; neither can an incomparable selected SCC pair. At most two
selected branches can move outside a common passive SCC in one section,
one on each side. Selected branches inside T remain unrestricted by this
argument. This retains the genuinely shared-SCC gap.

These are necessary statements about globally co-occurring branches, even
when their baseline matrix amplitudes vanish. They are not a statement that
the original quantum queries have a definite causal order.

### 6. Independent finite tests

`branch_condensation_cut_record_checks.py/_checks.json/.log` checks every
condensation order ideal of the forward and reversed Lugano calibrations:
502 cuts each, giving all eight possible subsets of the three straddling
queries. The multi-flag pivot has no new choice coordinate; both full choice
functions remain total and unique, and no pivot enters a recurrent SCC.
The three-flag record has exactly four nonzero rank-two origin projections.
Exact rational contractions verify the marked tensor and noncommuting
private record fillers, rather than only scalar phases.

The baseline-zero DAG counterexample is also tested at all ten of its
condensation ideals. Its two active branches genuinely co-occur, but at
most one original vertex straddles any cut. Its selected/passive intervals
are separated, so the new theorem does not incorrectly reject it.

Finally, the checker exhausts all355 partial-order structures on four
endpoints with every possible SCC identification and1241 linear extensions.
It verifies equivalence of the order-ideal, cut-interval, four-endpoint
separability, and (for nondegenerate pairs) complete endpoint-set ordering
conditions. The elementary proof above is the parameter argument; this
finite test independently audits the combinatorial equivalence including
every tie pattern.

<a id="rg-044"></a>

## RG-044 — One-SCC scalar status record

**Statement.** One-SCC scalar status record

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### Statement

For any SCC L of a valid finite routed graph, the complete pattern of native
branches selected inside L can be exposed at one new native scalar-record
vertex. Its algebra is C^k, where k is the number of reachable layer-status
patterns. All old native branch dimensions and freedoms remain unchanged.
At baseline value 1 on each record branch, the original tensor is recovered.

For a red L, the new record branches can be placed immediately before L in
a condensation topological order; for a green L they can be placed
immediately after L. The rewrite preserves bi-univocality and weak loops.
A singleton SCC may be assigned either color for this purpose. This creates
a classical direct-sum phase record, not a full quantum M_k port.

### 1. Literal local routes

Add an isolated M1 vertex A with empty input and output tuples. This is
allowed by the routed framework: empty products have dimension one, and
its baseline scalar filler is 1. For every native vertex J that has a
branch in L, define a finite label

    g_J(b) = b, if the selected J branch b lies in L;
             *, if it lies outside L.

Introduce two scalar-sector wires J->A and A->J with label set consisting
of these alternatives. Append the fixed label g_J(b) to the input and output
tuples of each old J branch b. This leaves its entire old practical quantum
space and full native matrix algebra unchanged.

Replace A by one scalar branch A_s for each tuple s=(s_J)_J of labels. Its
incoming and outgoing flag tuples are both the fixed tuple s, so its
practical input/output dimensions are one. Unreachable A_s can be removed
afterward. Parallel flag wires can equivalently be bundled with existing
arrows without changing these practical rectangles.

### 2. Section and choice bijections

Every old globally consistent section determines exactly one tuple s, by
its selected J branches, and hence exactly one new consistent section with
A_s selected. Conversely any new consistent section restricts to an old
one, and the two flag wires force its A label to be that same tuple.

All old complete forward and reverse choice coordinates are unchanged:
appending a fixed label at a branch does not add a choice. Every A_s has
only one input and one output tuple, so the new coordinates are singleton
sets. Thus the full forward and reverse choice maps correspond bijectively
to the old ones, including all dormant old coordinates. Bi-univocality is
preserved without selecting a currently active branch coordinate.

There are no selector-dependent changes to the old fillers or old choice
vectors. This simplification is particular to starting from an empty M1
pivot; the more general recipient-refinement proofs need their full dormant
vector argument.

### 3. Exact new edge classification

Old branch statuses as functions of the complete choice tuples are
unchanged, so all old dashed edges are unchanged. Old wire conditional
sector sets are unchanged as well. On a new wire, every co-occurring pair
(J_b,A_s) has the single fixed sector g_J(b)=s_J, of dimension one. Hence
no new wire gives a solid edge.

Every A_s has a singleton output coordinate, so it has no outgoing green
edge. It has a singleton input coordinate, so it has no incoming red edge.
The only possible new edges are therefore:

- green v->A_s, when changing an old output coordinate changes the pattern
- red A_s->v, when changing an old input coordinate changes the pattern

If the pattern changes, at least one status of a branch b in L changes.
For a green v->A_s this witnesses an OLD green edge v->b for some b in L.
For a red A_s->v it witnesses an OLD red edge b->v for some b in L. This
includes changes between the star alternative and a selected L branch;
no assumption about the positions of J's outside siblings is needed.

If L is red, no old green edge can be internal to L. Every new green parent
v therefore lies strictly before L in the condensation partial order.
Every new red target lies in L or strictly after it. Placing all A_s just
before L makes every new edge advance the chosen SCC order.

If L is green, every new green parent lies in L or strictly before it,
while every new red target lies strictly after it. Placing all A_s just
after L again makes every new edge advance the SCC order.

Consequently the old SCCs and their single internal colors are unchanged;
each A_s is a new singleton SCC, and no new directed cycle is created.
This proves the weak-loop condition for both colors. The argument uses
only the actual choice-dependence definition and does not presume an
exchange-algebra projection was already available on an edge.

### 4. Exact marked contraction and completeness

Let G_s denote the old contraction retaining the complete layer-status
pattern s. At the new scalar-record filler z=(z_s), the rewritten tensor is

    G_new(u,z) = sum_s z_s G_s(u).

This is a coherent tensor-contraction identity, not a measurement or a
classical averaging operation. Setting every z_s=1 gives the old G(u).
The new graph is valid with its full native freedoms, so the rewrite has
the independent private-ancilla validity of the routed framework.

At any unitary old context, a single native C^k slot has orthogonal
normalized branch projections summing to I. Every reachable A_s is faithful,
so its represented rank is positive and k<=D. This gives a graph-theoretic
route to the same-layer joint-pattern projection/faithfulness conclusion.
The already proved green-layer fixed-future and red-layer fixed-past
identities additionally identify the side on which this phase record acts
when only fillers of L vary.

The rewrite exposes only one SCC's actual native-status pattern. It does
not make arbitrary records from different SCCs simultaneously commute,
create a laboratory-input C^7 context, or contract the surrounding network
into a product-state hub. Adding arbitrarily many new pivots is outside the
fixed-vertex termination potential proved previously.

### 5. Cyclic calibration

[branch_layer_scalar_record_lift_checks.py](../branch_layer_scalar_record_lift_checks.py) starts from the exact binary
Lugano graph with six native M2 lab branches, eight scalar hub branches,
and an M8 future decoder. The three losing lab branches form its green SCC.
The complete native-status pattern of that SCC has four reachable values:
000,100,010,001 for the winner-bit vector w(o).

The checker adds three literal bidirectional flag-wire pairs and one C^4
record vertex. It checks all 64 forward and eight reverse complete choices,
including dormant lab coordinates, preserves all eight sections, and checks
all conditional wire-sector sets. The losing green SCC is unchanged; all
new record branches are singleton SCCs after it. The literal time reverse
places the record before the red SCC with the same validity checks.

The exact phase contraction is a four-sector future-row mask in the green
host and a four-sector past-column mask in the red host. Each record
projection has rank two. Its full phase polynomial is unitary for every
unit-modulus phase and native unitary context, as also certified by the
actual valid route. No quartet realization is claimed by this calibration.
