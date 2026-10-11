# Serial interfaces

[Topic index](../../README.md) · [Shared result index](../../../../RESULTS.md#rg--exact-native-routed-graph-universality)

Each result below has one owner. Exact scope and proof are updated here. Source-level mathematical arguments and finite certificates are distinguished from a new formal verification.

<a id="rg-013"></a>

## RG-013 — Canonical serial columns and complete promotion

**Statement.** A canonical serial-column subspace admits the stated complete native column replacement.

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### 1. Precise setting and conclusion

Let

    F:M_d x product_(j=2)^N M_(d_j) -> L(H)

be a normalized complex multilinear process, independently unitary-preserving
under all separate private matrix amplifications. Write x for the first
query and y for all other queries, and put

    alpha(x)=F(x,I),       V(y)=F(I,y).

The complete single-map theorem makes alpha a unital *-homomorphism.
The map V is itself an independently complete unitary process on the
other ports. The order convention below is that the first query acts
first: its represented matrix is on the right of V.

There is a canonical largest orthogonal projection S satisfying

    F(x,y)S=V(y)alpha(x)S       for all matrix tuples.       (1)

The projection S automatically commutes with alpha(M_d). It is exactly
the common right kernel of the coefficient matrices of

    D(x,y)=F(x,y)-V(y)alpha(x).                            (2)

For 0<rank S<dim H, the exact map

    G(B directsum b,y)=V(y)B+F(b,y)(I-S),                 (3)

where B is any matrix on SH, is an independently ancillary-complete
unitary process with native first input L(SH) directsum M_d. Its original
query embedding is

    x -> (alpha(x)|SH) directsum x.                      (4)

The native branch B has its full matrix freedom, including arbitrary
unitaries on SH tensor the first port's private ancilla. The boundary H
and every other original port are unchanged.

### 2. The common kernel automatically reduces the original factor

Let K be the common right kernel in (2). Equivalently, v belongs to K
exactly when D(x,y)v=0 for all matrix tuples. Fix a unitary tuple y and
define

    pi_y(x)=V(y)* F(x,y).

For this fixed y, pi_y is a unital independently complete unitary-preserving
linear map, hence a *-homomorphism. This uses only legitimate independent
amplification at the first port; the fixed factor V(y)* is tensored with
the identity on that private ancilla. For v in K we have

    pi_y(x)v=alpha(x)v     for every x and every unitary y. (5)

For arbitrary a,x in M_d, multiplicativity gives

    (pi_y(x)-alpha(x))alpha(a)v
      =pi_y(x)pi_y(a)v-alpha(xa)v
      =(pi_y(xa)-alpha(xa))v=0.                         (6)

Thus alpha(a)v has the same equality at all unitary contexts. Unitaries
linearly span each other input algebra, so multilinearity extends it to
all matrix contexts. Therefore alpha(a)K is contained in K for every a.
Applying this also to a* proves that K reduces alpha. Its orthogonal
projection S consequently commutes with alpha(M_d), as claimed.

Equation(1) follows immediately. Conversely every projection T satisfying
(1) with T in place of S has range in K. Thus T<=S. The common-kernel
definition makes S unique without choosing any tensor basis or decoder.

One can also infer that K reduces every pi_y and that pi_y|K=alpha|K.
This statement concerns normalized one-query slices. It does not say
that K reduces V(y) or F(x,y).

### 3. An explicit finite algorithm

Choose matrix-unit bases x_p of M_d and y_t of the tensor product of the
other input matrix spaces (each y_t is a tuple of matrix units). Compute

    C_(p,t)=F(x_p,y_t),
    V_t=F(I,y_t),
    alpha_p=F(x_p,I),
    D_(p,t)=C_(p,t)-V_t alpha_p.

Then the positive matrix

    L=sum_(p,t) D_(p,t)* D_(p,t)                        (7)

has kernel exactly K. The orthogonal projection onto ker L is S. This
is a finite exact linear-algebra construction from the full coefficient
tensor of F; it is not claimed to have polynomial input complexity or
to depend only on the one- and two-slot faces. For exact rational or
algebraic coefficient data, its kernel can be obtained without sampling
unitary inputs or a numerical tolerance.

Because alpha is a unital representation of the simple algebra M_d,
rank S is a multiple of d. No choice of multiplicity decomposition is
needed to compute S. A different choice of coefficient bases gives the
same common kernel, even though the particular positive Gram matrix L
may change.

### 4. Complete native promotion and maximality within this criterion

Set J(y)=V(y)S. At amplified unitary contexts this is an isometry on the
amplified S carrier. Equation(1) is a coefficient identity, so it
amplifies entrywise with all separate private ancillas. The general
column-replacement lemma in
[RG-015: Joint quartet column promotion](serial-interfaces.md#rg-015), Section1, applies
and proves (3)--(4).

Explicitly, the original F(b,y) maps the S input carrier onto V(y)SH,
because alpha(b)|SH is unitary. It maps the complementary input carrier
onto the orthogonal complementary output carrier. Replacing its S
column by V(y)B leaves those two ranges unchanged. The same argument
permits an arbitrary pair of independent unitary blocks

    B in L(SH) tensor M_n,   b in M_d tensor M_n

at the native port, with all other ports independently amplified. Thus
the construction promotes the entire matrix branch, not merely the
original encoded alpha(M_d) subfamily.

Every column-replacement criterion of the form

    F(x,y)T=J_T(y)alpha(x)T,

with T reducing alpha, is already included: setting x=I forces
J_T(y)=V(y)T. Therefore T<=S. Conversely every reducing subprojection
T<=S obeys that criterion. This proves maximality among these serial
columns for the fixed original query, normalization and order convention.

If S=0, this construction supplies no nonzero promoted branch. If S=I,
then F(x,y)=V(y)alpha(x) globally and G(B,y)=V(y)B promotes the whole
boundary to one full matrix input; an extra passive summand would be
unused. These endpoint cases do not require the proper-column lemma.

### 5. The quartet's canonical first serial column is exactly rank four

For the retained entangled-support M16 quartet in its stated right
normalization, let

    S0=I1 tensor P0_2 tensor (I34-q_C),
    q_C=proj span{|01>,|-,+>}.

The exact identity proved in
[RG-015: Joint quartet column promotion](serial-interfaces.md#rg-015), Section2, is

    F(x,y)S0=U234(y)alpha(x)S0.

At x=I it says V(y)S0=U234(y)S0. Since S0 reduces alpha, the right side
above is also V(y)alpha(x)S0. Hence S0<=S.

If rank S were larger than four, its rank would be an even integer at
least six. Section4 would give an actual native promotion with a used
M_(rank S) branch containing the entire original M2 unitally, on the
original boundary. That contradicts
[RG-012: Native capacity and analytic carrier methods](native-interfaces.md#rg-012), Section8,
which excludes every such used native branch of dimension at least six.
This includes S=I by the endpoint construction just described.

Therefore rank S=4 and S=S0. This deduction uses the independently
proved native branch theorem, not a route for the quartet. It also
agrees with the independently proved uniqueness of any used native M4
carrier in [RG-012: Native capacity and analytic carrier methods](native-interfaces.md#rg-012).

### 6. Scope and the remaining constructive question

The theorem supplies a canonical maximal serial column and a complete
native extension. The column's output V(y)SH generally moves with the
other unknown queries. Hence it is not a fixed reducing sector, and the
statement makes no assertion of a largest routable sector or of graph
universality. The coefficient-kernel algorithm is for the fixed original
query and origin; no origin-independent maximality is claimed here.

For the quartet it explains why the rank-four active interface can be
found canonically from the tensor, rather than only guessed from its
support presentation. Realizing the resulting full native M4 directsum
M2 tensor as a valid global routed graph remains a separate task.

<a id="rg-014"></a>

## RG-014 — Serial-column covariance

**Statement.** Serial-column covariance

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### 1. Statement

Let F be a normalized independently ancillary-complete multilinear unitary
process with balanced original matrix ports, acting on the boundary H.
For each original query i, let S_i(F) be the canonical maximal serial-column
projection defined in [RG-013: Canonical serial columns and complete promotion](serial-interfaces.md#rg-013).
Thus, writing alpha_i(a)=F(a_i,I_-i) and V_i(y)=F(I_i,y_-i),

    F(a_i,y_-i) S_i = V_i(y) alpha_i(a) S_i.             (1)

Every S_i reduces its own represented single alpha_i. For an arbitrary
tuple u of original unitary queries, set

    F^u(x)=F(u1 x1,...,uN xN) F(u)*.                     (2)

Then, simultaneously for every i,

    S_i(F^u)=F(u) S_i(F) F(u)*.                          (3)

In particular all ranks, pairwise intersection dimensions, commutators,
and the dimension of the span of their ranges are invariant under a common
change of original query origins. The projection onto the complement of
that span transforms by the same conjugation. This includes the endpoints
S_i=0 and S_i=I.

### 2. Transport of one serial column

Fix i and temporarily write S=S_i(F), alpha=alpha_i, V=V_i,
v=u_i, and w=u_-i. Put A=alpha(v), U=V(w), and C=F(u).
All three matrices A,U,C are unitary. Equation(1) and reduction give

    C S=U A S,     T:=C S C*=U S U*.                    (4)

Indeed A S A*=S. Taking adjoints also gives

    C* T=S A* U*.                                      (5)

For any first argument a and any tuple y of the other matrix arguments,
apply the full coefficient identity(1) at (va,wy):

    F^u(a,y) T
      =F(va,wy) S A* U*
      =V(wy) A alpha(a) S A* U*.                       (6)

The multiplication wy is componentwise in the original input algebras.
There is no commutation assumption on U or V(wy) with A or S.

Let beta(a)=F^u(a,I) and V^u(y)=F^u(I,y). Setting y=I
or a=I in(6) yields

    beta(a)T=U A alpha(a) S A* U*,
    V^u(y)T=V(wy) S U*.                               (7)

The first identity maps TH into itself because S reduces alpha. Applying
it to a* shows that T reduces beta. Multiplying the two identities on
this reducing carrier now gives exactly

    V^u(y) beta(a) T
      =V(wy) A alpha(a) S A* U*
      =F^u(a,y)T.                                     (8)

Consequently T is a serial column for F^u, and its canonical maximality
implies C S_i(F) C* <= S_i(F^u).

### 3. Equality by the inverse origin

Set v_j=u_j* at every port. Directly from F(I)=I,

    F^u(v)=F(u)*,        (F^u)^v(x)=F(x).               (9)

Apply the already proved inclusion to F^u at this inverse origin. It gives

    F(u)* S_i(F^u) F(u) <= S_i(F).

Combining with the forward inclusion proves(3). The same C=F(u) is used
for every i, even though the intermediate U=V_i(u_-i) depends on i.
Thus the whole family, not just each rank separately, is conjugated.

The proof is algebraic and uses the maximal-column theorem only to know
reduction and maximality. It needs no continuous selection of comparisons,
no optimization over origins, and no putative routed representation.

### 4. Exact consequence for the entangled quartet

The exact coefficient-kernel calculation in
`check_canonical_serial_column_round35.py` gives all four canonical columns
of the right-normalized retained quartet:

    S1=I1 P0_2 Cperp_34,                     rank4,
    S2=I2 tensor proj span{|0,0,1>,|1,-,+>}_134,
                                                rank4,
    S3=E3,                                      rank2,
    S4=E4,                                      rank2.

Here C=proj span{|01>,|-,+>} on qubits34. These four projections
are pairwise orthogonal and leave a rank4 complement R. The exact Gram
matrices have ranks12,12,14,14, respectively, using all256 original
matrix-unit tuples for each query. This is a full finite coefficient
calculation, not a sample of unitary contexts.

It follows from(3) that at EVERY common original unitary origin the four
canonical columns remain pairwise orthogonal with these same ranks and
leave a rank4 complement. Changing the original query origins cannot make
these serial columns span the boundary. This is a limitation of this
specific first-query-column criterion, not a proof of nonroutability.

The result remains compatible with both the actual native promotion and
the absence of proper globally reducing sectors. A serial column need not
be a reducing process sector; its output subspace moves with the other
queries.





**Reproduction limit:** supporting helpers were not supplied; the analytic argument remains available. See the [artifact map](../REPRODUCIBILITY.md#rg-014).

<a id="rg-015"></a>

## RG-015 — Joint quartet column promotion

**Statement.** Four mutually orthogonal quartet serial columns admit simultaneous complete native promotion; the single four-plus-two extension is its specialization.

**Status:** source-level result. **Scope:** A complete process tensor, not a routed realization. Exact maximal kernels are retained with the common proof.

### 1. Simultaneous orthogonal-column replacement

Let F(x1,...,xN) be a normalized independently ancillary-complete multilinear
unitary process on H, with single homomorphisms alpha_i. Let S_i be pairwise
orthogonal projections, each reducing its own alpha_i. Put R=I-sum_i S_i.
Suppose known independently complete isometry-valued multilinear maps
J_i(x_bar_i):S_i H -> H satisfy the exact coefficient identities

    F(x) S_i=J_i(x_bar_i) alpha_i(x_i) S_i.            (1)

Extend each J_i by zero on S_i-perp when writing operators on H. At port i
replace M_(d_i) by L(S_i H) directsum M_(d_i), with arbitrary independent
inputs B_i directsum b_i. Define

    G((B_i directsum b_i)_i)
      =sum_i J_i(b_bar_i) B_i+F(b1,...,bN) R.         (2)

Then G is independently completely unitary preserving and multilinear in
its N native algebra inputs. It restricts exactly to F along

    x_i -> (alpha_i(x_i)|S_i H) directsum x_i.         (3)

For the proof, fix arbitrary unitary passive fillings b_i. Equation(1)
makes ran J_i(b_bar_i)=F(b)S_i H, because alpha_i(b_i) preserves S_i and
acts unitarily there. These output ranges are pairwise orthogonal, and
their orthogonal complement is F(b)RH. Arbitrary active unitary B_i maps
the corresponding input column unitarily onto ran J_i. Thus (2) is a sum
of unitary maps on complete orthogonal input/output column partitions.
The same argument holds with independent private ancillas K_i, allowing
arbitrary B_i in U(S_i H tensor K_i) and b_i in U(d_i dim K_i) at EACH
native port. All amplified S_i remain orthogonal, while all J_i are
amplified coefficientwise by identities on that port's private space.

Each term indexed by i uses B_i linearly and each other native variable
through its passive component b_j once. The last term uses every b_i once.
Thus multilinearity in the full direct-sum variables is literal, not only
an equality for unitary inputs. Substituting (3) turns every summand into
its F(x)S_i column, proving the complete tensor identity.

The simultaneous conclusion is not inferred from separate safety of each
promotion. It uses the common original F and its simultaneous orthogonal
columns, which are essential to the output orthogonality argument.

### 2. Four mutually orthogonal quartet serial columns

Use the normalized quartet F=Phi(W)D0, its projections E_i, and the notation
of [RG-015: Joint quartet column promotion](serial-interfaces.md#rg-015). On coordinates134
let

    g0=|0,0,1>,       g1=|1,-,+>,
    J=|g0><g0|+|g1><g1|.

The two vectors are orthogonal due to their first-qubit values. Set

    S1=I1 P0_2 (I34-q_C),             rank4,
    S2=I2 tensor J_134,               rank4,
    S3=E3,                            rank2,
    S4=E4,                            rank2,
    R=I-S1-S2-S3-S4,                  rank4.          (4)

S1 and S2 are orthogonal because the 34 components of g0,g1 lie in C.
S1 is orthogonal to S3,S4 due to input2. In S2, the g0 term has input1=0,
input4=1 and is orthogonal to E3; the g1 term has input1=1 and is also
orthogonal to E3. For E4 the g0 term has the wrong input1, and g1 has
input3=- orthogonal to its required +. Finally E3 E4=0. This proves all
six pairwise orthogonalities in (4).

Each S_i is trivial on its own original input factor, contains E_i, and
is orthogonal to E_j for j!=i. Hence it reduces
alpha_i(x)=R_i x_i R_i, R_i=I+(Z_i-I)E_i, and

    D0 S_i=R_i S_i,
    F(x)S_i=U_bar_i(x) alpha_i(x_i) S_i,
    U_bar_i(x)=product_(j!=i) x_j.                    (5)

The proof is the same exact two-term column expansion as for S1: all
E_j S_i terms with j!=i vanish before any unsupported commutation is
attempted. Only x_i and its own E_i commute. The factor U_bar_i can be
moved to the left because it acts on the other original target/private
spaces and commutes with x_i and Z_i. Formula(5) holds on arbitrary matrix
coefficients, including all independent ancillary amplifications.

Every E_i annihilates R and D0 R=R. Therefore the remaining column is

    F(x)R=W(x)R,       W(x)=product_i x_i.             (6)

These are moving serial columns, not reducing sectors of F.

### 3. Explicit joint native tensor

Use the four native algebras

    B1=M4 directsum M2,       B2=M4 directsum M2,
    B3=M2 directsum M2,       B4=M2 directsum M2.

The actual extension is the completely explicit polynomial

    G((B_i directsum b_i)_i)
      =sum_(i=1)^4 [product_(j!=i) b_j] B_i
         +[product_(j=1)^4 b_j] R.                   (7)

Each B_i is an arbitrary full matrix supported on S_i; each b_i is an
arbitrary original qubit matrix. Products of the passive b_j are on their
original distinct factors. Equation(7) contains no unknown F on its right
side. All native branch fillers are independent. Complete validity follows
from Section1 and (5)--(6), not from sampled unitarity.

At a port's identity slice the native representation is

    pi_i(B_i directsum b_i)=B_i+alpha_i(b_i)(I-S_i).

The branch multiplicities are (1,6) at ports1 and2 and (1,7) at ports3 and4.
The original query embeddings are those in (3), with fixed factor decodings
on S_i. Substituting them gives exactly the original normalized quartet on
the original sixteen-dimensional boundary, coefficientwise and with one
appearance of each original matrix variable. This is a joint native
extension; it is not an assumption of simultaneous admissibility based
only on four separate one-port checks.

### 4. What a routed host must still supply

There is also a precise limitation of iterating this promotion. If the
chosen S_i are the canonical maximal serial columns of the original F,
then they remain EXACTLY the canonical serial columns of G. Indeed a vector
in the full serial coefficient kernel of G remains in the serial kernel
after restriction of all native inputs along (3), so that kernel is
contained in S_i H. Conversely (7) gives

    G(native) S_i=U_bar_i(b) B_i,
    alpha_i^G(native_i) S_i=B_i,
    G(I_i,native_bar_i) S_i=U_bar_i(b) S_i.

These identities imply that S_i H lies in G's serial coefficient kernel.
Thus the two inclusions give equality directly; no generalization of a
matrix-factor rank argument is required for the native direct-sum inputs.
The exact all-four Gram calculation in
`check_canonical_serial_column_round35.py` proves that the particular
quartet S_i in (4) are canonical, with kernel ranks4,4,2,2. Hence the joint
promotion leaves a rank-four residual for this criterion. This is a
limitation of serial-column iteration, not a nonroutability theorem.

The five input columns in (7) are the orthogonal boundary spaces
S1,S2,S3,S4,R. Their output spaces depend on the passive native fillers:

    U_bar_1 S1, U_bar_2 S2, U_bar_3 S3, U_bar_4 S4, W R.

They are simultaneously orthogonal for every common passive filling by the
proof above. They are not fixed output sectors. Consequently one cannot
turn (7) into five disjoint fixed serial routes merely by naming these
columns as route branches.

A concrete host certificate must implement the changing recombination
through allowed local occurrence/choice predicates and fixed routed spaces.
In particular it must use each original query once after substitution,
retain all independent native B_i and b_i fillers, and admit independent
internal edge insertions. The earlier J/L six-plus-two wrapper cannot be
reused as an unchanged contracted interface: its faithful single native
M6 branch is now excluded by the contextual-center theorem.

The remaining constructive target is therefore the exact finite tensor(7)
with these four native ports. An implementation of the variable output
partition by reusing inverse unknown queries would not meet that target.
The complete tensor in (7) is not a routed construction. Its original quartet restriction is excluded by [RG-001](obstruction.md#rg-001).

### 5. Exact certificate

`check_quartet_joint_serial_promotion_round35.py` checks every S_i and its
own-factor commutation, all six orthogonalities, the exact ranks and support
containments, all256 original matrix-unit tuples in the four column
identities and residual identity, and exact original tensor reconstruction.
It also checks independent full active/passive fillers and a simultaneous
two-private-ancilla example on dimension64. The output is
`quartet_joint_serial_promotion_round35_checks.json`.

These checks verify the stated finite matrices and examples. The general
complete-unitarity theorem is Section1; the checker does not assert a
routed graph or enumerate arbitrary actual processes.

### Exact maximal-column certificate

### 1. Exact result

The canonical first-acting serial columns of the four original queries
are respectively

    S1=I1 tensor P0_2 tensor (I34-q_C),
    S2=I2 tensor (|001><001|+|1,-,+><1,-,+|)_134,
    S3=E3,
    S4=E4.

Their ranks are4,4,2,2. These are exactly the columns used by
[RG-015: Joint quartet column promotion](serial-interfaces.md#rg-015); in particular its
two rank-two columns are already maximal in this criterion. All four
are pairwise orthogonal and their complementary input projection has
rank four. This is a fixed-origin, original-query statement, not a
classification of all possible native tensor extensions or a route.

### 2. Reproducible exact certificate

For each query i and all256 tuples of original two-by-two matrix units,
form the coefficient difference

    D_i(x)=F(x)-F(I_i,x_bar_i)alpha_i(x_i)

and its positive Gram matrix L_i=sum_x D_i(x)*D_i(x). The helper
`check_canonical_serial_column_round35.py` constructs the rational
quartet supports and normalized coefficients explicitly. Its only
import is exact matrix/embedding utilities from the main-guarded
positive-extension checker. It recovers each kernel independently;
the proposed S_i are used only to compare the resulting projections.

The exact calculations give L_i S_i=0 and the following nonzero principal
minor certificates (indices are zero-based in standard binary order):

| Query | Minor indices | Determinant | Kernel rank |
| --- | --- | ---: | ---: |
| 1 | 0,1,4,5,6,7,8,9,12,13,14,15 | 1289031254016 | 4 |
| 2 | 0,2,3,4,6,7,8,9,10,12,13,14 | 644513529856 | 4 |
| 3 | 0,1,2,3,5,7,8,9,10,11,12,13,14,15 | 7298703509422080 | 2 |
| 4 | 0,1,2,3,4,5,6,7,8,9,10,11,12,13 | 1824675877355520 | 2 |

Each minor gives the lower rank bound matching the upper bound from
L_i S_i=0. Hence ker L_i is precisely ran S_i. In addition, the helper
constructs a rational nullspace matrix K_i and checks directly that
K_i(K_i* K_i)^(-1)K_i*=S_i, as well as each own-single reduction and
all six pairwise orthogonalities. There is no sampled-unitary inference
or numerical tolerance. The exact output is
`canonical_serial_column_round35_checks.json`.

The native joint process remains a separate analytically proved
column-replacement construction. These finite computations identify
its columns canonically from the full quartet coefficient tensor;
they do not verify a global graph or replace complete-unitarity proofs.

### Preservation of canonical kernels

### Added Section4: exact preservation of the canonical kernels

The subsequently added two-inclusion argument was reread and also passes.
Restriction of every native input along its original unital embedding
takes the native serial coefficient identity to the original one, so
the new kernel is contained in the old maximal S_i. Conversely the
explicit joint polynomial has column U_bar_i(b)B_i on S_i, and its
native single acts there as B_i. Its identity-i face is U_bar_i(b)S_i.
These identities give the native serial equality on the entire S_i.
Thus the canonical kernels are exactly preserved by this joint
promotion. The proof uses no multiplicity divisibility for direct-sum
inputs and has no graph-theoretic consequence beyond the stated
limitation of the serial-column criterion. No correction is requested.

The helper's final addition equating every amplified output projection
to W S_i W* (and the residual to W R W*) was also inspected and
described as an exact check. 

### Single-column replacement proof

### 1. A general unitary-column replacement lemma

Let F:M_d x product_j M_(d_j) -> L(H) be a normalized independently
ancillary-complete multilinear unitary process. Write alpha for its first
single homomorphism. Let S be an orthogonal projection reducing alpha,
with 0<rank S<dim H. Suppose a known multilinear map J of the other inputs,
from SH to H, is independently complete isometry-valued. Extend J by zero
on Sperp, so J=JS and J*J=S at unitary tuples. Suppose coefficientwise

    F(x,y) S=J(y) alpha(x) S.                          (1)

The assertion includes the corresponding entrywise independent private
ancillary amplifications. Let B be an arbitrary matrix on SH, embedded as
S B S in L(H), and let b in M_d be independently variable. Then

    G(B directsum b,y)=J(y) B+F(b,y)(I-S)              (2)

is an actual independently ancillary-complete multilinear unitary process
with native input L(SH) directsum M_d, and it restricts to F along

    x -> (alpha(x)|SH) directsum x.                   (3)

Here the native port permits the full unitary group in BOTH branches;
there is no restriction of B to the embedded original query family.

Proof: for unitary b,y, equation(1) says F(b,y) maps SH isometrically onto
ran J(y), since alpha(b) preserves SH and J(y) is an isometry. Full
unitarity of F then maps the complement onto (ran J(y))perp. The two
columns in (2) have these orthogonal
input and output carriers and are unitary on their respective carriers.
Their sum is therefore unitary. With a private ancilla K at the native
port, B is any unitary on SH tensor K, and b any unitary in M_d tensor L(K).
Equation(1) and the same two-column proof hold after that amplification
and all independent other-port amplifications. The original complete
unitarity premise of F applies to b, while B can be independently chosen.
Linearity in B directsum b and multilinearity in y are explicit in (2).
Substitution of (3), using (1), gives F coefficientwise.

Normalization of F also gives J(I)=S (the inclusion SH -> H before extension
by zero). A useful special case is J(y)=U(y)S, where U is a complete unitary-valued
multilinear map on the full boundary. No such full-boundary extension of J
is needed for the general lemma.

This lemma replaces one already controlled column of an actual tensor. It
does not claim that SH is a fixed reducing sector of F: its output carrier
ran J(y) can depend on the other unknown queries. It introduces no boundary
compression, prepared state, discarded register, extra query, or arbitrary
joint operation among the original laboratories.

### Distinct failed single-column ansatz

### 5. Exact certificate and a distinct failed ansatz

The helper `check_quartet_four_plus_two_extension_round35.py` verifies (4)--(5)
on all original matrix-unit tuples, selected full native unitary fillings,
and a native/outside private-ancilla example. Its result is
`quartet_four_plus_two_extension_round35_checks.json`. These finite checks
support the algebraic complete proof; they do not replace its quantifiers.

A superficially similar transport formula is different and fails. If
T_B=Phi^(-1)(B D0), the candidate Phi(T_B U)D0 is not in general unitary for
a full native B. For the allowed reflection B=I-2 P0_1 E1 and original
contexts (x2,x3,x4)=(X,I,H), its column-unitarity defect has rank4 and squared
Hilbert--Schmidt norm4. The helper records that exact counterexample as a
guard against confusing that ansatz with the proven column replacement (6).





**Reproduction limit:** supporting helpers were not supplied; the analytic argument remains available. See the [artifact map](../REPRODUCIBILITY.md#rg-015).

<a id="rg-016"></a>

## RG-016 — Canonical last rows

**Statement.** Canonical last rows

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### 1. The maximal output-last projection

Let F:M_d x product_j M_(d_j) -> L(H) be normalized, complex multilinear,
and independently unitary-preserving with all separate private matrix
ancillas. Write alpha(x)=F(x,I) and V(y)=F(I,y). Define

    D_last(x,y)=F(x,y)-alpha(x)V(y).                    (1)

There is a canonical largest orthogonal projection T satisfying

    T F(x,y)=T alpha(x)V(y)                            (2)

for all matrix tuples. It is the projection onto the common left kernel
of the matrices in (1), equivalently the common right kernel of their
adjoints. It automatically commutes with alpha(M_d).

For a unitary outside tuple y, pi_y(x)=F(x,y)V(y)* is a unital complete
unitary-preserving linear map, hence a *-homomorphism. The row identity
is T(pi_y(x)-alpha(x))=0. As x ranges over the whole *-algebra, taking
adjoints makes the common left and right agreeing spaces identical.
The multiplicativity argument from the first-column theorem now shows
that this common kernel reduces alpha: for a vector v in it,

    (pi_y(x)-alpha(x))alpha(a)v
      =(pi_y(xa)-alpha(xa))v=0.                        (3)

This holds at every unitary y and extends to every coefficient context
by multilinearity. Reduction for a* gives the stated commutation.
Every projection satisfying (2) is contained in this common kernel,
so T is exactly maximal without an additional choice of decoder.

If D_(p,t)=F(x_p,y_t)-alpha(x_p)V(y_t) for matrix-unit coefficient bases,
the positive finite Gram matrix

    L_last=sum_(p,t) D_(p,t) D_(p,t)*                  (4)

has kernel ran T. This is an exact finite algorithm from the complete
coefficient tensor. For a full original M_d port, rank T is a multiple
of d. The kernel and reduction proof also works for a finite direct-sum
C*-algebra input, without this last divisibility statement.

### 2. Complete output-row native promotion

For 0<rank T<dim H, let B be an arbitrary matrix on TH, extended by zero
off T, and let b be an independently variable original M_d matrix. Set

    G(B directsum b,y)=B V(y)+(I-T)F(b,y).             (5)

This is a normalized independently ancillary-complete unitary process
with native port L(TH) directsum M_d. Substitution

    x -> (alpha(x)|TH) directsum x

recovers F coefficientwise. Indeed T F(b,y)=alpha(b)T V(y). At unitary
tuples, the original F maps V(y)*TH onto TH, and its complementary row
maps V(y)*Tperp H onto Tperp H. The new active row B V(y) has the same
input and output carriers. Their orthogonal sum is therefore unitary.
This remains exact when B and b are arbitrary independent unitary
blocks sharing the native private ancilla and the other ports have
their own independent ancillas. Equation(5) is multilinear; it uses
no unknown inverse query in its definition.

The cases T=0 and T=I have the analogous obvious interpretations: no
nonzero promotion, or the full serial identity F(x,y)=alpha(x)V(y)
with G(B,y)=B V(y). The statement concerns moving input carriers,
not a fixed globally reducing process sector or a routed realization.

An alternative derivation uses the adjoint-reversed complete process

    F_sharp(x_1,...,x_N)=F(x_1*,...,x_N*)*.

It is complex multilinear and independently complete: its amplified
evaluation is the adjoint of the amplified F at the adjoint local
inputs. Its canonical first-column projection is precisely T_i(F).
This uses balanced original ports. No closure of a particular routed
or QC-QC implementation class under reversal is asserted here.

### 3. Right-normalized original origins leave the output rows fixed

Use exactly the convention

    F^u(x)=F(u_1x_1,...,u_Nx_N)F(u)*.                 (6)

For each original query i,

    T_i(F^u)=T_i(F).                                 (7)

In contrast, the first-column projection transforms as
S_i(F^u)=F(u)S_i(F)F(u)*. This asymmetry reflects which boundary the
normalizing unitary multiplies; one must not apply the first-column
conjugation formula to a last-output row.

To prove (7), fix i, abbreviate T=T_i(F), v=u_i, w=u_-i,
A=alpha(v), U=V(w), C=F(u). The old row identity and reduction give

    T C=A T U,       T U C*=A* T.                    (8)

For beta(a)=F^u(a,I), the same identity at (va,w) gives

    T beta(a)=A alpha(a) A* T.                       (9)

Since beta is a homomorphism, the adjoint identity at a* proves that
T reduces it. At a general other tuple y,

    T F^u(a,y)=A alpha(a)T V(wy)C*,
    T V^u(y)=A T V(wy)C*.

Using (9), their right sides imply

    T F^u(a,y)=T beta(a)V^u(y).

Thus T_i(F)<=T_i(F^u). The componentwise inverse origin u* returns F
exactly, so the reverse inclusion proves equality. The proof holds
coefficientwise and needs no continuous comparison choices.

For a left-normalized convention F(u)*F(ux), the corresponding output
projection would instead be conjugated by F(u)*. Equation(7) is
specific to the stated right normalization.

### 4. Native-extension monotonicity

If a normalized native process G restricts to F along unital embeddings
at every original port, every output-last row of G restricts to an
output-last row of F. Consequently

    T_i(G)<=T_i(F).                                  (10)

This only uses coefficient identities and applies to native finite
direct sums. In particular zero output-last rows cannot be repaired
by enlarging the native inputs while preserving the entire original
query restriction. The conclusion is about this serial criterion,
not about all possible physical implementations of G.

### 5. An exact Gram identity in arbitrary local dimensions

Let H be a tensor product of original query spaces, D=dim H. Use the
orthogonal-cylinder phase family

    Phi(W)=W+sum_k (U_k-I)W E_k,
    E_k E_l=0 for k!=l,
    E_k=I_k tensor e_k,       e_k an orthogonal projection,
    D0=Phi(I),          F(x)=Phi(tensor_k x_k)D0*.

Here U_k is an arbitrary unitary acting only on query k. The established
orthogonal-support theorem makes F independently ancillary-complete.
Fix i, identify H=C^d_i tensor C^n, write E=E_i, U=U_i, r=rank e_i,
and tau=Tr U. Both endpoint values r=0,n are allowed. Define

    K(U)=2d I-conjugate(tau)U-tau U*.

Then the exact output-last coefficient Gram is

    L_i=[r(I-E)+(n-r)E] K(U).                        (11)

The two factors commute. If U is nonscalar and 0<r<n, the Gram is
positive definite and T_i=0. If U is scalar, or E is zero or I,
the Gram is zero and T_i=I. Thus in this phase family each canonical
last row is either zero or the entire boundary. These conclusions do
not depend on the other supports or their ranks.

Here is a direct derivation. Let x=e_ab be a d-by-d matrix unit and
Y range over matrix units on the other factors, equivalently over
products of their matrix units. Put R_i=I+(U-I)E. The normalized
single is alpha_i(x)=R_i x R_i*, and right normalization cancels from
the row Gram. For each k put

    t_k=sum_Y Y E_k Y*=(Tr_bar_i E_k) tensor I_bar_i.

For k=i, t_i=rI. For k!=i, t_k acts only on query i and commutes with
U_k. Orthogonality of the E_k kills cross terms with distinct support
labels. Expanding gives

    sum_Y Phi(xY)Phi(Y)*
      =n x+sum_k [x t_k(U_k*-I)+(U_k-I)x t_k
                         +(U_k-I)x t_k(U_k*-I)]
      =(n-r)x+r U x U*.                             (12)

For k!=i the bracket vanishes by unitarity of U_k and its commutation
with x,t_k. For i it is r(UxU*-x). Putting x=I shows that
sum_Y Phi(Y)Phi(Y)*=nI.

Both diagonal terms of the row-defect Gram equal DI. For the first,
Phi is Hilbert--Schmidt unitary: it applies a unitary left phase
separately on each orthogonal right-support subspace, including the
complement with phase I. The images of full matrix units therefore
form an orthonormal basis, whose products sum to DI. For the second,
use (12) and sum_ab alpha(e_ab)alpha(e_ba)=dI.

The mixed term is

    C_i=sum_ab [(n-r)e_ab+r U e_ab U*] R_i e_ba R_i*.

The matrix-unit twirl and the partial traces

    Tr_i R_i=d(I-e_i)+tau e_i,
    Tr_i(U*R_i)=conjugate(tau)(I-e_i)+d e_i

give

    `C_i=[d(n-r)I+r conjugate(tau)U](I-E)`
          +[(n-r)tau U*+rdI]E.

Consequently L_i=2DI-C_i-C_i*, which is (11). On an eigenvector of U
with eigenvalue lambda, K(U) has eigenvalue

    2d-conjugate(tau)lambda-tau conjugate(lambda)
       =sum_(mu in spectrum U, with multiplicity) |lambda-mu|^2.

This vanishes for some lambda exactly when U is scalar; otherwise all
such eigenvalues are strictly positive. The asserted alternatives follow.
For a qubit Pauli Z, tau=0 and K=4I, hence

    L_i=4r I+2(D-4r)E_i.                             (13)

Its eigenvalues are4r on E_i-perp and2D-4r on E_i. For0<r<D/2,

    det L_i=(4r)^(D-2r)(2D-4r)^(2r).

For a rank-two support (r=1), the determinant is
4^(D-2)(2D-4)^2. The exact helper includes unequal query dimensions,
complex nonscalar phases, scalar phases, and both endpoint supports.

### 6. Quartet result, both-end geometry and routed calibration

Every quartet support E_i is nonzero rank two. With D=16, (13) gives

    L_i=4I+24E_i,       det L_i=210453397504,
    T_1=T_2=T_3=T_4=0.                              (14)

The exact helper `check_canonical_last_columns_round36.py` independently
constructs every matrix-unit defect and all four Grams, verifies (14),
and compares them with the first columns. All sixteen first/last
intersections, overlap traces and commutators are zero because every
last projection is zero. The first-column dimensions remain4,4,2,2,
with rank-four complement. Equation(7) makes every last row zero at
every original origin. Equation(10) also makes all last rows zero for
any native extension through the stipulated unital original embeddings,
including the joint native tensor of round35.

This gives a concrete limitation on promoting a last-output row or
constructing a cover by such rows. It does NOT exclude cyclic routing.
As an exact calibration, consider the three-qubit family

    E1=I1 P1_2 P0_3,
    E2=P0_1 I2 P1_3,
    E3=P1_1 P0_2 I3.

It belongs to the explicitly routed tripartite class proved in
[RG-069: Exact tripartite orthogonal-support routes](positive-routes.md#rg-069) (and the computational-cylinder
class in [RG-070: Coded-cylinder routes](positive-routes.md#rg-070)). Its first columns have ranks2,2,2,
but all three last columns vanish: (13) gives L_i=4I+8E_i and
det L_i=589824 at D=8. Thus a valid weak-loop routed graph can have no
nonzero canonical last-query output row. The quartet's same property
cannot by itself be used as a graph-wide obstruction.

The useful constructive content here is the exact row-promotion
criterion, its origin behavior, and the native-extension monotonicity.
The endpoint theorem alone is not a universal routed criterion; [RG-001](obstruction.md#rg-001) supplies the quartet obstruction.





**Reproduction limit:** supporting helpers were not supplied; the analytic argument remains available. See the [artifact map](../REPRODUCIBILITY.md#rg-016).

<a id="rg-017"></a>

## RG-017 — Last-query isometric coverage criterion

**Statement.** Last-query isometric coverage criterion

**Status:** source-level result. **Scope:** The stated isometric endpoint hypotheses are required; serial coverage is not necessary for arbitrary routed hosts.

### 1. Exact suffix model and theorem

Let F be a normalized independently complete unitary process on H with
balanced original ports, and write alpha_i(x)=F(x_i,I_-i). Let T_i(F)
be the maximal output-last projection from
[RG-016: Canonical last rows](serial-interfaces.md#rg-016), so

    T_i F(x_i,y)=T_i alpha_i(x_i)F(I_i,y).

Assume finite spaces K_i and E, a fixed unit vector eta in E, and fixed
maps V_i:C^(d_i) tensor K_i -> H tensor E satisfying

    V_i*V_j=delta_ij I,

with the off-diagonal identity interpreted as the zero map between
different domains. Suppose prefix maps A_i(x_bar_i):H -> C^(d_i)
tensor K_i, each independent of x_i, obey

    J_eta F(x)=sum_i V_i(x_i tensor I)A_i(x_bar_i),
    J_eta v=v tensor eta.                            (1)

No isometry condition is imposed on these prefix maps. Then there exist
positive effects P_i with

    sum_i P_i=I,
    [P_i,alpha_i(M_(d_i))]=0,
    P_i=T_i(F)P_i T_i(F).                            (2)

In particular the output-last projections span H. The individual P_i
need not be projections and the T_i need not be orthogonal.

### 2. Proof of the positive partition

Put W_i=V_i*J_eta. Multiplying (1) by V_i* gives

    W_i F(x_i,y)=(x_i tensor I)A_i(y).               (3)

At x_i=I this says A_i(y)=W_i F(I_i,y). At all other inputs identity,
it gives W_i alpha_i(x_i)=(x_i tensor I)W_i. Thus P_i=W_i*W_i commutes
with alpha_i, and (3) yields

    W_i[F(x_i,y)-alpha_i(x_i)F(I_i,y)]=0.            (4)

Left multiplication by W_i* and restriction to the support of P_i
show that its support lies in the common left kernel of the row
defects. It is consequently contained in T_i(F). These identities
extend from unitaries to all matrix coefficients by linear spanning.

The row map V from the direct sum of the V_i domains is an isometry.
At the identity tuple, (1) and F(I)=I show that J_eta H lies in ran V.
Hence

    sum_i P_i=J_eta* V V* J_eta=I.

This proves (2). It also provides a finite necessary semidefinite test,
strictly stronger than bare range coverage, with the explicitly computed
T_i as supports. No converse is asserted.

### 3. Why a standard pure unitary QC-QC has this model

The primary description is the corrected June2023 version of Wechs,
Dourdent, Abbott and Branciard,
[arXiv:2101.08796v3](https://arxiv.org/pdf/2101.08796v3),
SectionV.B, Eqs(46),(50),(59)--(62), and AppendixB.3(a).
The final internal map receives the direct sum indexed by the last
query. Its preceding prefix at label i contains every other query once
and does not contain i. The map is initially required to be isometric
only on its coefficient-effective input space. The final process is
obtained by tracing the environment of a pure process vector.

To transfer the theorem without assuming ambient isometry, collect all
coefficients of the just-after-last-query prefix into a map A. Its
range is the effective input subspace of the final internal map L.
The final trace-preserving coefficient identity is

    A*L*L A=A*A.

Therefore L is an isometry on ran A. Extend that restriction to an
isometry V on the whole direct sum of last-query target/memory domains,
by embedding its orthogonal complement into fresh final environment
space. The environment can be made large enough to accommodate every
added direction. All original prefix coefficient vectors lie in ran A,
so the entire original process tensor is unchanged. No earlier-layer
completion or free variation of previously tied query occurrences is
needed for this argument.

The columns of V are the fixed orthogonal isometries V_i in Section1.
The old last-label prefix maps are the A_i; their independence of x_i
follows from the used-set rule and does not require them to be mutually
isometric. Thus the completed circuit has the sum in (1).

Finally, if the reduced process is the pure unitary tensor F, its
purified coefficient vector has the form F tensor eta with one fixed
eta. Indeed, writing its environmental coefficients as w_e gives
sum_e |w_e><w_e|=|F><F|. Positivity forces each w_e to be proportional
to F. The proportionality coefficients form one normalized eta.
This is process-tensor purity, not context-dependent purification of
individual inserted unitary channels. It proves exactly the fixed
environment premise of (1).

Consequently every standard pure unitary QC-QC satisfies (2). The
proof neither assumes time-reversal closure of that class nor imports
the first-query suffix completion from round35.

### 4. A broad orthogonal-cylinder phase consequence

For the arbitrary-dimensional phase family of Section5 in
[RG-016: Canonical last rows](serial-interfaces.md#rg-016), the exact output-last Gram
at a port with local dimension d_i, E_i=I_i tensor e_i,
r_i=rank e_i, n_i=D/d_i and own phase U_i is

    L_i=[r_i(I-E_i)+(n_i-r_i)E_i] K(U_i),
    K(U_i)=2d_i I-conjugate(Tr U_i)U_i-(Tr U_i)U_i*.

If every E_i is proper and nonzero and every U_i is nonscalar, all
T_i are zero. Thus these
independently complete unitary processes admit no standard QC-QC
realization. The result applies both to the entangled quartet and to
the explicitly routed cyclic three-qubit example in that source.
The latter confirms why this is only a QC-QC obstruction: valid
weak-loop routed graphs can fail last-query output coverage.

Native extensions through unital original query embeddings inherit
T_i(G)<=T_i(F). Therefore they cannot supply output-last rows absent
from the original process. This excludes only realization proposals
having the exact suffix structure above; it does not exclude a
genuinely cyclic routed realization of the extension.
