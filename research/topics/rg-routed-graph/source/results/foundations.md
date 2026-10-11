# Foundations

[Topic index](../../README.md) · [Shared result index](../../../../RESULTS.md#rg--exact-native-routed-graph-universality)

Each result below has one owner. Exact scope and proof are updated here. Source-level mathematical arguments and finite certificates are distinguished from a new formal verification.

<a id="rg-002"></a>

## RG-002 — Complete finite-algebra bipartite comparison

**Statement.** A normalized independently complete bilinear unitary preserver on finite C*-algebras has two represented multiplication orders separated by a commuting projection.

**Status:** source-level result. **Scope:** Whole finite C*-algebras, including centers, kernels and multiplicities; the comparison projection need not be unique.

### 1. Exact theorem

Let A and B be arbitrary finite-dimensional unital complex C*-algebras,
including finite direct sums of matrix algebras. Let H be finite dimensional
and let F:A x B -> L(H) be complex bilinear, with F(1,1)=I. Suppose it is
independently completely unitary preserving in the following precise sense:
for every m,n>=1, its entrywise separate amplification

    `F^[m,n](a tensor X,b tensor Y)=F(a,b) tensor X tensor Y`

is unitary on each tuple of unitaries in A tensor M_m and B tensor M_n.
The common tensor-factor convention is fixed as in the retained matrix
input theorem. No unitary mixing distinct central summands of A or B is
assumed available; A tensor M_m remains the direct sum of its amplified
simple summands.

Set alpha(a)=F(a,1), beta(b)=F(1,b). Then these are unital
*-homomorphisms, and there exists an orthogonal projection P commuting
with both represented algebras such that

    F(a,b)=P alpha(a)beta(b)+(I-P)beta(b)alpha(a).          (1)

Neither homomorphism is required to be faithful. If q is the common
kernel of their cross commutators and z=I-q, then the comparison is
unique on z. On q the pair is the ordinary commuting product; all choices
are obtained by adding any projection in the common commutant on q.

Only amplification by a private two-dimensional ancilla at one laboratory
at a time is used to establish the normalized-slice homomorphisms. The
remaining proof is at the original boundary dimension. This statement
does not introduce arbitrary joint operations across the two laboratories.

### 2. Complete unitary preservation gives homomorphic slices

Let phi:A->L(H) be unital and suppose phi and its entrywise amplification
phi^[2] send all unitaries to unitaries. Expanding the norm identity at
exp(it h), for any Hermitian h, gives self-adjoint preservation and
phi(h^2)=phi(h)^2. Hermitian decomposition and polarization extend this
Jordan square identity to arbitrary elements. Apply the same reasoning
to phi^[2] on A tensor M2. For arbitrary a,a' in A, put

    X=[[0,a],[a',0]].

Its square has diagonal entries aa' and a'a. The diagonal entries of
`phi^[2](X)^2 therefore give`

    phi(aa')=phi(a)phi(a').                             (2)

Thus phi is a unital *-homomorphism. This argument does not use full
matrix units in A, connected homomorphic/antihomomorphic orientation
components, simplicity, or an invertible commutator in A.

In particular it proves the assertion for alpha and beta. For a fixed
unitary v in B, define phi_v(a)=beta(v)* F(a,v). Its amplification is

    `(beta(v)* tensor I2) F^[2,1](a,v),`

so the complete-unitary premise gives exactly the hypothesis just used.
It is unital because F(1,v)=beta(v). Consequently every normalized
first-variable slice is homomorphic, and similarly every normalized
second-variable slice is homomorphic. Thus, for unitary v and u,

    F(aa',v)=F(a,v)beta(v)*F(a',v),
    F(u,bb')=F(u,b)alpha(u)*F(u,b').                     (3)

Entrywise amplification here is the actual private-ancilla amplification
of the given bilinear map. Nothing substitutes an independently chosen
homomorphism for that amplification.

### 3. Differentiation and the factor-free strict-support argument

Define h(a,b)=F(a,b)-alpha(a)beta(b). Differentiate the first equation(3)
at v=exp(it y), y Hermitian, and the second at u=exp(it x). Complex
linearity extends the resulting identities to arbitrary x,y. They are

    h(aa',b)=h(a,b)alpha(a')+alpha(a)h(a',b),
    h(a,bb')=h(a,b)beta(b')+beta(b)h(a,b').              (4)

The cancellation includes the derivative of beta(v)* or alpha(u)*; it
does not require alpha(A) and beta(B) to commute. This is the exact
mixed-embedding reduction from the retained source, with no use of
simplicity in the differentiation step.

Write C(a,b)=[alpha(a),beta(b)]. Comparing the two expansions of
h(aa',bb') gives

    C(a,b)h(a',b')=h(a,b)C(a',b').                      (5)

Sections1--3 of [RG-075: Support of mixed biderivations](higher-order.md#rg-075) use only (4),
adjoint closure, and finite spanning bases. They therefore extend without
change to A and B. Explicitly, q is reducing for both algebras by the
commutator product identities. Equation(5) kills both off-diagonal blocks
of h across q and z. On z choose a finite skew-adjoint cross-commutator
family C_mu with zero common kernel. Its positive Gram is invertible.
The retained Gram reconstruction gives the unique fixed coefficient T
such that

    z h(a,b) z=C(a,b)T=T C(a,b),
    [T,alpha(A)|z]=[T,beta(B)|z]=0.                     (6)

The final joint commutation follows from the two Leibniz identities,
not from an unproved equality of two commutant algebras. No individual
cross commutator needs to be invertible.

The matrix-unit double-inner formula in Section4 of that source is NOT
needed. In particular this proof does not silently reuse its single-factor
implementer formula for a direct sum.

### 4. Reflection identities and the commuting support

Every finite-dimensional C*-algebra is complex-linearly spanned by its
Hermitian reflections: spectral projections span its Hermitian part,
and p=(I-(I-2p))/2. Central summands cause no problem for this statement.

Take reflections r in A, s in B, and denote a=alpha(r), b=beta(s).
The comparison product G(x,y)=alpha(x)beta(y) is unitary on unitary tuples,
has the same one-variable faces as F, and h=F-G vanishes when either
input is identity. Put x=epsilon u I+i v r and y=eta u' I+i v' s,
with positive u,v,u',v', u^2+v^2=u'^2+v'^2=1. The correction is

    h(x,y)=-v v' h(r,s),

independently of the two signs. The nonconstant sign coefficients of
F*F-G*G=0 give

    h(r,s)*=-h(r,s),
    {h(r,s),a}={h(r,s),b}=0.                           (7)

These coefficients involve only identity and single-slot faces and the
positive correction square is sign independent, exactly as in the retained
reflection calculation. No full-matrix assumption enters.

Both h and G are block diagonal across q,z, so their actual restrictions
remain unitary on unitary tuples. On q, a and b commute. Equation(7)
makes h commute with ab, while ab is a Hermitian unitary. Consequently

    (ab+h)*(ab+h)=I+h*h.

Unitarity forces h(r,s)=0 on q. Spanning by reflection pairs proves that
F equals the commuting product on the entire q block. This bypasses
all possible direct-sum inner-derivation subtleties.

### 5. Projection-valued comparison on strict support

On z, substitute (6) into (7). Since C(r,s) is skew-adjoint and T
commutes with the represented algebras, skewness gives

    C(r,s)(T*-T)=0.

Reflection commutators span the full cross-commutator family, whose
common kernel on z is zero. Thus T=T*. Put P_z=I_z+T. Equation(6) is
then

    F(r,s)|z=P_z ab+(I_z-P_z)ba.

Here P_z is Hermitian and commutes with a and b. Direct expansion yields

    F(r,s)*F(r,s)-I_z
       =P_z(I_z-P_z)(ab-ba)^2.                        (8)

The square of a skew-adjoint matrix has the same kernel as that matrix.
Using commutation with P_z, (8) and the zero common commutator kernel
therefore force P_z(I_z-P_z)=0. Hence P_z is an orthogonal projection.
Adding any common-commutant projection on q proves (1). Conversely each
such P gives a bilinear independently completely unitary-preserving map,
by its reducing ordered-product summands.

For uniqueness, the difference of two valid comparisons annihilates
every cross commutator on both sides and is therefore supported on q.
This is the same exact comparison-choice freedom as for full factors,
but the common commuting algebra on q can now have several simple types.

### 6. What is and is not transferred from the older proofs

The canonical proof [RG-002: Complete finite-algebra bipartite comparison](foundations.md#rg-002) cannot simply be quoted
unchanged: its commutator invertibility and target Pauli probe are written
for a common full-matrix embedding. The present proof replaces both.
Its continuous Jordan-orientation argument can also be extended blockwise,
but the private2x2 argument above avoids needing that extension.

The Gram strict-support theorem is genuinely factor free. The commuting
reflection theorem is likewise factor free after replacing its final
matrix-unit spanning sentence by the finite-C*-algebra spectral-projection
spanning fact. The safe-algebra theorem in [RG-077: Safe adapter algebras, phase obstruction and code rotation](construction-boundaries.md#rg-077)
does use connectedness of a finite C*-algebra unitary group and innerness
on matrix orbit blocks, but neither it nor its maximality statement proves
this bipartite comparison result. It is a separate memory-observable
criterion and does not imply any arbitrary host extension.

Most importantly, a factor-specific DIMENSION consequence does not survive
unchanged. On a commuting carrier, finite algebra representations factor
through A tensor B, which can have several simple summands. For
A=M6 direct-sum M2 and B=M2, a carrier may support the M2 tensor M2
summand and have dimension4. It need not have dimension at least12,
or the full native practical-space dimension times2. Thus the unrestricted-M4/M8 contextual full-strictness argument cannot be copied
verbatim to M6 direct-sum M2.

Likewise, native center projections and the weights of their represented
summands must be retained: no fixed common multiplicity or full-factor
relative commutant follows merely from knowing the total practical
dimension8. A genuine sectorized host application must identify its
normalized algebra, its embedding of the original qubit query, the actual
single-slot representation and its complete private-ancilla quantifiers.

### 7. Scope of the theorem

Under the exact complete-unitary model of Section1, the bipartite comparison
formula has a factor-free proof. Applications must identify the actual
whole native algebra and retain its represented centers and multiplicities.
This algebraic classification alone neither constructs a routed host nor
proves the quartet obstruction; that additional graph argument is RG-001.

### Required proof qualifications

The comparison is applied to entire finite-algebra vertices before selecting a branch. On the common commutator kernel, reflection positivity forces the correction to vanish; on its orthogonal complement the finite Gram inverse supplies the multiplier. Neither faithful representations nor a unique comparison projection are needed.

<a id="rg-003"></a>

## RG-003 — Branch faithfulness under complete extensions

**Statement.** Finite-algebra branch support and mixed-block identities retain their complete-private-extension hypotheses.

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### 1. Setup and statement

At a selected vertex, let one branch b have equal practical input
and output dimensions m>0. Its filling is an unrestricted unitary
between those spaces; other branches have their independent full
unitary fillings. Every vertex occurs once in the tensor contraction,
so contraction is complex linear in each local operator.

Fix unitary fillings at all other vertices and fix unitary reference
fillings at the other branches of the selected vertex. After choosing
a reference unitary J_b to identify branch b's input and output,
write the external contraction as

    F(U,z)=L(U)+z C,   U in U(m), z in U(1).        (1)

Here z multiplies all the other branches of this vertex. If b is
its only branch, omit C and z. Assume the external spaces have
equal dimensions and (1) is unitary for every U,z.

**Branch-faithfulness lemma.** For these fixed other fillings,
either L is injective on M_m, or L is identically zero.
In particular, L cannot annihilate a nonzero rank-one operator
while having any nonzero coefficient on the same branch.

Consequently, if a rank-one entry of branch b vanishes identically
under contraction for every compatible filling at all other vertices,
then the entire branch is operationally zero for every such filling.

### 2. Unitary preservation gives a Jordan map

Left-normalize (1) by the fixed unitary F(I,1)^*. This gives a
unital complex-linear map

    Phi:M_m direct-sum C -> L(P)

that maps every unitary of its domain algebra to a unitary.
For Hermitian h, expand Phi(exp(ith))^*Phi(exp(ith))=I at zero.
The first derivative gives

    Phi(h)^*=Phi(h),

and the second gives

    Phi(h^2)=Phi(h)^2.

Polarizing over Hermitian h,k and then extending complex linearly
gives

    Phi(a b+b a)=Phi(a)Phi(b)+Phi(b)Phi(a).

Thus Phi is a unital Jordan *-homomorphism. It is positive because
every positive element is the square of a Hermitian element.
No private-ancilla or complete-positivity assumption is needed
for this step.

The kernel on a full matrix summand is either zero or the whole
summand. The next elementary argument proves the full injectivity
claim, without invoking a Jordan-algebra structure theorem.

### 3. Elementary kernel proof

Suppose Phi_b(a)=0 for a nonzero matrix a.
The Jordan * identity gives

    Phi_b(a^*a+aa^*)=0.

Both terms are positive, so each has zero image. Spectrally
decompose the nonzero positive matrix a^*a as a positive linear
combination of orthogonal rank-one projections. Their images
are positive and their weighted sum is zero, so every projection
with positive weight has zero image. In particular some rank-one
projection p has Phi_b(p)=0.

For any unit vector v orthogonal to a unit vector u spanning p,
let q=|v><v| and h=|u><v|+|v><u|. Since

    ph+hp=h,

the Jordan identity forces Phi_b(h)=0. Squaring gives

    Phi_b(p+q)=Phi_b(h^2)=Phi_b(h)^2=0,

so Phi_b(q)=0. Completing u to an orthonormal basis yields
Phi_b(I_m)=0. Positivity then forces Phi_b(x)=0 for every
Hermitian x, by bounding x between scalar multiples of I_m.
Complex linearity proves Phi_b=0 and hence L=0.

The reference identification J_b preserves rank one, so the
claim applies to actual input-output matrix entries even when
those branch spaces use different bases.

### 4. A graph-combinatorial corollary

Suppose a routed branch is reachable: some global compatible
index assignment uses it, and every quantum sector on that
assignment has positive dimension.

Then every locally permitted pair of input and output sector
tuples in that branch must extend to some global compatible
index assignment.

If a permitted pair did not extend, any matrix unit supported
on that input-output pair would have identically zero
contraction for all other compatible local fillings: every
summand in the network contraction would contain an
inconsistent wire-index assignment.

The branch-faithfulness lemma would then make the entire branch
operationally zero. But the reachable assignment supplies a
nonzero coefficient: choose one basis vector in every sector
along the assignment and choose matching matrix units at each
vertex. Their contraction is one nonzero external matrix unit.
This use of nonunitary matrix units is legitimate because
compatible full unitaries linearly span each local direct-sum
matrix space, and the network is multilinear.

This contradiction proves the corollary.

Unreachable branches are excluded from the statement. They may
be deleted rather than being treated as active matrix factors.
The condition is necessary for universal unitary validity; it
does not itself prove bi-univocality or weak loops.

### 5. Apply it to a proposed quantum star hub

In the star layout A_i<->H, each adapter is either inactive
(sending a nonnull output to H and receiving null) or active
(receiving nonnull from H and sending null).

Let S_in be the null pattern of a hub input tuple and S_out
the active pattern of its output tuple. Every global assignment
requires

    S_in=S_out,

independently of the terminal decoder or quantum dimensions.

A hub branch whose rectangular route contains an input tuple
with pattern S and an output tuple with pattern T different
from S therefore has a structurally zero rank-one corner.
If it has any reachable entry, the corollary rules it out.

Hence every reachable full matrix hub branch must have one
fixed active/null pattern throughout its input and output
sets. A coherent full unitary branch cannot simply merge
different active-laboratory histories.

This conclusion does not assume that the terminal decoder
records the active set. It addresses the potential circularity
of a proof that attempts to impose mutually incompatible
reverse choices before establishing their extendibility.

### 6. Relation to the quartet and scope

The safe algebra M2 direct-sum C found for the quartet passes
this necessary condition. Its active M2 matrix units have
nonzero contextual action; there is no contradiction to that
admissible-node construction.

The condition instead rejects a proposed repair that promotes
the two incompatible active histories to one unrestricted
quantum hub branch. Its cross-history matrix entries cannot
occur in any global assignment even though its diagonal
histories are reachable.

Thus this is a genuinely graph-wide necessary invariant and
a concrete rejection certificate for that proposed graph.
It is not an invariant violation by the quartet independent
of representation, and it is not a counterexample to routed
universality. A more elaborate graph may avoid the missing
corners altogether.

<a id="rg-004"></a>

## RG-004 — Commuting origins force the product tensor

**Statement.** A normalized multilinear unitary preserver with commuting single-slot representations equals their product.

**Status:** source-level result. **Scope:** Representation premise is essential; commutative phase inputs need only ordinary unitarity.

### Theorem (stronger than complete-unitary phase rigidity)

Let A_1,...,A_n be finite-dimensional unital complex C*-algebras and let

    F : A_1 × ... × A_n → M_D

be complex multilinear, normalized by F(1,...,1)=I. Suppose F sends every tuple of ordinary unitaries to a unitary. Define

    α_i(a)=F(1,...,1,a,1,...,1).

Assume each α_i is a unital *-homomorphism and the ranges of α_i and α_j commute for i≠j. Then, for all inputs,

    F(a_1,...,a_n)=α_1(a_1)...α_n(a_n).

Thus no private-ancilla assumption is needed once the stated properties of the single-slot maps are given. In particular the requested lemma for A_i=C^{m_i} is true for every n. The proof does not infer a tensor from its pairwise marginals: it explicitly kills the possible full n-slot correction.

### Direct proof by signed reflections

Induct on n. The case n=1 is tautological. For n≥2 every proper identity face satisfies the hypotheses, so its full tensor factors by induction. Set

    G(a_1,...,a_n)=α_1(a_1)...α_n(a_n).

This is multilinear and unitary on every unitary tuple. The difference F−G vanishes on every proper identity face.

Choose arbitrary Hermitian reflections r_i∈A_i, meaning r_i*=r_i and r_i²=1, and put

    a_i=α_i(r_i),
    A=a_1...a_n,
    K=F(r_1,...,r_n)−A,
    L=i^n K.

The a_i are commuting Hermitian unitaries, so A*=A. Choose any positive real c_i,s_i with c_i²+s_i²=1. For independent signs ε_i∈{−1,+1}, put

    x_i(ε_i)=ε_i c_i 1+i s_i r_i,
    t=∏_i s_i>0.

Every x_i is unitary. Because F−G vanishes on every proper identity face, multilinearity gives the exact identity

    F(x_1,...,x_n)=G(x_1,...,x_n)+t L.                 (1)

There are no lower-degree correction terms. Write G_ε=G(x_1,...,x_n). Its product expansion is

    G_ε=Σ_{S⊆[n]} i^{|S|}(∏_{i∈S}s_i)
          (∏_{j∉S}c_j)(∏_{j∉S}ε_j) A_S,
    A_S=∏_{i∈S}a_i,       A_∅=I.

All A_S are Hermitian. Both sides before adding the correction in (1) are unitaries, hence

    0=t(G_ε*L+L*G_ε)+t²L*L                            (2)

for every sign tuple. The characters ∏_{j∈T}ε_j are linearly independent.

1. The full character ∏_{j=1}^n ε_j in (2) has coefficient

       t(∏_j c_j)(L+L*).

   Thus L*=-L.

2. For each i, the character ∏_{j≠i}ε_j has coefficient

       t s_i(∏_{j≠i}c_j)(−i a_i L+i L*a_i).

   It is a nonconstant character because n≥2, so the correction square contributes nothing. Substituting L*=-L yields

       a_i L+L a_i=0.                                (3)

3. The constant coefficient of (2), divided by t², is

       (−i)^n A L+i^n L*A+L*L
       =(−i)^n A L−i^n L A+L*L.

   From (3), moving L through all n reflections gives LA=(−1)^n AL. Since i^n(−1)^n=(−i)^n, the two mixed terms cancel exactly. Therefore

       L*L=0,

   whence L=0 and K=0.

We have proved F(r_1,...,r_n)=G(r_1,...,r_n) for all reflection tuples. Hermitian reflections complex-linearly span every finite-dimensional C*-algebra: spectral projections span its Hermitian part, and every projection p equals (1−r)/2 for r=1−2p. Multilinearity therefore gives F=G on all input tuples. This closes the induction.

#### Why this argument is not a marginal-identification shortcut

Agreement on proper faces is used only to isolate the single residual K in (1). The full unitary identities, including their constant sign coefficient, force K*K=0. No independent assumption removes a higher-order interaction.

### In the phase case the representation premise is automatic

For a unital complex-linear φ:C^m→M_D sending all phase vectors to unitaries, write

    φ(z)=Σ_a z_a P_a,       Σ_a P_a=I.

The Fourier coefficients of φ(z)*φ(z)=I on the m-torus give

    P_a*P_b=0 for a≠b.

Consequently

    P_a=(Σ_b P_b)*P_a=P_a*P_a.

Thus P_a is self-adjoint and idempotent; the P_a are mutually orthogonal projections summing to I. Hence φ is a unital *-homomorphism. In the original question only mutual commutation between the different slots' projection families is an additional assumption; no amplification is required at all.

### Proof of the alternative contextual-transport proof

Assume now the original independent complete-unitary hypothesis, permitting arbitrary finite C*-algebra slots. At a unitary context u=(u_1,...,u_n), define the normalized right-relative single-slot map

    ρ_i^u(a)=F(u)*F(u_1,...,u_i a,...,u_n).

The corresponding one-slot private-ancilla amplification is the actual separate amplification of F, with all frozen slots tensored with identities. It is unital and completely unitary-preserving; hence ρ_i^u is a *-homomorphism. (The usual elementary 2×2 argument suffices.)

Suppose the ranges of all ρ_i^u commute at this particular reached context u. The normalized two-slot map

    H_{ij}^u(a,b)=F(u)*F(u_1,...,u_i a,...,u_j b,...,u_n)

is bilinear, normalized, and independently completely unitary-preserving. Its singles are precisely ρ_i^u and ρ_j^u. The bipartite comparison theorem therefore reduces to

    H_{ij}^u(a,b)=ρ_i^u(a)ρ_j^u(b).                   (4)

Alternatively, the n=2 case of the direct proof above establishes (4) from ordinary unitarity and the stated single-slot representations, without using the full comparison theorem.

Change only coordinate j, setting u'_j=u_j v with v unitary. Then

    F(u')=F(u)ρ_j^u(v).

For i≠j, equation (4) gives

    ρ_i^{u'}(a)
      =ρ_j^u(v)*ρ_i^u(a)ρ_j^u(v)
      =ρ_i^u(a).

For i=j, multiplicativity of the normalized one-slot map gives

    ρ_j^{u'}(a)
      =ρ_j^u(v)*ρ_j^u(va)
      =ρ_j^u(a).

All right-relative representations therefore remain identical after the coordinate change. In particular their mutual commutation is propagated, rather than assumed at an arbitrary context. Starting at the identity and changing coordinates one at a time reaches every unitary tuple. The successive identities for F then telescope to the product of the origin representations. Unitary spanning extends the result to all inputs.

This independently validates the transport argument, including multiplication order and the own-slot normalization. The exact complete bipartite comparison theorem is preserved in:

The direct signed-reflection proof above is self-contained and does not depend on its strict-support reconstruction.

### Scope caution and supplementary exact checks

For noncommutative matrix input algebras, ordinary unitarity preservation alone does not imply that an origin single-slot map is a *-homomorphism: matrix transposition is the elementary counterexample. The stronger theorem therefore retains its explicit *-representation premise. Complete single-slot amplification implies that premise, and the preceding phase-algebra Fourier argument implies it directly for C^m. These are distinct statements.

The portable checker `verify_signed_reflection_coefficients.py` uses exact Gaussian rational arithmetic and formal noncommuting words. For n=2,3,4,5,6 it evaluates every sign tuple, independently Fourier-transforms the unitary-defect expression, checks the full-sign and all-but-one coefficients, and verifies that imposing exactly skew-adjointness and the individual anticommutation relations leaves only the positive square in the constant coefficient. All five cases pass; the saved output is `signed_reflection_coefficient_checks.json`. This finite check is supplementary; the argument above proves every n.





**Reproduction limit:** supporting helpers were not supplied; the analytic argument remains available. See the [artifact map](../REPRODUCIBILITY.md#rg-004).
