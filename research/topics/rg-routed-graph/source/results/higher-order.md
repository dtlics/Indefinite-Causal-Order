# Higher order

[Topic index](../../README.md) · [Shared result index](../../../../RESULTS.md#rg--exact-native-routed-graph-universality)

Each result below has one owner. Exact scope and proof are updated here. Source-level mathematical arguments and finite certificates are distinguished from a new formal verification.

<a id="rg-074"></a>

## RG-074 — Higher-dimensional cube structure

**Statement.** Higher-dimensional cube structure

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### 1. Dimension-independent scalar-opposite-edge gluing

Select two output labels of each laboratory and relabel them 0,1. All identities below concern this selected binary cube inside the full output alphabet; they are inherited from the full process. Normalize its base vertex by a fixed right unitary so that

`V000=I`, `A=V100`, `B=V010`, `C=V001`, `T=V110`.

Let i,j denote the first two inputs and K the third input factor, of arbitrary finite dimension. Suppose the c=0 i,j face is bidirectional. Its two strict changes are

`Delta_i(X)=B^dagger X B-X`,

`Delta_j(Y)=A^dagger Y A-Y`,

both nonzero. The singleton equations put A on jK and B on iK. The face identities give

`Delta_i(X) Delta_j(Y)=0` for every X,Y.                         (2)

Expanding over the independent i and j matrix factors gives commuting coefficient algebras on K. Their strict change ideals have nonzero orthogonal support projections p_i,p_j. This construction is valid in every finite dimension; no support is assumed rank one.

#### Theorem

If `C=V001` is scalar, then

`V_(a,b,1) is proportional to V_(a,b,0)` for every a,b in {0,1}. (3)

Thus the third output is irrelevant throughout this binary cube, up to phases of the retained output record.

If the first two output alphabets are binary and every initial third-output edge `V_(0,0,c) V_(0,0,0)^dagger` is scalar, applying the theorem to every c proves that the third laboratory is a global influence sink.

#### Proof

Absorb C's phase and take C=I. The singleton equations alone imply

`V101=L_j A`, `V011=L_i B`,                                     (4)

where L_i,L_j are local unitaries on the indicated input factors. For example, V101 is on jK by singleton i, while V101 A^dagger is on ij by singleton K; their intersection makes the quotient local on j.

The opposite i,j face has strict changes

`Delta'_i(X)=Phi_i(L_i^dagger X L_i)-X`,

`Delta'_j(Y)=Phi_j(L_j^dagger Y L_j)-Y`,

where `Phi_i(X)=B^dagger X B` and `Phi_j(Y)=A^dagger Y A`. They again obey the pair-annihilation identity (2).

**Exactly one non-scalar L is impossible.** Suppose L_i is non-scalar and L_j is scalar. On the support p_j of the unchanged j-direction ideal, the original i embedding is its baseline, because p_i p_j=0. Hence

`Delta'_i(X) p_j=(L_i^dagger X L_i-X) tensor p_j`.

Choose X making the local difference nonzero, and Y making Delta_j(Y) nonzero. Since Delta_j is supported on p_j and acts on jK, their product is the tensor product of two nonzero matrices on independent i and jK factors. It is nonzero, contradicting opposite-face pair annihilation. The argument is symmetric in i,j.

**Both L's non-scalar are impossible.** In the i,K face at output j=1, normalize by B^dagger. Its K-output edge is

`V011 B^dagger=L_i`,

a non-scalar local unitary on i. Its strict coefficient support on spectator j is therefore the identity. Pair annihilation forces the opposite K-input change along `T B^dagger` to vanish. This edge already acts only on jK, so it must be local on j. Therefore T and B induce identical conjugations of the full K algebra. Symmetrically, T and A induce identical K conjugations. Thus

`A^dagger Z_K A=B^dagger Z_K B` for every Z_K.                    (5)

The two sides respectively belong to L(jK) and L(iK), so their common value belongs to L(K). Conjugation by A therefore restricts to an automorphism of the full matrix algebra L(K). Every such automorphism is inner, and A must be a product unitary on jK.

But then its nonzero strict change of the j-input is a nonzero local matrix on j tensored with the identity on K. Its strict coefficient support is all of K, contradicting the nonzero orthogonal support p_i. Hence both non-scalar L's are impossible.

We conclude that L_i and L_j are scalar. Remove these record phases. The vertices V111 and T now induce the same conjugations of both local i and local j algebras, by their singleton equations. Their quotient lies in L(K). The singleton K equation simultaneously puts that quotient in L(ij). It is scalar. This proves (3).

#### What the lemma replaces

For qubits, the earlier proof enumerated preserved versus exchanged rank-one controller assignments. The argument above avoids that enumeration entirely. The only ingredients are orthogonal strict supports, a local non-scalar change having full spectator support, and the intersection of two tensor-factor algebras. It therefore remains available when controller sectors have arbitrary multiplicities.

The lemma is local to the selected binary output cube. It does not assert that one scalar edge forces a global sink when either of the other output alphabets has additional, unchecked labels.

### 2. A general orthogonal-support construction

Let E_1,E_2,E_3 be pairwise orthogonal projections on I such that E_i is trivial on input factor I_i. Suppose for each output label a of laboratory i we have a unitary A_i(a), also trivial on I_i, with

`A_i(a)-I = E_i[A_i(a)-I]E_i`.                                  (6)

In particular, A_i(a) is the identity on the orthogonal complement of E_i. Set

`V_o=A_1(o_1) A_2(o_2) A_3(o_3)`.

Because the nonidentity supports are orthogonal,

`V_o=I+sum_i [A_i(o_i)-I]`,

and every V_o is unitary. More generally,

`V_o V_o'^dagger
 = I+sum_i [A_i(o_i) A_i(o_i')^dagger-I]
 = I+sum_(i in D) [A_i(o_i) A_i(o_i')^dagger-I]`.                (7)

Each nonidentity summand in (7) is trivial on input I_i for an index i belonging to D. Consequently it is in ker Q_D. The identity term is in that kernel too, proving (1) exactly.

Thus (6) yields an ancillary-complete valid process in any finite dimensions. The proof does not use genericity, cancellation approximations, or a census. The construction also generalizes directly to any number of mutually orthogonal supports E_i, each trivial on its own input factor.

### 3. Explicit dimensions (3,3,2)

Take

`I1=I2=C^3`, `I3=C^2`,

and equal local output dimensions. The past and future both have dimension 18, and S is a unitary between spaces of dimension 324.

On I1 and I2 let

`Pi_1=Pi_2=diag(1,1,0)`;

on I3 let

`Pi_3=diag(1,0)`.

Subscripts on these projectors always indicate the tensor factor, even where their matrices coincide. With cyclic indices define

`E_1=Pi_2(I-Pi_3)`,

`E_2=Pi_3(I-Pi_1)`,

`E_3=Pi_1(I-Pi_2)`.

These projections are pairwise orthogonal: each pair product contains one Pi_r(I-Pi_r). Their nonzero ranks are respectively 6,3,4. The complementary sector has rank 5.

Let

`X_tilde = [[0,1,0],[1,0,0],[0,0,1]]`,

`Z_tilde = diag(1,-1,1)`,

`Z_minus = diag(-1,1)`.

The source output i drives target input j=i+1 modulo three, controlled on the complement of Pi_k for k=i+2. Explicitly choose

`U_2(0)=I_3`, `U_2(1)=X_tilde`, `U_2(2)=Z_tilde`,

`U_3(0)=I_2`, `U_3(1)=Z_minus`, `U_3(2)=I_2`,

`U_1(0)=I_3`, `U_1(1)=X_tilde`.

Here U_2 is indexed by the three labels of output1, U_3 by the three labels of output2, and U_1 by the two labels of output3. Every U_j is identity on ker Pi_j. Put

`A_i(o_i)=I+[U_(i+1)(o_i)-I](I-Pi_(i+2)),                     (8)`

with the tensor placements implicit. Equations (6) hold, so (7) proves exact process validity.

### 4. Why this family escapes the three-qubit structural cover

**No source or sink.** Each generator A_i has genuine influence on both other input factors. It acts nontrivially on target i+1 and is coherently controlled by a nontrivial projector on input i+2. Consequently the full influence graph has all six possible directed edges. This was checked independently using conjugated local matrix units, not inferred solely from the displayed gate support.

**The blocks are entangling.** The block V100=A_1(1) is identity on I1 and a controlled X_tilde on I2I3. Its operator Schmidt rank across I2:I3 is two. Since V000=I, no fixed right past-boundary normalization can make all V_o product unitaries: a product presentation would make every relative block V_o V000^dagger product as well.

**The normalized blocks do not commute.** The two blocks

`V100=A_1(1)`, `V200=A_1(2)`

restrict to Pauli X and Z on the rank-two target sector within E_1. Their commutator is nonzero; its squared Frobenius norm on the full 18-dimensional block space is 24. Therefore the normalized blocks cannot be simultaneously diagonal in any basis, in particular any product input basis. Fixed product input basis changes merely conjugate this commutator.

The dimensional mechanism is explicit: a rank-two input sector can carry noncommuting target operations, while a three-valued source output supplies two independent nonidentity choices. With rank-one qubit sectors those target operations are only phases. Here each selected binary subcube can have its own diagonalizing target basis, but the choices X and Z arising from different output labels have no common target basis.

These facts distinguish the family from the three-qubit source/sink, product-block, and product-basis-diagonal cover under the same boundary normalization conventions. They do not exclude an entirely different representation using a more general transformation of the global future, and they do not prove failure of routed realizability.

### 5. Verification and completed routed construction

The exact-integer verification in `check_higher_dimension_cube.py` checks all 153 distinct pairs of the 18 blocks using the scaled erasure maps

`d_i id - I_(I_i) tensor Tr_(I_i)`.

Every resulting PE matrix is exactly zero. It also checks block unitarity, all six actual influence edges using full local matrix units, the nonzero commutator, and the entangling edge. As a separate consistency check, twelve random tuples of local unitaries gave evaluated-unitarity error at most `1.45e-15`. The results are recorded in `higher_dimension_cube_checks.json`.

The construction is naturally related to the three disjoint active sectors of the binary Lugano function, with noncommuting quantum operations inside higher-dimensional sectors. That resemblance is a route-design lead, not a proof of a valid graph: sector projectors act across different physical inputs, so a naive controlled-order circuit can inadvertently retain or erase an order register incorrectly.

The exact valid routed graph is now proved in [RG-069: Exact tripartite orthogonal-support routes](positive-routes.md#rg-069), with independent review in [RG-069: Exact tripartite orthogonal-support routes](positive-routes.md#rg-069). The construction handles arbitrary joint payload unitaries in the local-sector envelopes derived below, including this explicitly noncommuting family. The example is therefore a proved routed extension beyond the three-qubit structural cover, not a counterexample to the conjecture.

### 6. Every three-party orthogonal-support family has local Lugano envelopes

The orthogonal-support construction in Section 2 admits a stronger reduction in exactly three parties. Suppose E_i are arbitrary pairwise orthogonal projections, with E_i trivial on its own factor I_i. They need not be product projections on the other two factors.

#### Local-support lemma

If E_i E_j=0 and k is the remaining input factor, their reduced support projections on I_k are orthogonal.

Write `E_i=I_i tensor e_i` and `E_j=I_j tensor e_j`, with e_i on I_jI_k and e_j on I_iI_k. Tracing their zero product over I_i and I_j gives

`[Tr_(I_j) e_i] [Tr_(I_i) e_j]=0`.                             (9)

The factors in brackets are positive. Their support projections are therefore orthogonal. Moreover positivity implies that e_i is supported on the tensor product of its local reduced supports: if v is in the kernel of a reduced matrix, the nonnegative sum of expectations of e_i over a basis of the traced factor vanishes; every term vanishes, so e_i annihilates that entire tensor slice.

Define

`Pi_1 = support_(I1)(E_3)`,

`Pi_2 = support_(I2)(E_1)`,

`Pi_3 = support_(I3)(E_2)`.

Here support means the support of the appropriate nontrivial reduced matrix, ignoring scalar identity factors. Applying (9) at each shared input gives

`E_1 <= Pi_2(I-Pi_3)`,

`E_2 <= Pi_3(I-Pi_1)`,

`E_3 <= Pi_1(I-Pi_2)`.                                         (10)

Thus arbitrary entangled supports E_i fit inside the same pairwise orthogonal binary local-sector envelopes as the explicit family.

Every A_i satisfying (6) consequently preserves both local sector flags in its envelope. It may act as an arbitrary joint unitary on the two payload spaces `ran Pi_(i+1) tensor ran(I-Pi_(i+2))`; no product assumption on this payload action follows or is needed for (10).

This supplies a direct algebraic bridge from the PE construction to a potential routed realization: a nonzero active envelope identifies one laboratory i, and both other laboratories occupy inactive envelope labels. A reversed-hub route may therefore collect both other payloads at that active branch, apply the output-controlled joint A_i(o_i)^dagger, and forward them to the future. The completed full practical-space and branch-graph verification is in [RG-069: Exact tripartite orthogonal-support routes](positive-routes.md#rg-069); equation (10) itself is proved here independently of that route. Together they prove routed realizability for every three-party orthogonal-support family in arbitrary finite dimensions.

#### Why the local-envelope argument is special to three parties

For four or more parties, tracing E_iE_j only separates supports on a joint complementary system, not on an individual input factor. Already with four qubit inputs,

`E_1=I1 tensor I2 tensor |Phi+><Phi+|_(34)`,

`E_2=I1 tensor I2 tensor |Phi-><Phi-|_(34)`,

`E_3=E_4=0`

are orthogonal and each trivial on its own input. Their reduced supports on both I3 and I4 are full, so no separation by orthogonal local support projectors is possible. This is an obstruction to this particular local-envelope proof, not to routing: these two sectors can be treated as an ordinary pair-order controller in the joint spectator system, followed by the remaining laboratories.





**Reproduction limit:** supporting helpers were not supplied; the analytic argument remains available. See the [artifact map](../REPRODUCIBILITY.md#rg-074).

<a id="rg-075"></a>

## RG-075 — Support of mixed biderivations

**Statement.** Support of mixed biderivations

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### Theorem

Let alpha:M_r->M_D and beta:M_s->M_D be unital *-homomorphisms. Let h:M_r x M_s->M_D be complex bilinear and an associative derivation in each variable for the corresponding represented bimodule actions. Put

    C(x,y)=[alpha(x),beta(y)],
    q=projection onto intersection_(x,y) ker C(x,y),
    z=I-q.

Then q commutes with both represented algebras, which commute on its range. Every h(x,y) is block diagonal across z and q. On z,

    z h(x,y) z = C(x,y) T = T C(x,y),

where T is supported on z and commutes with alpha and beta. On q, there is an operator V on qH such that

    q h(x,y) q = [alpha_q(x),[beta_q(y),V]].

Conversely, these expressions, with the specified support and commutation assumptions, are mixed biderivations. The strict-sector coefficient T is unique. The commuting-sector implementer V can have gauge freedom.

### 1. The common kernel is reducing

The identities

    [aa',b]=a[a',b]+[a,b]a',
    [a,bb']=[a,b]b'+b[a,b']

show that the common kernel of all cross commutators is invariant under each represented algebra. Adjoint closure makes it reducing, so q commutes with alpha and beta. On q their commutators vanish, which is exactly the asserted commutation.

Choose Hermitian bases x_mu and y_nu of the two input matrix spaces and enumerate their cross commutators as C_mu. Each C_mu is skew-adjoint. Their common kernel is qH and the span of their ranges is zH. On z, the positive Gram operator

    S=sum_mu C_mu* C_mu

is invertible. No individual commutator is required to be invertible.

### 2. Compatibility kills the off-diagonal blocks

Expanding h(xu,yv) in the two possible orders yields

    C(x,y)h(u,v)=h(x,y)C(u,v).                    (1)

Write h_mu=h(x_mu,y_mu), with the same enumeration of input pairs. Because C_mu has support z, the z-to-q block of (1) gives

    C_mu z h_nu q=0 for every mu.

The zero common kernel on z forces z h_nu q=0. The other off-diagonal block gives

    q h_mu z C_nu=0 for every nu.

Their ranges span z, so q h_mu z=0. Bilinearity extends the result from basis pairs to every h(x,y).

### 3. A Gram reconstruction supplies the strict-sector coefficient

Work on zH and suppress compression notation. Multiplying (1) on the left by C_mu* and summing gives

    S h_nu=R C_nu,
    R=sum_mu C_mu* h_mu.

Set T=S^(-1)R. Then h_nu=T C_nu. Substituting in (1) gives

    [C_mu,T] C_nu=0 for every nu.

The ranges of the C_nu span zH, hence [C_mu,T]=0. Therefore

    h(x,y)=C(x,y)T=T C(x,y).

The original derivation identities now provide the additional commutation that the compatibility identity alone would not supply. For instance, compare h(xu,y) computed as C(xu,y)T with its first-slot Leibniz expansion. After cancellation,

    C(x,y)[alpha(u),T]=0.

The common kernel on z is zero, so [alpha(u),T]=0. The same calculation in the other variable gives [beta(v),T]=0. This proves the claimed joint commutation without asserting that the cross-commutator algebra and the joint image algebra have the same commutant.

If C(x,y)T=0 for all x,y, the same common-kernel argument forces T=0, proving uniqueness.

### 4. The commuting sector is a double inner derivation

On qH the two represented algebras commute. Use matrix units e_ab of M_r and set

    L(y)=(1/r) sum_(a,b) h(e_ab,y) alpha(e_ba).

The elementary matrix-unit implementer formula gives

    h(x,y)=[L(y),alpha(x)].

Because alpha(e_ba) commutes with every beta(v), the second-slot Leibniz rule for h makes L a beta-derivation. Its analogous matrix-unit formula supplies V with L(y)=[V,beta(y)]. Thus

    h(x,y)=[[V,beta(y)],alpha(x)]
          =[alpha(x),[beta(y),V]].

This proof uses only finite sums and the two Leibniz identities. The converse follows by the commutator derivation rule and the commutation of alpha with beta on q.

### 5. Application: ordinary-pair support localization of higher corrections

Suppose normalized ancillary-complete multilinear unitary maps F,G have the same one-slot homomorphisms and agree on every proper identity face. Let H=F-G. The separately proved [RG-076: Higher corrections are multiderivations](higher-order.md#rg-076) makes H a derivation in each argument.

Assume their common face on slots i,j is the ordinary ordered product alpha(x)beta(y), or its reverse. For fixed other arguments, apply this theorem to h(x,y)=H(...,x,...,y,...). Its strict block is C(x,y)T, with T independent of x,y and commuting with both ranges.

Evaluate all slots on Hermitian reflections and use the signed-rotation Fourier identity. Besides skewness and anticommutation with individual reflections, the ordinary pair coefficient gives

    C(r_i,r_j) H(r_1,...,r_N)=0,                 (2)

provided N>=3. On z, equation (2) becomes C(r_i,r_j)^2 T=0. Every such C is skew-adjoint, so ker C^2=ker C, and consequently C(r_i,r_j)T=0. Reflection pairs span all cross commutators. Their zero common kernel on z forces T=0.

By multilinearity in the other arguments,

    H=q H q.                                    (3)

Thus an ordinary ordered pair confines any invisible higher correction to that pair's commuting reducing sector.

**Corollary.** If even one common ordinary ordered pair has no nonzero commuting reducing sector, then F=G. This holds in arbitrary dimensions and requires no invertible individual reflected commutator.

For several ordinary pairs, H is supported in the intersection of their commuting reducing subspaces. The corresponding projections need not commute; a zero intersection suffices for uniqueness.

### 6. Dimension-six and multiplicity-two consequences

A nonzero commuting reducing sector for unital factors M_r and M_s carries a unital representation of M_r tensor M_s=M_(rs). Its dimension is therefore a positive multiple of rs.

Hence two Md factors in dimension2d have no such sector for d>=3. Any ordinary ordered pair of them gives the proper-face uniqueness corollary. A noncommuting M2/M3 pair in M6 also has no commuting reducing sector, because the only possible nonzero sector has dimension6 and would make the entire pair commute.

These conclusions provide a replacement for the dimension-four invertible-reflection argument. They do not classify the remaining higher commuting-sector multiderivations, guarantee existence of a process with specified proper faces, or by themselves prove routed universality. Section 4 does classify the two-variable commuting-sector biderivations completely.

<a id="rg-076"></a>

## RG-076 — Higher corrections are multiderivations

**Statement.** Higher corrections are multiderivations

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### Theorem

Let N>=2. Let F,G: product_i M_(d_i) -> M_D be normalized complex multilinear maps that preserve unitarity with independent local ancillary extensions. Suppose they have the same homomorphic one-slot faces rho_i and agree whenever any argument equals the identity. Then H=F-G is a derivation in each argument, with the corresponding rho_i-bimodule action:

    H(...,xy,...)=rho_i(x)H(...,y,...)+H(...,x,...)rho_i(y).

The other arguments may be arbitrary matrices. The conclusion also holds under bare unitarity plus homomorphic faces when the already proved automatic independent amplification theorem applies.

### 1. Signed-reflection identity

Choose local Hermitian involutions r_i and positive a_i,b_i with a_i^2+b_i^2=1. For independent signs epsilon_i, the inputs

    X_i=epsilon_i a_i I+i b_i r_i

are unitary. Because H vanishes on identity faces, K=H(X_1,...,X_N)=i^N(product b_i)H(r_1,...,r_N) is sign-independent. Unitarity gives

    G(X)^*K+K^*G(X)+K^*K=0.

The all-sign coefficient implies K*=-K. The coefficient omitting sign i, which is nonconstant for N>=2, implies

    {K,rho_i(r_i)}=0.

Fix reflections in every slot other than i and write delta(x)=H(r_1,...,x,...,r_N). Scalar factors cancel, yielding

    {delta(r),rho_i(r)}=0

for every Hermitian involution r. Also delta(I)=0.

### 2. Projection identities imply the Jordan derivation rule

For any orthogonal projection p, use r=I-2p to obtain

    delta(p)=rho_i(p)delta(p)+delta(p)rho_i(p).       (1)

If p and q are orthogonal, applying (1) to p+q and subtracting the two separate equations gives

    rho_i(p)delta(q)+delta(q)rho_i(p)
      +rho_i(q)delta(p)+delta(p)rho_i(q)=0.          (2)

For a Hermitian matrix x=sum_lambda lambda p_lambda, its spectral projections are mutually orthogonal. Equations (1) and (2) consequently give

    delta(x^2)=rho_i(x)delta(x)+delta(x)rho_i(x).    (3)

Polarization first gives the anticommutator identity for pairs of Hermitian matrices. Writing any matrix as h+ik then extends (3) to arbitrary complex x. Thus delta is a Jordan derivation.

### 3. A private two-dimensional ancilla supplies the full Leibniz rule

Amplify only slot i by a private two-dimensional ancilla. The process output carries that ancilla, and its normalized embedding is the matrix amplification rho_i^(2). The other slots act trivially on it. The differences of the two amplified maps are exactly the entrywise amplification delta^(2), and they still agree on every extended identity face.

The same reflection/projection argument proves (3) for delta^(2) on M_2(M_(d_i)). Apply it to

    Z=[[0,x],[y,0]].

The upper diagonal block of delta^(2)(Z^2)=rho_i^(2)(Z)delta^(2)(Z)+delta^(2)(Z)rho_i^(2)(Z) is

    delta(xy)=rho_i(x)delta(y)+delta(x)rho_i(y).

Hence delta is an associative derivation. This proof uses the stated independent ancilla condition; it does not silently promote a Jordan derivation to an associative derivation or invoke an external classification theorem.

Finally, identities and Hermitian reflections span each local matrix algebra. Multilinearity in the fixed other arguments extends the result from reflection tuples to arbitrary matrix tuples.

### 4. Compatibility of two of the derivation rules

Freeze every argument but slots i,j. Write h(x,y) for the resulting bilinear map, alpha=rho_i, beta=rho_j. Expanding h(xu,yv) in the two orders and cancelling common terms gives

    [alpha(x),beta(y)] h(u,v)
       =h(x,y)[alpha(u),beta(v)].                 (4)

This is the mixed biderivation identity already encountered for the two-slot problem, now valid for any higher correction invisible on all proper identity faces. There is no assumption that the embedding ranges commute or coincide.

For fixed other inputs, a canonical inner implementer for slot i is

    T_i=(1/d_i) sum_(a,b) delta(e_ab) rho_i(e_ba),

and delta(x)=[T_i,rho_i(x)]. For x=e_kl, expanding delta(e_kl e_ab) gives

    rho_i(e_kl) sum_(a,b) delta(e_ab)rho_i(e_ba)
      =sum_b delta(e_kb)rho_i(e_bl)-d_i delta(e_kl),

while multiplication of that sum on the right by rho_i(e_kl) gives its first term. Subtraction proves the formula on matrix units and hence everywhere. The implementer is multilinear in the other fixed arguments; no innerness theorem is assumed.

### 5. What is not proved

Equation (4) alone does not turn h into a central coefficient times a cross commutator on arbitrary overlapping embeddings. The algebra generated by cross commutators can have a larger commutant than the joint image algebra; this was explicitly disproved in earlier work. Nor is an individual invertible cross commutator guaranteed by noncommutation.

The new theorem reduces uniqueness of a larger process with fixed proper faces to a finite system of simultaneous derivation identities, together with the remaining unitarity equations. A classification of these mixed multiderivations, or suitable support vanishing lemmas, remains a concrete next step.
