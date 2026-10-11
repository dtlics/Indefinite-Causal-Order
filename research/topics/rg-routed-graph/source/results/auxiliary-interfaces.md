# Auxiliary interfaces

[Topic index](../../README.md) · [Shared result index](../../../../RESULTS.md#rg--exact-native-routed-graph-universality)

Each result below has one owner. Exact scope and proof are updated here. Source-level mathematical arguments and finite certificates are distinguished from a new formal verification.

<a id="rg-052"></a>

## RG-052 — Multiplicity-one supported-cut theorem

**Statement.** A multiplicity-one auxiliary branch forces the exact supported before/after group cut, with its proper-block phase removed.

**Status:** source-level result. **Scope:** Only the selected multiplicity-one block; repeated multiplicities are not removable by this theorem.

### Statement

Let G(a,x_1,...,x_n) be a normalized independently private-ancilla-completely unitary multilinear process, where the auxiliary algebra is a finite-dimensional C*-algebra A and original queries are M_{d_i}, d_i>1. Put F(x)=G(1_A,x) and F(I)=I.

Suppose A has a simple summand M_r whose origin representation β(a)=G(a,I) has multiplicity one on a nonzero rank-r projection Q. Here a is supported only on that summand; β(M_r)=Q M_D Q, and β(1_{M_r})=Q. Other auxiliary summands can have arbitrary allowed dimensions and multiplicities.

Then there is a fixed partition L,R of the original queries such that, coefficientwise,

    G(a,x)=F_R(x_R) β(a) F_L(x_L),                 (1)
    F_L=F(x_L,I_R),  F_R=F(I_L,x_R).

In addition, for every original unitary tuple,

    F_R† F F_L† Q=Q,
    Q F_R† F F_L†=Q.                              (2)

Equivalently, the active auxiliary coefficient has moving input and output supports

    Π_L(x_L)=F_L† Q F_L,
    Ω_R(x_R)=F_R Q F_R†,

and the target agrees with the group-cut piece there:

    F Π_L=F_R Q F_L=Ω_R F.                         (3)

Neither Q nor Π_L is assumed to reduce any original single. Empty L or R is allowed. The conclusion does not assert a factorization of the whole boundary when 0<Q<I.

### 1. The active block has a unique orientation against each query

Fix the other original queries to a unitary tuple u, and normalize the auxiliary/query two-port restriction by F_0=F(I_i,u) on the right. Its auxiliary single is a unital representation of A; the selected central block retains rank r and multiplicity one at every context. This follows from continuity of the represented central projection's integer rank on the connected spectator unitary space; equivalently, finite-dimensional representation multiplicities are locally constant.

The complete finite-C*-algebra bipartite theorem gives a comparison projection P commuting with both singles. On the selected irreducible auxiliary block P is scalar, either 0 or I. Therefore its active coefficient obeys exactly one of

    G(a,x_i,u)=G(a,I_i,u) F_0† F(x_i,u),            (L_i)
    G(a,x_i,u)=F(x_i,u) F_0† G(a,I_i,u).            (R_i)

The comparison on the complementary auxiliary blocks need not be scalar and is not used.

If both active identities held at one context, the original unital M_{d_i} representation would commute with the full matrix algebra on the selected rank-r carrier. It would then reduce that carrier and restrict there to a scalar unital representation. No scalar unital *-representation of M_{d_i}, d_i>1, exists. Thus the two active identities are disjoint even when r=1.

Each identity locus is closed, they cover the connected spectator unitary space, and they are disjoint. Hence one holds globally. This gives the fixed partition L,R without needing a continuous choice of comparison projectors on the complement.

### 2. Two recovery orders isolate a scalar only on Q

Telescoping L first then R, and R first then L, as in the full-boundary theorem gives

    G(a,x)=F F_L† β(a) F_L
          =F_R β(a) F_R† F.

Hence C=F_R† F F_L† commutes with every β(a). A unitary commuting with Q M_D Q has the form

    C=c(x)Q ⊕ C_perp(x),

with c a continuous scalar phase. No condition is imposed on the complementary unitary C_perp. In particular,

    G(a,x)=c(x) F_R β(a) F_L.                      (4)

Removing c is necessary even though Q is proper and generally moves under the original queries. The determinant proof for a full-boundary block cannot simply be applied to Q, because the one-query singles need not reduce it.

### 3. Elementary proportional-linear-map lemma

Let L,M:M_d(C)→V be complex-linear maps into any finite-dimensional complex vector space. Suppose L has linear-image dimension at least two and, for every unitary U, M(U)=c(U)L(U). Then M=λL for a constant scalar λ.

For any two coordinate functionals on V, the corresponding 2-by-2 minor of (L(U),M(U)) is a complex polynomial in the entries of U and vanishes on U(d). This makes it identically zero on M_d(C). A self-contained density justification is: choose a real Hermitian basis H_1,...,H_{d²}; the holomorphic map (z_j)↦prod_j exp(i z_j H_j) has invertible derivative at zero. The polynomial composed with this map vanishes for all real z near zero, hence by successive one-variable analytic continuation for all complex z near zero. The holomorphic inverse-function theorem then makes the polynomial zero on an open neighborhood of I, hence everywhere.

Thus L(A),M(A) are proportional for every matrix A. Choose A,B whose L-images are independent. Comparing A,B,A+B makes their proportionality constants equal. Every other nonzero L-image is independent of one of these, so has the same constant. If L(C)=0, compare C+A and C+B to obtain M(C)=0. Hence M=λL.

### 4. Apply the lemma to remove the proper-block phase

Fix every query except x_i=U and choose the active input a=1_{M_r}. Both sides of (4), without the scalar, are complex-linear maps of U:

    M(U)=G(1_{M_r},U,u),
    L(U)=F_R Q F_L.

The linear image of L has dimension at least two. For i∈L, after removing fixed invertible factors it is U↦Q rho(U), where rho is a unital representation of M_{d_i}; for i∈R it is U↦rho(U)K for a fixed nonzero matrix K. Such a nonzero left or right M_{d_i}-module cannot have dimension one. Explicitly, dimension one would imply Q rho(x)=λ(x)Q or rho(x)K=λ(x)K, with λ(1)=1; multiplying x,y would make λ a scalar unital representation of M_{d_i}, impossible for d_i>1.

The lemma therefore makes c(U,u) constant in U. The proportionality scalar is defined uniquely because L(U) has rank r at every unitary U. Applying this to each original variable makes c constant everywhere, and c(I)=1 gives c=1. Equation(1) follows. The commutant expression for C then gives (2), and multiplication by the appropriate factors gives (3).

The coefficient identity (1) extends to all independent private ancillary systems. The moving-support expressions are consequences at unitary tuples; no arbitrary merger of the before or after queries is used.

### 5. Exact necessary cut spaces for a fixed target

For each partition define the fixed subspace

    K_L = intersection_{unitary x} ker(F_R(x_R)† F(x) F_L(x_L)†−I).

Any multiplicity-one auxiliary branch with before-set L has Q≤projection(K_L). An exact finite list of query contexts yields a rigorous upper bound on K_L. A zero bound rules out that orientation of the branch. A nonzero finite-test bound is not yet equality with the all-context space or evidence of a host.

The quartet computation is in [auxiliary_supported_cut_spaces.py](../auxiliary_supported_cut_spaces.py). It first intersects all exact Pauli cross-pair constraints, then tests surviving vectors against all higher-party Pauli contexts. Its output is explicitly labeled a finite-context upper bound. Any claimed surviving carrier will need a parameter-level proof before being called exact.

### Limits

Multiplicity one is material. If the active block has multiplicity greater than one, its comparison can be a nontrivial projection on that multiplicity space, and simultaneous active orientations can occur without forcing a scalar original representation. This proof does not cover that case.

This theorem gives a supported cut for an actual auxiliary block after the other auxiliaries are fixed. It neither deletes a vertex nor assumes Q is a native sector at another vertex. It does not imply arbitrary-host nonroutability.

### Later exact quartet completion

The positive cut spaces have since been proved for all parameters and all private ancillary dimensions in [RG-053: Exact quartet cuts and an interior complete extension](auxiliary-interfaces.md#rg-053). The exact proper cut spaces are S1,S2,E3,E4 for singleton-before sets, K12=I12 tensor |−,1><−,1|34 for before={1,2}, and zero for the other nine proper sets. The proof combines the exact finite upper bounds with the parameter-level cylinder-cut lemma; no positive finite-test bound is being promoted without a lower-bound proof.

### Complete phase-mask sufficiency

### 4. Phase-mask sufficiency and ancillary systems

The four physical source carriers are orthogonal rank-two own-factor cylinders, and E_jC_g=0 for j≠i(g). The proposed serial identity is correct:

    F_raw(U) C_g = U_bar_i R_i U_i C_g.

Its derivation moves only the own output Z_i through U_bar_i and the own query U_i through E_i. It does not commute E_i or R_i with spectator queries.

The original verifier contains an empty `pass` loop where a direct coefficient check is described. This is a checker omission, not a proof flaw: the preceding structural facts already support the written algebraic derivation. The independent checker fills this gap by verifying all four identities symbolically with sixteen unconstrained complex matrix entries, without invoking unitary equations.

Because U_i preserves C_g, its image under F_raw is independent of U_i and commutes with the own output-bit projection. Each proposed phase therefore preserves the corresponding image carrier. The four image carriers remain orthogonal by unitarity of F_raw, so arbitrary simultaneous real control phases preserve unitarity. Boundary row and column phases then yield the entire displayed 35-dimensional family, resolving the possible gap between infinitesimal necessity and finite-t sufficiency.

This also survives independent private ancillas: C_g is identity on its own qubit and every ancilla, U_i preserves that amplified cylinder, and U_bar_i excludes that own qubit. The proof uses coefficient identities and actual independent query operations, with no merged filler.

For a Boolean mask, torus unitarity makes its two coefficient pieces orthogonal partial unitaries. This also permits an independently ancillary-amplified two-sector phase input, so the stated complete phase-extension interpretation is consistent. It does not supply a routed realization.

<a id="rg-053"></a>

## RG-053 — Exact quartet cuts and an interior complete extension

**Statement.** All fourteen proper quartet cut spaces are exact; the nontrivial K12 cut supplies a complete M4 direct-sum C auxiliary extension.

**Status:** source-level result. **Scope:** An abstract complete tensor; RG-035 rules out using its specified phase as an actual native branch.

### 1. Result

For every partition L,R of the four original queries, write

    F_L=F(U_L,I_R),    F_R=F(I_L,U_R),
    K_L=intersection_U ker(F_R† F F_L†−I).

The exact all-unitary-context cut spaces are:

- L=∅ or L={1,2,3,4}: all C¹⁶
- L={i}: the canonical S_i, with ranks 4,4,2,2
- L={1,2}: the rank-four physical cylinder

      Q₁₂=I₁⊗I₂⊗|−><−|₃⊗|1><1|₄

- The other nine proper before-sets: zero

The minus ray in this projector is normalized. A new general cylinder lemma supplies an all-parameter lower bound; its subspaces match the independently audited finite Pauli upper bounds exactly. Thus the positive dimensions here are no longer merely finite-test survivors.

The Q₁₂ cut also supplies an explicit independently completely unitary native auxiliary extension with algebra M₄⊕C on the original sixteen-dimensional boundary. It is a process-tensor extension, not a routed host.

### 2. Normalized orthogonal-cylinder form

For the supplied quartet put

    δ_i(U_i)=Z_i U_i Z_i−U_i,
    W=product_i U_i.

The exact normalized tensor is

    F(U)=W+sum_i U_bar_i δ_i(U_i) E_i.              (1)

Here U_bar_i is simply the product of the independent original query matrices except i. It does not denote an enlarged native operation.

To derive (1), multiply the given raw formula by D₀. Orthogonality of the E_i and the own-factor relation `[E_i,Z_i]=0` give `E_iD₀=Z_iE_i`. The two terms containing WZ_i cancel, leaving `(Z_i W Z_i−W)E_i=U_bar_i δ_i E_i`. No spectator commutation through E_i is assumed.

Fixing queries outside L to identity removes their δ terms, so

    F_L=W_L+sum_{i∈L} W_{L\i} δ_i E_i.            (2)

### 3. Physical-cylinder cut lemma

Let Q be any projection satisfying

    [Q,U_i]=0 for every physical query matrix at every i∈L,
    E_jQ=0 for every j∈R.

Equivalently, Q is a physical L-cylinder annihilated by all after-query supports. Then Q⊆K_L, including under arbitrary independent private ancillary systems.

For j∈R, projector orthogonality and (2) give the coefficient identity

    F_L E_j=W_L E_j.

Taking adjoints, using the cylinder commutation, and then E_jQ=0 gives

    E_j F_L†Q=E_j W_L†Q=E_jQ W_L†=0.              (3)

The full tensor decomposes as

    F=W_R F_L+sum_{j∈R} U_bar_j δ_j E_j.

At unitary query tuples, (3) and unitarity of F_L therefore imply

    F F_L†Q=W_RQ=F_RQ.                            (4)

Left multiplication by F_R† proves `F_R† F F_L†Q=Q`. The middle matrix is unitary, so Q is fixed pointwise and its orthogonal complement is invariant as well. Thus also `QF_R† F F_L†=Q`.

Every step remains true with independent private ancillas. Q is tensored with identity on all of them and still commutes with the before-query operations. Each E_j is also tensored with those identities. The F_L amplification is unitary, and the displayed algebraic identities use only the actual independent query operations.

The lemma is sufficient in general. It is not asserted that every target's group-cut space must be a physical cylinder.

### 4. Matching all fourteen proper upper bounds

For a fixed proper L, the largest physical L-cylinder annihilated by every E_j, j∈R, is

    Q_L = I_L ⊗ projection ker( sum_{j∈R} Tr_L E_j ).

Partial-trace positivity establishes the annihilation condition; the checker additionally verifies every `E_jQ_L=0` directly. The parameter lemma proves `ran(Q_L)⊆K_L`. The independently reconstructed Pauli constraints prove `K_L⊆K_L^Pauli`.

[continuous_product_supported_cut_audit_all_cylinders.py](../continuous_product_supported_cut_audit_all_cylinders.py) computes Q_L exactly for every proper partition and checks that its range equals the previously certified Pauli upper space. Hence both inclusions are equalities.

For the four singleton cuts these are exactly the previous canonical cylinders:

- S₁=I₁⊗|0><0|₂⊗projection span{|+,0>,|1,−>}₃₄
- S₂=I₂⊗projection span{|0,0,1>,|1,−,+>}₁₃₄, with the factors placed in their original order
- S₃=E₃ and S₄=E₄

For L={1,2}, the E₃ constraint forces the remaining fourth factor to 1 and the E₄ constraint forces the third factor to −, giving Q₁₂. For the other nine proper cuts the largest cylinder is zero and matches the independently established zero upper bound.

In addition to this structural proof, [continuous_product_supported_cut_audit_parameter.py](../continuous_product_supported_cut_audit_parameter.py) verifies the Q₁₂ cut directly with sixteen unconstrained complex query matrix entries. It substitutes `U_i†=adj(U_i)/det(U_i)` for i=1,2 and clears `det(U₁)det(U₂)`. The resulting polynomial vanishes on all four columns of Q₁₂. This is a separate exact symbolic identity, not a finite sample of angles.

### 5. The supports genuinely move

Take Q=Q₁₂ and define

    Π_L=F_L†QF_L,          Ω_R=F_RQF_R†.

The exact identities are

    FΠ_L=F_RQF_L=Ω_RF.

Here `F_RQ=W_RQ`, so `Ω_R=W_RQW_R†`. There is no assertion that Q reduces the normalized original singles at queries 1 or 2. In fact:

- With only query1=X, `||Π_L−Q||_HS²=3` and its difference has rank 4
- With only query2=X, `||Π_L−Q||_HS²=4` and its difference has rank 4

The exact overlaps are

    tr(E₁Q)=1/2,    tr(E₂Q)=1,    E₃Q=E₄Q=0.

Thus this carrier is not a residual sector orthogonal to every original support, and it must not be treated as a fixed input sector under the before queries.

### 6. A positive M₄⊕C auxiliary extension

Regard `Q M₁₆ Q` as M₄, with identity Q. For a supported active matrix a and scalar b define

    G(a⊕b,U)
       = F_R a F_L + b [F−F_R Q F_L].             (5)

This is multilinear in the auxiliary input and every original query. The before/after partition is disjoint, so no query is duplicated in the first term. At `a=Q,b=1` it is F, while at the all-identity original context

    G(a⊕b,I)=a+b(I−Q).

The origin auxiliary representation therefore has a multiplicity-one M₄ block on Q and a scalar passive block with multiplicity 12.

For unitary a on Q, the active term in (5) is a partial unitary from Π_L to Ω_R. The remaining term is

    F−F_RQF_L=F(I−Π_L),

a partial unitary from the complementary input to the complementary output. These supports are orthogonal, proving unitarity for every independent a and scalar unitary b.

The same proof covers an arbitrary auxiliary private ancilla. The active input is an arbitrary unitary on Q⊗A_aux; the passive input is an independent arbitrary unitary on A_aux. The latter commutes with all original-query operators and their support projections. Both pieces retain the orthogonal moving input/output supports, tensored with I_aux. The cylinder lemma already holds with all original private ancillas, so this proves complete independent unitarity of (5).

The checker also exercises a genuinely ancillary active input: an 8-by-8 SWAP couples the active M₄ block to its own qubit ancilla, while the passive scalar block independently receives Pauli Y on that ancilla. With four rational mixed query rotations, the resulting 32-by-32 unitary identity is checked exactly.

Any fixed nonzero subprojection of Q similarly yields an M_r⊕C auxiliary extension for 1≤r≤4, using the same cut identity. This is an existence statement about native process tensors, not about routed realizations.

The passive twelve-dimensional coefficient in (5) is essential. It contains the target's complementary dynamics and has not been replaced by an ordinary serial circuit. Thus (5) does not by itself construct a host for F or remove the unresolved complementary problem.

### 7. Exact phase covariance

Activate the auxiliary with `a=zQ,b=1`, where |z|=1, and put

    K_z=I+(z−1)Q.

After right normalization by K_z†, the resulting process has precisely the same formula (1), with

    E₁(z)=K_zE₁K_z†,    E₂(z)=K_zE₂K_z†,
    E₃(z)=E₃,          E₄(z)=E₄.                 (6)

Indeed Q commutes with the physical before-query matrices, so

    F_RQF_L = WQ + sum_{i∈{1,2}} U_bar_i δ_i Q E_i.

Substitute this into `F+(z−1)F_RQF_L` and multiply by K_z†. The before terms become `U_bar_iδ_iK_zE_iK_z†`; the after terms are unchanged because E_jQ=0. This proves (6) coefficientwise. The checker verifies the full symbolic identity for sixteen unconstrained complex query entries and arbitrary nonzero complex z, using K_z^{-1}; on the unit circle that inverse is K_z†.

At z=−1 the first spectator projector becomes fully product:

    E₁(−1)=I₁⊗|0><0|₂⊗|0><0|₃⊗|+><+|₄.

The second spectator vector, on factors 1,3,4, becomes the normalized version of

    2|0,1,1> + |1,−,−>.

Its three local Schmidt ranks are still 2,2,2. E₃,E₄ are unchanged. The first Bell spectator has been removed, but the second entangled support remains. In fact this phase family acts only on factors 3,4, so it cannot eliminate E₂'s entanglement across factor 1 versus factors 3,4.

This is exact process-tensor covariance. There is no claim that activating or absorbing this auxiliary preserves the existence of a routed graph, or that the transformed quartet is equivalent for graph realization purposes.

### 8. Certificates and scope

- [continuous_product_supported_cut_audit_all_cylinders.py](../continuous_product_supported_cut_audit_all_cylinders.py) and `_checks.json`: all fourteen exact proper cut spaces, via parameter lower bounds plus exact upper bounds
- [continuous_product_supported_cut_audit_parameter.py](../continuous_product_supported_cut_audit_parameter.py) and `_checks.json`: structural identities, separate determinant-cleared direct identity, and genuine auxiliary-ancilla unitary test
- [continuous_product_supported_cut_audit_covariance.py](../continuous_product_supported_cut_audit_covariance.py) and `_checks.json`: overlaps, moving-support witnesses, full phase covariance, and transformed local ranks

All checks use the original dimension-16 fixtures. The host-wide necessary consequence applies to multiplicity-one auxiliary summands as proved in [RG-052: Multiplicity-one supported-cut theorem](auxiliary-interfaces.md#rg-052); multiplicity greater than one remains outside that theorem. Neither the complete cut-space classification nor the positive native interface supplies a routed host or settles the universal problem.

<a id="rg-054"></a>

## RG-054 — Multiplicity-free auxiliary classification

**Statement.** Multiplicity-free auxiliary classification

**Status:** source-level result. **Scope:** All auxiliary branches have multiplicity one; repeated-multiplicity extensions are outside the theorem.

### Statement

Let G(a,x) be an actual complete auxiliary extension of the normalized quartet F, with a finite-dimensional native algebra A=⊕_b M_{r_b}, G(1_A,x)=F(x). Assume every represented simple summand is used and has multiplicity one at the identity origin. Write β(a)=G(a,I) and Q_b=β(1_b). Thus rank Q_b=r_b and the Q_b form an orthogonal partition of I16.

Equivalently, for a reachable-reduced native vertex, its total practical branch dimension Σ_b r_b saturates 16. This includes a full M16 vertex, but also arbitrary multiplicity-free direct-sum algebras and sixteen scalar branches.

Exactly one of the following tensor forms occurs:

1. **Entirely future:** G(a,x)=β(a) F(x)
2. **Past plus serial one-query pieces:** the native simple blocks partition into A_0,A_1,...,A_4, with represented group identities Q_0,Q_1,...,Q_4, such that

       Q_i≤S_i,  [Q_i,α_i(M2)]=0  (i=1,...,4),
       Q_0=I−Σ_i Q_i,

   and

       G(a,x)=F(x) β(a_0)
               +Σ_i U_bar_i β(a_i) α_i(x_i).              (1)

Here S_i are the known mutually orthogonal serial carriers of ranks 4,4,2,2, and α_i(x)=R_i x_i R_i. Zero serial groups are allowed. The past group is always nonzero because Σ_i rank S_i=12<16. Individual simple blocks inside a serial group need not reduce α_i; the group projection Q_i does.

In particular, the genuinely dynamic before={1,2} carrier cannot appear as a block in a multiplicity-free auxiliary vertex. The positive M4⊕C extension from the supported-cut construction avoids this restriction because its passive C block is represented with multiplicity 12.

### 1. Group blocks by their supported-cut orientation

The audited multiplicity-one branch theorem gives each Q_b a unique before-set L_b and

    G(a_b,x)=F_{R_b} β(a_b) F_{L_b}.

The exact quartet cut-space classification permits only:

- L=∅, called the past group Q_p
- L={1,2,3,4}, called the future group Q_f
- L={i}, with Q_i≤S_i
- L={1,2}, with Q_12≤K_12=I12⊗|−,1><−,1|34

All nine other proper before-sets have zero cut space. Summing blocks with a common before-set gives orthogonal group projections whose sum is I.

At an arbitrary original unitary tuple, the represented central projections at the auxiliary's input and output are respectively

    Π_L=F_L† Q_L F_L,
    Ω_L=F_R Q_L F_R†.

Each family is an orthogonal partition of I, since the normalized auxiliary one-port map is a unital representation. This is an actual native-vertex constraint, not a supposition that arbitrary supported cuts combine into one extension.

### 2. Past and future groups cannot coexist

If Q_p and Q_f were both nonzero, output orthogonality would give

    Q_f F(x) Q_p=0

for every original unitary tuple. Multilinearity then gives this identity on every coefficient of F.

Those coefficients span all of M16. Indeed the raw row formula is

    row_o F_raw(x)=row_o(⊗_i x_i) V_o,

and V_oD0 is invertible for each o. Fixing an output row o and varying the sixteen original input matrix-unit columns therefore spans the entire o-th row space. The resulting 256 coefficient matrices span M16.

No two nonzero projections Q_p,Q_f can satisfy Q_f M16 Q_p=0. Hence Q_p=0 or Q_f=0.

### 3. Two finite exact linear systems

Choose any rational full-column matrices B_i spanning S_i, and B_12 spanning K12. Write each unknown supported operator as

    Q_i=B_i X_i B_i†,  Q_12=B_12 X_12 B_12†.

For the linear calculations, X_i need not yet be Hermitian, positive, or idempotent. There are 4²+4²+2²+2²+4²=56 complex coordinates. Imposing necessary identities on this larger linear space can only weaken the constraints, so the rank bounds are valid for actual projections.

#### No future group: input conservation

If Q_f=0, differentiating Σ_L Π_L=I at the identity context gives

    [α_1(h),Q_1+Q_12]=0,
    [α_2(h),Q_2+Q_12]=0,
    [α_3(h),Q_3]=0,
    [α_4(h),Q_4]=0                                  (2)

for h=X,Y,Z. The exact rational constraint matrix has rank 46 and kernel dimension 10. Its kernel is precisely

    Q_12=0,
    Q_i∈S_i α_i(M2)' S_i,

with component dimensions 4,4,1,1. No positivity or projector equation is needed for this conclusion.

#### No past group: output conservation

If Q_p=0, for every allowed proper cut we have F_R Q_L=W_R Q_L. This follows from Q_L≤K_L and the cylinder lemma: every omitted-query support E_j annihilates K_L. Therefore differentiating Σ_L Ω_L=I gives

    [h_1,Q_2+Q_3+Q_4]=0,
    [h_2,Q_1+Q_3+Q_4]=0,
    [h_3,Q_1+Q_2+Q_4+Q_12]=0,
    [h_4,Q_1+Q_2+Q_3+Q_12]=0                       (3)

for physical h_i=X_i,Y_i,Z_i. The exact rational constraint matrix has rank 56. Its kernel is zero. Hence every proper-cut group vanishes and Q_f=I.

[auxiliary_multiplicity_free_exact.py](../auxiliary_multiplicity_free_exact.py) builds these systems directly from the portable quartet supports, computes their exact rational nullspaces, verifies the two ranks, and checks every past-kernel generator has zero Q12 component and commutes with its claimed original α_i. Y-commutator equations are divided by i only to keep all coefficients rational. The report is [auxiliary_multiplicity_free_exact_checks.json](../auxiliary_multiplicity_free_exact_checks.json).

These are necessary first-derivative identities at one origin, used to establish an exact linear upper bound. The conclusion does not extrapolate sampled positivity or unitarity to parameters. The full parameter identities follow from the branch theorem once this finite linear elimination fixes the permitted supports.

### 4. Assemble the tensor form

If Q_f≠0, Section2 gives Q_p=0 and the output calculation makes Q_f=I. Every auxiliary block is in the future group, so G=β(a)F.

If Q_f=0, the input calculation removes Q12 and makes each Q_i reduce α_i. The remaining past group is Q_0=I−Σ_iQ_i. The branch theorem gives G_0=Fβ(a_0), and for a serial group

    G_i=F_{bar_i} β(a_i) α_i(x_i)
       =U_bar_i β(a_i) α_i(x_i),

because β(a_i) is supported on S_i, where F_{bar_i}=U_bar_i. This is (1), coefficientwise and under every independent private-ancilla amplification.

Conversely the displayed form is completely unitary for arbitrary independent unitary native inputs whenever the stated orthogonal reducing supports and block representations are used: it is an orthogonal-column promotion with arbitrary unitary actions on the serial columns and an arbitrary unitary on the residual past columns. This converse is a tensor construction, not a routed realization.

### Exact scope

This substantially constrains auxiliary vertices whose represented simple blocks all have multiplicity one. It leaves auxiliary vertices with any repeated simple-block representation unclassified. For example, a scalar branch of rank greater than one is not multiplicity one even though its native matrix size is only one.

The formula permits algebraic absorption into boundary/serial operations in a tensor expression. It does not prove that moving, merging, or deleting the corresponding graph vertex preserves bi-univocality, weak loops, or independent native filler freedom. No such graph rewrite is assumed here.

<a id="rg-055"></a>

## RG-055 — Strict full-matrix boundary rigidity

**Statement.** Every nontrivial full M_r auxiliary on the D16 quartet boundary is boundary multiplication when all original-query comparisons have fixed strict orientations.

**Status:** source-level result. **Scope:** All r dividing 16; ten spectral and four scalar-commutant certificates. This subsumes the M4 strict and full-M16 special cases.

### Statement and hypothesis

Let G(a,U) be an independently private-ancilla-complete multilinear extension
of the normalized quartet F on its original dimension-16 boundary, with one
unital full matrix auxiliary M_r, r>1. Suppose one fixed strict before/after
orientation is valid for each original query at every spectator context.
Then G is exactly F(U)beta(a) or beta(a)F(U), where beta(a)=G(a,I).

This is an abstract complete-extension theorem with a strict-orientation
hypothesis. It neither assumes nor proves that every routed auxiliary has
such orientations. A unital M_r representation in M16 implies r divides16,
so r=2,4,8,16 are the only nontrivial cases.

### 1. A fixed proper partition would put every cocycle in one commutant

For the global strict partition L,R, the two audited telescoping identities
imply

    C_L(U)=F_R(U_R)* F(U) F_L(U_L)* in beta(M_r)'.

The commutant is unitarily conjugate to I_r tensor M_(16/r). Thus every
eigenvalue of every C_L(U) has multiplicity divisible by r, and beta(M_r)
must commute with the ENTIRE family of C_L(U). Both are exact necessary
conditions at scalar-unitary contexts; one counterexample suffices.

The empty-side partitions directly give the two boundary formulas. It remains
to exclude the fourteen proper nonempty subsets L.

### 2. Ten partitions have an odd spectral multiplicity

The real Pauli representatives I,X,Z,XZ give exact odd-multiplicity witnesses
for

    {1}, {3}, {4}, {1,3}, {1,4}, {3,4}.

One typical scaled characteristic polynomial is

    (x+64)^2 (x−64)^8
    (x²+64x+4096)
    (x⁴+64x³+4096x²+262144x+16777216),

where the last two factors are squarefree and occur with exponent one. The
certificate gives the precise four-query tuple for each partition.

The rational SU2 matrices

    q(a,b,c,d)=(a I+i b X+c XZ+i d Z)/5,

using the Pythagorean quadruples (1,2,2,4), (2,1,4,2), (2,4,1,2), (4,2,2,1)
at the four queries, supply an odd multiplicity for the further partitions

    {2}, {2,3}, {2,4}, {1,2}.

All matrix entries are Gaussian rationals. The characteristic polynomials
are computed after clearing a positive real denominator. Exact squarefree
decomposition over Q(i) records a factor of odd multiplicity. Because
characteristic zero polynomials are separable after squarefree reduction,
its complex roots have exactly that multiplicity. Every nontrivial allowed
r is even, so each such witness excludes beta(M_r)' for every r>1.

The finite witness certificates are [strict_auxiliary_cocycle_spectral_test_checks.json](../strict_auxiliary_cocycle_spectral_test_checks.json)
and [strict_auxiliary_cocycle_generic_spectral_test_checks.json](../strict_auxiliary_cocycle_generic_spectral_test_checks.json). Their use is
negative and exact, not a numerical inference about a generic parameter.

### 3. The four remaining cocycle families have scalar common commutant

For L equal to all queries except j, a single cocycle can have all spectral
multiplicities even. We instead intersect its necessary commutator equations
across finitely many original-query contexts.

[strict_auxiliary_last_query_commutant.py](../strict_auxiliary_last_query_commutant.py) begins with the real Pauli
contexts and adds two or three of the recorded rational-quaternion contexts.
For each j it saves255 independent rows from

    [X,C_L(U)]=0

in the256 unknown matrix entries of X. Independence is checked after exact
reduction from Gaussian rationals to the verified prime field F_1000033,
using a verified square root of −1 as the image of i. No denominator in the
selected contexts vanishes modulo that prime.

A nonzero modular minor is a nonzero Gaussian-rational minor. Thus the
characteristic-zero commutator rank is at least255. The identity matrix is
an explicit common kernel vector, giving the matching upper bound255. The
common commutant is exactly the scalars for all four remaining partitions.

No nontrivial full matrix algebra beta(M_r) can lie in that scalar commutant.
This excludes the remaining four cases without asserting that one chosen
normal cocycle must have a simple eigenvalue.

### 4. Conclusion and graph consequence

All proper strict partitions are excluded, so only boundary multiplication
survives. The tensor equality is obtained from the strict identities; it
therefore includes all independent private-ancilla amplifications.

For an ACTUAL one-branch quantum auxiliary in a routed quartet host, the
branch-centrality theorem consequently forces at least one nontrivial
comparison with an actual original-query native branch event if the auxiliary
is genuinely interior. The one-branch M8/M16 rank arguments forbid this
entirely. For M4 it can only be S1 or S2, requiring Q1=S1 or Q2=S2. For M2
it can select a rank-two or rank-four central active carrier in S_j.

The latter actual commuting events justify complete direct-sum refinements
of the auxiliary variable as in [RG-057: Actual M4 event refinement](auxiliary-interfaces.md#rg-057). Their
repeated-multiplicity residual blocks are not classified here. No graph
deletion, graph-refinement closure, or quartet host construction follows.

### Rank-four polynomial witness method

### 1. The remaining cocycle lies in an M4 commutant

The already audited two telescoping identities for a strict partition L,R
are

    G(a,U)=F F_L† beta(a) F_L
          =F_R beta(a) F_R† F.

Therefore

    C_L(U)=F_R† F F_L† belongs to beta(M4)'.

A unital M4 representation on D16 has multiplicity four. Its commutant is
unitarily conjugate to I4 tensor M4.

If L is empty or all four queries, C_L is I by its definition and the
corresponding identity is already pure boundary multiplication. Suppose
instead L,R are both nonempty and choose i in L and j in R. Set all other
queries to identity. Then the cocycle is

    C_ij(U_i,U_j)=alpha_j(U_j)† F_ij(U_i,U_j) alpha_i(U_i)†.

### 2. A rank-four element of this commutant obeys a rigid polynomial

If D belongs to a unital M4 commutant on D16 and rank D=4, write it up to
unitary conjugacy as I4 tensor d. Then rank d=1. Every rank-one matrix obeys
`d²=Tr(d)d`, so

    4D²=Tr(D)D.                                        (1)

This requires no normality assumption. Unitary cocycles happen to make
D=C_ij−I normal, but that extra fact is not needed.

### 3. Exact crossing-pair witnesses

For every ordered pair i!=j, choose

    U_i=(3I+4iX)/5, U_j=X,

except for (i,j)=(3,4), where use `U_i=(3I+4iY)/5`.
The independent checker uses the exact cylinder fixtures and the raw
right-normalized quartet formula. It verifies, after exact simplification,

    C_ij†C_ij=I,
    rank(C_ij−I)=4,
    4(C_ij−I)²−Tr(C_ij−I)(C_ij−I) != 0.

The squared Hilbert–Schmidt norms of the last defect are positive rationals;
the JSON records their exact values and a nonzero matrix entry for all
twelve ordered pairs. No numerical spectral multiplicity or sampled-rank
inference is used.

Thus C_ij cannot belong to beta(M4)' for ANY origin embedding of M4. Every
proper partition has a crossing pair and is excluded. Only the two empty-
side partitions survive, proving the statement coefficientwise and hence
with all independent private-ancilla amplifications.

### Full-boundary scalar-removal method

### 1. Every auxiliary/query comparison has a unique scalar side

Fix the other original queries to arbitrary unitaries u. Put F_0=F(I_i,u) and normalize the resulting two-port process on the right by F_0†. Its auxiliary single is a unital representation of M_D on C^D, hence its image is all M_D.

The complete bipartite unitary-process theorem gives a comparison projection in the joint commutant of the two singles. Since the auxiliary image is all M_D, this projection is 0 or I. The two resulting possibilities are exactly

    G(A,x_i,u)=G(A,I_i,u) F_0† F(x_i,u)             (L_i)

or

    G(A,x_i,u)=F(x_i,u) F_0† G(A,I_i,u).            (R_i)

They cannot both hold as coefficient identities: that would make the nontrivial M_{d_i} single commute with all of M_D. A unital representation of M_{d_i}, d_i>1, is faithful and not scalar.

The set of spectator unitary contexts satisfying each identity is closed, since these are finitely many continuous matrix-coefficient equalities. They are disjoint and cover the connected product of spectator unitary groups. Each is therefore also open, so one side holds at every context. This fixes the partition L,R without choosing comparisons from a continuous family or making a generic-context inference.

### 2. Recover the complete auxiliary map in two orders

Write

    F_L=F(x_L,I_R),  F_R=F(I_L,x_R).

Turn on the L queries first using (L_i). Their right factors telescope, giving G(A,x_L,I_R)=A F_L. Then turn on the R queries using (R_i); their left factors telescope. This gives

    G(A,x)=F(x) F_L† A F_L.                        (2)

Turning on R first and L second instead gives

    G(A,x)=F_R A F_R† F(x).                        (3)

Equating (2),(3), and multiplying by F_R† on the left and F_L† on the right, shows that

    C(x)=F_R† F(x) F_L†

commutes with every A∈M_D. Thus C(x)=c(x)I, where c is a continuous unit-modulus scalar function of the original unitary tuple. Consequently

    F(x)=c(x) F_R F_L.

The scalar must be removed; it is not harmless for equality of the full tensor.

### 3. Exact removal of the scalar ambiguity

Let H(x)=F_R F_L. Since each original variable occurs in exactly one factor, H is itself multilinear and independently completely unitary preserving.

Fix all variables except x_i=U. Normalize the two one-query slices at U=I on the right:

    rho(U)=F(U,u)F(I,u)†,
    sigma(U)=H(U,u)H(I,u)†.

Both are unital *-representations of M_{d_i} on C^D. They have the same multiplicity D/d_i, so

    det rho(U)=det sigma(U)=(det U)^(D/d_i).

But rho(U)=[c(U,u)/c(I,u)] sigma(U). Therefore

    [c(U,u)/c(I,u)]^D=1.

The ratio is continuous on the connected U(d_i) and equals 1 at I. It is identically 1. Thus c is independent of every original variable, and c(I,...,I)=1 proves c=1. This proves (1) on every unitary tuple. Multilinearity and unitary spanning give the full coefficient identity, hence every independent private-ancilla amplification.

<a id="rg-056"></a>

## RG-056 — Abstract M8 quotient method and actual unbranched rigidity

**Statement.** Every actual one-branch M8 auxiliary is boundary-only; the qubit-commutant quotient argument also gives the stated abstract scalar-commutant criterion.

**Status:** source-level result. **Scope:** Actual branch centrality removes the genericity condition for routed hosts. No graph deletion or proper-support M8 classification follows.

### Statement

Let a finite bi-univocal weak-loop routed host realize the exact normalized
quartet F on its original dimension-16 boundary, with the original queries
inserted once at native vertices through complete monopartite insertions.
Take an auxiliary native vertex with one globally reachable branch and
native algebra M8. Normalize its fixed filler into the variable, giving

    G(a,U), G(I8,U)=F(U), beta(a)=G(a,I), beta(I8)=I16.

Then its entire complete coefficient map is one of

    G(a,U)=F(U) beta(a),
    G(a,U)=beta(a) F(U).

This is an exact boundary-multiplication identity for its native variable.
It is not a proof that deleting, contracting, or relocating the actual graph
vertex preserves the routed certificate.

### 1. Branch-centrality forces scalar comparisons without genericity

The one-branch auxiliary has constant status and a singleton branch SCC.
Choose a topological order around that SCC. For each original native query
vertex j, the branch-centrality theorem applies with the auxiliary as its
single-branch query. The order comparison P_j is a sum of represented central
branch identities of the actual native query algebra A_j, and commutes with
the auxiliary image B=beta(M8).

At the quartet baseline the exhaustive native classification gives

    A_j=A_j^active direct_sum M2,
    Q_j<=S_j, rank(S_j)<=4.

A central projection of A_j is zero or identity on its simple passive M2
summand. Thus either P_j<=Q_j or I-P_j<=Q_j. Its rank is consequently at
most4 or at least12.

On the other hand B has multiplicity two in M16, so B' is isomorphic to M2
with physical rank-eight minimal projections. Every projection commuting
with B has rank0,8,16. The two rank restrictions force P_j=0 or I.

No orientation uniqueness is used. The comparison came from one fixed
topological branch split e_j. Reachable native faithfulness implies e_j=0
or1 whenever its represented projection is0 orI. Therefore every branch of
the actual query vertex j lies on the same side of the auxiliary in the
chosen ordering. The same branch split is valid after changing the other
original query fillers: no context-dependent choice is needed.

Equivalently, the normalized auxiliary/original-query identity has a global
strict orientation for every original query and every spectator context.
It may coincide with the opposite identity at commuting contexts; this
does not affect its existence or its fixed choice.

### 2. The existing cocycle proof now applies to every origin embedding

The already independently reviewed proof in
[RG-056: Abstract M8 quotient method and actual unbranched rigidity](auxiliary-interfaces.md#rg-056), Sections2–4, uses its former
generic hypothesis only to obtain these global strict orientations. The
remaining argument is independent of that hypothesis:

1. Telescope the chosen before/after query partition L,R in both orders
2. Obtain C(U)=F_R* F F_L* in the fixed commutant N=B'≅M2, with C=I on
   every one-query coordinate face
3. Apply the proved qubit-valued representation-quotient lemma: for two
   unital M2 representations whose unitary quotient lies in N, either they
   agree or both represented algebras lie in N
4. At most one distinct quartet origin factor alpha_i(M2) can lie in N
5. Analytic continuation makes C independent of every other query, and its
   coordinate-face identity removes the possible last dependence

Hence C=I, and

    F=F_R F_L, G(a,U)=F_R beta(a) F_L.

Every nontrivial L/R partition would give a strict ordered identity on each
crossing two-query face. The twelve exact Pauli order witnesses exclude all
such partitions. Therefore L or R is empty, giving one of the two stated
boundary coefficient maps.

Multilinearity makes the scalar-unitary coefficient identity an equality of
the full original-query tensor, and therefore of all independent private-
ancilla amplifications.

### What the graph information adds

The previous abstract complete-extension theorem needed a scalar origin
joint commutant between B and each original factor. Some aligned M8 embeddings
have extra rank-eight comparison directions and were left open. Here the
comparison must additionally be branch-central in the ACTUAL native query
port. Its active rank budget excludes rank eight. The graph therefore removes
every one of those exceptional comparison directions without resolving the
auxiliary multiplicity qubit into native branches.

One-branch native matrix dimensions must divide16. Combining this result
with the full-M16 theorem leaves only native M2 and M4 as possible genuinely
interior unbranched quantum auxiliaries. Scalar M1 is a global phase. Branched vertices, proper supports and smaller repeated multiplicities are not classified by this auxiliary theorem. The complete quartet host question is settled separately by [RG-001](obstruction.md#rg-001).

### Qubit-valued representation quotient lemma

### 3. Qubit-valued representation quotient lemma

Fix a tensor decomposition `H=C⁸⊗C²`, with `N=I₈⊗M₂` and `B=M₈⊗I₂`. Let ρ,σ:M₂→M₁₆ be unital *-representations. Suppose

    c(U)=σ(U)ρ(U)† ∈ N     for every U∈U(2).        (4)

Then either `σ=ρ`, or both represented algebras lie in N. The same conclusion holds when the quotient is `ρ(U)†σ(U)`, by taking inverses and adjoints.

#### 3.1 The cocycle-generated algebra

Let D be the unital C*-algebra generated by all c(U). The representation identities give

    c(UV)=c(U)ρ(U)c(V)ρ(U)†,
    ρ(U)c(V)ρ(U)†=c(U)†c(UV).

Thus ρ(U) normalizes D. A unital C*-subalgebra of N≅M₂ is scalar, a diagonal C⊕C, or all N.

If D is scalar, the determinant characters of ρ and σ coincide: both are eight copies of the defining M₂ representation. Hence `c(U)^16=1`. Continuity on connected U(2), with c(I)=1, gives c=I.

If D is diagonal, connectedness makes ρ(U) fix its two minimal projections rather than permute them. These projections have physical rank eight. Both ρ and σ reduce them, and each restricted M₂ representation has multiplicity four. Comparing determinants on each sector gives `c_k(U)^8=1`, so again c=I. This argument concerns a mathematical invariant subspace of two fixed representations; it does not grant an independent native filler on either sector.

#### 3.2 If D=N, a two-eigenvalue argument leaves only one active factor

If D=N, ρ(U) normalizes N. Differentiating the induced automorphisms of M₂, whose derivations are inner, gives for every traceless Hermitian h∈M₂

    ρ(h)=A_h⊗I₂+I₈⊗B_h,

with A_h,B_h traceless Hermitian and linear in h. Equivalently this follows by locally implementing the automorphism of N with a unitary on its second factor and observing that the remaining unitary lies in B.

A nonzero traceless h has exactly two eigenvalues ±r, and so does ρ(h). If both A_h and B_h were non-scalar, their Kronecker sum would have at least three distinct eigenvalues: the minimum, maximum, and `min spec(A_h)+max spec(B_h)`, which lies strictly between them. Hence for every h, either A_h=0 or B_h=0.

Two proper real linear kernels cannot cover the three-dimensional space of traceless Hermitian h. It follows that either all A_h vanish or all B_h vanish. Thus ρ(M₂) lies entirely in N or entirely in B.

In the first case, (4) puts σ(M₂) in N as well. In the second case, ρ commutes with N, so c becomes an ordinary continuous unitary representation. For a traceless Hermitian h write

    c(exp(it h))=exp(it k_h).

Differentiation gives `σ(h)=ρ(h)+k_h`, with k_h traceless Hermitian in N. The same two-eigenvalue argument forces k_h=0, since ρ(h) is non-scalar in B. The central one-parameter group has c(exp(itI))=I directly from unitality of both representations. Therefore c is trivial and σ=ρ. This completes the lemma.

### 4. Remove C without resolving the multiplicity qubit

At most one of the four origin factors α_i(M₂) can lie in N. If two did, each would equal the four-dimensional algebra N, whereas the quartet factors are distinct. Exact distinctness is especially simple here: `α_i(Z)=Z_i`, and for i≠j this operator is Hilbert–Schmidt orthogonal to the entire algebra α_j(M₂).

Fix any i whose origin factor is not contained in N. Hold every other query unitary fixed.

If i∈L, write

    F_L(U)=ρ(U)F_L(I),
    τ(U)=F_R†F(U)F_L(I)†,
    C(U)=τ(U)ρ(U)†.

Put C₀=C(I). Then `σ(U)=C₀†τ(U)` and ρ(U) are unital *-representations of M₂, and

    σ(U)ρ(U)†=C₀†C(U)∈N.

If i∈R, use instead

    F_R(U)=F_R(I)ρ(U),
    τ(U)=F_R(I)†F(U)F_L†,
    σ(U)=τ(U)C₀†,
    ρ(U)†σ(U)=C(U)C₀†∈N.

All these normalizations are by fixed unitaries for the chosen one-query slice. At the all-identity spectator context, ρ=α_i, whose image is not contained in N. The same remains true on a neighborhood. The quotient lemma therefore gives `C(U,u)=C(I,u)` there. Real analyticity on the connected full unitary context space extends this independence from x_i globally.

Thus C is independent of every original variable except possibly the single one whose factor lies in N. Equation (3) removes that final dependence as well. Consequently C=I identically.

We have proved the full group factorization

    F=F_R F_L,       G=F_R β(a)F_L.

Every nontrivial partition is excluded by the quartet's twelve exact ordered-pair witnesses in [auxiliary_full_boundary_checks.json](../auxiliary_full_boundary_checks.json). Therefore L or R is empty, proving (1). Multilinearity extends the result to the entire coefficient tensor and hence to its independent private-ancilla amplifications.

### Abstract genericity test and aligned exceptions

### 5. Exact nonempty open set and aligned exceptions

The companion checker expresses a traceless basis of N as three Hermitian matrices and forms, for each original i, the linear map

    n ↦ ([n,α_i(X)],[n,α_i(Y)],[n,α_i(Z)]).

Rank three is exactly condition (H) for that i. For `N=α₃(M₂)`, all four ranks are three. A second rational witness, obtained by conjugating a physical qubit algebra by the real Householder reflection in v=(1,2,...,16), also has all four ranks three.

These rank conditions are open. In unitary-conjugacy coordinates for N, failure is the zero set of analytic minors. The explicit common witness means those conditions are not identically zero. Since U(16) is connected, their simultaneous full-rank locus is open dense. This is a statement about origin embeddings, not a probabilistic assumption about a hypothetical host.

For comparison, the exact canonical aligned cases give the following possible traceless origin joint-commutant directions:

- N=α₁(M₂): Z₁ against original3 and original4; none against originals1,2
- N=α₂(M₂): Z₂ against originals1,3,4; none against original2
- N=α₃(M₂): none against any original
- N=α₄(M₂): Z₄ against original3; none against originals1,2,4

These are allowable comparison directions only. No extension realizing a nontrivial direction is asserted. They do not classify arbitrary aligned factors N, and no commutation assumption is made for different directions in a general N.

<a id="rg-057"></a>

## RG-057 — Actual M4 event refinement

**Statement.** Actual S1/S2 comparison events give complete M4 direct-sum refinements and classify their multiplicity-one selected blocks.

**Status:** source-level result. **Scope:** Repeated complements remain unclassified; strict orientation is resolved by RG-055.

### 1. Only the actual rank-four query carriers can give a nontrivial comparison

Take an actual unbranched native M4 auxiliary in a quartet routed host. Its
unital origin image B has multiplicity four, so B' is M4 and every commuting
projection has physical rank a multiple of4. By branch-centrality, the
comparison with original native port j is <=Q_j or has complement<=Q_j.

For ports3,4 the rank bound2 forces a scalar comparison. For ports1,2 a
nontrivial comparison is possible only if Q_j=S_j has rank4; the comparison
is then S_j or I-S_j. No intermediate proper carrier is possible. The rank
argument makes no genericity assumption about the auxiliary embedding.

### 2. A nontrivial comparison supplies a real commuting event

Fix such j. Let e_j be the central sum of query-j branches selected by the
chosen topological before/after split. It is the active identity or its
complement. At the auxiliary's identity baseline, the audited original-query
native tensor gives the exact branch marker F(U)S_j. Hence its normalized
output projection is

    P_j(U)=F(U) S_j F(U)*.

The branch-centrality identity with the whole actual native query-j algebra
says this projection commutes with the normalized auxiliary image

    beta_U(a)=G(a,U) F(U)*.

This remains true after varying query j, because the central branch identity
commutes with its whole native representation. Consequently

    [ F(U)* G(a,U), S_j ]=0.                            (1)

The same argument applies to arbitrary independent private extensions: the
central event is S_j tensored with the private identities, and the native
branch-centrality argument is unchanged by these private input/output wires.
In particular, (1) is obtained in the complete setting, not by inferring a
free-word identity merely from a scalar-unitary equality of degree three.

### 3. Derived complete refinement

Define a new coefficient tensor on M4 direct_sum M4 by

    G_tilde(a direct_sum b,U)
       =G(a,U)S_j+G(b,U)(I-S_j).                        (2)

It is multilinear in the four original queries and linear in the new native
direct-sum variable. Let J_U(a)=F(U)*G(a,U). At every private context J_U is
a unital *-representation of M4, and (1) says it reduces the two displayed
constant input projections. For independently arbitrary unitary branch
fillers a,b, including their auxiliary private ancilla, the normalized
operator J_U(a)S_j+J_U(b)(I-S_j) is unitary: all cross terms vanish and each
diagonal term is the corresponding projection.

Thus (2) is genuinely independently ancillary-complete. Its diagonal
restriction a=b recovers the original one-branch slot. This refinement is
derived from a simultaneously available actual query-branch event. It is
not a generic rule that every multiplicity can be split into native branches.
It is a complete process tensor; no routed realization of the refined slot
is claimed.

If both S1 and S2 arise as nontrivial comparisons, they are orthogonal and
both commute with J_U. The same argument gives an M4 direct_sum M4
direct_sum M4 refinement on constant carriers S1,S2,I-S1-S2, with origin
representation multiplicities1,1,2. With only one such carrier the
multiplicities are1,3.

### 4. The refined rank-four block has only a past or serial placement

The S_j block in (2) is a full M4 representation with multiplicity one and
fixed-past central coefficient F(U)S_j. Apply the audited proper-block cut
theorem and exact cut-space classification. The rank-four support S_j can
fit only an empty before set, the singleton before set {j}, or the full
before set. Other proper cut carriers are either orthogonal, smaller, or
the distinct rank-four Q_{12}.

The full-before placement would give G_active(a,U)=beta(a)F(U). At its
identity a=I4 this would imply F(U)S_j=S_j F(U) for all U. The audited full
matrix coefficient span of F makes its commutant scalar, excluding the
proper nonzero S_j. Therefore the refined active coefficient is either

    F(U) beta(a) S_j,

or

    U_bar_j beta(a) S_j alpha_j(U_j).

The first is a past insertion, the second the genuine single-query serial
column insertion. The original graph comparison fixes which is consistent
with the relative j/auxiliary order. The repeated-multiplicity complement
has not been classified or assumed removable.

### Scope of this method

If every original-query comparison is scalar, the original M4 auxiliary
has a fixed strict before/after partition and an M4-valued multiplicity
cocycle. The strict full-matrix theorem [RG-055](auxiliary-interfaces.md#rg-055) excludes an interior auxiliary in that case. If nontrivial comparisons occur, the remaining rank12 or rank8
representation still has multiplicity3 or2. These are actual residual
mathematical cases, not omitted graph assumptions.

### Required proof qualifications

Private completeness of the refinement comes from the actual branch-central identity after independent amplification, not from promoting a scalar cubic commutator. The selected original central event commutes with the entire native representation at every spectator context.

<a id="rg-058"></a>

## RG-058 — Actual M2 event refinement

**Statement.** An interior actual unbranched M2 auxiliary has a rank-two or rank-four actual commuting event and the resulting complete direct-sum refinement.

**Status:** source-level result. **Scope:** A rank-two selected block is past or serial; rank-four blocks and repeated complements are not classified.

### 1. An actual nontrivial comparison is unavoidable

Let a one-branch native M2 auxiliary of a valid routed quartet host have
coefficient map G(a,U), with G(I,U)=F(U), on the original D16 boundary.
Its origin representation has multiplicity eight. Choose one fixed
branch-SCC topological ordering around its constant-status singleton.

Against every original native port j, graph branch-centrality supplies a
central native branch sum e_j. If all represented comparisons are0 orI at
the original baseline, reachable native faithfulness makes every e_j
literally0 or1. The same fixed branch sums then give global strict
orientations at every original spectator context. The now-audited
strict-oriented full-matrix theorem forces G to be boundary multiplication.

Consequently a genuinely interior G has a nontrivial branch-central
comparison at some original port j. The actual native port has one passive
M2 summand and an active ideal Q_j<=S_j. Taking either e_j or its complement
as necessary gives a central ACTIVE native event e with origin projection

    0<P=rho_j(e)<=Q_j<=S_j.

It commutes with the auxiliary origin M2. Every projection in the auxiliary
commutant has even physical rank, while rank S_j<=4. Hence rank P is2 or4.
For j=3,4 it is necessarily P=E_j. Rank4 is possible only for j=1,2 and
forces P=Q_j=S_j. A rank2 P at j=1,2 need not equal E_j or be a physical
own-factor cylinder.

### 2. The actual event yields COMPLETE reduction

Centrality at the original native port implies P reduces alpha_j. The exact
classified native marker, evaluated on the prescribed original filling, is

    C_e(U)=F(U)P.

This holds coefficientwise because P<=S_j and the active serial identity is
valid on S_j. It is not an inferred classical label at some new vertex.

Repeat the complete commutation proof from
[RG-057: Actual M4 event refinement](auxiliary-interfaces.md#rg-057): at each fixed spectator context,
the branch-central projection commutes with both normalized pair singles;
conjugating by the original j filler preserves the event. Attach arbitrary
independent private input/output wires and apply the same graph proof to
the same central native branch sum e tensor I. The resulting exact identity
is

    [F(U)†G(a,U), P tensor I_private]=0

for every extended original context and every auxiliary matrix on its own
private extension. No amplification of a scalar-only cubic commutator is
being assumed.

Therefore

    G_tilde(a⊕b,U)=G(a,U)P+G(b,U)(I−P)

is a linear, independently complete M2+M2 auxiliary tensor. At every private
context its normalized two summands act on reducing complementary
projections, so arbitrary unitary a,b have zero cross terms and unitary
sum. Diagonal restriction a=b recovers the original G.

Its origin multiplicities are1,7 when rank P=2, and2,6 when rank P=4.
This is an algebraic complete refinement derived from an ACTUAL available
event. No routed realization of the refined slot, graph deletion, or
independent control of hidden multiplicities is asserted.

### 3. The rank-two block has only two placements

If rank P=2, the selected refined M2 block has multiplicity one, with fixed
input central coefficient F(U)P. The proper-block cut theorem applies.

The exact quartet cut spaces are the single-query carriers S_i, the
rank-four Q12 for before-set{1,2}, zero for the other nine proper cuts, and
the full space for the two empty-side cuts. The S_i are mutually orthogonal.
Moreover

    S_j intersect Q12 = {0}, for every j.

This last matrix-geometric fact is independently checked in
[strict_auxiliary_complete_independent_audit.py](../strict_auxiliary_complete_independent_audit.py) by the exact rank16 of the
stacked equations (I−S_j)v=(I−Q12)v=0. Consequently a nonzero P<=S_j can
fit only the empty-before, singleton-{j}, or full-before cut.

The full-before/future placement would give central coefficient P F(U),
whereas the actual coefficient is F(U)P. Their equality for all U would
make P commute with the full matrix coefficient span of F, which is
impossible for a proper nonzero projection. Thus the selected block is
precisely one of

    G_active(a,U)=F(U) beta(a)P,

    G_active(a,U)=U_bar_j beta(a)P alpha_j(U_j).

The first is a past insertion; the second is the single-query serial
insertion. The actual graph comparison determines the compatible relative
order on this irreducible block.

The rank14 complementary representation has multiplicity seven and is not
classified by that theorem. If rank P=4, the selected block itself has
multiplicity two, and neither it nor the rank12 complement is classified
by this multiplicity-one argument.

### 4. Several actual events

If more than one original port gives a nontrivial comparison, choose the
small active projection P_j at each. They lie in the mutually orthogonal
S_j and all reduce the same normalized auxiliary representation at every
private context. The same calculation yields a complete direct-sum M2
refinement on all P_j and the residual identity minus their sum, with origin
multiplicities rank(P_j)/2 and the corresponding residual multiplicity.

This does not justify splitting a rank4 selected event into two rank2
pieces: even when its original native active algebra has several branches,
only the particular comparison SUM is proved to commute with the auxiliary.
Individual finer events need not do so. All repeated blocks remain explicit.

### Scope of this method

The result supplies an unavoidable actual compatible event for every
interior one-branch M2 auxiliary and bounds its carrier to a proved original-
query serial support. It does not show that a host needs such an auxiliary,
that its repeated complement is removable, or that any complete refinement
lifts to a routed graph. This method does not classify all branched auxiliaries. The complete exact quartet host question is settled by [RG-001](obstruction.md#rg-001).
