# Native interfaces

[Topic index](../../README.md) · [Shared result index](../../../../RESULTS.md#rg--exact-native-routed-graph-universality)

Each result below has one owner. Exact scope and proof are updated here. Source-level mathematical arguments and finite certificates are distinguished from a new formal verification.

<a id="rg-005"></a>

## RG-005 — Global persistence of finite comparison choices

**Statement.** An exact finite analytic disjunction locks a comparison globally; this does not choose continuously from a continuous projection family.

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### General analytic selection lemma

Let M be a connected real-analytic manifold, and let f₁,…,f_r:M→[0,∞) be real-analytic functions. If their zero sets cover M, one f_s vanishes identically. Indeed a nonzero real-analytic function on connected M has a zero set with empty interior, and a finite union of such closed nowhere-dense sets cannot cover M.

### Application retaining full comparison identities

Fix original query i of the orthogonal-cylinder phase quartet, together with an actual independently complete native replacement G as in the accompanying query-2 theorem. Keep the i-origin fixed. Let u range over all product origins at the other original queries, a connected manifold U(2)^3. Set U=∏_{k≠i}u_k, N(u)=G(1,u), and define the normalized common-frame native representation

    π_u(a)=U*G(a,u)N(u)*U.

For each spectator j, let β_{j,u}(x) be the corresponding normalized original single and H_{j,u}(a,x) the normalized native/original pair, with j-input u_jx and all other original inputs at u. Explicitly,

    H_{j,u}(a,x)=U*G(a,u₁,…,uⱼx,… )N(u)*U,
    β_{j,u}(x)=H_{j,u}(1,x).

The omitted slot in G is the native i-slot a. These are real-analytic in u, for each matrix coefficient a,x.

Assume the exact original i,j comparison family is a fixed finite set C_{ij} in this common frame, as occurs at all quartet pairs except 34. At every u the finite-C*-algebra bipartite theorem supplies a comparison P∈C_{ij} satisfying all three identities

    [P,π_u(a)]=0,
    [P,β_{j,u}(x)]=0,
    H_{j,u}(a,x)=Pπ_u(a)β_{j,u}(x)+(I−P)β_{j,u}(x)π_u(a).

For each candidate P, take the sum of squared Hilbert–Schmidt norms of the residuals over finite coefficient bases a,x. This is a nonnegative real-analytic function on U(2)^3. Its zero sets cover the domain; hence ONE FIXED P_j satisfies all identities at EVERY u.

Apply this independently for each finite-family spectator j. The choices can be made simultaneously because the identities concern the same actual G; no commutation between the chosen P_j is inferred or required.

This strengthens the one-parameter commuting-row argument: one may use the same fixed comparison both to transport the native representation and to constrain its commutant, uniformly through all spectator contexts.

### Locked one-step corollary

At u=I, untwist by R_i. For each selected P_j and each c∈U(2), let

    v_{j,c}=remove_i( R_i c_j* [P_j+(I−P_j)A_j(c)] R_i ).

Writing q_j=remove_i(R_iP_jR_i)=remove_i(P_j), the relative native algebra B₀ obeys

    B₀ ⊆ {q_k, v_{j,c}*q_kv_{j,c} : j,k selected, c∈C}',

for any finite set C of contexts. Crucially the bit choosing P_j is locked to the same bit choosing q_j; independent choices here would give weaker bounds. [locked_contexts.py](../locked_contexts.py) computes these necessary commutants exactly.

The continuous pair 34 is excluded from the finite selection step. Treating its full projection manifold as two points would invalidate the proof.

### Scope of this method

The same comparison identities hold at nontrivial u. They determine successive transports of π_u along spectator-origin paths. Different paths reaching the same u must give the same native representation; holonomy must therefore commute with it. This offers stronger necessary constraints, but no such constraints are asserted proved by the one-step checker.

<a id="rg-006"></a>

## RG-006 — All-origin pair geometry

**Statement.** The strict and commuting sectors of every quartet pair comparison are origin rigid, with the stated dimension-independent pure-support extension.

**Status:** source-level result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### 1. Closed evaluation of the rank-two orthogonal-support family

Let H be the tensor product of N qubit input factors. Take nonzero mutually orthogonal projections

    E_i=I_i⊗|ψ_i><ψ_i|_(bar i),

and the output-recording blocks V_o=I−2Σ_i o_iE_i. These are the established independently ancillary-complete processes. Let P_i^1 and Z_i=I−2P_i^1 act on tensor factor i. The forward closed evaluation, with arbitrary original qubit matrices w_i and W=⊗_i w_i, is

    F(w)=W−2Σ_i P_i^1 W E_i.                         (1)

Indeed its o-th row is the o-th row of W V_o. For unitary w_i put z_i=w_i* Z_i w_i and

    D_w=I+Σ_i(z_i−I)E_i.

Each z_i commutes with E_i, and the E_i are orthogonal, so D_w is a Hermitian unitary and

    F(w)=W D_w.                                     (2)

The adjoints in (2) are a factorization on unitary inputs; the actual map (1) remains complex multilinear with one use of each original argument.

### 2. Every local-origin shift has explicit singles and pair faces

Fix arbitrary original unitary origins u_i. Let U=⊗_i u_i, z_i=u_i*Z_i u_i, and normalize

    F_u(x)=F(u_i x_i)F(u)*.

Use the common U frame, writing F_u(x)=U \widehat F_u(x) U*. For unitary x_i define X=⊗x_i. Equation (2) gives

    \widehat F_u(x)=X[I+Σ_i(x_i* z_i x_i−I)E_i]D_u.

In particular set

    R_i=I+(z_i−I)E_i,
    K_i(x_i)=z_i x_i z_i−x_i.

The one-slot and two-slot formulas are exactly

    A_i(x_i)=R_i x_i R_i=x_i+K_i(x_i)E_i,            (3)
    B_ij(x_i,x_j)=x_i x_j+x_j K_i(x_i)E_i
                                  +x_i K_j(x_j)E_j. (4)

To check cancellation, only the i,j terms change in D after activating those arguments, and E_iD_u=z_iE_i. No commutation of x_j with E_i is assumed. The formulas extend to all matrix arguments by linearity. Although the actual single embeddings depend on z_i, the following pair geometry does not.

### 3. Uniform exact strict and commuting sectors

For i≠j, let S_(i|j) be the support on the remaining N−2 factors of Tr_j |ψ_i><ψ_i|. Set

    H_(i|j)=I_i⊗I_j⊗S_(i|j),
    H_(j|i)=I_i⊗I_j⊗S_(j|i),
    C_ij=I−H_(i|j)−H_(j|i).                         (5)

Here the symbols denote projections, with the tensor positions restored to their original order. Orthogonality E_iE_j=0 implies S_(i|j)S_(j|i)=0: in Schmidt-component notation, every component of ψ_i on the shared N−2 factors is orthogonal to every component of ψ_j. Thus the three projections in (5) are orthogonal. Each is trivial on i,j and reduces A_i,A_j.

On H_(i|j), E_j vanishes and (4) equals A_j A_i; on H_(j|i) it equals A_i A_j. On C_ij both E_i and E_j vanish, A_i and A_j are the original separate tensor factors, and they commute.

These are the **exact** strict sectors, not merely containing spaces. To prove full strictness on H_(i|j), diagonalize z_i by an input-i unitary, which does not affect the commuting-support question. On this sector write

    R_i=|+><+|_i⊗I+|−><−|_i⊗T,
    T=I−2|ψ_i><ψ_i|,

where ψ_i belongs to H_j⊗ran S_(i|j) and has full Schmidt support on the second factor. The conjugated off-diagonal input-i matrix units have T as their other-factor entry, while A_j is the original M2 on factor j. Their cross commutators therefore have off-diagonal entries [T,b_j].

The common kernel K of all [T,b_j] reduces b_j and T. Since T has a one-dimensional negative space, that negative space cannot contain a nonzero reducing M2 module. Hence T=I on K and K is orthogonal to ψ_i. But the M2_j orbit of ψ_i spans all H_j⊗ran S_(i|j), by its full Schmidt support. No nonzero M2_j-reducing subspace can be orthogonal to that orbit. Therefore K=0. The off-diagonal i matrix units and their adjoints kill both possible input-i components, proving full strictness on H_(i|j). The opposite sector is symmetric.

Consequently the exact cross-commutator support of A_i,A_j in the common U frame is

    Z_ij=H_(i|j)+H_(j|i),                            (6)

independently of every origin u. In the actual normalized output frame it is U Z_ij U*. This establishes persistent partiality uniformly, including nongeneric origins.

### 4. All exact pair-comparison choices are origin rigid

Use the convention that P_ij multiplies A_i A_j. On the strict sectors, the comparison is uniquely H_(j|i). On C_ij the represented pair is M4⊗I on its multiplicity space. Its joint commutant consists exactly of I_ij⊗M(c_ij), where c_ij=rank(C_ij)/4.

Thus every exact comparison has the form

    P_ij=H_(j|i)+q_ij,
    q_ij in I_ij⊗M(c_ij),   q_ij²=q_ij=q_ij*,
    q_ij=C_ij q_ij C_ij.                             (7)

There are no omitted off-diagonal freedoms: subtract the particular comparison H_(j|i). Its product with every cross commutator is zero on both sides, so the difference is supported entirely on the common commuting kernel C_ij.

The complete choice family (7), not just its ranks, is independent of u in the common frame. In the original normalized frame every candidate is simultaneously conjugated by the same U. Therefore existence of incidently commuting/transitive comparison choices is invariant under **all** original local origin shifts for this entire rank-two orthogonal-support family.

### 5. Apply the formula to the retained M16 quartet

Use the exact supports from [RG-072: Quantum-support geometry and the envelope boundary](positive-routes.md#rg-072):

    ψ_1=|0>_2 |Φ+>_34,
    ψ_2=(|0,0,1>_134+|1,−,+>_134)/sqrt(2),
    ψ_3=|0,1,0>_124,
    ψ_4=|1,1,+>_123.

The ordered pairs (12,13,14,23,24,34) have exact strict ranks

    (12,12,12,12,12,8),                              (8)

and commuting ranks (4,4,4,4,4,8), at every origin. Thus no pair in this example can become full strict by freezing the other original laboratories or by additionally shifting its own endpoints.

For the decisive pairs 12 and 23, each commuting multiplicity is one. Let

    q_C=proj span{|01>,|−,+>} on34,
    q_Φ=|Φ+><Φ+| on34.

The only two comparisons on 12 are

    P_12^(0)=I12⊗q_C,
    P_12^(1)=I12⊗(I34−q_Φ).                          (9)

The only two comparisons on 23 are

    P_23^(0)=P0_1 I23 P0_4,
    P_23^(1)=P0_1 I23 P0_4+P1_1 I23 P−_4.            (10)

In the standard 34 basis,

    q_C=(1/3)[[1,0,−1,−1],
              [0,3,0,0],
              [−1,0,1,1],
              [−1,0,1,1]].

Direct exact calculation gives the squared Hilbert–Schmidt commutator table

    ||[P_12^(a),P_23^(b)]||_HS²:

                 b=0       b=1
         a=0     8/9       16/9
         a=1     1          2.                       (11)

One can verify it using only four-dimensional matrices: the input2 identity contributes a factor two, and the two input1 sectors in (10) contribute the commutators with I3⊗P0_4 and I3⊗P−_4. Their squared norms are both 4/9 for q_C and both 1/2 for I−q_Φ.

All four entries are nonzero. Hence even these two incident edges have no commuting comparison choice. Common conjugation by U preserves every number in (11), so this obstruction survives every origin shift. No analysis of the continuum of choices on pair34, other incident pairs, triangle inequalities, or higher-order tensor matching is needed for this obstruction.

### 6. Exact scope and constructive implication

The quartet admits no compatible-comparison realization at any original local origin. The generic-full route of therefore has a persistent obstruction on every pair, and even allowing all partial-pair freedoms cannot produce its comparison constructor.

This conclusion is consistent with the retained QC-QC obstruction, but provides a direct local operator certificate and the complete moving pair geometry. It does **not** exclude a valid cyclic routed graph, whose branch dependencies need not admit these comparisons. Such a route must exploit structure beyond a global comparison assignment, rather than merely find a better normalization or context.

In particular the new result does not rule out transported J/L branches. Their required motion is now more sharply specified: local origin shifts alone only conjugate the fixed pair-support geometry in (5), and cannot convert it into a comparison-compatible one. Producing the two-branch interface by a genuinely cyclic full-practical-space graph remains a separate construction problem.

### 7. Dimension-independent extension for pure complementary supports

The same pair-geometry theorem extends to arbitrary local dimensions d_i≥2, with mutually orthogonal E_i=I_i⊗|ψ_i><ψ_i| and arbitrary nonconstant output phase functions χ_i. Put Z_i=diag(χ_i(o_i)). The closed map becomes

    F(w)=W+Σ_i(Z_i−I)W E_i=W D_w,
    D_w=I+Σ_i(w_i* Z_i w_i−I)E_i.

D_w is unitary, though it need not be Hermitian. Accordingly the normalized formula uses D_u* in place of D_u. Equations (3)–(4) hold with

    R_i=I+(z_i−I)E_i,
    A_i=R_i x_i R_i*,
    K_i=z_i x_i z_i*−x_i.

The envelopes (5) are unchanged in form. To check exact strictness, diagonalize z_i with eigenvalues λ_a. On H_(i|j), A_i sends an input-i matrix unit e_ab to

    e_ab⊗[I+(λ_a conjugate(λ_b)−1)|ψ_i><ψ_i|].

For every b there is some a with λ_a≠λ_b because χ_i is nonconstant. The corresponding cross commutators therefore test every input-i component against the common kernel of [|ψ_i><ψ_i|,M_(d_j)]. This kernel is zero on H_j⊗ran S_(i|j): its negative-reflection part would have dimension at most one<d_j, and full Schmidt support again makes the M_(d_j) orbit span the whole carrier. Thus the strict carrier is exactly the sum of the two envelopes for arbitrary d_i,d_j.

On its commuting complement the pair is M_(d_i d_j)⊗I, so every comparison is again H_(j|i) plus a projection in the complementary multiplicity algebra. All these families are origin rigid up to the same common product conjugation U. This extension is a uniform proof, not a conclusion from the qubit checker.

### 8. Exact certificate

`check_quartet_origin_rigid_comparisons_round23.py` is described as producing `quartet_origin_rigid_comparison_checks_round23.json`. It verifies the original rational supports and their orthogonality; constructs all pair envelopes exactly; checks strict Gram ranks at the identity; verifies the displayed exhaustive 12/23 candidates and all four nonzero commutator norms; and checks twelve one-slot and six two-slot identities at an explicit nontrivial rational-unitary product origin. All calculations are exact. Gaussian-rational matrix arithmetic prevents symbolic expression growth without a numerical tolerance.

The finite origin checks corroborate the formulas. The uniform statements for all origins and all dimensions are established analytically above; the certificate is not a sample-based proof of them or of nonroutability.





**Reproduction limit:** supporting helpers were not supplied; the analytic argument remains available. See the [artifact map](../REPRODUCIBILITY.md#rg-006).

<a id="rg-007"></a>

## RG-007 — Exact second-port algebra containment

**Statement.** Every complete native algebra at query 2 lies in the exact active-support matrix algebra plus its scalar complement after untwisting.

**Status:** source-level result. **Scope:** All spectator contexts and independent private systems; exact necessary containment, not a routed construction.

### Statement and quantifiers

Let F be the normalized four-qubit orthogonal-cylinder process in [RG-001](obstruction.md#rg-001), acting on H=(C²)^⊗4. Replace original query 2 by a finite-dimensional C*-algebra A with a unital whole-query inclusion ι:M₂→A. Suppose G:A×M₂×M₂×M₂→M₁₆ is multilinear and independently completely unitary preserving, and restricts exactly to F through ι (including coefficientwise private-ancilla extensions). Normalize the origin so π(a)=G(a,I,I,I) is a unital representation and πι=α₂.

Write R₂=I+(Z₂−I)E₂, so α₂(x)=R₂x₂R₂. Then

    R₂ π(A) R₂ ⊆ M₂ ⊗ [ M₂(J) ⊕ C·(I₈−J) ],

with query 2 removed from the eight-dimensional multiplicity coordinates 134, and

    J=|001><001|+|1,−,+><1,−,+|.

Here M₂(J) means all matrices supported on ran J, and C·(I₈−J) is the scalar algebra on its six-dimensional complement. Equivalently, every actual whole-query native algebra at query 2 is contained in the known represented M₄⊕M₂ promotion, whose physical carriers are S₂=I₂⊗J (rank four) and I−S₂ (rank twelve).

This includes arbitrary fixed auxiliary contexts and does not require faithful representation of unused summands. For a valid routed host, only reachable summands count; their representation is faithful by the earlier reachability theorem. It says nothing about a putative encoding distributed across several native vertices.

### Analytic reduction to finite exact tests

Because π(A) contains α₂(M₂), finite-dimensional matrix units give

    R₂π(A)R₂=M₂⊗B₀

for a unital finite-dimensional C*-subalgebra B₀⊆M₈. The finite-context necessary-condition theorem applies separately for spectator j=1,3,4. Its proof is reproduced conceptually here to specify the quantifiers.

For each j the native/original bipartite comparison theorem supplies one P in the exact two-element original comparison family, oriented so

    G₂ⱼ(a,c)=Pπ(a)Aⱼ(c)+(I−P)Aⱼ(c)π(a).

Thus [P,π(A)]=0. On shifting query j to any c∈U(2), then removing the physical origin cⱼ, the actual native representation becomes V_cπ(A)V_c*, where

    V_c=cⱼ* [P+(I−P)Aⱼ(c)].

It fixes α₂ pointwise, hence R₂V_cR₂=I₂⊗v_c. At every c, each of the three incident original pairs has one of its two exact comparisons commuting with the actual native algebra. There are eight possible rows. The sum of squared commutators of a finite basis of v_cB₀v_c* with a row is a real-analytic function of c. These eight zero sets cover connected U(2), so one row vanishes identically. This argument selects a row without presuming that any initially selected comparison varies continuously.

Consequently B₀ lies in at least one K_{j,P,row}, where

    K_{j,P,row}={ p, v_c* q v_c : q in row, c in C }',
    C={I,X,Y,Z,(3I+4iX)/5,(3I+4iY)/5,(3I+4iZ)/5}.

Every matrix here is Gaussian rational. Containment is valid for this finite C because it follows from the all-context analytic statement; the finite list is not being used to infer sufficiency or analytic continuation.

Apply the three spectator conditions simultaneously. Exact linear algebra gives:

- For j=1: the 16 candidates collapse to four distinct algebras of dimensions 6,5,7,9
- After intersection with the 16 candidates for j=3: precisely two distinct algebras remain, of dimensions 5,6
- After intersection with the 16 candidates for j=4: every candidate intersection is the same dimension-five algebra M₂(J)⊕C(I−J)

This proves the asserted containment. Since the already audited joint native promotion realizes the full represented M₄⊕M₂ algebra at query 2, the upper bound is attained. Attainment is a complete extension result, not a routed-host construction.

### Exact finite algebra certificate and reproducibility

Run `python context_closure.py` under `source/`. It imports immutable rational fixtures and the matrix-algebra decomposition routine from the source directory. The file `context_closure.json` records all final components, and `context_closure.log` records each candidate dimension and each exact intersection stage. No floating-point linear algebra is used.

The commutant implementation updates a matrix-unit basis by exact nullspaces of [A,X]=0 constraints. Intersections are exact nullspaces of [V_A | −V_B]. Reduced row spaces identify duplicate algebras, not only isomorphic abstract profiles. Final center projectors and component dimensions are exact. The query-2 noncommutative center projector printed in the log is exactly J above.

Dependencies for the mathematical reduction are the supplied [RG-002: Complete finite-algebra bipartite comparison](foundations.md#rg-002), [RG-006: All-origin pair geometry](native-interfaces.md#rg-006), and [RG-011: Context transport and rectangular holonomy](native-interfaces.md#rg-011). The last candidate has been rederived above but still warrants independent audit.

### Consequences and limits

Every nonzero simple factor in the represented native algebra has size at most four. If a represented M₄ factor occurs, its support is exactly S₂ and its multiplicity is one. The residual rank-twelve carrier supports only the scalar-relative M₂ representation. Purely M₂ direct-sum refinements can partition the two-dimensional J sector, but cannot distinguish arbitrary subspaces inside J⊥. Hence at most three nonzero central components are possible. Components may be identified diagonally, so this is an upper bound rather than an exhaustive list of possible centers.

No assertion is made that every subalgebra of the displayed maximal algebra extends to a routed skeleton. The exact quartet no-host conclusion is [RG-001](obstruction.md#rg-001); this algebra bound alone is not that graph proof.

### Required proof qualifications

Finite-disjunction locking precedes sampling. The spectator tests only impose necessary commutators on that single globally locked alternative. Equality with the displayed algebra is an exact row-space assertion, not merely a dimension count.

<a id="rg-008"></a>

## RG-008 — Exact third/fourth-port algebra containment

**Statement.** At ports 3 and 4 the only represented native alternatives are M2 or M2 direct-sum M2 on E_i and its complement.

**Status:** source-level result. **Scope:** Continuous pair comparison is relaxed by existential linear elimination, so it is not sampled. The earlier M6/M8-only exclusions are subsumed.

### Theorem

Let G be any independently ancillary-complete multilinear native replacement of one entire original quartet query i=3 or4, on the same sixteen-dimensional boundary and with a unital whole-query inclusion of M₂. Write π for its origin representation and α_i(x)=R_ix_iR_i for the original single. Then

    R_i π(A) R_i ⊆ M₂ ⊗ span_C{e_i,I₈−e_i},
    E_i=I_i⊗e_i.

Here e₃=|010><010| on factors124 and e₄=|11+><11+| on123. In particular the represented native algebra is either the original diagonal M₂, or exactly M₂⊕M₂ on physical carriers E_i and I−E_i, with multiplicities1 and7. A nonfaithful kernel can be omitted. In an actual valid skeleton reachable branches are faithful, so there are at most two reachable branches, both of native matrix size two.

The full two-branch algebra is attained by the previously proved serial-column promotion with S_i=E_i. This theorem supersedes the larger-size exclusion for these ports, while retaining the same fixed-boundary, whole-query hypotheses. It is not a routed-host existence or impossibility theorem.

### 1. Discrete comparisons remain locked

As in the independently audited global-persistence theorem, choose one fixed original comparison P₁ and P₂ for the pairs of native query i with spectators1 and2. Each is one of two exact choices, producing four bit rows. They satisfy the full native/original bipartite identity at every spectator origin.

Untwist by R_i. Since π(A) contains α_i(M₂), it becomes M₂⊗B₀ for a unital C*-algebra B₀⊆M₈. The exact one-step locked-context commutants from [locked_contexts.py](../locked_contexts.py) give a linear subspace K_bits containing B₀. Its dimensions for bits00,01,10,11 are18,2,6,5 respectively. These commutants are necessary conditions already established independently.

Let j be the other last port: j=4 when i=3, j=3 when i=4. This pair has a continuous comparison family. We do not discretize it or assume a globally constant member.

### 2. Relax the continuous comparison into a free linear variable

At the identity spectator origins the actual native/original bipartite theorem supplies one comparison P for the i,j pair, valid for every native matrix and every j-input. In the original and untwisted frames it has the form

    P=H+Q,
    Q=CQC,

where, on H=(C²)^⊗4,

    C=I₁ P0₂ I₃₄,
    H=P1₁ P1₂ I₃₄ for i=3,
    H=P0₁ P1₂ I₃₄ for i=4.

The full family requires Q to be an appropriate rank0/1/2 projection on the first factor within C, but we discard all such nonlinear restrictions. This can only enlarge the necessary solution space. P is trivial on original factor i and commutes with R_i. On the multiplicity space write h=remove_i(H), c=remove_i(C), p=remove_i(P).

For any X∈B₀ introduce Y=pX. Since [p,X]=0 and (I−c)p=h=p(I−c),

    (I−c)Y=hX,
    Y(I−c)=Xh.                                      (1)

In the relaxation Y is otherwise an arbitrary complex8×8 matrix. The same Y accompanies every original i-matrix coefficient t: if

    A=R_i(t_i⊗X)R_i,
    B=R_i(t_i⊗Y)R_i,

then B=PA=AP. No nonlinear relation between X and Y is imposed in the certificate. In particular it does not solve for or sample the continuous projector Q.

### 3. Reconstruction linear in A and B

Change spectator j first from identity to u_j. Put a_j=R_ju_jR_j, with u_j on physical factor j. Because P commutes with A and a_j, the actual normalized native representation after that step is

    T_j(A,B;u_j)=u_j* [ B+a_j(A−B)a_j* ]u_j.         (2)

To check (2), start with V=u_j*[P+(I−P)a_j]. The cross terms in VAV* vanish; PAP=B and (I−P)A(I−P)=A−B. Thus (2) is exactly the actual transport, for arbitrary non-Hermitian coefficient matrices as well.

Next change spectators1 and2, in that order. Their globally locked comparisons give fixed transports

    V_k(u_k)=u_k*[P_k+(I−P_k)R_ku_kR_k],  k=1,2.

Their own origins were still identity when changed, so these formulas remain valid after the earlier j-change. Write V=V₂V₁ and U for the physical tensor product of all spectator inputs, with the i-input equal to I. The native tensor value is forced to be

    L_X,Y(u)=U V T_j(A,B;u_j) V* U* F(I_i,u).         (3)

This uses the continuous comparison only at the first identity-origin step. No assumption that it persists at later origins is used. Formula(3) is linear in X,Y. An actual extension must additionally make it complex linear in every original spectator input.

### 4. Finite exact linear elimination

For each of the four discrete rows, start with pairs (X,Y) in K_bits×M₈ and impose (1). For t=|0><0| and t=|0><1| on the original i-factor, impose the following matrix equalities, all consequences of multilinearity in j:

    L_X,Y(u₁,u₂,(3I+4iσ)/5)
       −[3L_X,Y(u₁,u₂,I)+4iL_X,Y(u₁,u₂,σ)]/5=0,     (4)

with σ∈{X,Y,Z} and u₁,u₂∈{I,X,Y,Z}. The checker may stop adding equations once the projected X-space has dimension two, then explicitly verifies that it is span{I₈,e_i}. It does not infer equality merely from the dimension.

Every calculation is over Gaussian rationals. Constraints are linear in the entries of X,Y. The exact nullspace is projected onto X by column-space computation. Results:

    i=3, bits00: initial X-dimension16 → final2
    i=3, bits01: initial2 → final2
    i=3, bits10: initial4 → final2
    i=3, bits11: initial3 → final2
    i=4, bits00: initial16 → final2
    i=4, bits01: initial2 → final2
    i=4, bits10: initial4 → final2
    i=4, bits11: initial3 → final2

The “initial” columns here are after imposing (1); this explains their difference from the one-step commutant dimensions. In every case the final two-dimensional image is exactly span{I,e_i}, with rank(e_i)=1. Therefore B₀ lies in that algebra for every possible continuous pair comparison, proving the theorem.

Because B₀ is a unital C*-subalgebra of C², it is either the diagonal scalar algebra C or all C². Tensoring with the whole original M₂ gives the stated exhaustive represented-algebra alternatives.

### 5. Certificates and limits

Portable exact checker: [verify_last_port_maximality.py](../verify_last_port_maximality.py), importing only [exact_fixtures.py](../exact_fixtures.py), [context_closure.py](../context_closure.py), and [tensor_tools.py](../tensor_tools.py) from `source/`. It writes [last_port_maximality_checks.json](../last_port_maximality_checks.json) and prints the elimination stages. Run with Python3 and SymPy. The separate completed exploratory exact run is `relaxed_comparison_elimination_cached.log`; numerical scouts played no role in this uniform proof.

The proof establishes a necessary algebra bound through a relaxation, so omitting projector equations and using only two coefficient units is safe. The existence of the canonical full two-branch promotion proves attainment of the resulting algebra bound. It does not prove that every original routed realization can be enlarged at its native vertices, does not impose any bound on auxiliary-node count, and does not turn the promoted process into a routed graph.

### Alternative exact M6/M8 exclusion witnesses

### 1. Discrete global comparisons and possible larger summands

At query i=3 or4, its pairs with queries1 and2 each have two exact original comparisons. Global analytic persistence locks one bit for each pair across all original origins. The exact one-step commutants in [locked_contexts.py](../locked_contexts.py) give these relative-algebra profiles on the eight-dimensional multiplicity space:

    00: C(rank1) ⊕ C(rank3) ⊕ M4(rank4)
    01: C(rank1) ⊕ C(rank7)
    `10: C(rank1) ⊕ C(rank3) ⊕ [M2⊗I2](rank4)`
    11: C(rank6) ⊕ M2(rank2).

Therefore a represented relative simple factor M_k with k≥3 can occur only in row00, only within the multiplicity-one M4 carrier K, and only with k=3 or4 and multiplicity one. Native sizes are twice these relative sizes, by the whole-query unital M2 inclusion. Thus only native M6 and M8 remain to exclude.

On the physical space H, the carriers are

    K_3=I123⊗P1_4,
    K_4=I12⊗P−_3⊗I4.

They are trivial on the original query factor, have physical rank eight, and are untouched by R_i (E_iK_i=0).

### 2. The continuous pair34 cannot support M8, and restricts M6 to two endpoints

Put

    H3=P0_1 P1_2 I34,
    H4=P1_1 P1_2 I34,
    C=I1 P0_2 I34.

All comparisons on pair34, oriented with query3 first in the algebraic formula, are

    P34=H4+q_1 P0_2 I34,

where q is ANY orthogonal projection on the first qubit, including arbitrary rank-one projections. For query4 use the complement. This is the full continuous family, not an endpoint substitution.

Every actual native/original comparison must commute with the native algebra. K_i reduces P. On K_i's four-dimensional relative space, the eigenvalue multiplicities of P are 1+3, 2+2, or3+1 according to rank q=0,1,2, with the two eigenvalues both present. Hence a full M4 on K_i cannot commute with P. This excludes native M8.

An M3 of multiplicity one commuting with P must have its rank-three carrier wholly in one eigenspace of P. Such an eigenspace exists only for rank q=0 or2, and then its carrier is exactly that three-dimensional eigenspace. Therefore arbitrary rank-one q cannot support an M6. This is a rank argument for the full continuous family.

For query3, q=I gives a commutative necessary native-relative algebra after one spectator4 context is combined with the fixed discrete comparison row. For query4 the corresponding excluded endpoint is q=0 before complementing P. [exact_m6_exclusion.py](../exact_m6_exclusion.py) verifies the commutants exactly (dimension four, all basis commutators zero).

Only these two native M6 possibilities remain:

    i=3: P=H4, physical carrier p3=K3(I−H4)
    i=4: P=H3, physical carrier p4=K4(I−H3).

Both have rank six. Their full M6 matrix algebra would be contained in the native image.

### 3. Transport determines a candidate evaluation, which must be multilinear

At i=3, let spectator order be (4,1,2); at i=4 use (3,1,2). Start with the actual comparison P from Section2 for the first spectator. The two later comparisons P1,P2 are the globally locked row00 comparisons. At the first step every origin is identity. At each later step its own origin is still identity, and its original one-slot embedding depends only on its own origin, so the transport is

    V_j(c)=c_j*[P_j+(I−P_j)R_jc_jR_j].

Let V be their product in that chronological order (last factor applied on the left), and U the physical tensor product of spectator inputs. For any native a with π₀(a)=A, the actual extension is necessarily

    G(a,u)=U V A V* U* F(I_i,u).                         (1)

This is obtained by successively applying the exact right-normalized representation transport; it does not assert that its right side is multilinear for arbitrary A. Multilinearity of an actual G imposes that additional requirement.

### 4. Two exact violations

Use computational basis indices 0,…,15, lexicographically ordered by qubits1,2,3,4. The rational unitary (3I+4iX)/5 is the indicated complex linear combination of I and X; similarly for Y.

At i=3 choose the native matrix A=|0001><0001|, which lies in M6(p3). Fix x1=x2=X and vary x4. Let H(c) denote the right side of (1). Exact rational matrix multiplication gives

    [H((3I+4iX)/5)−(3H(I)+4iH(X))/5]_(0,12)=48/125 ≠0.

The defect has rank two and squared Hilbert–Schmidt norm 576/625. This contradicts linearity in query4.

At i=4 choose A=|00−0><00−0|, which lies in M6(p4). Fix x1=I,x2=X and vary x3. Exact multiplication gives

    [H((3I+4iY)/5)−(3H(I)+4iH(Y))/5]_(2,4)=96/125 ≠0.

Its defect has rank two and squared Hilbert–Schmidt norm 1152/625. This contradicts linearity in query3.

These are matrix-coefficient contradictions, not numerical unitarity tests. Every full native M6 factor on its forced carrier contains the chosen projection, so the witness excludes the entire factor, irrespective of the native coordinate basis or other summands.

### Required proof qualifications

The same auxiliary variable Y=pX is retained for all own-factor coefficients; existential elimination relaxes both positivity and p^2=p. A bound on this enlarged linear solution set covers every actual continuous comparison. The complete kernel-descent and simultaneous-tensor arguments are owned by RG-009 and RG-010.

<a id="rg-009"></a>

## RG-009 — Passive quotients and unique active serial ideals

**Statement.** Every quartet native original interface has one passive M2 quotient and active unit Q_i <= S_i; each active ideal has its forced serial tensor.

**Status:** source-level result. **Scope:** Origin-kernel summands vanish at every complete context; reachable branches exclude such unused summands.

### Setting

Let G be an actual independently ancillary-complete multilinear process with four finite-dimensional native C*-algebras A_i, all original qubit queries included unitaly and wholly in their corresponding native ports. Its restriction is the normalized entangled quartet F on H=C¹⁶. Auxiliary native vertices of a proposed routed host have been fixed to arbitrary specified unitary fillers; no condition on their number or topology is imposed.

At the identity context let π_i be the native representation and α_i=π_iι_i the original single. Any origin-kernel simple summand of A_i vanishes at all native unitary contexts: normalized representations vary continuously over connected products of unitary groups, so each central support has constant rank. A zero support remains zero; multilinearity then kills that summand coefficientwise. We quotient these globally unused summands. The π_i are now faithful.

Write α_i(x)=R_ix_iR_i. Untwisting gives

    R_iπ_i(A_i)R_i=M₂⊗B_i,

with B_i⊆M₈ a unital C*-algebra. The exact canonical serial carriers are S₁,S₂,E₃,E₄, with ranks4,4,2,2 and pairwise orthogonal supports, as in the prior joint-promotion theorem. Put S₃=E₃,S₄=E₄.

### 1. Exact per-port alternatives

The following are necessary for the same actual G, by restricting its other native ports to their original queries.

#### Port1

Global comparison persistence supplies a bit row for its three finite comparison families. If the 12 bit is zero, the exact locked-context commutant is

    B₁⊆M₂(s₁)⊕C(I−s₁),  I₁⊗s₁=S₁.

Every selected comparison annihilates S₁. If the 12 bit is one, the exact locked commutant instead is

    B₁⊆span{e₁,I−e₁},  I₁⊗e₁=E₁,

and every comparison annihilates E₁. These assertions include all choices of the other two bits. They are exact outputs of the globally locked test, not merely upper bounds on abstract matrix sizes.

#### Port2

The audited containment gives B₂⊆M₂(s₂)⊕C(I−s₂), I₂⊗s₂=S₂. Every allowed original incident comparison, for either bit on each edge, annihilates S₂.

#### Ports3 and4

The audited maximality result gives B_i⊆span{e_i,I−e_i}, with E_i=I_i⊗e_i. Every original incident comparison annihilates E_i, including every member of the continuous pair34 family.

The portable checker [verify_first_port_serial_ideals.py](../verify_first_port_serial_ideals.py) verifies the eight port1 algebras, their comparison annihilation, the six port2 annihilation identities, and the actual pairwise products S_iS_j=0. The last two algebras were established by [verify_last_port_maximality.py](../verify_last_port_maximality.py).

### 2. A canonical passive M2 quotient

In each case choose L_i=S_i, except in port1's 12-bit-one case choose L₁=E₁. The algebra B_i lies in

    M_{rank(L_i)/2}(l_i) ⊕ C(I−l_i).

Restriction to the nonzero complementary carrier defines a character χ_i:B_i→C. Its kernel is an ideal; let q_i be that ideal's identity. Then q_i≤l_i. Tensoring χ_i with M₂ gives a surjective unital *-homomorphism

    p_i:A_i→M₂,   p_iι_i=id.

The finite-dimensional algebra splits as

    A_i=A_i^act ⊕ M₂,
    Q_i=π_i(1_{A_i^act})=R_i(I_i⊗q_i)R_i ≤ L_i ≤ S_i.

The active ideal may be zero. The passive factor is exactly M₂, not an arbitrary larger matrix algebra. Every A_i input has a unique active component a_i and passive qubit matrix b_i. Its represented active matrix A_i=π_i(a_i) is supported on Q_i. Since Q_i is central in the native image, it reduces α_i.

Crucially, Q_i need NOT be trivial on its original physical qubit: the R_i conjugation can entangle that factor with the relative ray. What is proved and used is Q_i≤S_i and [Q_i,α_i(M₂)]=0.

The known pairwise orthogonality of the S_i therefore gives

    Q_iQ_j=0 (i≠j),  R_Q=I−Σ_iQ_i ≥0,
    rank(R_Q)=16−Σ_i rank(Q_i).

This establishes true simultaneous orthogonality, not an inference from constant individual ranks. The passive ranks are at least12 at ports1/2 and at least14 at ports3/4; all passive quotients are nonzero.

### 3. The active ideal has a unique one-port tensor

For all selected finite comparisons at port i, P_{ij}Q_i=0. At the continuous pair34 choose its actual comparison at identity and shift that spectator first. It also annihilates Q_i. Shift the other original spectators afterward, using their globally locked finite comparisons.

Let A be any represented active matrix, so A=Q_iAQ_i. For j≠i, E_jA=0 because Q_i≤S_i and S_i⊥E_j. Also E_j commutes with u_j. Therefore

    R_jA=A,  R_ju_jA=u_jA,  A_j(u_j)A=u_jA.

The exact native representation transport is V_j=u_j*[P_{ij}+(I−P_{ij})A_j(u_j)]. Since P_{ij} commutes with A_j and annihilates A, V_jA=A and AV_j*=A. Thus each shift leaves A unchanged in the common physical-origin frame.

At the final original spectator tuple u,

    G(a_i⊕0,u)=U_bar_i A.

Indeed right normalization gives U_bar_i A U_bar_i*F(I_i,u); on S_i the factor D_uD_0 equals identity because the i-origin is I and every other E_j annihilates S_i. This proves the displayed expression for all unitary u, then coefficientwise for all original matrices.

Subtract the original embedding of the passive component b_i. The entire one-port extension is therefore

    G(a_i⊕b_i,x_bar_i)
      =U_bar_i(x) A_i+F(b_i,x_bar_i)(I−Q_i).          (1)

This applies even when Q_i itself is a proper subprojection of S_i and when the active ideal is a direct sum rather than a full matrix algebra. There is no assumption that all of S_i is an actual native branch.

Coefficient equality yields equality under every independent private-ancilla amplification. The commuting and normalizing arguments are used only to establish the unamplified coefficient tensor, whose entrywise amplification is fixed.

### 4. Interface classification supplied, not graph construction

At ports1/2 the active relative ideal has support rank0,1,or2 and is a subalgebra of M₂ on that support; at ports3/4 it is zero or C on e_i. The corresponding physical active ranks are0,2,or4 and0,2 respectively. Distinct active central blocks may be present at the first two ports, but their total support still lies in S_i.

Consequently every actual host supplies four genuine orthogonal serial active ideals and four passive M₂ quotients, with one-port tensors exactly (1). The next theorem, [RG-010: Joint native tensor from saturated phase ranks](native-interfaces.md#rg-010), removes possible higher simultaneous native corrections. Neither result claims that a smaller routed native vertex can automatically be enlarged to the full canonical promotion.

### Complete kernel descent and last-port uniqueness

### Kernel propagation before identification

If a native simple summand is in the kernel of its origin representation, it vanishes at every unitary context. The right-normalized representations at other contexts are unital *-homomorphisms; their central support projections vary continuously on connected products of finite-dimensional unitary groups and therefore have constant rank. A zero-rank summand remains zero. Multilinearity and unitary spanning then kill its entire coefficient tensor. Thus quotienting by the origin kernel is valid for the full native process, not only its single-slot face. In a routed skeleton this applies after discarding globally unused branches.

### One-port tensor rigidity

Assume the maximality theorem at i=3 or4. If the represented native algebra is M₂ alone, its original-query inclusion is an isomorphism and its tensor is determined already. In the two-branch case, identify its origin representation as

    π(B⊕b)=B+b_i(I−E_i),

where B is an arbitrary matrix supported on E_iH (dimension2). The whole original query embeds as

    x ↦ α_i(x)E_i ⊕ x.

Then the ENTIRE complete extension, not just its single-slot image, is forced to be

    G_i(B⊕b,x_bar_i)=U_bar_i(x)B+F(b,x_bar_i)(I−E_i).   (1)

This is the canonical serial-column promotion. There is no alternative tensor with the same represented native algebra and original restriction.

#### Proof

For every original pair i,j, each allowed comparison P_{ij}, including the continuous pair34 family, annihilates E_i: its strict i-first column belongs to the opposite order sector, and its commuting freedom is orthogonal to E_i. Choose the actual native comparison supplied by the bipartite theorem at the first spectator shift; for the other two spectators use their globally locked finite comparisons. All of them annihilate any matrix A supported on E_iH.

Also R_j=I+(Z_j−I)E_j acts as identity on both A and u_jA: E_jA=0 and E_j commutes with u_j because E_j is trivial on its own j-factor. Hence

    A_j(u_j)A=u_jA,
    V_j(u_j)A= u_j*[P_j+(I−P_j)A_j(u_j)]A=A.

The adjoint relation similarly gives V_j A V_j*=A. Each step therefore keeps the native active matrix fixed in the common physical-origin frame. At the final spectator tuple u,

    G_i(A⊕0,u)=U A U*F(I_i,u)=U A.

For the last equality use F(I_i,u)=U D_u D_0, where D_uD_0 reduces E_i and equals identity there (the i-origin is I). Thus A D_uD_0=A. This proves the active term in (1) on every unitary spectator tuple, hence coefficientwise by multilinearity. Subtract this active contribution from the prescribed original embedding to determine the passive term. Private-ancilla equality follows from the coefficient tensor identity.

The actual native comparison at the continuous pair is used only at the first identity-origin step; no global selection of a continuous projector is assumed.

### Simultaneous rigidity at ports3 and4

Suppose both ports3 and4 have their maximal two-branch algebras in one actual independently complete extension, while ports1 and2 remain original. Then the extension is uniquely the simultaneous-column promotion

    G₃₄=J₃(b_bar3)B₃+J₄(b_bar4)B₄+F(b)(I−E₃−E₄).

To prove uniqueness, fix arbitrary original contexts u₁,u₂ and right-normalize at both native identities. The one-port result determines both native single representations. Their active-center projections are U E₃ U* and U E₄ U*, hence orthogonal. The finite-C* bipartite theorem for the two native ports then gives zero on every active3/active4 input pair, because both possible ordered products of their supported images vanish. Undo normalization and use original-input multilinearity to conclude that the active-active coefficient tensor is zero at all contexts.

The remaining terms are determined by the two one-port restrictions and the original tensor. This proves the simultaneous formula. It does not establish simultaneous rigidity when ports1/2 are also independently enlarged, since their non-original contexts are not covered by the one-port argument.

<a id="rg-010"></a>

## RG-010 — Joint native tensor from saturated phase ranks

**Statement.** Orthogonal active carriers and the saturated rank budget force every multi-active native coefficient to vanish, fixing the full joint tensor.

**Status:** source-level result. **Scope:** Joint statement requires phase Parseval and orthogonality; marginal classification alone is insufficient.

### General theorem

Let A_i=A_i^act⊕B_i be finite-dimensional unital C*-algebras, and let G be a normalized independently completely unitary-preserving multilinear map on these algebras, with external boundary dimension D. Let an original process F be included through one-port unital homomorphisms ι_i:B_i→A_i whose passive component is the identity map on B_i.

Suppose there are pairwise orthogonal projections Q_i on the boundary, each reducing its original single, such that:

1. Q_i is the represented central identity of the active ideal at the identity context; write r_i=rank Q_i
2. Every one-port extension, with all other ports restricted to their originals, is a serial-column promotion:

       G(a_i⊕b_i,b_bar_i)=J_i(b_bar_i)A_i+F(b)(I−Q_i),

   where A_i is the origin representation of a_i and

       J_i(b_bar_i)ι_i(b_i)|_{Q_i}=F(b)Q_i

   on the embedded active component
3. The specified original restriction and these one-port identities are actual coefficient identities, not selected numerical tests

Then the ENTIRE simultaneous native extension is uniquely

    G((a_i⊕b_i)_i)=Σ_i J_i(b_bar_i)A_i+F(b)R,
    R=I−Σ_i Q_i.                                    (1)

In particular every tensor coefficient using active inputs from two or more ports is zero. No assumption about pairwise commutation of arbitrary native algebras is made.

### 1. Determine the all-passive coefficient

Fix original unitary inputs b_i. At each native port put the original embedded active unitary multiplied by a phase z_i, and retain b_i on the passive factor. The resulting phase polynomial P(z) is unitary on the torus and multilinear in the pairs of active/passive scalar coefficients.

After left normalization by F(b)*, each single-variable face is

    I+(z_i−1)Q_i.

The finite-C*-algebra version of commuting-embedding rigidity therefore gives

    F(b)*P(z)=∏_i[I+(z_i−1)Q_i]=R+Σ_i z_iQ_i.        (2)

For completeness, commuting-embedding rigidity extends literally from matrix algebras to finite C*-algebras: Hermitian reflections span either algebra, and its signed-reflection proof uses only multiplicativity of the commuting single images. Induct on the number of slots. For a difference vanishing on every proper identity face, the all-sign coefficient gives K*=-K, the all-but-one coefficients give A_iK+KA_i=0, and the constant coefficient gives K*K=0 because the A_i commute. This proves the product formula without a full-matrix-input assumption.

The all-passive coefficient C_∅ depends only on the b_i, not on which active unitary was used in this calculation. From (2),

    C_∅(b)=F(b)R,
    ||C_∅(b)||_HS²=rank R=D−Σ_i r_i.                (3)

The equality rank R=D−Σr_i uses the explicitly assumed orthogonality. Constant individual ranks alone would not imply it.

### 2. Phase Parseval identities at arbitrary active unitaries

Now fix ARBITRARY independent active unitaries a_i and passive unitaries b_i. Write

    P_{a,b}(z)=G((z_i a_i)⊕b_i)_i=Σ_{S⊆[N]} z^S C_S(a,b).

Unitary values on the torus give the matrix Parseval identity and its trace:

    Σ_S C_S*C_S=I,
    Σ_S ||C_S||_HS²=D.                              (4)

For any fixed other phases, view P as A+z_iB. Unitarity for every z_i implies that B*B is a projection: equivalently normalize at z_i=1, obtaining the represented active central projection. Its rank is r_i. To justify that rank uniformly, all unitary contexts in finite-dimensional C*-algebras form a connected product of unitary groups; the normalized active central projection varies continuously, so its rank is constant and equals the identity-context rank r_i.

Averaging ||B||_HS² over all the other phases gives

    Σ_{S:i∈S} ||C_S||_HS²=r_i.

Summing over i,

    Σ_S |S|·||C_S||_HS²=Σ_i r_i.                    (5)

These are exact finite Fourier identities; integration only extracts coefficients and can equally be replaced by a finite roots-of-unity average.

### 3. Saturation forces every multi-active coefficient to vanish

Subtract (4), after separating its constant term (3), from (5):

    Σ_{|S|≥2} (|S|−1)||C_S||_HS²
      =Σ_i r_i−[D−||C_∅||_HS²]=0.

Every summand is nonnegative. Hence C_S=0 whenever |S|≥2, for every arbitrary unitary choice of all active and passive inputs. Those unitaries span each finite C*-algebra, so every such multi-active coefficient map vanishes on all matrices.

For a singleton {i}, restrict the other native ports back to their original embeddings. All terms with another active input have just been shown zero. The given one-port promotion identity therefore identifies

    C_{ {i} }=J_i(b_bar_i)A_i.

Together with (3), this proves (1) coefficientwise. All independent private-ancilla extensions coincide because they are entrywise amplifications of this same tensor. No separate joint-ancilla or unrestricted merged-node assumption is used.

### 4. Application: exhaustive joint original-query interfaces of the quartet

The preceding [RG-009: Passive quotients and unique active serial ideals](native-interfaces.md#rg-009) supplies these hypotheses for every actual joint native extension of the quartet with whole unital original-query inclusions on the fixed sixteen-dimensional boundary. Its Q_i satisfy

    Q₁≤S₁, Q₂≤S₂, Q₃≤E₃, Q₄≤E₄,

and the four larger supports are genuinely orthogonal. Its one-port maps have J_i=U_bar_i restricted to Q_i. Thus every such native family is exactly

    G((a_i⊕b_i)_i)=Σ_i [∏_{j≠i}b_j]A_i+F(b)R_Q,
    R_Q=I−Σ_iQ_i.                                  (6)

This includes proper, non-physical-cylinder Q_i: they need only reduce the original α_i and lie in S_i. It also includes the zero-active-ideal case at any port.

Equivalently, the actual native tensor is a restriction of the known joint maximal promotion on S₁,S₂,E₃,E₄ through the explicit unital one-port homomorphisms

    a_i⊕b_i ↦ [A_i+α_i(b_i)(S_i−Q_i)] ⊕ b_i.

The bracket is the maximal active matrix on S_i. The formula is a *-homomorphism because Q_i and S_i reduce the original factor and the two summands occupy orthogonal blocks.

This exhausts the complete native ORIGINAL-QUERY interface tensors of a hypothetical host after its auxiliary fillers are fixed. It does not bound auxiliary count, promote smaller graph vertices to larger ones, or prove that the maximal promotion itself has a routed host. Those remain the actual graph-realization problem.

### Required proof qualifications

For the all-passive coefficient, commuting-origin rigidity is used before weighted phase Parseval. The identity sum_{|S|>=2}(|S|-1)||C_S||^2=0 is a positive sum, so all multi-active coefficients vanish. A claim inferred only from marginals would miss this step.

<a id="rg-011"></a>

## RG-011 — Context transport and rectangular holonomy

**Statement.** Actual native representations must obey compatible transport along rectangular spectator-context paths.

**Status:** source-level result. **Scope:** Necessary identities for the existing native algebra, not permission to enlarge it.

Assume the global finite-comparison persistence theorem, with fixed comparisons P_j for selected spectators j. In its notation, right-multiply origin u_j by c. Let c_j act on physical factor j. Direct substitution and right normalization give

    π_{u c_j}(a)=V_j(u,c) π_u(a) V_j(u,c)*,
    V_j(u,c)=c_j*[P_j+(I−P_j)β_{j,u}(c)].

Indeed the new normalizer is N(uc_j)=Uβ_{j,u}(c)U*N(u), and the new common frame is Uc_j. Insert the globally valid bipartite comparison identity for H_{j,u}. Since P_j commutes with π_u(A) and β_{j,u}, the result is the displayed unitary conjugation.

In the orthogonal-cylinder phase family with original i-origin fixed, the original spectator single is

    β_{j,u}(c)=R_j(u_j)c_jR_j(u_j)*,
    R_j(u_j)=I+(u_j*Z_ju_j−I)E_j.

It depends on u_j alone. Hence if only origins of spectators other than j have changed, V_j(u,c)=V_j(I,c). The two paths changing distinct spectator origins j and k from identity to c,d therefore give

    Ad(V_k(d)V_j(c))π₀ = Ad(V_j(c)V_k(d))π₀.

The relative unitary

    H_{jk}(c,d)=[V_k(d)V_j(c)]* V_j(c)V_k(d)

commutes with π₀(A). Moreover every fixed P_l commutes with the final native representation, so π₀(A) commutes with

    [V_j(c)V_k(d)]* P_l V_j(c)V_k(d).

Untwisting by R_i reduces all of these to 8×8 multiplicity-space commutators. These are exact necessary conditions for any actual complete native extension. No assumption that the transports commute as matrices is made.

The checker `holonomy_contexts.py` imposes the one-step conditions, all finite-context two-step comparison conjugates, and the rectangular holonomies, using exact Gaussian-rational arithmetic and the seven contexts in the preceding checker. [holonomy_last_ports.py](../holonomy_last_ports.py) repeats the last two queries first as a separate targeted run.

For queries 3 and 4, restricting to their discrete incident comparisons with spectators 1 and 2 gives the following relative-algebra profiles, written (matrix size, carrier rank):

- comparison bits 00: (1,1)+(1,3)+(4,4), unchanged
- bits 01: (1,1)+(1,7), unchanged
- bits 10: (1,1)+(1,3)+(1,4), reduced from (1,1)+(1,3)+(2,4)
- bits 11: (1,6)+(2,2), unchanged

Thus actual two-context consistency excludes the surviving noncommutative M₂ factor of multiplicity two in the bits-10 case. This is a stricter obstruction than separate one-context commutants. The other noncommutative cases remain. Pair 34 still has its continuous comparison family and is not discretized by this theorem.

Finite calculations prove only these necessary algebra containments. They do not assert that any surviving algebra integrates to a complete multilinear native process, much less a routed graph.

### Whole-native context transport

### 1. Native and original data

Use the normalized orthogonal-support quartet on H=(C2)^tensor4. Its
original singles are A_i(x)=R_i x_i R_i, with
R_i=I+(Z_i-I)E_i. Suppose an actual independently ancillary-complete
process G replaces query i by a finite direct sum

    A=direct_sum_b M_(2k_b),

and contains the whole original query through a unital component inclusion
x -> direct_sum_b(x tensor I_(k_b)), up to fixed adapters. Normalize those
adapters and all other origins. Write pi:A->M16 for its single homomorphism.
The relative algebra B=pi(A) intersect A_i' becomes an algebra B0 in M8
after untwisting by R_i:

    R_i B R_i = I_i tensor B0.

Its b-th nonzero simple component is represented as M_(k_b) tensor I_(m_b).
No assumption of faithful representation of every native summand is made.

Choose an outside original query j whose actual pair with i has finitely
many comparison choices. Fix one comparison P actually supplied by the
native/original bipartite theorem, in the convention

    G_(i,j)(a,c)=P pi(a) A_j(c)+(I-P) A_j(c) pi(a).     (1)

It commutes with pi(A) and A_j. Upon restriction to the original query,
P belongs to the exact original comparison family. If the stored pair is
ordered j<i, complement its stored projector to use convention(1).

### 2. Exact context transport of the relative algebra

Shift original query j to an arbitrary c in U2, right-normalize, and
remove the common physical origin c_j. Its native single is

    pi_c(a)=c_j* G_(i,j)(a,c) A_j(c)* c_j
           =V_c pi(a) V_c*,
    S_c=P+(I-P)A_j(c),       V_c=c_j* S_c.            (2)

The first equality includes the right normalizer A_j(c)*. The second
follows because P commutes with pi(a), A_j(c), and hence S_c is unitary.
This is the actual native representation of the shifted process, not an
independently chosen completion of its original pair data.

The frozen all-origin pair formula
[RG-006: All-origin pair geometry](native-interfaces.md#rg-006), Sections2–4,
says that after removing the common c_j, the original single at i is
still exactly A_i. Its own phase Z_i has not changed. Restricting(2) to
the original embedded M2 therefore gives

    V_c A_i(x) V_c*=A_i(x) for every x.

Consequently R_i V_c R_i belongs to the standard i-factor commutant and
has the unique form

    R_i V_c R_i=I_i tensor v_c.                       (3)

Here v_c is a unitary on the eight-dimensional multiplicity space,
real-analytic in c. The relative algebra at this context, in the same
untwisted frame, is exactly v_c B0 v_c*.

### 3. A finite comparison row persists analytically

Select any set of incident original pairs at i whose comparison families
are finite. Their Cartesian product is a finite list of rows

    q_s=(q_(s,ell))_ell,      s in S.

The all-origin theorem makes this same list valid in the common frame
of Section2 for every c. Comparisons remain unchanged by the R_i untwist.
At every c, the actual finite-C* bipartite theorem supplies some row s(c)
commuting with the entire native algebra, hence with v_c B0 v_c*.
No compatibility or commutation between different comparisons is required.

There exists a SINGLE row s such that

    [v_c X v_c*,q_(s,ell)]=0

for every c in U2, every X in B0, and every selected incident edge ell.

Proof. Choose a finite complex basis X_1,...,X_t of B0 and set

    f_s(c)=sum_(a,ell) ||[v_c X_a v_c*,q_(s,ell)]||_HS^2.

These are real-analytic functions on the connected real-analytic manifold
U2. At every c at least one is zero. If none vanished identically, each
zero set would have empty interior by analytic uniqueness. Its complement
would be open and dense, and the finite intersection of those complements
would be nonempty, contradicting their joint zero-set cover. Thus one
f_s is identically zero, which proves the claim. No continuity of the
selected comparison row s(c) has been assumed.

### 4. Exact finite witnesses give rigorous upper bounds

For any finite list of original contexts CsubsetU2, define

    K_(P,s,C)={p, v_c* q_(s,ell) v_c : c in C,ell}'
                 inside M8,                         (4)

where R_i P R_i=I_i tensor p. Then the actual relative algebra B0 is
contained in K_(P,s,C) for at least one actual choice P and one row s.
Indeed it commutes with p from(1), and Section3 gives all other equations.

Thus one may compute all these finitely many commutants exactly and bound
the represented simple summands of B0. Any such bound is uniform over all
actual G: its proof uses finite matrices only as NECESSARY conditions
selected from the already uniform statement of Section3. It does not infer
all-origin sufficiency from sampling. If every candidate commutant is
commutative, no used native summand larger than M2 is possible. More
generally, nonunital embeddings of each M_(k_b) into the displayed exact
represented simple blocks give the appropriate capacity bounds.

For query2 every incident pair has exactly two choices, so rows have three
bits. For queries3 and4, the mutual pair34 has a continuous rank-one
projection freedom. That family must not be replaced by two endpoints.
It is legitimate to omit edge34 from the selected rows: this weakens the
necessary test but leaves all conclusions obtained from(4) valid. The
remaining edges to queries1 and2 give four finite rows. This is the
explicit convention in the companion computation.

### 5. Scope

The theorem allows arbitrary fixed auxiliary unitaries around the native
port, including a surrounding valid cyclic host. It requires a precise
whole-query native inclusion and complete freedom of every native branch.
It does not contract a distributed original-query implementation to a
single node. It supplies neither an extension G for a surviving algebra
nor a routed graph. Origin-dependent native centers and multiplicities
are kept distinct throughout.





**Reproduction limit:** supporting helpers were not supplied; the analytic argument remains available. See the [artifact map](../REPRODUCIBILITY.md#rg-011).

<a id="rg-012"></a>

## RG-012 — Native capacity and analytic carrier methods

**Statement.** Analytic comparison-capacity and contextual-center arguments identify the used rank-four carrier and exclude the specified sectorized M6 enlargements.

**Status:** source-level result. **Scope:** Proof methods supporting the stronger exhaustive RG-007–RG-010 classification; no additional competing interface status.

### 1. Statement

Use the normalized entangled-support M16 quartet and the native model
of [RG-012: Native capacity and analytic carrier methods](native-interfaces.md#rg-012): an actual complete
host G has a finite direct-sum native port, and contains the ENTIRE original
first qubit query unitally in each native summand, up to fixed unitary
adapters. Native branch fillers have the complete independent-ancilla
freedom required by [RG-002: Complete finite-algebra bipartite comparison](foundations.md#rg-002).

Every used native branch of dimension at least six is already excluded
by [RG-012: Native capacity and analytic carrier methods](native-interfaces.md#rg-012). Any used M4
branch must have multiplicity one and the same represented central carrier

    S=I1 tensor P0_2 tensor (I34−q_C),                 (1)
    q_C=proj span{|01>,|−,+>} on34.

Its physical rank is four. Consequently there can be AT MOST ONE used
M4 branch. Every other used branch is M2. Unused summands are ignored
coefficientwise by [RG-018: Reachable native branch capacity](layer-structure.md#rg-018).

On S the native M4 range is the entire L(SH). The other M2 branches may
split the remaining multiplicity space; this theorem neither removes
those splittings nor asserts that the full native tensor is determined
by its single face. In particular it does not alone construct a host.

### 2. What the eight comparison commutants allow for a relative M2

Let pi be the native single representation, and let Z=pi(e) be the
central support of a used M4 summand. Its relative algebra, commuting
with the original A1, is a possibly nonunital M2 in one of the eight
comparison joint commutants on K=qubit2 tensor qubits34. Its unit z has
rank twice the native M4 multiplicity, with Z=I1 tensor z after untwisting.

Put C=q_C, L=I34−q_Phi, and E=I1 tensor P1_2 tensor I34. The exact
locations of the relevant simple components of the audited table are:

| Incident row | Components able to support a relative M2 |
| --- | --- |
| 000,001,010 | full M2 on P0_2 tensor C and on P0_2 tensor Cperp |
| 011 | four full M2 blocks P_eps_2 tensor C_sigma, eps=0,1, C_sigma=C or Cperp |
| 100,101,110 | one M3 block on P0_2 tensor L |
| 111 | two M3 blocks on P0_2 tensor L and P1_2 tensor L |

In an M2 simple block the relative M2 unit is either zero or the whole
block. In an M3 simple block it is either zero or a rank-two projection;
this is the genuine continuous corner freedom absent from the M3-branch
argument. Scalar simple components cannot support it, even if they have
physical multiplicity two, three, or four.

The locations follow from the exact table and its visible input2 blocks.
On input2=0 the other two incident comparisons vanish and q12 splits
34 into C/Cperp in rows0**, or Phi/Phi_perp in rows1**. The full table
exhausts all remaining components. In row011 the comparison P1_2 itself
separates input2, giving the four displayed M2 blocks; row111 similarly
has the two displayed M3 blocks. In all rows the unit z of a relative M2
therefore commutes with the physical input2 projection.

The original untwisting R1 acts only on P0_2 q_Phi. It commutes with
every allowed unit just listed: C is orthogonal to Phi, the entire
Cperp block contains Phi, and every L corner is orthogonal to Phi.
Thus in original physical coordinates

    [Z,E]=0.                                         (2)

Moreover, if Z has a nonzero input2=1 component, the incident comparison
row MUST be011 or111. In either case the native/third comparison is E.
These are conclusions about central carriers; an arbitrary relative M2
corner of an M3 block has not been assumed central in that joint algebra.

### 3. Two elementary orbit facts

First, let f0,f1 be real-analytic functions on a connected real-analytic
manifold, with f0 f1=0 everywhere. Then one function is identically zero.
If f0 is not identically zero, it is nonzero on a nonempty open set, where
f1 vanishes; analytic continuation makes f1 vanish everywhere. One can
justify that continuation directly: the set of points at which all local
derivatives vanish is closed by continuity and open by local analyticity,
so on a connected manifold it is either empty or everything.

Second, both local-third-qubit projection orbits

    {c3 C c3*: c in U2},   {c3 L c3*: c in U2}         (3)

have scalar joint commutant on qubits34. For C, the exact four-Pauli
algebra calculation in Section5 of
[RG-012: Native capacity and analytic carrier methods](native-interfaces.md#rg-012) already generates all M4.

For L it is equivalent to consider the rank-one Bell projection Phi.
Let a Hermitian operator T commute with every c3 Phi c3*. Each corresponding
unit Bell vector psi_c=(c tensor I)|Phi+> is then an eigenvector of T.
Its eigenvalue <psi_c,T psi_c> depends continuously on c and belongs to
the finite spectrum of T. Since U2 is connected, it is constant. The
four Pauli Bell vectors span the entire four-dimensional space, so T is
scalar. Applying this to the Hermitian and skew-Hermitian parts proves
the assertion for the full joint commutant. This proof uses the entire
continuous orbit; the four Bell Pauli projections alone would not suffice.

### 4. No M4 carrier can meet input2=1

Suppose Z E is nonzero. By Section2 the identity native/third comparison
is E. Its exact pair face and RIGHT normalization at original query3=c
give, for native b,

    pi_c(b)=E pi(b)+(I−E) A3(c)pi(b)A3(c)*.            (4)

In particular the representation on EH is unchanged:

    pi_c(b)|E=pi(b)|E.                                (5)

At each c, the native/second pair has some comparison supplied by the
finite-C* pair theorem. Restricting it to the original embedded qubit
makes it one of the two exhaustive original contextual choices

    Q0(c)=I12 tensor c3 C c3*,
    Q1(c)=I12 tensor c3 L c3*.                        (6)

No native full-strictness or continuous choice of that comparison is
assumed. At least one of these two projections commutes with the entire
native single pi_c. Both commute with E, so compression and (5) imply
that, for every c, at least one of the two orbit projections commutes
with the frozen representation pi|E.

Choose a finite Hermitian basis b_mu of the native algebra. For t=0,1,
let f_t(c) be the sum over mu of squared Hilbert–Schmidt norms of

    [pi(b_mu)|E, Q_t(c)|E].

These are nonnegative real-analytic functions on connected U2, and their
product is zero at every c. Section3 implies that one f_t is identically
zero. Either orbit in (3) has scalar commutant on34; hence

    pi(A_native)|E subset M2_1 tensor I34.             (7)

But Z E nonzero means the M4 summand has a nonzero representation on EH:
E commutes with pi because it is a native incident comparison. Such a
representation of the simple algebra M4 is injective, and cannot fit in
the four-dimensional algebra M2_1 tensor I34. This contradiction proves

    Z≤I−E=I1 tensor P0_2 tensor I34.                   (8)

The argument applies branch by branch even if several native summands
are present. It handles the continuous relative M2 corners inside M3
without selecting one comparison branch continuously.

### 5. Original query2 forces the unique remaining carrier

Choose the exact identity native/second comparison Q. It is either

    Q0=I12 tensor C,       or       Q1=I12 tensor L.    (9)

It commutes with pi and A2. Right normalization at original query2=c
therefore gives

    Z_c=Q Z+(I−Q) A2(c) Z A2(c)*.                     (10)

The original second single has its twist supported on E2, whose 34
Schmidt support is C. Thus on either complementary space in (9), its
action is the ordinary physical c2. Both Q choices are trivial on qubit2.
Using [Q,Z]=0, (10) becomes

    Z_c=QZ+c2(I−Q)Zc2*.                              (11)

At this original query2 context the exact comparison table is conjugated
by c2 in the retained all-origin frame. Its relative M2 units still have
the positions of Section2. Untwisting introduces no change to those units,
so every possible contextual M4 carrier satisfies

    [Z_c,c2 E c2*]=0.                                 (12)

Conjugating (11)–(12) by c2*, the term (I−Q)Z commutes with E by (2).
It follows that

    [QZ,c2 E c2*]=0 for every c in U2.                 (13)

The orbit of the physical qubit2 rank-one projection spans that full M2.
Hence QZ commutes with every operator on qubit2. Yet QZ is supported on
input2=0 by (8). No nonzero operator with that support can commute with
the full qubit2 factor, so QZ=0.

If Q=Q1, Section2 places the whole relative M2 carrier inside L, giving
QZ=Z and a contradiction. If Q=Q0, the only possible input2=0 relative
M2 units are the full C and Cperp components, separately or together.
The condition QZ=0 leaves precisely the nonzero carrier (1).

Its relative rank is two, so the native M4 multiplicity is one. Distinct
native simple summands have orthogonal represented centers. Two used M4
summands would both have the same nonzero center S, which is impossible.
Combining this with the already proved exclusion of all used branches
of dimension at least six proves Section1.

### 6. Boundary of the result and a constructive feature

For a minimal M4 direct-sum M2 port, a used M4 branch therefore has
multiplicity one and the passive original-qubit M2 has multiplicity six.
The represented range on S is all M4, while on its complement the single
M2 acts as the original A1. In a larger native direct sum, extra M2
central splittings are not excluded by this theorem.

The survivor has a useful feature: S contains the original support E1
and is orthogonal to E2,E3,E4. Every allowed native incident comparison
annihilates S, and the required center motion under the other original
queries agrees with their physical product conjugation. Thus the preceding
M6 center mismatch does not exclude this carrier. The separate source
[RG-015: Joint quartet column promotion](serial-interfaces.md#rg-015) now constructs an
actual complete extension on this carrier. Its global routed host remains
open. No pair table or single-algebra embedding alone is promoted to a
host or a route here.

The helper `check_quartet_unique_m4_carrier_round35.py` independently
checks all eight simple-component locations, finite generating subsets
of the two projection orbits, and the symbolic Hadamard defect identity
whose off-diagonal block is −qT/2. Its result is
`quartet_unique_m4_carrier_round35_checks.json`. These finite identities
support the proof; the analytical argument supplies the all-context and
complete-process implications.

### Comparison-capacity calculation

### 2. General incident-comparison capacity test

For each j!=i, freeze every other port of G at its normalized origin.
The retained exact bipartite unitary-process theorem provides a comparison
projection Q_ij commuting with pi(M_r) and A_j and satisfying

    G_ij(a,b)=Q_ij pi(a)A_j(b)
               +(I-Q_ij) A_j(b)pi(a).               (3)

Restrict (3) to the embedded original M_(d_i). Thus Q_ij is one of the
exact comparison choices for the original actual pair F_ij. No compatible
choice among different j is assumed; the projections may fail to commute
with one another. Each must nevertheless commute with the SAME pi(M_r).

Untwist A_i to M_(d_i) tensor I_(D/d_i). Write each selected Q_ij as
I_(d_i) tensor q_ij and define its multiplicity-space joint commutant

    C_i(q)={q_ij: j!=i}' inside M_(D/d_i).             (4)

Equations (2)--(3) imply a **unital** embedding M_k -> C_i(q).
If C_i(q) is abstractly the direct sum of the simple matrix algebras
M_(n_a), then

    k divides every n_a.                              (5)

Indeed composition with each simple-coordinate projection is a unital
representation M_k -> M_(n_a); all irreducible representations of M_k
have dimension k. Conversely, this divisibility is sufficient for an
abstract unital embedding into C_i(q), but it supplies only this necessary
pair-data test, not an extension G or a route.

This proof uses the ordinary full-factor bipartite classification. It
does not silently extend that theorem to a superselected replacement
algebra. In particular no M6 directsum M2 conclusion is inferred from
(5).

### 3. Exact first-port comparison choices of the quartet

Use the actual M16 quartet and conventions from
[RG-006: All-origin pair geometry](native-interfaces.md#rg-006). At the identity
origin its first single factor is

    A_1(x)=R_1 (x tensor I_234) R_1,
    R_1=I+(Z_1-I)P0_2 q_Phi,
    q_Phi=|Phi+><Phi+| on34.

Every incident comparison commutes with R_1. Thus conjugating by R_1
untwists A_1 without changing the comparison projections. On the
eight-dimensional multiplicity space 234, the exhaustive choices are

    q_12^0=I_2 tensor q_C,
    q_12^1=I_2 tensor (I_34-q_Phi),
    q_13^0=P1_2 tensor I_3 tensor P0_4,
    q_13^1=P1_2 tensor I_34,
    q_14^0=P1_2 tensor Pplus_3 tensor I_4,
    q_14^1=P1_2 tensor I_34,                           (6)

where C=span{|01>,|-,+>} and

    q_C=(1/3) [[1,0,-1,-1], [0,3,0,0],
               [-1,0,1,1], [-1,0,1,1]].

Exhaustion follows from the exact rank-four commuting carriers of each
of these three original pairs: their multiplicity is one, so only the
zero or whole commuting carrier can be added to the strict comparison.
The frozen proof establishes this for every original origin, not
only for generic operations.

### 4. The eight represented joint commutants

The following are the complete C*-algebra decompositions of (4) on its
physical eight-dimensional space. In the table, M_n tensor I_t has
physical sector rank n t. Repeated scalar summands are independent.

| Bits (12,13,14) | Represented joint commutant | Complex dimension | Center dimension |
| --- | --- | ---: | ---: |
| 000 | C directsum C I3 directsum M2 directsum M2 | 10 | 4 |
| 001 | C directsum C directsum C I2 directsum M2 directsum M2 | 11 | 5 |
| 010 | C directsum C directsum C I2 directsum M2 directsum M2 | 11 | 5 |
| 011 | M2 directsum M2 directsum M2 directsum M2 | 16 | 4 |
| 100 | C directsum C I4 directsum M3 | 11 | 3 |
| 101 | C directsum C directsum C directsum C I2 directsum M3 | 13 | 5 |
| 110 | C directsum C directsum C directsum C I2 directsum M3 | 13 | 5 |
| 111 | C directsum C directsum M3 directsum M3 | 20 | 4 |

The companion exact certificate
`check_quartet_native_enlargement_round34.py` forms the three commutator
equations over the rationals, computes their common kernel, and computes
the center of this resulting algebra. It then constructs a separating
Hermitian central element with distinct rational eigenvalues. Its exact
spectral projections give every displayed physical central-sector rank;
the dimension of the algebra compressed to each sector is the displayed
simple matrix size squared. Thus the table records the actual represented
block sizes and multiplicities, not a guessed decomposition from the
overall dimension alone.

For the especially relevant row011 the decomposition is also immediate:
q_13=q_14=P1_2, while q_12=I_2 tensor q_C. Their four joint eigenspaces
have dimension two. For row111 replace the rank-two q_C by the rank-three
I-q_Phi; the two input2 values each give dimensions three and one.
The other six rows are checked by the exact rational central projectors.

### Unrestricted-enlargement obstruction

### 2. The only possible dimension4 data

Normalize as in that source. Denote the replacement single embedding by
B:M4->M16 and the original singles by A2,A3,A4. The enlargement restricts
to the exact original A1 on its embedded M2. Put

    E=I1 tensor P1_2 tensor I34,
    Q=I12 tensor q_C,
    C=span{|01>,|-,+>} on34.

The original identity comparisons forced by the pair-data invariant are

    P_(B,2)=Q,             P_(B,3)=P_(B,4)=E.          (1)

Each commutes with B and its other endpoint. The range of E has dimension
eight, so B restricted to EH is a nonzero unital M4 representation there.

### 3. The enlarged pair stays full strict in every query3 context

Freeze the original third input at any c in U2, with fourth input identity,
and normalize by the resulting one-slot output A3(c). Let B_c and A2_c
be the replacement and second-port single factors in this actual pair.
Their restriction to the original embedded M2 at the replacement port
is exactly the original quartet's normalized pair12 in that same context.

The quartet's all-origin theorem makes the common commuting carrier of
that restricted pair rank four at every c. Hence the common commuting
carrier of B_c(M4) and A2_c(M2) has rank at most four. A nonzero such
carrier would support a unital representation of M4 tensor M2=M8 and
would therefore have rank at least eight. It must be zero. Thus the
replacement/second pair is full strict for EVERY c in U2.

Its exact comparison Q_c is unique and depends continuously on c. For
example it is recovered by the finite commutator Gram inverse, whose
Gram is nonsingular by the preceding full-strict argument. A continuous
projection on connected U2 has constant rank, so rank Q_c=rank Q=8.

Restricting its pair formula to the original first query makes Q_c one
of that quartet pair's exact comparison choices. By the retained
all-origin formula these choices are

    c3 Q c3*,
    c3 [I12 tensor (I34-q_Phi)] c3*,                  (2)

where c3 acts on the original physical third factor. Their ranks are
eight and twelve. Therefore the unique rank-eight choice is forced:

    Q_c=c3 Q c3*.                                     (3)

This is a global statement over U2, not an assumption that full
strictness survives only near identity. No inverse-query operation is
introduced; normalization is merely the standard output frame change.

### 4. The native algebra is frozen on the E sector

The exact actual pair face between the replacement port and original
query3, using (1), is

    G_(B,3)(b,c)=E B(b)A3(c)+(I-E)A3(c)B(b).

Normalize its output by A3(c)*. Since E commutes with both endpoint
factors, this gives

    B_c(b)=E B(b)+(I-E)A3(c)B(b)A3(c)*.              (4)

Consequently the E block of B_c is precisely the unchanged B(b)|E.
Every exact pair comparison commutes with its endpoint singles. Equations
(3)--(4) imply

    [B(b)|E, I1 tensor c q_C c*]=0
       for all b in M4 and all original c on qubit3.   (5)

Here the qubit2 factor has been fixed to its E=1 value; E commutes with
the comparison orbit because all c act on qubit3. The surviving physical
space is qubit1 tensor qubits34.

### 5. The local-query orbit of q_C has scalar commutant

It suffices to use c=I,X,Y,Z on qubit3. In Pauli notation on34,

    q_C=I tensor (3I+X-Z)/6
        -X tensor (I+X+Z)/6
        +Y tensor Y/6
        +Z tensor (I-X-Z)/6.                          (6)

The four Pauli conjugates isolate each of these four Pauli components
by signed averaging. The generated unital algebra therefore contains
I tensor (X-Z), Y tensor Y, and the displayed X and Z components.
Commuting the latter two with I tensor (X-Z) gives nonzero scalar
multiples of X tensor Y and Z tensor Y. Products with Y tensor Y then
give Z tensor I and X tensor I, hence the full first-qubit M2 tensor I.
Multiplying Y tensor Y by Y tensor I supplies I tensor Y. The two
noncommuting matrices Y and X-Z generate the second M2. Thus the orbit
algebra is the entire M4 on34, and its commutant is scalar.

Equation(5) now forces

    B(M4)|E subset M2_1 tensor I34.

This is impossible: the left side is a nonzero unital representation
of the simple algebra M4 and is injective, whereas the right side is
only M2. This contradiction excludes the last possible dimension4
enlargement and proves the conclusion.

### Sectorized capacity calculation

### 2. A nonunital capacity test on each native branch

Untwist A_1 to M2 tensor I8 with the retained unitary R_1. The exact
incident comparisons are unchanged by this conjugation. For a choice
row b=(b12,b13,b14), let C_b be their joint commutant on the eight-dimensional
original-qubit multiplicity space K=C8.

On a represented native branch s, the relative algebra inside pi(M_(2k_s))
that commutes with A_1 is a copy of M_(k_s), with physical multiplicity m_s
on K. Its unit is the branch projection z_s, where Z_s=I2 tensor z_s.
It is a possibly NONUNITAL subalgebra of C_b, and

    rank_K z_s=k_s m_s.                                (2)

If C_b is represented as a direct sum of simple blocks M_n tensor I_t,
then on each such block a nonzero representation of M_(k_s) has unit of
rank a multiple of k_s in M_n. This follows by restricting to its unit
and using the dimensions of irreducible M_(k_s) modules. The total n
does not need to be divisible by k_s when that unit is proper. This is
why the earlier UNITAL full-factor capacity test cannot simply be reused.

In particular:

* if k_s exceeds every simple size n, then m_s=0;
* for k_s=3 and n≤3, its unit on an M3 block is either zero or the entire
  identity, and it vanishes on all M1 and M2 blocks.

Thus any M3 relative branch occupies whole M3 simple blocks of C_b.
Its represented center is then CENTRAL in C_b, even though this is not
true for a general smaller relative branch.

### 3. The exact M3 carriers of the quartet comparison table

Write Phi=|Phi+><Phi+| on qubits34 and L=I34−Phi. On K=qubit2 tensor
qubits34, the rows with b12=1 have

    q12=I2 tensor L,
    q13^0=P1_2 tensor I3 tensor P0_4,
    q13^1=P1_2 tensor I34,
    q14^0=P1_2 tensor Pplus_3 tensor I4,
    q14^1=P1_2 tensor I34.                             (3)

The audited table in [RG-012: Native capacity and analytic carrier methods](native-interfaces.md#rg-012)
gives the following complete list of M3 simple carriers:

| Incident row | M3 carriers in the physical multiplicity space K |
| --- | --- |
| 000,001,010,011 | none |
| 100,101,110 | P0_2 tensor L, once |
| 111 | P0_2 tensor L and P1_2 tensor L, once each |

Here every M3 block has multiplicity one. The carrier locations follow
directly from (3), in addition to their abstract block sizes. On input2=0,
both q13 and q14 vanish, and q12 splits the Bell line from its rank-three
complement. Hence P0_2 tensor L is a full M3 commutant block in every
row1**. For row111, both q13,q14 equal P1_2, so the same Bell/complement
split also occurs on input2=1. The retained exact table exhausts the other
simple components and shows that rows100,101,110 have no second M3 block.
Rows0** contain only simple sizes at most two.

There are no possible off-diagonal central carriers joining these blocks:
they are inequivalent joint representations of the selected comparison
algebra. In particular row111 distinguishes the input2 values by q13,
and distinguishes the Bell line from its complement by q12.

All incident comparison projections commute with R_1, and R_1 is the
identity on the full carrier I2 tensor L. Therefore twisting back to
the original A_1 representation does not move any M3 carrier in this table.
The same displayed carrier projections apply in the original physical
quartet coordinates, with an additional identity on qubit1.

### 4. Exact consequences for M6 direct-sum M2

For A_native=M6 direct-sum M2 with multiplicities (k,l), equation(1) is

    6k+2l=16,  or equivalently 3k+l=8.                 (4)

If the M6 branch is present, the possibilities are exactly (k,l)=(1,5)
or (2,2); in particular the M2 branch is then present as well. If the
M6 branch is absent, (k,l)=(0,8). It is impossible for only the M6 branch
to occur, because6 does not divide16.

Let Z=pi(1_M6 direct-sum 0). If k=1, the comparison row must be one of
100,101,110,111 and

    Z=I1 tensor P0_2 tensor L                          (5)

for the first three rows. In row111 it is either (5) or

    Z=I1 tensor P1_2 tensor L.                         (6)

There is no continuous family of other rank-six carriers: the relative
M3 occupies one WHOLE simple M3 component, so its unit is precisely the
corresponding central projection. On this six-dimensional Z carrier,
pi(M6) is the entire matrix algebra L(ZH), since its multiplicity is one.
On the complement the native M2 is the original first-qubit representation
with multiplicity five. Thus the operator range of the native single
algebra is determined by its carrier, though an internal algebra
identification still admits the usual unitary coordinate freedom.

If k=2, the comparison row is forced to111 and

    Z=I12 tensor L.                                   (7)

This uses both rank-three M3 commutant components. The relative M3 acts
diagonally on those two copies, possibly with different inner coordinate
identifications. The capacity argument fixes the rank-twelve central
carrier, not every matrix in the embedded multiplicity-two M6 algebra.
Its complementary native M2 carrier is I12 tensor Phi, of rank four.

### 5. The same carrier constraints hold for a branch of a larger algebra

Nothing in Sections2–3 used the presence of only two native summands.
For ANY A_native of Section1, every summand with k_s≥4 must be absent
in the single representation, since the largest simple size in every
incident-table joint commutant is three. Every present summand with k_s=3
has multiplicity m_s=1 or2 and exactly the carriers (5)–(7), with the
same row restrictions. Other native summands may occupy the remaining
simple components, but they cannot alter these M3 carriers.

This assertion is deliberately specific to relative M3 or larger branches.
A relative M2 can occupy a proper rank-two corner inside an M3 block.
One must not conclude from the full-factor M4 no-go that every sectorized
native M4 summand is absent. The nonunital representation issue is real.

At a shifted ORIGINAL quartet origin u, the complete family of incident
comparison choices is conjugated by the common product U=tensor_i u_i,
as in the retained all-origin theorem. Untwisting A_1 again introduces
no change on the M3 carriers after passing to that common frame, because
the phase R_1(u) is still identity on I2 tensor L. Therefore every present
native M6 branch at that origin has carrier

    U[I1 tensor P_eps_2 tensor L]U*,   eps in{0,1},

when its multiplicity is one, or

    U[I12 tensor L]U*

when its multiplicity is two. The row restrictions above persist.
This is a statement about the actual normalized single representation
at that context; it does NOT assume that its center stays fixed when
other original queries change.

### Contextual-center contradiction

### 2. Single representations and absent native branches

Normalize at identity and write pi for the native single representation.
Complete unitary preservation makes pi a unital *-homomorphism, whose
restriction along iota is the original single factor A1. Let e6,e2 be the
two native central units. If pi(e6) is nonzero, the multiplicities k,l obey

    6k+2l=16,

so (k,l)=(1,5) or (2,2). In particular both summands are then faithful.

If instead pi(e6)=0, this summand cannot appear only at higher order. For
any tuple z of unitaries at the three other original ports, put

    U_z=G(1,z),       pi_z(b)=G(b,z) U_z*.

The normalized native slice is a unital homomorphism by the same complete
single-map argument. Thus pi_z(e6) is a continuous projection as z ranges
over the connected product U2^3. Its rank is constant, and is zero at the
identity. Hence G(e6 b,z)=0 for all b and all unitary z. Unitaries linearly
span each original matrix algebra, so multilinearity makes the same
identity hold for every matrix tuple. This proves the claimed global
irrelevance of an absent native summand.

### 3. Exact all-origin capacity table, with its central carriers

Use right normalization, as in the frozen quartet pair theorem. Define

    Q=I12 tensor (I34-q_Phi),
    E=I1 tensor P1_2 tensor I34,
    Z_0=I1 tensor P0_2 tensor (I34-q_Phi),
    Z_1=I1 tensor P1_2 tensor (I34-q_Phi).

The original first single is A1(x)=R1(x1 tensor I234)R1, where
R1=I+(Z1-I)P0_2 q_Phi. In particular R1 fixes Q,Z_0,Z_1 pointwise.
It commutes with every incident comparison.

The native bipartite theorem supplies an exact comparison for each native
pair. Restriction along iota makes it one of the original exhaustive two
choices on that pair. Untwist A1 by R1. On the eight-dimensional multiplicity
space the three chosen comparisons and their joint commutant are precisely
the audited table in [RG-012: Native capacity and analytic carrier methods](native-interfaces.md#rg-012).
The relative native algebra is M3 directsum C, represented with multiplicities
k,l, and is contained in that joint commutant.

The necessary part of that exact represented table is:

| bits (12,13,14) | M3 simple corners and their physical carriers in 234 |
| --- | --- |
| 000,001,010,011 | none; all simple sizes are at most2 |
| 100,101,110 | one M3, on P0_2 tensor Phi_perp |
| 111 | two M3's, on P0_2 tensor Phi_perp and P1_2 tensor Phi_perp |

Every displayed M3 corner has representation multiplicity one. These are
exact central carriers, not merely dimension estimates. The single M3 in
the middle row is already visible on the P0_2 block, where the other two
comparisons vanish. The complete audited table shows there is no second
M3 elsewhere. For row111 the decomposition is the simultaneous input2 and
Phi/Phi_perp decomposition. The new helper independently checks the exact
central projectors in all eight rows.

A nonzero representation of M3 in a simple summand of size at most3 must
use an entire M3 summand. Its support cannot occupy a proper subspace of
one of those corners, or any M1/M2 corner. Thus:

* If k=1, pi(e6) is exactly Z_0 or Z_1. The first pair comparison is Q.
  The Z_1 choice is possible only in row111.
* If k=2, only row111 is possible, and pi(e6)=Q. The native comparisons
  with ports3 and4 are both E. The embedding of the same M3 into its two
  corners may have an arbitrary inner relative identification; the center
  Q and the comparison conclusions are independent of that identification.

In the k=1 case the full represented native algebra image is uniquely
determined by its chosen center: it is full M6 on that carrier and the
original first-query M2 with multiplicity5 on its complement. Inner changes
of the abstract M6 coordinates do not change this represented image.

Now freeze any original unitary origins u2,u3,u4 while leaving u1=I. Put
U=I1 tensor u2 tensor u3 tensor u4. In the common U frame the first single
is still R1 x1 R1 and every original comparison family is unchanged by the
exact all-origin theorem. Therefore the same table and relative-algebra
argument apply after decoding by U R1. Since R1 fixes the above carriers,
in the actual right-normalized output frame the necessary native centers
are exactly

    rank6: U Z_0 U* or U Z_1 U*,
    rank12: U Q U*.                                   (2)

The native single representation is always taken at that actual context.
Equation(2) is not an assertion that a native center normally follows a
chosen coordinate rotation; it is a necessary consequence of all three
actual contextual pair faces and the exhaustive quartet comparison table.

### 4. Rank-six contradiction from the second original query

Suppose pi(e6)=Z_epsilon, epsilon=0 or1. Section3 forces the native/second
pair comparison to be Q. For b in the native algebra and c in U2, the pair
formula is

    G_(B,2)(b,c)=Q pi(b) A2(c)+(I-Q) A2(c) pi(b).

Right normalization gives

    pi_c(b)=Q pi(b)+(I-Q) A2(c) pi(b) A2(c)*.           (3)

Q commutes with A2 and Z_epsilon<=Q. Evaluating (3) at the central native
unit e6 therefore yields

    pi_c(e6)=Z_epsilon                                (4)

for every c. The actual native center has stayed fixed, even though its
carrier need not commute with A2 itself.

Choose c=H, the Hadamard unitary, at original query2. Equation(2) requires
the same rank-six center to equal H2 Z_0 H2 or H2 Z_1 H2. These are the
Pplus_2 and Pminus_2 carriers tensored with I1 and Phi_perp; neither equals
Z_epsilon. Each squared Hilbert--Schmidt difference is6. This contradicts
(4) and excludes both rank-six placements, independently of the last two
identity comparison bits.

### 5. Rank-twelve contradiction from the third original query

Suppose pi(e6)=Q. The only possible row is111, so the native/third pair
comparison is E. Freezing query3 at c and right-normalizing gives

    pi_c(e6)=E Q+(I-E) A3(c) Q A3(c)*.                 (5)

Because E commutes with A3, the first term is an unchanged rank-six block
and the second is a unitarily moved rank-six block. Thus the center still
has rank12. In particular

    E pi_c(e6) E=E Q.                                 (6)

Equation(2), applied at the same context, instead requires pi_c(e6)=c3 Q c3*.
Since E commutes with c3, its E corner must be E c3 Q c3*. At c=X this is
different from E Q: X on qubit3 takes Phi to the orthogonal Bell vector Psi.
The squared Hilbert--Schmidt difference of these E corners is4. This
contradicts (6), independently of how the two active M3 copies were coupled.

No continuous comparison selection, full strictness of a native pair, or
claim that four Bell Pauli projectors generate M4 is used in either case.
Only the exact finite centers and one actual original context per case
are needed.





**Reproduction limit:** supporting helpers were not supplied; the analytic argument remains available. See the [artifact map](../REPRODUCIBILITY.md#rg-012).
