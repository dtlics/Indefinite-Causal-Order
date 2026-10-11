# Auxiliary geometry

[Topic index](../../README.md) · [Shared result index](../../../../RESULTS.md#rg--exact-native-routed-graph-universality)

Each result below has one owner. Exact scope and proof are updated here. Source-level mathematical arguments and finite certificates are distinguished from a new formal verification.

<a id="rg-059"></a>

## RG-059 — Complete auxiliary tangent space and integrability tests

**Statement.** The exact complete real tangent dimension is 583, with a 557-dimensional boundary/cut family and 26 rational extra directions.

**Status:** source-level result. **Scope:** First-order completeness is not integrability. Thirteen chosen extra representatives fail norm invariance; others passing finite tests are not certified extensions.

### 1. The real-linear space

Let F be the normalized quartet. For an arbitrary complex multilinear coefficient tensor C on the same original queries and boundary, define the complete tangent condition

    F(U)† C(U) = C(U)† F(U)                         (1)

for every tuple of independently arbitrary private-ancilla unitary extensions of the four original queries.

Every actual complete auxiliary extension G(a,x), normalized by G(1,x)=F(x), supplies elements of this space: for every self-adjoint auxiliary H, differentiate G(exp(i tH),x)†G(exp(i tH),x)=I at t=0 to obtain C=G(H,x).

Condition (1) alone does not imply an auxiliary extension. An actual auxiliary algebra also requires its whole pointwise representation law, e.g. the compatibility of G(H²,x) with G(H,x)†G(H,x). Arbitrary first-order directions need not integrate into a finite native unitary slot.

### 2. Why finite operator-block word equations are exact

Write the original extended qubit U_i as a 2-by-2 matrix of arbitrary operators u_{ab} on its private ancillary space. Every term of F†C or C†F has at each party exactly one word u_{ab}†u_{cd}. Use only

    sum_a u_{ab}†u_{ad}=δ_bd I.

Eliminate the four words u_{1b}†u_{1d}, replacing each by δ_bd I−u_{0b}†u_{0d}. This leaves a 13-dimensional formal word space: the constant plus twelve unreduced words. No within-party scalar commutation is used.

These thirteen operator-valued functions are linearly independent already when the private ancillary dimension is two. Here is a finite-dimensional justification, avoiding an assumption that formal words are automatically independent. An equivalent basis is the constant and the twelve functions

    [U†(σ_k⊗I_2)U]_{bd},  k=X,Y,Z,  b,d=0,1,

where the bracket is the physical-qubit block, an operator on the private ancilla. If a linear combination vanishes for all U∈U(4), take one fixed off-diagonal ancillary matrix entry r≠s. The resulting scalar functions are matrix coefficients of the conjugation representation on traceless M4. That representation is irreducible: a nonzero invariant complex subspace under all unitary conjugations contains a nonzero traceless matrix unit or diagonal difference and their unitary conjugates, hence all traceless matrices. Matrix-coefficient orthogonality for this finite-dimensional unitary representation, or its elementary Haar average, implies that a relation among its coefficients is precisely a relation among the corresponding tensors of input/output vectors. The three input matrices σ_k⊗I are independent; the four output matrices |d><b|⊗|s><r| are independent and traceless. Thus all twelve coefficients vanish. A diagonal ancillary entry then kills the constant coefficient.

Independence at four independent parties follows by tensoring these finite function spaces and their separating evaluation functionals. Therefore (1) is equivalent to vanishing of all reduced word coefficients. This proves both necessity and sufficiency for every independent private-ancilla dimension.

### 3. Exact XOR block decomposition and anti-linearity

The quartet coefficient belonging to original matrix units with output word o and input word a is

    T_{o,a}=|o><a| V_o D0.

Each has only future row o. For an arbitrary C coefficient, group its future row r and original query-output word o by their bitwise XOR δ=r xor o. The reduced equations preserve this XOR label, because a unitary relation only removes equal output rows at a party.

There are therefore sixteen independent blocks, each with 4096 complex coefficient variables. Since the T_{o,a} are real, split C=C_real+i C_imag. The real equations are

    F† C_real−C_real† F=0,

while the imaginary equations have the **opposite** sign,

    F† C_imag+C_imag† F=0.

The exact enumeration solves both systems separately. In particular, a nonzero-XOR future-Hamiltonian block contains eight real-symmetric directions and eight imaginary-antisymmetric directions; neither sector is discarded.

### 4. Exact rank certificates so far

[auxiliary_tangent_output_block.py](../auxiliary_tangent_output_block.py) directly enumerates the reduced coefficient equations. It saves, for every rank-contributing row, its normal-word label and boundary matrix entry. Coefficients are exact integers after scaling F by four; row reduction is over the prime field F_1000003, providing a rigorous lower bound on the rational/real constraint rank. The explicit row identifiers permit exact recomputation independently of saved echelon forms.

Across the 32 real/imaginary systems, the resulting upper bound on the complete tangent-space real dimension is 583. The only blocks exceeding the ordinary future-Hamiltonian directions are δ=0,1,2,4,8,12 (bits are in the standard four-bit output-word order).

The independently constructed boundary-plus-supported-cut family is

    C=F H_p + H_f F + sum_{L∈{{1},{2},{3},{4},{1,2}}} F_R H_L F_L,

where H_p,H_f are arbitrary Hermitian M16 matrices and H_L is an arbitrary Hermitian matrix on the proved cut carrier K_L. Every summand satisfies (1) completely by the supported-cut identities. Its explicitly generated coefficient vectors have total dimension 557 (exact modular independence, with the matching elementary parameter-count upper bound). The generator record is in [auxiliary_tangent_cut_span_checks.json](../auxiliary_tangent_cut_span_checks.json).

The cut-family parameter count is 568. Eleven explicit independent parameter redundancies lower its dimension to at most 557: the shared scalar between past and future multiplication, and the ten serial-support matrices commuting with their α_i, whose serial insertions coincide with past insertions. The modular lower bound is 557, so this cut-family dimension is exact.

The gap has now been closed constructively. [auxiliary_tangent_extract_extra.py](../auxiliary_tangent_extract_extra.py) finds free-coordinate complements of the explicit cut span in each retained modular echelon system and lifts them to rational vectors, with denominators at most 12 and numerator magnitudes at most 78. [auxiliary_tangent_verify_extras.py](../auxiliary_tangent_verify_extras.py) then verifies **every** reduced operator-block coefficient equation for all 26 lifted vectors over the integers, not modulo a prime. The arithmetic has a conservative absolute bound 9984, so no int64 overflow is possible. Their independence modulo the cut span is retained under rational lifting. Consequently the complete tangent-space real dimension is exactly 557+26=583.

The extra quotient dimensions are:

- δ=0: nine real-coefficient and seven imaginary-coefficient directions
- δ=1 (query4 output difference): one in each sector
- δ=2 (query3): one in each sector
- δ=4 (query2): three in each sector

All other XOR blocks are exhausted by the explicit cut/boundary directions.

### 5. Initial integrability checks and their limited conclusion

For a genuine auxiliary Hermitian H, the operator J_H(U)=F(U)†G(H,U) is a represented copy of H at every context. In particular its spectrum and squared Hilbert–Schmidt norm are context-independent.

[auxiliary_tangent_extra_integrability.py](../auxiliary_tangent_extra_integrability.py) checks this invariant exactly on the chosen rational extra representatives. Thirteen already have unequal squared norms at an identity and a Pauli-X context, excluding those particular tensors as G(H,·) for every Hermitian H. All thirteen remaining chosen representatives passed the recorded rational-rotation norm tests, which alone prove nothing positive. Two of them have since been rescaled to genuine projection-valued sections of ranks4 and5: every reduced coefficient of C†C−F†C vanishes exactly. Their complete C⊕C extensions and independent audits are in [RG-060: Two complete phase slots beyond the cut/local span](auxiliary-geometry.md#rg-060) and [RG-060: Two complete phase slots beyond the cut/local span](auxiliary-geometry.md#rg-060). Thus a blanket non-integrability claim for the extra quotient is false.

This does not exclude arbitrary linear combinations of extra directions, or their translates by the 557-dimensional cut/boundary space. First-order Hermiticity is not an auxiliary matrix-unit product law, even when a tangent is part of a continuous family of complete processes.

### Scope

This finite coefficient calculation is intended to constrain repeated-multiplicity auxiliary vertices, beyond the preceding multiplicity-free theorem. It is not a scalar sampling test. Still, first-order completeness alone does not establish a process, auxiliary algebra, route, or weak-loop host. Further spectral and multiplicative constraints are essential.

### Required proof qualifications

The upper dimension bound is a nonzero exact modular-minor certificate; the lower bound is supplied by 557 boundary/cut directions and 26 rational lifts whose every reduced word coefficient vanishes over the integers. This matching upper/lower argument, rather than a modular numerical guess, proves dimension 583.

<a id="rg-060"></a>

## RG-060 — Two complete phase slots beyond the cut/local span

**Statement.** Explicit projection sections give complete C direct-sum C extensions of ranks 4/12 and 5/11 beyond the stated cut/local family.

**Status:** source-level result. **Scope:** Exact characteristic-zero nonmembership and specific same-coefficient promotion obstruction; no routed host.

### 1. Closed coefficient formulas

Use the normalized quartet row tensor

    F(U)_{o,p}=<o|W(U) V_o D0|p>,
    W=U1⊗U2⊗U3⊗U4,  V_o=I−2 sum_i o_i E_i.

Define two ordinary diagonal projectors on the four laboratory INPUT qubits, with omitted factors equal to identity:

    P_(4)=|0><0|_1 |0><0|_4 + |1><1|_1 |0><0|_3,
    P_(5)=|0><0|_3 + |0><0|_1 |1><1|_2 |1><1|_3.

Their ranks are 8 and 10 respectively; their own qubit factors 2 and 4 are identities. Define multilinear coefficient tensors

    C_4(U)_{o,p}=1_{o2=0} <o|W(U) P_(4) V_o D0|p>,
    C_5(U)_{o,p}=1_{o4=0} <o|W(U) P_(5) V_o D0|p>.     (1)

The subscripts 4 and 5 refer to their represented ranks on the original boundary, not the ranks of P_(4),P_(5).

These formulas agree exactly with rational tangent representative0 divided by4 and representative6 multiplied by−1 in [auxiliary_tangent_extra_directions.json](../auxiliary_tangent_extra_directions.json). Unlike the earlier safe-table phase masks, these are masks on the original laboratory INPUT/OUTPUT coefficient labels (o,n), not on external source labels (o,p). Mixing up those two notions would give a false contradiction with the 35-dimensional table-mask theorem.

### 2. Complete projection identities

For both C=C_4,C_5, the following are exact under independently arbitrary private ancillas at all four original queries:

    F†C=C†F,
    C†C=F†C.                                         (2)

Hence J(U)=F(U)†C(U) is an orthogonal projection at every extended unitary context. At the identity tuple, F(I)=I and (1) gives the diagonal projections

    J_4(I)=|0><0|_2 P_(4),   rank4,
    J_5(I)=|0><0|_4 P_(5),   rank5.

The complete constant-rank property therefore gives ranks 4 and5 on the original boundary at all unitary contexts (multiplied by the product of the private dimensions after amplification).

#### Exact parameter certificate

The first identity in (2) was verified in the complete tangent coefficient system. For the second, [auxiliary_tangent_projector_extensions.py](../auxiliary_tangent_projector_extensions.py) expands C†C−F†C in the independent operator-block words of the four original unitaries and reduces **only**

    sum_a u_{ab}†u_{ad}=δ_bd I.

Because C and F preserve the original laboratory-output row in their coefficients, only the five equal-output normal words occur at each party, giving 5^4=625 normal-word keys. Every 16-by-16 matrix coefficient vanishes exactly over the integers after clearing the displayed rational denominators. No scalar-entry commutation, finite-ancilla sampling, or numerical tolerance is used.

The 13-word independence/completeness argument in [RG-059: Complete auxiliary tangent space and integrability tests](auxiliary-geometry.md#rg-059) explains why this is a parameter-level certificate at all private dimensions. The upper bound on the intermediate integer magnitudes is small compared with int64, and the structural matrices are explicitly rational. [auxiliary_new_projector_structure.py](../auxiliary_new_projector_structure.py) independently reconstructs the conditional process projectors, and [auxiliary_new_projector_frames.py](../auxiliary_new_projector_frames.py) converts them to the simple laboratory-input projectors in (1).

### 3. Actual native auxiliary extensions

Let the additional auxiliary algebra be C⊕C. For scalar entries a,b define

    G_r(a⊕b,U)=a C_r(U)+b[F(U)−C_r(U)],  r=4 or5.      (3)

This is linear in the auxiliary and multilinear in every original query, and G_r(1⊕1,U)=F(U).

Equation(2) gives

    G_r(a⊕b,U)=F(U)[a J_r(U)+b(I−J_r(U))],

which is unitary for phases a,b. More importantly, for an arbitrary private auxiliary ancilla K, replace a,b by independently arbitrary unitaries A,B on K. The two terms act on orthogonal J_r and I−J_r sectors, so the same formula is unitary even when A and B do not commute. This proves independent private-ancilla completeness for the auxiliary as well as for all originals.

The origin auxiliary representation has branch multiplicities (4,12) for r=4 and (5,11) for r=5. Thus neither extension is covered by the multiplicity-free auxiliary theorem.

### 4. These interfaces are genuinely outside the previous families

The explicit 557-dimensional real tangent span generated by arbitrary past/future Hamiltonians and the five exact supported cuts does not contain C_4 or C_5. They remain outside the expanded family obtained by adding ordinary gates immediately before and after each original query. The independent audit establishes the relevant XOR-zero real constructive block has rank168 over Q; adding either projector raises that rank to169. Thus non-membership holds over R, without relying on a modular non-membership test alone. See [auxiliary_new_projector_independent_membership_checks.json](../auxiliary_new_projector_independent_membership_checks.json). A reported total expanded dimension566 is not needed for this result and is kept separate from the audited rank168 claim.

Both left/right insertions at the known maximal native query promotions add no further linear directions: active-left is the corresponding supported-cut term; active-right is past multiplication on S_i; and either passive term is the full physical query-local term minus its active counterpart. These are coefficient identities, including private ancillas.

The multiplicity-one cut theorem supplies another useful consequence. Neither phase branch can be freely promoted to a full M_r block acting irreducibly on the same represented rank-r carrier while retaining its active coefficient C_r. Such a promotion would force C_r=F_R Q F_L for one of the exact supported cuts, putting it in the excluded 557-dimensional span. For r=5 the absence of any proper cut of rank at least5 already strengthens this obstruction. This is an obstruction to this specific auxiliary-branch enlargement, not to the C⊕C extension itself.

### 5. What remains to construct

These are new exact quantum auxiliary records with substantial repeated multiplicity. They directly invalidate an attempt to exclude the entire extra tangent quotient by constant-spectrum arguments: at least two extra directions satisfy the full projector law.

The phase-twisted processes obtained from (3) are valid. A phase choice may simplify their control geometry, but a routed realization of one restriction would not by itself realize the whole auxiliary family. A valid finite host must still exhibit this record with independent native fillers, satisfy both complete choice domains, and have only weak branch-graph loops.

### Characteristic-zero novelty and promotion obstruction

### 4. Characteristic-zero novelty, without a modular-membership caveat

Both candidates lie entirely in the XOR-zero real coefficient block. The constructive family is XOR graded: the boundary and supported-cut pieces have the grading explained in the tangent audit; physical pre-insertions preserve the query-output row, and physical post-insertions split according to the inserted one-qubit matrix's diagonal/off-diagonal grading. Thus other blocks cannot cancel a missing zero-real component.

The checker independently constructs all zero-real coefficient vectors from:

- Both arbitrary boundary Hamiltonian families
- All four singleton supported cuts and the {1,2} cut, using the independent carrier bases
- Every real physical one-qubit pre- and post-insertion

Uniform scaling by four makes these 192 nonzero generator vectors integral. Exact rational DomainMatrix elimination, rather than modular inference, gives rank 168. Adding either projector raises the rational rank to169; adding both raises it to170.

Therefore each projector is outside the entire boundary/cut/physical-query-local family over R, and their two quotient classes are independent. This conclusion does not depend on trusting a modular non-membership residual or on first proving the full family's dimension across its other blocks.

For clarity, modular non-membership alone would need a verified characteristic-zero baseline rank to exclude real membership. The explicit rational ranks here supply that missing safeguard.

The stated maximal-native insertion reduction is also correct coefficientwise. On an active serial carrier, inserting H before the represented α_i(U_i) in the written product gives `U_bar_i H α_i(U_i)`, a supported-cut term; inserting it on the other side gives `U_bar_i α_i(U_i)H=F H`, a past boundary term. An insertion on the passive M₂ branch is the full physical query-local insertion minus its embedded active counterpart. These are linear coefficient identities and remain valid under independent private ancillas. They do not promote or merge a routed vertex.

### 5. Independent same-coefficient promotion obstruction

A full M_r active branch represented irreducibly on the same rank-r origin carrier would satisfy the audited multiplicity-one supported-cut theorem. Its central coefficient would therefore have to be `F_R J_r(I)F_L` for one of the exact cut orientations.

The checker verifies that neither origin projection is contained in any proper cut carrier. For rank five, the rank bound alone suffices. For rank four, direct projection products exclude S₁,S₂ and K₁₂, while the other proper carriers have smaller rank.

Both endpoint alternatives also fail on actual Pauli contexts:

- C₄−FJ₄(I): query2=X gives squared Hilbert–Schmidt defect 8
- C₄−J₄(I)F: query4=X gives defect 4
- C₅−FJ₅(I): query4=X gives defect 10
- C₅−J₅(I)F: query3=X gives defect 6

All unmentioned queries are identity. These are exact evaluations. Thus promotion to full M₄ or M₅ while retaining the specified active coefficient is impossible, independently of the expanded-span novelty calculation. This does not forbid their actual C⊕C extensions or a different interface with a different coefficient.

<a id="rg-061"></a>

## RG-061 — The two phase slots cannot be filled jointly

**Statement.** The prescribed rank-four and rank-five phase marginals have no simultaneous complete extension.

**Status:** scoped negative result. **Scope:** Every complex off-XOR mixed correction is covered; a host is not required to contain either slot.

### Statement

Let F be the normalized quartet and C4,C5 the two specified complete projection coefficients in [RG-060: Two complete phase slots beyond the cut/local span](auxiliary-geometry.md#rg-060):

    C4(U)_{o,p}=1_{o2=0}<o|W P_(4) V_o D0|p>,
    C5(U)_{o,p}=1_{o4=0}<o|W P_(5) V_o D0|p>,

with

    P_(4)=P0_1 P0_4 + P1_1 P0_3,
    P_(5)=P0_3 + P0_1 P1_2 P1_3.

There is no multilinear independently complete unitary extension containing BOTH of these exact phase interfaces as independently variable slots. More explicitly, no multilinear coefficient tensor E on the four original queries can make

    G(z,w,U)=F(U)+(z−1)C4(U)+(w−1)C5(U)
                      +(z−1)(w−1)E(U)                  (1)

unitary for every |z|=|w|=1 and every independently ancillary-extended original unitary tuple.

Thus no valid routed host can expose both of these specified coefficients as independently fillable phase slots, regardless of its auxiliary count or topology. This does NOT say that any host for F must contain either interface, much less both. It does not establish that F itself is nonroutable.

### 1. Every joint extension obeys a mixed second-derivative equation

Put z=exp(it), w=exp(is) in (1), differentiate G†G=I, and take the ts coefficient. Necessarily

    F†E+E†F=C4†C5+C5†C4.                            (2)

Every possible relative order or coherent reducing-subspace mixture of orders obeys this same equation. We make no bipartite comparison choice at all.

Equation(2) must hold after arbitrary private ancillary extensions of the original queries. Their operator-block words u_ab†u_cd have the exact 13-dimensional quotient described in [RG-059: Complete auxiliary tangent space and integrability tests](auxiliary-geometry.md#rg-059): eliminate u_1b†u_1d using

    u_1b†u_1d=δ_bd I−u_0b†u_0d.

Those normal functions are already independent on a two-dimensional private ancilla at each original party. Consequently every reduced word coefficient in (2) must vanish separately.

### 2. No missing complex or off-XOR coefficient can repair the obstruction

The F,C4,C5 coefficient matrices are real. Splitting E into real and imaginary coefficient tensors separates (2): its real part is the PLUS system F†E_R+E_R†F, whereas the imaginary part is homogeneous.

Both C4 and C5 preserve the original query-output word as their future row. Hence their right side has output XOR zero. The reduced equations preserve the XOR label, because the unitary relations eliminate only equal output rows. Therefore only the real XOR-zero part of E contributes to the four equations below. Arbitrary complex coefficients in every other block remain allowed; they simply cannot change these necessary equations.

### 3. Four explicit coefficient equations

Let e_(r,a,p) denote four times the real E coefficient whose original output word and future row are both r, whose original input word is a, and whose external source coordinate is p. Words are numbered 0,...,15 in the standard four-bit order.

Define three real linear combinations of these otherwise arbitrary unknown coefficients:

    A=e_(10,2,2)−e_(11,2,2)−e_(14,2,2)+e_(15,2,2),
    B=e_(10,3,0)−e_(11,3,0)−e_(14,3,0)+e_(15,3,0),
    C=e_(10,6,6)−e_(11,6,6)−e_(14,6,6)+e_(15,6,6).

At each original party use these normal-word labels:

    0: I,
    1: u00†u00,
    2: u00†u01,
    3: u01†u00,
    4: u01†u01.

The following four exact coefficients of (2), with the common rational denominator cleared, are:

- Word key (0,1,0,1), boundary entry (2,2): 8A=0
- Word key (0,1,0,2), boundary entry (2,0): −4A+4B=0
- Word key (0,2,0,1), boundary entry (2,6): 4A+4C=16
- Word key (0,2,0,3), boundary entry (0,6): 4B−4C=0

Subtracting the first two equations from the last two gives 0=16. Equivalently, the first two force A=B=0, the third forces C=4, and the fourth forces C=0.

This is an exact contradiction for arbitrary real E coefficients. Section2 shows that it excludes arbitrary complex E as well. No hypothesis about E's rank, supports, matrix units, phase spectrum, or auxiliary order has been introduced.

### 4. Small standalone verification

Run

    python auxiliary_joint_phase_four_row_verifier.py

It imports only the portable quartet support matrices, reconstructs F and the two closed Boolean masks, forward-expands the four normal coefficients, and checks that the weighted left sides cancel on every one of the 4096 real XOR-zero variables while the right side is 16. It uses exact SymPy rational arithmetic throughout. The full term lists and PASS result are in [auxiliary_joint_phase_four_row_verifier_checks.json](../auxiliary_joint_phase_four_row_verifier_checks.json).

The larger modular discovery program and rational elimination are retained as provenance ([auxiliary_joint_phase_affine_obstruction.py](../auxiliary_joint_phase_affine_obstruction.py), [auxiliary_joint_phase_exact_certificate.py](../auxiliary_joint_phase_exact_certificate.py)). The final four-row proof does not use their modular ranks or require the exact583-dimensional tangent classification. It uses only the already independently verified normal-word independence lemma.

### 5. What this changes in the construction search

Each interface separately is a genuine complete C⊕C extension of F. They cannot both be freely inserted into one common process, even allowing an unknown mixed coefficient and all possible orders. This is a concrete obstruction to combining individually valid auxiliary interfaces, beyond the older warning about maximal original-query lifting.

The result narrows a proposed host only if that host is separately shown to contain both exact interface coefficients. It does not show either one is necessary in an arbitrary host, and it does not obstruct realizing either individual family on its own.

<a id="rg-062"></a>

## RG-062 — Four-sector phase records and diagonal input flags

**Statement.** Both displayed four-sector slots are complete; exactly 320 diagonal laboratory-input flags lie in four maximal seven-sector contexts.

**Status:** source-level result. **Scope:** Specified diagonal flag class; not arbitrary quantum encodings.

### 1. Both four-sector auxiliary slots are complete

For a diagonal laboratory-input projector \(P\), let

\[
 (L_P(U))_{o,p}=\langle o|W(U)P V_oD_0|p\rangle.
\]

Take either \((P,j)=(P_4,2)\) or \((P_5,4)\), with the audited predicates

\[
 P_4(n)=(n_1=0,n_4=0)\ \lor\ (n_1=1,n_3=0),
\]
\[
 P_5(n)=(n_3=0)\ \lor\ (n_1=0,n_2=1,n_3=1).
\]

Write \(P_1=P\), \(P_0=I-P\), and let \(O_o=|o\rangle\langle o|_j\)
be the fixed physical output-bit projections. The four coefficients are

\[
 C_{o,p}(U)=O_oL_{P_p}(U),\qquad o,p\in\{0,1\}.          \tag{1}
\]

The independent forward-word verifier establishes all16 identities

\[
 C_s^*C_t=\delta_{st}F^*C_t                               \tag{2}
\]

under arbitrary independent private ancillas at the original queries. It
checks all625 normal-word keys and all256 boundary matrix entries per pair.
The coefficients sum to \(F\). Thus \(J_s=F^*C_s\) are mutually orthogonal
projections summing to identity. For the sector order
\((o,p)=(0,0),(0,1),(1,0),(1,1)\), their origin ranks are

- \(P_4\): \((4,4,4,4)\)
- \(P_5\): \((3,5,3,5)\)

Consequently

\[
 G(a_1,\ldots,a_4,U)=\sum_s a_s C_s(U)
\]

is a genuine complete native \(\mathbb C^4\) auxiliary slot. For an arbitrary
auxiliary private ancilla, the four \(a_s\) become independent, possibly
noncommuting unitaries. Equation (2) makes all cross terms vanish and proves
unitarity directly. These are two separate interfaces, not a simultaneous
extension of the original \(C_4\) and \(C_5\) records.

#### Useful interface interpretation

The input marginal is the complete coarse flag \(L_P\), of rank8 or10. The
other marginal is the fixed future output flag:

\[
 \sum_p C_{o,p}=O_oF,\qquad \sum_o C_{o,1}=L_P.
\]

Equation (1) and the projection identities imply

\[
 [L_PF^*,O_o]=0
\]

at every extended context. Thus the four-sector record jointly resolves a
moving coarse input flag with one ordinary output-bit flag. It is not a
fixed-boundary input predicate: exact Pauli witnesses give

| Flag | Failure of \(L_P=FP\) | Failure of \(L_P=PF\) |
|---|---|---|
| \(P_4\) | query4=X, squared Hilbert–Schmidt defect4 | query4=X, defect8 |
| \(P_5\) | query4=X, defect4 | query3=X, defect12 |

Unspecified queries are identity. Commutation with this output Z flag does
not assert commutation with the full output \(M_2\), and does not authorize a
full-M2 promotion of the moving input flag.

### 2. Exact classification of diagonal laboratory-input flags

The audit also classifies all projectors diagonal in the 16 laboratory-input
labels whose coefficient \(L_P\) is a complete flag. This is a restricted
interface classification, not a classification of all auxiliary projectors.

For a real diagonal vector \(h=(h_0,\ldots,h_{15})\), complete Hermiticity of
\(F^*L_h\) is exactly the following six linear constraints:

\[
\begin{aligned}
 h_0-h_{13}-h_{14}+2h_{15}-h_3&=0,\\
 h_1-h_{11}+h_{15}-h_5&=0,\\
 h_8-h_{11}-h_{13}-h_{14}+2h_{15}&=0,\\
 h_9-h_{11}-h_{13}+h_{15}&=0,\\
 h_{10}-h_{11}-h_{14}+h_{15}&=0,\\
 h_{12}-h_{13}-h_{14}+h_{15}&=0.
\end{aligned}                                                     \tag{3}
\]

The exact coefficient Gram has rank6, so this real linear space has dimension10.
Enumerating all \(2^{16}\) Boolean vectors gives exactly320 solutions to (3).
Every one independently satisfies the complete projector identity
\(L_P^*L_P=F^*L_P\). The linear space in (3) is **not** closed under pointwise
multiplication, so the320 flags cannot all be combined into one record.

They are precisely the union of the Boolean algebras generated by the following
four maximal seven-atom partitions of the decimal input labels:

1. \(\{0,3\},\{1,5\},\{2\},\{4\},\{6\},\{7\},\{8,9,10,11,12,13,14,15\}\)
2. \(\{0,3\},\{1,8,9,10,11\},\{2\},\{4\},\{5,12,13,14,15\},\{6\},\{7\}\)
3. \(\{0,8,9,12,13\},\{1,5\},\{2\},\{3,10,11,14,15\},\{4\},\{6\},\{7\}\)
4. \(\{0,8,10,12,14\},\{1,5\},\{2\},\{3,9,11,13,15\},\{4\},\{6\},\{7\}\)

Each partition defines a complete native \(\mathbb C^7\) auxiliary by the same
orthogonal-projection argument. Maximality follows within the diagonal-mask
class: any proper complete subflag of an atom would leave a complementary
Boolean flag satisfying (3), which is also complete. The13 inclusion-minimal
nonempty flags have exactly these four disjoint exact covers, and all320
flags are unions of a cover's atoms. These finite checks are recorded exactly.

#### The two coarse input flags are compatible

Both \(P_4\) and \(P_5\) are unions of the third partition. Their joint
input-only record has four ranks

\[
 (\operatorname{rank}P_4P_5,
   \operatorname{rank}P_4(I-P_5),
   \operatorname{rank}(I-P_4)P_5,
   \operatorname{rank}(I-P_4)(I-P_5))=(7,1,3,5).
\]

Thus \(L_{P_4}\) and \(L_{P_5}\) do have a simultaneous complete scalar
extension. This does not contradict the exact no-joint theorem for
\(C_4=O_{2,0}L_{P_4}\) and \(C_5=O_{4,0}L_{P_5}\): those include additional
output-bit resolutions, and their prescribed simultaneous marginals fail the
mixed second-derivative condition.

### Scope of the flag classification

The four-sector and seven-sector formulas are explicit native **process
interfaces** with independently arbitrary branch fillers. They provide an
exact algebraic meaning for the records. They do not supply the native edges,
sector matchings, complete edge-choice domains, or weak-loop verification of
a routed host, so no routed realization is claimed.

For the rank-eight \(P_4\) flag, a separate exact origin-space argument now
excludes every full unital M2 lift of that fixed coefficient; see
[RG-063: No full-qubit lift of the specified rank-eight flag](auxiliary-geometry.md#rg-063). This is stronger than failure
of the natural controlled laboratory-input qubit ansatz, while remaining
restricted to that exact coarse marginal.

### Certificate files

- [auxiliary_four_sector_independent_audit.py](../auxiliary_four_sector_independent_audit.py) and `_checks.json`: all16
  four-sector cross identities, origin ranks, marginal formulas, boundary witnesses
- [auxiliary_four_sector_input_flags.py](../auxiliary_four_sector_input_flags.py) and `_checks.json`: exact rank6
  Hermiticity system, all65536 Boolean masks,320 complete flags, and four maximal
  seven-sector partitions

The scripts use only the exact support fixture and forward operator-word
reduction. They do not infer parameter-level positivity from sampled contexts.

<a id="rg-063"></a>

## RG-063 — No full-qubit lift of the specified rank-eight flag

**Statement.** No full-qubit lift of the specified rank-eight flag

**Status:** scoped negative result. **Scope:** The exact P4 coefficient; both real and imaginary tangent sectors are included.

### Theorem

Let \(L=L_{P_4}\) be the complete rank-eight flag coefficient

\[
 L(U)_{o,p}=\langle o|W(U)P_4V_oD_0|p\rangle,
 \qquad
 P_4=|0\rangle\langle0|_1|0\rangle\langle0|_4
       +|1\rangle\langle1|_1|0\rangle\langle0|_3.
\]

There is no independently private-ancilla-complete multilinear extension
\(G(A,U)\), with a unital full \(M_2\) auxiliary slot, satisfying

\[
 G(I,U)=F(U),\qquad G(e_{00},U)=L(U).                     \tag{1}
\]

The conclusion holds for every choice of the offdiagonal coefficient maps
and every origin embedding of \(M_2\) with this prescribed \(e_{00}\) image.
The coarse classical \(\mathbb C\oplus\mathbb C\) flag remains valid, as do
the separately proved four- and seven-sector classical refinements.

### 1. Necessary complete linear space

Put \(C_Z=2L-F\). For a candidate Pauli coefficient \(C_X=G(X,\cdot)\),
the normalized one-query representation at every extended context gives

\[
 F^*C_X=C_X^*F,\qquad C_Z^*C_X+C_X^*C_Z=0.              \tag{2}
\]

Indeed \(J_Z=F^*C_Z\) and \(J_X=F^*C_X\) are Hermitian and anticommute.
The same equations necessarily hold for \(C_Y=G(Y,\cdot)\). Equations (2)
are linear in the real and imaginary parts of the candidate coefficient map.

The independent verifier reconstructs the selected coefficient equations of
(2) in every one of the16 XOR sectors, separately for real and imaginary
unknowns. It uses the independently derived integer quartet coefficient

\[
 T_{r,a,p}=4\delta_{a,p}-8\sum_{i:r_i\ne a_i}(E_i)_{a,p}
\]

and \(T_Z(r,a,p)=(2P_4(a)-1)T_{r,a,p}\). Raw operator-block products are
forward-reduced by the same unitary block relations used in the independently
audited13-word theorem; no saved echelon matrix is trusted.

Every original tangent rank row and every added anticommutator row is
reconstructed and independently eliminated over the verified prime1000003.
The resulting nullity upper bounds are:

| XOR sector | Real nullity | Imaginary nullity |
|---|---|---|
| 0 | 9 | 9 |
| 4 | 2 | 2 |
| Every other sector | 0 | 0 |

Moreover, the supplied22 rational candidate directions are checked against
**every reconstructed selected row over the rationals**, and are independently
linearly independent. Consequently the common kernel of this selected
necessary system is exactly22-dimensional over the reals. Every actual
complete solution of (2) lies in it. For this no-lift proof it is unnecessary
to assume that all vectors in the selected kernel solve every remaining word
equation, although the separate full verifier also checks that stronger fact.

This establishes the needed upper bound directly, without relying on the
author's modular summary or saved row-reduced matrices.

### 2. The real and imaginary origin spaces differ

At the identity tuple, \(F(I)=I\) and \(J_Z(I)=2P_4-I\). Order the positive
and negative origin basis vectors as

\[
 H_+:(0,2,4,6,8,9,12,13),\qquad
 H_-:(1,3,5,7,10,11,14,15).
\]

Every Hermitian matrix in the necessary origin image has the form

\[
 X_0=\begin{pmatrix}0&B\\B^*&0\end{pmatrix},
 \qquad B=S+iT,
\]

where \(S\in\mathcal R\), \(T\in\mathcal I\) are real eight-by-eight
matrices. Exact rational extraction of the22 coefficient directions gives

\[
 \dim\mathcal R=\dim\mathcal I=11,\qquad
 \dim(\mathcal R+\mathcal I)=15,\qquad
 \dim(\mathcal R\cap\mathcal I)=7.                       \tag{3}
\]

Origin evaluation has rank22. In particular, the22-dimensional real tangent
space must **not** be treated as an eleven-dimensional complex offdiagonal
space: multiplication by \(i\) does not preserve the allowed upper-right
blocks. The missing closure is decisive for a genuine Pauli pair.

### 3. The Pauli-pair condition forces a fixed kernel

In any unital \(M_2\) representation with the prescribed Z image,

\[
 Y_0=-iZ_0X_0.
\]

The upper-right block of \(Y_0\) is therefore \(-iB=T-iS\). Since \(Y_0\)
must also lie in the necessary origin image, both \(S\) and \(T\) must lie
in \(\mathcal R\cap\mathcal I\).

The exact intersection consists of the real matrices

\[
\begin{pmatrix}
0&a&0&0&0&0&0&0\\
b&0&0&c&2b&0&0&0\\
d&0&0&e&2d&0&0&0\\
f&0&0&g&2f&0&0&0\\
0&0&0&0&0&a&0&0\\
0&0&0&0&a&0&0&0\\
0&0&0&0&0&0&a&0\\
0&0&0&0&0&0&0&a
\end{pmatrix},\qquad a,b,c,d,e,f,g\in\mathbb R.          \tag{4}
\]

Hence the same formula with complex parameters contains every possible B of
a simultaneous allowed X/Y pair. Its third column is identically zero. In
the displayed negative-sector ordering this column is the physical origin
basis vector with decimal label5, namely \(|0101\rangle\). It follows that

\[
 X_0|0101\rangle=0.
\]

But a represented Pauli must satisfy \(X_0^2=I\). This contradiction proves
the theorem. No nonlinear search for individual involutions, no genericity
assumption, and no lifting of multiplicity into native branches is used.

### 4. Exact certificate and scope

[auxiliary_four_sector_qubit_obstruction.py](../auxiliary_four_sector_qubit_obstruction.py) and
[auxiliary_four_sector_qubit_obstruction_checks.json](../auxiliary_four_sector_qubit_obstruction_checks.json) certify:

1. All32 reconstructed necessary row ranks
2. Exact rational annihilation and independence of the22 candidate directions
3. Rank22 of their origin evaluation
4. The ranks11,11,15,7 in (3)
5. An exact basis for (4), including its common zero column

The source row locations are taken from the previously audited tangent
certificates and [auxiliary_input_flag_quantum_lift_scout_checks.json](../auxiliary_input_flag_quantum_lift_scout_checks.json); their
actual coefficients and ranks are rederived. The candidate coefficient
directions are read from [auxiliary_input_flag_anticommutant_basis_checks.json](../auxiliary_input_flag_anticommutant_basis_checks.json).
All output certificates are newly written live files.

This is a fixed-marginal qubit-promotion obstruction on the original
16-dimensional boundary. It does not classify other coarse flags, general
repeated-multiplicity auxiliaries, or routed hosts. In particular, a valid
classical phase record need not be the Z restriction of a quantum qubit slot.

<a id="rg-064"></a>

## RG-064 — Interior M4 cut and prescribed C4 phase are incompatible

**Statement.** Interior M4 cut and prescribed C4 phase are incompatible

**Status:** scoped negative result. **Scope:** Exact fixed marginals and all active ordering cases; no unrestricted auxiliary no-go follows.

### 1. Fixed marginal interfaces

Use \(L=\{1,2\}\), \(R=\{3,4\}\),

\[
 Q=I_{12}\otimes|-,1\rangle\langle-,1|_{34},\qquad
 F_L=F(U_1,U_2,I,I),\quad F_R=F(I,I,U_3,U_4).
\]

The complete interior cut slot has native algebra \(M_4\oplus\mathbb C\) and
prescribed coefficient map

\[
 G_{\rm cut}(a\oplus\lambda,U)
   =\lambda F(U)+F_R(U_R)(a-\lambda Q)F_L(U_L),            \tag{1}
\]

where the active M4 is the full corner \(QM_{16}Q\), with multiplicity one.
Its active coefficient is

\[
 A_a(U)=G_{\rm cut}(a\oplus0,U)=F_RaF_L.
\]

The other marginal is the independently audited C4 phase slot

\[
 G_4(z\oplus w,U)=zC_4(U)+w[F(U)-C_4(U)].                \tag{2}
\]

We allow any complex multilinear mixed coefficient and impose no ordering
ansatz at the outset. The passive cut branch retains its full scalar freedom
and represented multiplicity12.

### 2. Why the entire active coefficient has only two possible orders

Fix an original unitary tuple U and right-normalize a hypothetical joint
extension by \(F(U)^*\). The finite-C*-algebra complete bipartite comparison
theorem supplies a projection P commuting with both normalized singles.

The selected active cut representation has image the full matrix algebra on
the rank-four carrier

\[
 Q_{\rm out}(U)=F_RQF_R^*.
\]

Since P commutes with the whole cut representation, it commutes with this
central carrier and restricts there to either0 or identity. It may be
nontrivial on the twelve-dimensional passive complement. That complementary
freedom disappears when the cut input is supported on its active M4 summand.

Consequently the mixed active coefficient

\[
 E_a(U)=G_{\rm joint}(a\oplus0,\,1\oplus0,\,U)
\]

obeys, for **every** active a, one of the two identities

\[
 E_a(U)=C_4(U)F(U)^*A_a(U),                              \tag{3a}
\]
\[
 E_a(U)=A_a(U)F(U)^*C_4(U).                              \tag{3b}
\]

The phase algebra being nonsimple, with one-dimensional summands, causes no
problem: the comparison projection is scalar because of the active M4's
multiplicity one, not because of any irreducibility or dimension condition
on the phase algebra. No claim is made that the comparison is scalar on the
whole boundary or that it is unique.

#### Global locking without a uniqueness assumption

For the finite basis of16 active matrix units, each displayed identity defines
a real-analytic closed locus in the connected original context manifold
\(U(2)^4\). These two loci cover the manifold. One therefore contains an open
set, and real-analytic continuation makes that identity hold everywhere.
Equivalently, take the product of the two nonnegative analytic sums of squared
matrix-entry defects and use analytic unique continuation.

This argument allows the two loci to overlap at contexts where the phase
representation commutes with the active cut algebra. No disjointness or
continuous selection of comparison projections is assumed. Thus one of
(3a),(3b) must hold globally, including all active a.

This is an application of the already used complete finite-C* bipartite theorem,
not of the supported-cut phase-removal theorem with an inapplicable condition
that the other factor have matrix size greater than one.

### 3. Two exact one-query linearity contradictions

Choose the single active rank-one matrix

\[
 a=|10\rangle\langle10|_{12}\otimes
          |-,1\rangle\langle-,1|_{34}.
\]

Put \(J=XZ\) and \(V=(3I+4J)/5\). All three matrices I,J,V are exact unitaries.
Every original-query multilinear E must obey, on any fixed spectator slice,

\[
 E(V)=\frac35E(I)+\frac45E(J).                           \tag{4}
\]

The following violations use zero-based boundary matrix indices:

| Candidate order | Varied query | Other queries | Entry of the defect in (4) |
|---|---|---|---|
| \(C_4F^*A_a\) | query1 | all identity | \((1,0)=-24/125\) |
| \(A_aF^*C_4\) | query4 | query2=X; queries1,3=I | \((8,12)=24/125\) |

The full defect matrices have respectively8 and16 nonzero entries. Both
orders therefore fail even scalar-unitary-slice complex linearity. They
cannot equal the required multilinear mixed coefficient.

The active a need not itself be a unitary filler: it is a legitimate matrix
coefficient of the auxiliary slot, and the bipartite identity holds linearly
for all supported matrices. Every original-query test value is unitary.

### 4. Independent exact verification

The scout computes the ordered expressions from integer row tensors. A
separate verifier, [auxiliary_cut_C4_joint_independent_check.py](../auxiliary_cut_C4_joint_independent_check.py), reconstructs
F using the distinct normalized support formula

\[
 F(U)=\bigotimes_iU_i+
       \sum_i\left[(Z_iU_iZ_i-U_i)\otimes U_{\bar i}\right]E_i,
\]

with tensor factors in their original order. It constructs C4 directly from
the audited laboratory-input projector and output-bit mask. It verifies both
unitary slices and both rational nonzero entries above with SymPy exact
arithmetic. The full defect matrices are stored in
[auxiliary_cut_C4_joint_independent_checks.json](../auxiliary_cut_C4_joint_independent_checks.json).

No finite positive cut-space sample, modular inconsistency, or failure of one
chosen joint ansatz is promoted into the conclusion. The exhaustive step is
the proper-block comparison plus analytic locking; the two exact witnesses
then exclude its two possibilities.

### 5. Scope and constructive consequence

The result rules out a simultaneous independently complete
\((M_4\oplus\mathbb C)\times\mathbb C^2\) extension with exactly (1) and (2)
as its marginals. It includes arbitrary conditional mixtures and orientations
on the passive branch. It does not exclude a smaller cut subalgebra, a changed
phase coefficient, a different interior matrix interface, or another routed
construction of the quartet.

The earlier consistency of a mixed linear equation for one active generator
and the host-wide rank-two isotropy test remain valid necessary checks. They
are not sufficient for this full matrix interface. No graph deletion or
original-query regrouping follows.

<a id="rg-065"></a>

## RG-065 — Full mixed-curvature obstruction and four maximal alternatives

**Statement.** The 204 independent exact mixed forms have common radical dimension 546 and exactly four maximal simultaneous linear spaces of dimensions 556, 556, 568 and 570.

**Status:** source-level result. **Scope:** All typed sectors in the complete 583-dimensional tangent space; necessary conditions only. The weaker 1-form and 13-form restrictions are subsumed; minimal native interfaces remain in the radical.

### Conclusion

The common real zero locus of the 204 displayed quadratic forms is exactly
the union of four real linear spaces. Their full-tangent dimensions and
old eight-coordinate classes are:

- 556, with possible old coordinates a,h
- 556, with possible old coordinates b,h
- 568, with possible old coordinates d,f,g,h
- 570, with possible old coordinates c,d,e,f,g

Each space annihilates every complete bilinear form, and no one is contained
in another. They are therefore precisely the maximal simultaneously
isotropic real linear spaces for THIS 204-form family. The common radical
has dimension 546.

Every one host's full real filler span lies in one common alternative. The
classification neither exhausts all possible mixed obstructions nor proves
integrability, availability of an auxiliary algebra, or routability of any
space.

### 1. Exact descent and form-space verification

The verifier reads the 37-by-72 rational coordinate matrix L and checks
rank L=37 and identity on its chosen pivot columns. It reconstructs each
72-by-72 bilinear matrix B from the independently audited exact certificate,
takes its pivot principal matrix A, and verifies

    B=L^T A L

entry by entry. Thus the stated reduction really quotients by the full
35-dimensional radical inside the 72-dimensional nonboundary complement.
There is no assumption that simply selecting 37 arbitrary coordinates would
preserve the forms.

It independently recomputes the rational RREF of all 204 descended quadratic
coefficient rows and checks exact equality with the saved RREF. Off-diagonal
matrix entries contribute twice to the diagonal polynomial. The RREF rank
is 204.

Factoring those reconstructed polynomials over Q gives exactly 183 products
of real linear factors and 21 remaining quadrics. The verifier reconstructs
the 183 products from the saved 43 factor vectors and compares the normalized
polynomial multisets, including multiplicities. Thus it does not rely on
unverified factor labels or an exploratory modular output.

### 2. Independent coverage of the six intermediate spaces

First verify that each of the six proposed intermediate spaces annihilates
every one of the 183 product equations. To prove that they cover all common
zeros, a depth-first procedure starts from the entire 37-dimensional space.
At a node with linear constraint matrix M:

1. If ker M is contained in a verified target space, record a covered leaf
2. Otherwise select one product l_1 l_2 whose two linear factors remain
   nonzero on ker M
3. Branch to ker M intersect ker l_1 and ker M intersect ker l_2

Every zero of that product lies in one child. Each child strictly increases
the rational constraint rank. Exact RREF containment is used, and repeated
states are only deduplicated, not discarded heuristically.

This is independent of the author's incremental maximal-space enumeration.
It finishes with 612 distinct nodes, every terminal node covered. If no
unresolved product had remained outside the targets, the code would have
reported a missing solution space rather than silently terminating.

### 3. Coverage with the remaining quadrics

Independently verify that each of the four final target spaces satisfies
`N^T A_l N=0` for every one of the 204 matrices A_l, where the columns of N
span that target. This checks all bilinear pairings, not only selected
quadratic values.

Starting from the six intermediate spaces, the coverage procedure again
uses exact linear constraints. At each uncovered node, substitute its
rational nullspace parametrization into all forms and take the exact RREF
of the surviving quadratic span. Every polynomial selected from this span
vanishes at every solution still under consideration.

A factored real equation supplies its two real hyperplane alternatives.
When a pair q_1,q_2 of real equations has a complex factorization

    q_1+i q_2 = c l_1 l_2,

every real solution has l_1=0 or l_2=0 as a complex number. Each complex
linear equation is imposed as BOTH of its real and imaginary linear parts.
The converse implication for this pair also holds: a vanishing complex
product gives q_1=q_2=0. Other equations are retained and tested downstream.

The independent verifier uses symbols declared real, so taking real and
imaginary parts does not require a manual replacement of re(z) and im(z).
Every selected factorization is checked by exact polynomial multiplication;
every factor is checked homogeneous linear; its translation back to the
37 coordinates is checked against the free-coordinate identity block of
the nullspace basis. Every child strictly increases constraint rank.

The run finishes with 67 distinct nodes, 38 real-product branches, six
complex-pair branches, and all leaves contained in a verified final space.
There is no unresolved leaf. The selected polynomials, complex factors,
real child constraints and ranks are recorded in the JSON. Branching on a
necessary equation can temporarily retain extra points, but cannot lose a
solution; terminal bilinear verification removes that possible ambiguity.

Together with the intermediate cover, this proves the entire real zero
locus equals the union of the four targets.

### 4. Maximal linearity and dimensions

The four targets are pairwise noncontained, verified over Q. Any real linear
subspace lying in their finite union must be contained in one of them: over
an infinite field, finitely many proper linear subspaces cannot cover a
vector space. Consequently every common isotropic linear span lies in one
target, and none of the four targets admits a larger common isotropic
linear extension.

Their active-coordinate codimensions are 27,27,15,13. Since the active
quotient has dimension 37 and the radical dimension is 546, their full
sizes are 546+(37−codimension)=556,556,568,570.

The verifier also reconstructs the old eight functionals on the 72-coordinate
complement, checks that they descend through the new L, and evaluates them
on each final nullspace. Their nonzero-coordinate sets match exactly ah,
bh, dfgh, cdefg. This confirms the claimed refinement of the earlier four
alternatives, with no implicit change of baseline or basis.

### Scope

The inputs are exact necessary mixed-derivative forms on the full complete
tangent space. The all-Q_i=E_i native interfaces remain in their common
radical, as established in the separate full-sector audit. The result
organizes possible host filler spans; it does not make any of the four
spaces a realizable native algebra and does not resolve the quartet's
universal routed-host question.

### Complete typed-sector dual derivation and radical

### 1. Independent coefficient and word reconstruction

The verifier imports only the support fixtures, not the author programs or
scout pair lists. It reconstructs 4F from the support identity and generates
raw operator-block words forward. For equal local query outputs,

    u_0a†u_0b is retained;
    u_1a†u_1b = delta_ab I − u_0a†u_0b.

For unequal outputs the word u_ra†u_(1−r)b is retained independently. No
scalar-entry commutation is used. This is exactly the previously audited
13-word complete local basis; independent private ancillas justify
coefficient extraction in every four-party word sector.

For each saved weighted dual, the verifier expands all selected normal
coefficients using its own forward table and checks the resulting linear
functional on every possible coefficient of E over the integers. It tests
both E=X and E=iX explicitly. Thus it does not infer the dual identity from
modular elimination or the scout's residual rows.

### 2. Imaginary signs and shared future indices

Let a tangent basis direction with mask m and kind k have actual coefficient
`i^k V[f,a,p]`, future row f and query-output label `f xor m`, where k=0 or1.
For a raw word with first and second query-output labels r,t, a contribution
from directions C,D requires

    r xor t = m_C xor m_D.

The first product C†D uses the SAME future row

    f = r xor m_C = t xor m_D,

whereas the second product D†C uses

    g = r xor m_D = t xor m_C.

In particular f and g are generally different. Reusing r as a common future
row when the masks differ would be incorrect; the verifier checks both
identities above term by term.

The respective scalar phases are

    conjugate(i^k_C) i^k_D,
    conjugate(i^k_D) i^k_C.

Their real or imaginary parts are extracted explicitly in the code. Equal
kinds give the real coefficient with signs (+,+). A real C and imaginary D
give imaginary signs (+,−); imaginary C and real D give (−,+). Mixed parity
cannot enter the wrong real/imaginary sector.

Likewise, since F has real coefficients, substituting E=iX into
`F†E+E†F` gives `i(F†X−X†F)`. Thus the imaginary-sector dual annihilates the
MINUS linear system. The verifier derives this sign by complex conjugation,
rather than borrowing the author's parity convention.

Every compatible unordered pair among all 72 nonboundary directions is
generated independently and evaluated. All other pairs are ruled out by the
mask and real/imaginary typing just proved. Each resulting exact integer
matrix, after its explicitly checked gcd normalization, equals the supplied
bilinear matrix.

### 3. The boundary quotient is exact

The previously audited basis has 583 independent complete tangent vectors.
The verifier checks each of its 511 vectors labeled past or future against
actual coefficient identities `C=F H` or `C=H F`, taking H=C(I). It also
checks the corresponding real symmetric or imaginary antisymmetric
Hermiticity of H. The remaining 72 independent vectors therefore give the
stated complement, with the exact saved ordering.

For completeness, the boundary space has dimension exactly 511. Both maps
from Hermitian M16 into tangent directions are injective and have dimension
256. If `F H=K F`, evaluation at the identity gives H=K; this H then commutes
with every coefficient of F. The verifier proves the coefficient span of F
is all M16: for every fixed future row, its 16 coefficient row vectors form
an invertible matrix. Therefore H is scalar, and the intersection has real
dimension one. The sum has dimension 256+256−1=511.

Boundary directions are radical for EVERY mixed dual, not just for these
204. If C is tangent, put S=F†C=C†F. For a past direction D=F H with
H=H†, choose E=C H. Then

    F†E+E†F = S H+H S = C†D+D†C.

For a future direction D=H F, choose E=H C; the required identity follows
directly. Both E are original-query multilinear. Any functional annihilating
all mixed E therefore pairs every tangent C to zero with all boundary
directions. This proof does not assume C is integrable.

### 4. Exact independence and common radical

The sector support patterns are disjoint. Within every nonempty sector,
the verifier computes the rational rank of the coefficient rows and obtains
exactly their number; these ranks sum to 204. The six empty sector blocks
supply no claimed forms.

For the common radical, let B_l be the reconstructed 72-by-72 symmetric
matrices. The exact integer Gram matrix

    G=sum_l B_l^T B_l

has rational rank 37. Since it is positive semidefinite over R,
`ker G=intersection_l ker B_l`. The supplied 35-dimensional quotient radical
basis is checked for independence and exact annihilation. Adding the
511 boundary directions yields full radical dimension 511+35=546.

All int64 operations have explicit magnitude bounds before multiplication
and accumulation. Ranks and kernel verification are over Q, rather than
numerical tolerances or finite-field upper bounds. The audited basis file's
SHA-256 digest is recorded in the JSON.

### 5. Minimal original-query native interfaces remain compatible

For Q_i=E_i, active Hermitian matrices are spanned by

    E_i, X_i E_i, Y_i E_i, Z_i E_i.

Their serial left insertion is

    C_H(U)=U_bar_i H alpha_i(U_i).

For each of these 16 directions the verifier reconstructs every coefficient
in both possible XOR masks (zero and the own-query output bit). It solves
for its coordinates in the already audited tangent basis, then checks the
reconstruction on ALL 4096 coefficients in each typed block. Thus the test
does not rely on agreement at a chosen coordinate minor only.

The 72-coordinate complement vector is annihilated by all 204 B_l. For the
12 Pauli directions these exact coordinates agree with the author test.
The four active identities are also checked and lie in the boundary space.
Imaginary Y directions receive their actual factor i and remain part of the
real Hermitian tangent space.

This covers the whole active algebra on E_i. Active right insertions are
fixed-past insertions by the serial identity. To cover passive directions as
well, the following general reparametrization identity is useful.

Every ordinary physical query-local left or right insertion is radical for
EVERY mixed dual. For any complete tangent C, its defining identity is
`F†C=C†F` at every original unitary context. Replace one query by
`exp(itH)U_i` (or `U_i exp(itH)`) and differentiate, writing F'=iD and C'=iE.
The derivative is exactly

    F†E+E†F = D†C+C†D.

Here D is the physical query-local insertion in F, and E is the same linear
insertion in C. E remains original-query multilinear. Thus every mixed dual
pairs D with every tangent C to zero. No integrability of C is needed.

For an actual minimal native algebra, a passive left insertion with
Hamiltonian h is its physical query-left insertion minus the active serial
insertion with H=alpha_i(h)E_i. Both terms are radical by the preceding
proofs. Passive right insertions are handled by the corresponding physical
query-right insertion minus an active right insertion; the latter is a
fixed-past direction. Hence ALL Hermitian filler directions of each
minimal native interface, active and passive and on either side, lie in the
common radical, as does their span across the four native vertices.

This quantitative compatibility is established at the same F baseline. It
does not assert that the minimal complete joint native tensor has a routed
skeleton or that every radical tangent direction is integrable.

### Native first-port support implication

### 5. A consequence for every permitted port1 active algebra

Let Q1 be the central support of the actual query1 active ideal. The audited
native classification gives Q1<=S1 and [Q1,alpha1(M2)]=0, with a passive M2
quotient. No full-M4 promotion is assumed; the active ideal can have smaller
matrix summands or representation multiplicities.

The represented original Pauli Z restricted to that ideal is the allowed
self-adjoint native element H=alpha1(Z)Q1=Z1Q1. Equation (2) gives

    h(C_H)=Tr[(S1−E1)Q1]/3 >=0.                       (3)

It vanishes exactly when Q1<=E1. Positivity follows because S1−E1 is a
projection and Q1 is a projection supported on S1; vanishing trace of their
product is equivalent to their orthogonality.

Consequently, if Q1 is not contained in E1, the common host tangent span
contains a direction with h nonzero. Products ch and eh then force

    c=e=0 for EVERY auxiliary and query-native direction of that host. (4)

Conversely, any host with a direction having c or e nonzero must use
Q1<=E1 at its original query1 interface. This is a restriction on an actual
classified native port, not an assertion that a maximal promotion exists.
The previously audited phase C4 has e nonzero, so it belongs to the third
class and enforces this small-port1 restriction if it occurs in a host.

<a id="rg-066"></a>

## RG-066 — Safe-table phase masks

**Statement.** The specified safe coefficient table has exactly 35-dimensional phase freedom, with complete sufficiency from four serial carriers.

**Status:** source-level result. **Scope:** Specified table semantics, not every phase-valued or quantum auxiliary.

### Setup and statement

Use the fixed safe orthonormal product basis, in this order:

    001−, 10+0, 0001, 11−+, 0100, 0110, 11+0, 11+1,
    0000, 001+, 0101, 0111, 10+1, 10−+, 10−−, 11−−.

Let W map the computational labels p=0,...,15 to these normalized words. Set

    V_o=I−2 sum_i o_i E_i,
    T(U)_{o,p}=<o|(U1⊗U2⊗U3⊗U4)V_o W|p>.

Thus T(U)=F_raw(U)W is the exact table tensor used previously. For a real 16-by-16 array h, consider the continuous entrywise phase deformation

    T_h(t;U)_{o,p}=exp(i t h(o,p)) T(U)_{o,p}.

Then T_h(t;U) is unitary for every real t and every unitary original query tuple U if and only if

    h(o,p)=a(p)+b(o)
           +c1 o2 1_{p∈{2,10}}+c2 o2 1_{p∈{3,13}}
           +c3 o3 1_{p∈{4,5}} +c4 o4 1_{p∈{6,7}},        (1)

with arbitrary real a,b,c1,...,c4. The parameterization has one redundant constant between a and b, hence dimension 16+16−1+4=35. Every deformation in (1) also preserves independent private-ancilla unitarity, with the coefficient phase acting on the original external indices and identity on ancillary indices.

In particular, an independently phase-addressable routed flag whose exact tensor effect is a Boolean table mask m(o,p) must belong to this space. Conversely, every Boolean mask in the space gives a completely unitary phase extension at tensor level. No routed realization of that extension is claimed.

### Necessity: exact infinitesimal coefficient equations

Differentiating T_h†T_h=I at t=0 gives that T†(h⊙T) is Hermitian. For each pair of distinct source columns p,q this means

    sum_o [h(o,p)−h(o,q)] conjugate(T_{o,p}) T_{o,q}=0.    (2)

Put ψ_p(o)=V_o W|p>. For an arbitrary one-qubit unitary U_i,

    U_i†|o_i><o_i|U_i=(I+(-1)^o_i n_i·σ)/2,

where n_i ranges independently over the unit sphere. Therefore (2) is a multilinear polynomial in the four independent Bloch vectors. Its coefficients vanish separately: the functions 1,n_x,n_y,n_z are linearly independent on a sphere, and their tensor products are linearly independent on the product of four spheres. For every Pauli word A=σ_{a1}⊗...⊗σ_{a4},

    sum_o [h(o,p)−h(o,q)] (-1)^(sum_{i:a_i≠0} o_i)
           <ψ_p(o)|A|ψ_q(o)>=0.                           (3)

Real and imaginary parts give a real linear system on the 256 entries of h. Unnormalized product columns may be used in this computation: scaling each source column by a fixed nonzero real number rescales an entire (p,q) equation and does not change its solution space.

The retained certificate in [phase_mask_tangent_space_checks.json](../phase_mask_tangent_space_checks.json) contains 221 explicitly identified rows of (3). Every row is specified by its Pauli word, p,q, real/imaginary component, and its sixteen exact coefficients. With the unnormalized columns, multiplication by 64 makes all coefficients integral.

[phase_mask_exact_verifier.py](../phase_mask_exact_verifier.py) independently recomputes all 221 rows from E_i, verifies that no rational coefficient was rounded, and row-reduces their 221-by-256 integer matrix over the prime field F_1000003. The rank is 221. This is an exact lower bound on the rank over R, so the solution space of the full system has dimension at most 35. It is not a numerical rank/tolerance argument.

Section 2 below constructs 35 linearly independent solutions valid for every query tuple and t. Thus the dimension is exactly 35 and (1) is exhaustive. The verifier separately checks the 35 displayed generators are linearly independent over Q and annihilated by all retained rows.

### Sufficiency: four genuine serial carriers

Let C_g=W diag(1_{p∈g})W† for the four source-column groups in (1), and associate them with query i(g)=2,2,3,4 respectively. These are mutually orthogonal rank-two projections. In physical source coordinates they are exactly

- C1: own qubit2 arbitrary, spectator word on134 equal to 001
- C2: own qubit2 arbitrary, spectator word on134 equal to 1−+
- C3=E3: own qubit3 arbitrary, spectator word on124 equal to 010
- C4=E4: own qubit4 arbitrary, spectator word on123 equal to 11+

Each C_g is a physical own-factor cylinder, contains no support E_j with j≠i(g), and lies in the corresponding canonical serial carrier. Write

    R_i=I+(Z_i−I)E_i.

The coefficient formula for F_raw gives the exact identity

    F_raw(U) C_g = U_bar_i R_i U_i C_g.                    (4)

Indeed all E_j terms for j≠i annihilate C_g. For the remaining term, Z_i commutes with U_bar_i and E_i commutes with U_i, giving U_bar_i (Z_i−I)E_i U_i C_g=(Z_i−I)(U_bar_i U_i)E_i C_g. No commutation of E_i or R_i with U_bar_i is used. Equivalently one may use the previously proved serial-column identity with the source normalizer D0, noting D0 C_g=R_i C_g on this carrier.

Because U_i preserves the physical cylinder C_g, the image projection of (4) is

    Q_g(U)=U_bar_i R_i C_g R_i† U_bar_i†.

It is independent of U_i and commutes with the own output-bit projector O_i=|1><1|_i: both R_i and C_g commute with O_i, and U_bar_i acts on other laboratory factors. Since F_raw is unitary and the C_g are orthogonal, all Q_g(U) are orthogonal as well.

Consequently

    H(t;U)=F_raw(U)+sum_g [exp(i t c_g O_i(g))−I]F_raw(U)C_g

is unitary: on each orthogonal source carrier it applies a unitary preserving that carrier's orthogonal image, and on the remaining source space it leaves F_raw unchanged. Multiplying H on the left by diag(exp(i t b(o))) and on the right by W diag(exp(i t a(p))) gives exactly T_h(t;U).

The same argument is valid with arbitrary independent private ancillas. U_i acts on its qubit and own ancilla and still preserves C_g⊗I; U_bar_i excludes that qubit and commutes with its output-bit projector. The serial-column identities hold coefficientwise. Thus this is full complete-unitarity sufficiency, not merely scalar unitarity.

### Interpretation and scope

The four non-boundary phase freedoms are precisely controllable own-output phases on four orthogonal serial carriers. The individual β3 and β4 basis flags from the earlier table are outside (1); the safe parity β3 xor β4 is source-only and lies inside it.

The conclusion is useful whenever a proposed route exposes a classical record whose independently variable phase is exactly a fixed entrywise mask on this table. It allows arbitrary placement and number of auxiliary nodes under that explicit mask semantics. It does not establish that every auxiliary branch, coherent internal code, or alternative realization has such semantics.

No arbitrary-host exclusion or unrestricted routed-graph universality result follows from this mask classification alone.
