# Exact finite realization from a flat positive GYNI tester

Conditional finite-realization theorem, not an exact-value or
finite-attainment theorem. The annihilator below is an ADDITIONAL EXACT
certificate condition. It has not been derived for an unrestricted optimizer.
The quotient is a finite-dimensional spectral *-algebra quotient; it is usually
NOT a quotient by a finite dihedral GROUP. Rational angle matrices need not
have finite-order rotations.

<a id="p2-r13"></a>

## 1. The local spectral ideal has an unusually sharp truncated saturation

Let A=C[Z_2 * Z_2], with Hermitian involutions a,b, U=ab and
C=(U+U^{-1})/2. Let V_L be the span of all reduced words of length at most L;
dim V_L=2L+1. Select I distinct interior central eigenvalues c_j in (-1,1)
and a subset E of the endpoint eigenvalues {+1,-1}. Include BOTH scalar
characters over each selected endpoint. Put N=2I+|E| and q(C)=prod_j(C-c_j).
Let pi be evaluation on the corresponding interior M_2 summands and endpoint
scalar summands. The quotient algebra has dimension 2N=4I+2|E|.

Choose the following degree-N relation r:

- E empty: r=q(C)
- E={+1}: r=(a-b)q(C)
- E={-1}: r=(a+b)q(C)
- E={+1,-1}: r=(ab-ba)q(C)

The ideal J=ker pi equals rA=Ar. More precisely, for every L>=N,

    J intersect V_L = r V_(L-N).                         (1)

Proof. Every algebra element has a unique Laurent form f(U)+g(U)a. Up to an
invertible signed monomial, r is

    Q(U)=prod_j(U^2-2c_j U+1) prod_(e in E)(U-e).

Q has N distinct roots, is stable under reciprocal roots, and the quotient
is C[U,U^{-1}]/(Q) crossed with the inversion involution. Thus it has dimension
2N and the stated M_2/scalar decomposition. The rotation and reflection
parts of V_L each contain consecutive Laurent exponents. At L=N their
sizes are N+1 and N in one order or the other. Evaluation therefore has rank
2N, with one relation; at L<N there is no relation. In particular pi(V_L)
is the entire quotient for L>=N.

Right/left motion of r preserves word length: r a=sigma(a)r and
r b=sigma(b)r, with sigma respectively identity, signed interchange
(a,b)->(-b,-a), interchange (a,b)->(b,a), or simultaneous negation.
Multiplication by r is injective: r^*r is the nonzero central polynomial
listed in (4) below, and nonzero central polynomials are non-zero-divisors
in the Laurent normal form. Thus rV_(L-N) has dimension 2(L-N)+1.
It lies in J intersect V_L, whose dimension is exactly the same. This proves (1).

Let E_L:V_L -> A_S be the evaluation map, with A_S carrying its ordinary
Hilbert-Schmidt Choi-vector inner product. On coefficient dyads let

    Phi_L(B)=E_L B E_L^*,
    mu_L(B)=sum_(u,v) B[u,v] v^*u.

For setting flags sum mu over both flags. Define the linear kernel of Phi,
not merely its positive part. At every L>=N one has the exact saturation

    mu_L(ker Phi_L)=J intersect V_(2L).                  (2)

Indeed ker Phi consists of dyads having at least one leg in ker E_L.
Using (1), their products span r times all products of a word of length at
most L and a word of length at most L-N. Those products span V_(2L-N).
Equation (1) at 2L proves (2). The inclusion in J is automatic.
The Hermitian version follows by symmetrizing a preimage; both maps respect *.

## 2. Why saturation repairs the missing normalization step

For a local flagged coefficient array B=(B_0,B_1), call B a scaled TP array
when mu_L(B_0+B_1)=c I. This is a linear space; individual B_x need not be
positive. Its scale is c=sum_x Tr B_x, the identity coefficient of mu.

The analogous finite-algebra Choi space consists of all Hermitian arrays X
on the sector-preserving Choi space whose summed output partial trace is
c I on every input sector. It is exactly the linear span of finite-algebra
CPTP maps, since it has a strictly positive CPTP center.

**Surjectivity with scale.** Phi maps the universal scaled-TP linear space
ONTO this finite-algebra scaled-TP space, preserving c.

To prove this, first choose any Hermitian preimage B of X, possible since
E_L is onto. Its overlap defect mu(B)-cI lies in J intersect V_(2L).
By (2), choose a Hermitian D in ker Phi with mu(D)=mu(B)-cI. Then B-D is
universally scaled TP and has the same evaluated Choi array X.
This is a linear lifting assertion. D is not asserted positive, and no
positive universal extension of an arbitrary finite-grid channel is claimed.

<a id="p2-r14"></a>

## 3. Flat tester theorem

Let the parties have possibly different supports and word levels L_A>=N_A,
L_B>=N_B. Let Q_xy be four PSD matrices on V_(L_A) tensor V_(L_B). Assume:

1. Q is an exactly normalized universal word tester: for all local Hermitian
   scaled-TP coefficient arrays B,C with scales b,c,

       sum_xy Tr[Q_xy (B_x tensor C_y)]=bc.

   This is precisely the affine constraint in the SDP dual to universal
   NS-completion. It can be checked by the existing rational NS projector.
2. For every flag pair, Q_xy annihilates

       (ker E_A tensor V_B)+(V_A tensor ker E_B).          (3)

Then there exists a finite-dimensional VALID PHYSICAL PROCESS at the chosen
angle supports that has the same pairing as Q with every evaluated polynomial
Choi kernel, in particular the exact same GYNI score.

Proof. Choose any right inverses F_A,F_B of E_A,E_B and put

    Z_xy=(F_A tensor F_B)^* Q_xy (F_A tensor F_B).

This is PSD. Condition (3) implies
Q_xy=(E_A tensor E_B)^* Z_xy (E_A tensor E_B), independently of the chosen
right inverses. By scale-preserving surjectivity, every pair of finite-algebra
CPTP Choi arrays has universal scaled-TP preimages. Tester normalization
therefore says that Z pairs to one with every such pair. All coherent
cross-sector entries are retained. Z is thus a normalized reduced process
on the full direct sum of the selected irreducible Choi spaces.

The winning Kraus polynomials have length one and are evaluated exactly, so
the score is unchanged. The physical lift in section 5 completes the proof.

If such a Q and a feasible universal completion H have exactly the same
score/scale, their common value is the unrestricted optimum and it is attained
in the displayed finite dimensions. Neither matching nor (3) is asserted
for current numerical data.

## 4. A scalar ZERO test that forces the full coherent kernel condition

The condition (3) is much stronger than fitting scalar moments or applying
Gaussian/Radau quadrature to one tester slice. Positivity supplies a useful
exact alternative.

For Alice define the positive aggregate marginal

    M_A[u,v] = (1/(4 n_B)) sum_(x,y,w) Q_xy[u,w;v,w],
    n_B=dim V_B.

With the standard trace pairing, tester normalization implies
M_A[u,v]=ell_A(u^*v), with ell_A(I)=1.
(The channel overlap map itself uses v^*u, as in section 1.)
One proof is to contract Bob against the normalized uniform diagonal local
channel, then use that the orthogonal complement of ker mu is the range of
mu^*. The resulting Alice tester is independent of its output flag.
No assertion of traciality is needed.

At the MINIMAL level L_A=N_A, ker E_A is spanned by r_A. Therefore the single
nonnegative number ell_A(r_A^*r_A) is zero if and only if all Q_xy annihilate
r_A tensor V_B. This follows because 4 n_B ell_A(r_A^*r_A) is the sum of
nonnegative quadratic forms (r_A tensor e_w)^*Q_xy(r_A tensor e_w). Every
summand must vanish, and a zero quadratic form of a PSD matrix is a nullvector.
The analogous Bob test gives all of (3). At larger levels, test the spanning
relations r_A u, |u|<=L_A-N_A, or sum their nonnegative squared norms.

The minimal-level scalar polynomials are exactly

    r^*r = q(C)^2,                         E empty
           2(1-C)q(C)^2,                   E={+1}
           2(1+C)q(C)^2,                   E={-1}
           4(1-C^2)q(C)^2,                 E={+1,-1}.    (4)

They are nonnegative on [-1,1] and have degree N. This gives an objective-
compatible central flatness certificate using moments through degree N,
while positivity promotes it to every coherent tester entry. An approximate
zero, a small numerical eigenvalue, or quadrature matching fewer moments
cannot be substituted for exact zero.

## 5. Physical reconstruction

Apply the [unequal-sector CP lift](../physical-process/reduced_process_theorem.md#7-unequal-sector-generalization-of-the-physical-lift) to Z. That theorem owns the deterministic repair, every peripheral output charge, endpoint characters, and dimension formula. No extra assumption is needed beyond the normalized reduced process constructed in section 3.

## 6. Current frontier and limits

The certified six-angle support has four interiors and both endpoints, so
N=10, quotient-algebra dimension 20, and input/output dimensions 12/24.
At word level 10 a single degree-10 relation per party is enough for the
conditional flatness test. This is a sharper exact realization criterion
than arbitrary finite-rank or scalar quadrature guesses.

It does not say that an optimal level-10 tester is flat, that these particular
six angles are optimal, or that any unrestricted optimizer has finite support.
It does not construct a matching completion. The exact interval is owned by [CERTIFIED_BOUNDS.json](../../CERTIFIED_BOUNDS.json).

## 7. Relation to the output-dephased Jacobi recurrence

With T=a+b, D=a-b, one has C=T^2/2-I and ab-ba=-TD. Thus the scalar zero
polynomials in (4) are ordinary polynomials in T^2 and are valid at T=0 and
T=+/-2. No spectral denominator is inverted.

On the fixed output-sign row s, the corresponding module annihilator is

    q_s(t)=prod_(interior j)(t^2-2-2c_j)
           times (t-2s), if +1 is selected,
           times t, if -1 is selected.

Its degree is N and the first N Jacobi/coset polynomials span the local
output-sign row space. This is a complementary LOCAL recurrence, rather
than a fitted bivariate low-degree relation. It keeps separate outcome
signs and all coherent matrix rows. The proof above uses the ordinary word
space because its exact local TP-lifting statement is particularly direct;
no lower coset cutoff is claimed without its own saturation check.

## 8. The same mechanism works with the current safe rational denominators

Let h_A,h_B be fixed central Hermitian polynomial denominators, uniformly
invertible in every reflection representation. Replace local features u by
u h^{-1}. Assume h^2 lies in V_(2L), and the winning map has an exact coefficient
vector in the chosen feature space. Universal scaled TP now means

    mu_L(B)=c h^2,

and the tester normalization in section 3 uses this scale c. Evaluation is
E_(h,L):u -> pi(u)pi(h)^{-1}. Since pi(h) is invertible, ker E_(h,L)=ker E_L.
Thus the ideal-saturation theorem is unchanged. For a finite-algebra scaled-TP
Choi array, the preimage defect is mu(B)-c h^2 in J intersect V_(2L), and (2)
repairs it exactly. The same PSD tester reconstruction and all-charge physical
lift therefore apply without a polynomial-denominator degree penalty beyond
the explicitly stated feature/overlap containment conditions.

For the scalar-zero formulation, exhibit a strictly positive local coefficient
channel center C_B, with mu(C_B)=h_B^2 and both setting blocks positive definite.
Contract Q against C_B, equivalently against its positive square root on both
sides, to obtain the positive Alice aggregate. It is an overlap moment matrix
with ell_A(h_A^2)=1. At L_A=N_A its exact zero ell_A(r_A^*r_A)=0 forces the full
Alice kernel condition, because every eigenvalue of the Bob center is positive.
Exchange parties for the other condition. If no such strictly positive center
has been provided, retain the direct full-kernel test (3); do not infer this
scalar reduction from a singular contraction.

The already audited Laurent denominator
h=(1+rho U)(1+rho U^*) at rho=1/25 has precisely such an explicit positive
overlap-Gram center in the existing certificate repair. Therefore the
conditional theorem applies to that rational-feature family as well. It does
not assert a matching flat tester for its current degree-eight certificate.

## 9. Explicit special-support examples

At a Jordan angle theta, T has eigenvalues+/-2cos(theta). For a generic interior
angle, either output-sign row sees both eigenvalues. At theta=0, an output-sign
s row sees only2s; at theta=pi/2, it sees0.

Consequently, if there are four distinct interior angles theta_1,...,theta_4
and the endpoint theta=0, the exact local annihilator is

    q_s(t)=(t-2s) product_(j=1)^4(t^2-4cos^2(theta_j)).  (8)

It has degree9, matching the nine local algebra coordinates per output sign.
The first nine coset functions, degrees0 through8, span those coordinates.
At degree9 there is one exact polynomial relation. With both endpoints and
three interiors, the analogous annihilator is

    t(t-2s) product_(j=1)^3(t^2-4cos^2(theta_j)),

of degree8. This explains the earlier uniform-five-angle rank deficiency
without treating it as a true optimality relation.

For the full reflection algebra at the first support, a polynomial A(T)+B(T)D
vanishes exactly when A is divisible by
(t^2-4)product_j(t^2-4cos^2 theta_j), while B is divisible by the interior
product. Thus the NS defects of a finite-grid completion can be separated
from the universal identities explicitly.

For a support-specific extension one could add Kraus features containing q_s(T),
which vanish on the candidate support, while solving all universal NS
identities and maintaining a positive Gram kernel. Such an extension would
preserve the candidate complementary score if it existed. Positivity and
existence have not been established, and the current five-angle process is
not an exact KKT optimizer. No extension is claimed merely from divisibility. The polynomials q_s have zeros
on the physical spectral interval, so they may be used as vanishing Kraus
multipliers but cannot be inverted as universal denominators without a separate
removable-singularity proof at every root.
