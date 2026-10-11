# Quantitative completeness of the universal word hierarchy

This proof combines finite-SDP duality with a centered-path encoder, a full decoder and a formal GYNI symmetry average. Its bound concerns unrestricted optimal values.

<a id="p2-r05"></a>

## Theorem

Let omega be the unrestricted finite-dimensional process/instrument GYNI supremum after the labelled-projective modelling reduction. Let b_L be the minimum scale in the universal real reflection-word Gram SDP on all reduced words of length at most L, as defined in the [word certificate proof](../foundations/uniform_word_channel_theorem.md).

Let c_N be the physical fixed-instrument process optimum for the left regular
representation of D_N, of order 2N, with the usual output setting flags. For
every N>=2, the universal reflection-word optimum at length L=2N-1 satisfies

    omega <= b_(2N-1)
          <= c_N sec^4(pi/(4N-2))
          <= omega sec^4(pi/(4N-2)).                     (1)

Thus the excess is at most omega[sec^4(pi/(2L))-1] along odd L>=3. Its leading
asymptotic coefficient is omega*pi^2/(2L^2). If a wholly numerical upper error
is desired, replace omega by any already-certified universal upper bound (or
by 1). The bound is a theorem about optimal values; it does not imply that a
finite numerical solver has found the optimal c_N or b_L.

The following sections prove the finite process-SDP duality, universal circuit, decoder identity, and free-word coefficient constraints used by this theorem.

## Finite-SDP duality: fixed-instrument process SDP dual is an NS CP completion

For one party let D_A=I_(AI AO)/d_AO be the Choi operator of the completely
depolarizing channel, and let T_A=ker Tr_AO in the real Hermitian vector space.
The affine space of TP Choi matrices is D_A+T_A. The analogous definitions hold
for B, with setting flags INCLUDED in the output spaces.

A positive W is a normalized process exactly when

    <W,D_A tensor D_B>=1,
    <W,T_A tensor D_B>=0,
    <W,D_A tensor T_B>=0,
    <W,T_A tensor T_B>=0.

These follow by expanding normalization on products of TP maps. Conversely,
normalization on products of CPTP maps implies these equations by perturbing
D_A,D_B in every tangent direction; each depolarizing Choi matrix is positive
definite. Thus the dual of maximizing <G,W> is minimizing c subject to

    F=c D_A tensor D_B + A tensor D_B + D_A tensor B + Z >= G,
    A in T_A, B in T_B, Z in T_A tensor T_B.                (1)

The partial traces of F obey

    Tr_BO F=(cD_A+A) tensor I_BI,
    Tr_AO F=I_AI tensor (cD_B+B),
    Tr_AOBO F=c I_AI tensor I_BI.                          (2)

Since F>=G>=0, its positive marginal Choi matrices make F/c a CPTP
no-signalling channel. Conversely every scaled CPTP NS Choi matrix has the
form (1): subtract its two marginals and add the depolarizing product to obtain
Z with both output partial traces zero.

The primal white-noise process is positive definite and strictly feasible.
A sufficiently large depolarizing product is strictly dual feasible. Hence
finite-dimensional SDP Slater duality gives an attained completion of scale
exactly c_N. Pinch the classical output flags: this preserves (2), positivity,
and dominance of the flag-diagonal G, so write its CP flag blocks as F_xy.
All data for the finite dihedral permutation representation are real. Averaging
a completion with its complex conjugate gives real symmetric Choi matrices,
which have real Kraus factorizations. Finally c_N<=1, because the average over
settings of each party's full projective instrument is CPTP, and the product
of these channels contains the four winning CP branches.

## 1. Representatives forming a centered Cayley path

Let U=R0 R1 and q:D_infinity -> D_N reduce the exponent of U modulo N.
Use the infinite dihedral normal form (k,b)=U^k R0^b, with multiplication
(k,b)(l,c)=(k+(-1)^b l,b xor c). Label its Cayley line by
integers j:

    g_(2k)=U^(-k),
    g_(2k+1)=U^k R0.

The reduced word length of g_j is |j|. On these integer labels,

- R0 sends an even j to j+1 and an odd j to j-1
- R1 sends an even j to j-1 and an odd j to j+1

The finite quotient D_N identifies j modulo 2N. Choose the 2N representatives

    E={g_j:-N+1<=j<=N}.

On the interior path j=-N+2,...,N-1, of length m=2N-2, put

    eta_j=sqrt(2/(m+1)) sin(pi(j+N-1)/(m+1)),

and set eta=0 at the two endpoint representatives. This is a normalized
nonnegative vector. Every generator sends EVERY support element g into E,
with no wraparound: the support is separated from each endpoint of the
representative path by one vertex.

For s=R0,R1, write

    lambda_s=<eta,lambda_N(s)eta>.

The sum of the two matching adjacencies is the path adjacency, so the sine
vector gives exactly

    (lambda_R0+lambda_R1)/2=cos(pi/(2N-1)).               (2)

Neither generator needs to be encoded perfectly.
The average overlap is the largest possible Rayleigh value for this support
path, by the standard tridiagonal path eigenvalue formula.

## Deterministic polynomial, trace-preserving encode/apply/uncompute

Choose any real orthogonal O on C^(2N) with O|0>=eta, and let

    C_pi=sum_(g in E) |q(g)><q(g)| tensor pi(g^-1),
    T_pi=C_pi (O tensor I).

T_pi is unitary and T_pi(|0> tensor xi)=sum_g eta_g |q(g)> tensor pi(g^-1)xi. To lift a finite-grid channel:

1. Locally add the pure ancilla |0> and apply T_pi
2. Apply the finite-grid channel to the two dihedral ancillas, letting each
   original Hilbert space pass through as a local memory wire
3. Locally apply T_pi^* and discard the dihedral ancilla; retain the setting flag

Each step is a deterministic local channel supermap. Thus a scale-c NS channel
remains a scale-c NS channel, INCLUDING the flag-wise marginal identities.
This is the standard closure of complete no-signalling under local pre/post
channels with local memory: tracing all Bob outputs removes Bob's TP
postprocessing and leaves Alice's original marginal acting only on her encoded
input and memory; Bob's TP encoding cannot change that marginal.

All lifted Kraus operators are finite word polynomials. More explicitly, for
a finite-grid Kraus matrix L and decoded ancilla indices a,b, the lifted Kraus
operator is

    sum_(hA,hB,gA,gB)
       O_(hA,a) O_(hB,b) eta_gA eta_gB
       L_(hA hB,gA gB)
       pi_A(hA gA^-1) tensor pi_B(hB gB^-1).              (6)

## 2. The full decoded measurement is exactly noisy only in its outcome

For any representation pi, use the unitary encoder just defined.
For a finite-grid generator s, every support transition
h=sg lies in E. Therefore every decoded Kraus branch of the unitary reflection
channel is exactly

    B_a(s)=<a|T_pi^*[lambda_N(s) tensor I]T_pi|0>
          =b_a(s) pi(s),
    b(s)=O^T lambda_N(s)eta.

In particular sum_a b_a(s)^2=1 and b_0(s)=lambda_s. The identity channel has
only the decoded branch a=0, with Kraus operator I.

For the projector P_sigma=(I+sigma pi(s))/2, sigma=+/-1, the decoded CP map is
therefore

    rho -> [rho+pi(s)rho pi(s)
              +sigma lambda_s(pi(s)rho+rho pi(s))]/4
         =alpha_s P_sigma rho P_sigma
                    +(1-alpha_s)P_-sigma rho P_-sigma,  (3)
    alpha_s=(1+lambda_s)/2.

This is an exact CP identity in every representation, including endpoints.
No branch is operationally postselected. Equation (3) describes the channel
obtained by uncomputing and discarding the entire ancilla.

For the bipartite winning map, the lifted CP branch at setting flag (x,y)
therefore contains the original winning branch with coefficient alpha_x alpha_y,
plus other explicitly positive CP branches. Let Lift(F) be the lifted optimal
NS completion of scale c_N. Then

    Lift(F) >= sum_xy alpha_x alpha_y G_xy.               (4)

## Formal game automorphisms, including every output flag

For a,b in {0,1}, define the signed generator substitution

    phi_ab(R_t)=(-1)^b R_(t xor a),
    phi_ab(S_t)=(-1)^a S_(t xor b).

Combine this substitution with the flag permutation taking the old block
(x xor a,y xor b) to the new block (x,y). These transformations form a group
of four commuting involutions.

On every reduced word the substitution is a signed permutation of reduced
words of the SAME length. Generator interchange preserves word reduction;
simultaneous sign reversal multiplies a word by the character (-1)^length.
Thus each transformation is a real orthogonal signed permutation on the finite
coefficient space. Its congruence preserves positive Gram matrices and trace.
There is no need for a physical unitary implementing the substitution on an
arbitrary reflection representation, especially at unequal endpoint ranks:
substitution into a universally valid channel family is sufficient.

The winning coefficient vector transforms exactly as

    phi_ab(k_(x xor a,y xor b)) = k_(x,y).

To check this directly, the first reflected factor picks up
(-1)^(y xor b)(-1)^b=(-1)^y, and the second picks up
(-1)^(x xor a)(-1)^a=(-1)^x. The generator indices return to x and y.

Flag-wise NS is preserved in two equivalent ways:

1. Substitute new involutions into the universal NS channel identity, then
   permute each party's own output setting flag. Summing the discarded flag
   merely reindexes that sum.
2. In formal word coefficients, an overlap v'^*v is sent to the same
   nonidentity reduced word under the generator permutation, times its scalar
   character. Nonidentity overlap coefficients remain zero. No nonidentity
   word can be sent to identity by these substitutions.

The transformations do not mix Alice and Bob inputs or outputs. The sign at
Alice depends only on the fixed relabelling parameter b, never on a runtime
Bob flag. Hence there is no hidden conditional signalling operation.

Apply the four-element twirl to the COMPLETE channel Lift(F) and inequality
(4). At each winning flag the averaged coefficient is

    a^2=[(alpha_0+alpha_1)/2]^2
       =[(1+cos(pi/(2N-1)))/2]^2
       =cos^4(pi/(4N-2)).                                (5)

All remaining terms are positive. Thus the twirled scale-c_N channel dominates
a^2 G. Divide it by a^2 to get an exact universal NS completion of G.

## 4. Word length and coefficient identities

For every output representative h, |h|<=N. Every encoder-support g has
|g|<=N-1. Each lifted Kraus word hg^-1 consequently has length at most

    N+(N-1)=2N-1.

The twirl changes signs or interchanges letters but never increases this
length. All Kraus coefficients are real. Evaluate the universal NS identities
in a fresh regular dihedral quotient injective on the overlap words, for
example cyclic order Q=4N-1. Distinct regular group matrices are orthogonal,
and their vectorizations and outer products give independent coefficient
families. Comparing coefficients proves every exact flag-wise word SDP
constraint. The next section gives the coefficient comparison explicitly.

## Coefficient extraction in full detail

The following finite algebra argument requires no infinite-kernel limit.

Let L=2N-1. Overlap words have length at most 2L=4N-2.
Choose a fresh quotient of cyclic order Q=4N-1. Rotation exponents in that
ball range from -(2N-1) to 2N-1, and reflection exponents have no greater
width. Their width is less than Q, so no alias is possible.

In the left regular representation rho_Q, distinct group matrices are
Hilbert-Schmidt orthogonal:

    Tr(rho_Q(g)^* rho_Q(h)) = 2Q times indicator(g=h).

In particular the vectors vec(rho_Q(u)) for u in the radius-L word list are
linearly independent. Their ordered dyads

    |rho_Q(u)>><<rho_Q(u')|

are linearly independent as well. The matrices rho_Q(w)^T for all possible
overlap words w are independently linearly independent, including the identity.

The lifted channel is NS in EVERY representation; therefore it is NS in this
specific new regular representation. For fixed output flag x its Bob-traced
Choi matrix has the form

    sum_(u,u',w) C_(x,u,u',w)
          |rho_Q(u)>><<rho_Q(u')| tensor rho_Q(w)^T
      = J(A_x) tensor I.

Pair first with each nonidentity rho_Q(w)^T in Hilbert-Schmidt inner product.
The right-hand side vanishes. Pair next with each Alice dyad. Their independence
implies C_(x,u,u',w)=0, exactly the formal coefficient equations of the original
word SDP. Repeat with A and B reversed. These are precisely the required
flag-wise NS equalities. Taking both output traces recovers c=sum_xy Tr H_xy. This completes the theorem.

The larger quotient here is only an injective finite coefficient probe. It is
never used to reduce the lifted polynomial, and its order is unrelated to the
source quotient's accidental polynomial relations. One cannot replace this
argument by testing only the original D_N representation. 

## Consequences and limits

The proof does not assert that the limiting optimizer is represented by a
trace-class infinite Gram kernel, by rational Laurent functions, or by a
finite-dimensional process. Trace can escape to long words in a minimizing
sequence, and weak limits require care with noncompact translation operators.
An exact closed-form value still needs new information about optimizers.

The argument's sine coefficients and optimum finite-grid completion need not
be rational. At each FIXED finite word level, rational certificates can
approximate any real feasible completion arbitrarily closely in scale: round
its slack Gram factors to rationals, project the rational matrix onto the
rational NS coefficient subspace, and add a rational diagonal identity whose
norm bound dominates the projection error. The fixed-level dimensions are
finite, so this exact-repair error tends to zero with the rounding error.
This is the existing exact-repair construction, not a numerical feasibility
claim.


The word-certificate theorem gives omega<=b_L, and the finite regular-representation strategy is admissible, so c_N<=omega. Monotonicity of the nested word spaces fills the intervening even levels, so the complete hierarchy decreases to omega. All arguments include scalar endpoint representations, unequal ranks and coherent direct sums. Finite SDP optimal values in this theorem are exact mathematical optima, not raw solver outputs.

## Verification

The exact independent centered-path checker covers N=2,...,60 and checks representative injectivity, supported generator transitions, degree bounds, fresh coefficient probes and symbolic sine recurrences. The twirl checker verifies the formal flag/relabel identities. The alternative-window checkers test the shared encoder machinery and its exact error-channel repair identities. Author encoder stress programs include floating matrix calculations and are diagnostics. See [reproduction](../../REPRODUCIBILITY.md).
