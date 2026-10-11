# Complementary support equations and the missing positive-kernel compactness

The complementary-face criterion gives an
exact route by which a global dual could FORCE the conditional
finite realization, and identifies a genuine obstruction to extracting an
infinite universal completion merely from bounded finite-level Gram traces.
No finite-rank or finite-angle assumption is inserted into the original model.

<a id="p2-r15"></a>

## 1. The full complementary face, before choosing a spectral support

At a fixed universal polynomial or safe-central-rational feature level, let
H_xy be an exact feasible NS completion and G_xy=k_xy k_xy^*. Put S_xy=H_xy-G_xy.
Let Q_xy be an exact positive normalized tester for the SAME feature system.
For its score p and the completion's scale c,

    c-p = sum_xy Tr(S_xy Q_xy) >= 0.                    (1)

Equality holds if and only if S_xy Q_xy=0 for every flag pair. This follows
from Tr(SQ)=||S^(1/2)Q^(1/2)||_HS^2. All four flags, rather than an averaged
single block, are essential.

Choose exact matrices V_xy whose columns span ker S_xy. Every complementary
positive tester has exactly the form

    Q_xy=V_xy R_xy V_xy^*, R_xy>=0.                    (2)

The remaining equations are the FULL universal TP-tester affine equations
P_NS(Q)=I (or their weighted-denominator version). Consequently feasibility
of (2) and those equations is an exact primal-dual matching certificate;
merely observing small eigenvalues of S is not. This is a finite face problem
once an exact H is supplied. It does not assert that the existing H is optimal.

## 2. A dual slack can expose the local spectral ideal

Write K_xy=ker S_xy and let P_xy be its orthogonal projection. Define

    A_A=sum_xy Tr_B P_xy,    A_B=sum_xy Tr_A P_xy.       (3)

A local coefficient vector r lies in ker A_A exactly when
r tensor V_B is orthogonal to EVERY K_xy. This equivalence is the sum-of-
squares identity

    <r,A_A r>=sum_(xy,j) ||P_xy(r tensor e_j)||^2.

Therefore every complementary Q in (2) annihilates r tensor V_B. The Bob
statement is identical. If these forced local nullspaces contain the full
spectral-ideal kernels J_A intersect V_L and J_B intersect V_L, with L>=N
and real admissible central roots as in the preceding finite-realization
proof, EVERY feasible complementary tester reconstructs as a valid finite
physical process of the same score. At L=N it is enough that they contain
the degree-N annihilators r_A and r_B.

This is a sufficient way for a global dual to force flatness rather than
assuming a candidate tester is flat. It is not necessary: the affine
normalization equations in (2) can force a smaller face than ker S alone.

For a proposed support not forced by (3), the exact necessary and sufficient
matching equations within that support instead use

    range Q_xy subset K_xy intersect
        [(J_A intersect V_L)^perp tensor (J_B intersect V_L)^perp],

together with the complete affine equations and Q_xy>=0. The local ideal is
spectral, not a finite GROUP quotient. The [finite-realization theorem](../finite-realization/flat_tester_realization.md) supplies the
unequal-sector CP lift and every peripheral charge automatically.

The [spectral-ideal theorem](../finite-realization/flat_tester_realization.md#4-a-scalar-zero-test-that-forces-the-full-coherent-kernel-condition) owns the annihilator norms and their Jacobi-coordinate interpretation. No annihilator is inverted on the physical spectrum.

<a id="p2-r16"></a>

## 3. What the current exact global upper actually permits

The independently audited rational-L8 certificate has STRICTLY POSITIVE
coefficient slacks. This follows without an approximate eigenvalue:
its integer repair bound e obeys

    e^2 > ||E_xy||_F^2

for all four exact residual blocks. In the audited repair decomposition,
S_xy dominates (e I-E_xy)/D, where D is the exact residual denominator.
A strictly positive rational lower bound is

    S_xy >= [(e^2-||E_xy||_F^2)/(2 e D)] I > 0.         (4)

Indeed sqrt(s)<=e-(e^2-s)/(2e). The required integers come directly from the
independent exact audit and are checked by `check_resume_obstructions.py`.

Hence this particular repaired H has no complementary normalized Q at all:
its complementary face consists only of zero. This is entirely consistent
with its role as a nonmatching upper certificate. Reading small numerical
modes of its unrepaired discovery point as an exact complementary support
would be invalid. A successful exact search must change the completion,
not reinterpret the certificate's strictly positive repair as a nullspace.
No new numerical upper bound is claimed here; microscopic repair-rounding
improvements are irrelevant to the missing matching construction.

<a id="p2-r17"></a>

## 4. Global rank deficiency does not produce local spectral flatness

There is an exact counterexample inside the actual normalized process model.
Take two distinct rational interior angles and a shared maximally entangled
input state on their four-dimensional direct sum. Set W=rho_input tensor
I_outputs, with both setting flags included. This is a valid process, since
arbitrary local CPTP maps preserve trace. Its degree-two word tester has four
identical positive 25-by-25 blocks, each of rank eight, while each aggregate
local moment matrix is 5-by-5 and FULL RANK.

The tester is thus globally very rank deficient but has no local annihilator
of word degree at most two. All its exact universal affine equations pass.
The saved checker constructs it with rational matrices and verifies these
ranks by nonzero minors modulo a prime, together with exact kernel/dimension
bounds. This example is not claimed complementary to an optimal GYNI dual;
it establishes exactly that positivity, full normalization and global low
rank alone cannot supply the needed local recurrence.

<a id="p2-r18"></a>

## 5. Bounded-trace universal CP/NS kernels are not coefficientwise closed

This obstruction already occurs for one party. Let P_+=(I+a)/2,
P_-=(I-a)/2 and U=ab. For every positive integer m, consider the two Kraus
operators

    K_0=P_+,    K_1=U^m P_-.

They are polynomial and EXACTLY CPTP because

    K_0^*K_0+K_1^*K_1=P_++P_-=I.

In the orthonormal free-word coefficient basis their positive Gram B_m has
trace one. The second Kraus vector is supported on two words of lengths
2m and 2m+1, so for every fixed finite coefficient window it eventually
vanishes. The coefficientwise limit is therefore

    B_infinity=|P_+><P_+|,    mu(B_infinity)=P_+ != c I

for ANY scalar c. The missing half of the trace carries exactly the
nonconstant normalization term that cancels the low-degree branch.

Taking tensor products with a fixed unitary channel gives bipartite NS
examples. More specifically, adding epsilon times such a product channel
to ANY feasible GYNI completion preserves CP dominance, exact NS, and a
uniformly bounded scale, but the coefficientwise limit is not NS. Thus the
failure applies even to sequences of feasible GYNI completions.

This does NOT prove nonattainment, or show that an optimal sequence must
lose mass. It rules out the inference that bounded Gram trace and finite
coordinate compactness alone produce an optimal universal positive kernel.
The example preserves all representation sectors: its Kraus identities are
free-word identities, valid at all endpoints and arbitrary finite dimensions.

<a id="p2-r19"></a>

## 6. A sufficient weighted-tail invariant, with explicit uniform constants

A genuinely stronger estimate WOULD justify a positive infinite-kernel
construction. For a word u set w(u)=(1+|u|)^2 and for a pair (u,v) set
D_(u,v)=w(u)w(v). Suppose a sequence of exact finite polynomial universal
completions H^(m) has scales c_m decreasing to c, and satisfies the additional
UNIFORM bound

    sum_xy Tr(D H_xy^(m)) <= B < infinity.              (5)

Then a subsequence has a positive infinite Gram H, with the same target
CP-domination, exact NS in EVERY finite representation, and scale exactly c.
This gives an actual universal positive-kernel completion at c; it is an
optimizer if c is the unrestricted infimum. It does not produce a finite
physical process attaining c.

Here is a dimension-independent proof, including the endpoint issue. There
are two reduced words of each positive length, so

    Z=sum_u 1/w(u) <=3,
    sum_(max(|u|,|v|)>L) 1/[w(u)w(v)] <=12/(L+1)=:d_L.

For any Kraus factorization and ANY reflection representation, Cauchy-Schwarz
bounds the sum of squared operator norms of the coefficient tails by B d_L.
The entire Kraus operator series is absolutely norm convergent, since its
weighted coefficient square sum is finite and sum 1/D<=9. There is no
special exception at commuting reflections or scalar endpoint characters.

For each finite completion, truncating its Kraus coefficient vectors to
local lengths at most L changes the channel in diamond norm by at most

    2 sqrt(c_m B d_L)+B d_L.                            (6)

To see this, the full Stinespring operator has norm sqrt(c_m), its discarded
coefficient tail has norm at most sqrt(B d_L), and the truncated operator
has norm at most their sum. The usual difference-of-two-squares estimate
holds after arbitrary input amplification, proving (6).

Finite coefficient blocks have a convergent diagonal subsequence. Positivity
and target domination survive every finite compression. Bound (5) passes to
the limit by monotone finite sums, making its coefficient Gram trace class.
The unweighted trace outside the length-L square is at most B/(L+2)^2,
so no scale is lost. Equation (6) makes the evaluated maps a uniform limit
across ALL finite representations; exact NS and TP scale therefore pass to
the limit. Equivalently, factor the limiting positive Gram and use the
absolutely norm-convergent Kraus series just established.

The argument is a sufficient criterion, not a bound already known for GYNI.
It can be weakened with other summable reciprocal weights, but a tail
estimate has to be proved rather than assumed from a finite numerical fit.

<a id="p2-r20"></a>

## 7. Why ordinary normalization gives no such coercive estimate

Every polynomial normalized universal tester has

    Q_xy[(u,v),(u,v)]=1

for every pair of words and every flag pair: a single unitary word in a
single local output flag is a CPTP channel. Thus no such tester can satisfy
Q_xy>=alpha D with alpha>0 and unbounded diagonal D. The diagonal entries
alone contradict it. A direct coercive energy bound from one normalized
process/tester is therefore unavailable.

In the explicit escaping channel of section 5, the quadratic coefficient
energy grows with m, so it meets the bounded-trace hypothesis and violates
exactly the additional uniform-tail hypothesis. The existing certificates
only give finite energy at each finite level; they do not give a uniform B
as their scale approaches the unrestricted optimum.

## 8. Precise outcome and next genuinely missing step

The complementary face equations and weighted-tail criterion are exact.
Neither is verified for a matching candidate by the present data. The
current exact upper has an empty complementary face; global numerical ranks
and bounded trace cannot repair that gap. No new optimizer, analytically
evaluated endpoint, or improved certified interval is obtained.

A substantive continuation needs either an exact global completion with a
nonempty normalized complementary face that forces an admissible local
spectral ideal, or a proved uniform tail/regularity bound for a near-optimal
sequence together with an analytic evaluation of its scale. Choosing a
finite quotient, fitting old angles, or taking a coefficientwise limit does
not establish either missing assertion.

<a id="p2-r21"></a>

## 9. Exact minimal-level obstruction to making TP surjectivity positive

The spectral-ideal TP-surjectivity result is genuinely linear; it cannot be
upgraded silently to a positive universal channel lift, even for a single
interior angle at its minimal level.

Fix c in (-1,1) with c!=0, s=sqrt(1-c^2), and evaluate a=Z, b=cZ+sX.
There is one interior sector, N=2, and at L=2 the evaluation kernel is the
one-dimensional span of r=C-cI. The finite-algebra channel Ad(X) is unitary,
CPTP, and has rank-one Choi matrix. Its degree-one preimage is F=(b-ca)/s.

Suppose a positive universal level-two coefficient Gram lifted this precise
channel and were TP. Positivity and the rank-one evaluated Choi matrix imply
that every Kraus polynomial evaluates to a scalar multiple of X. Hence every
Kraus has the form

    K_j=alpha_j F+beta_j r,    sum_j |alpha_j|^2=1.

The same form covers extra setting flags: any flag absent from the finite
channel has alpha_j=0. Since r is central and Hermitian,

    sum_j K_j^*K_j=F^2+2 Re(gamma) rF+delta r^2,
    gamma=sum_j conjugate(alpha_j) beta_j, delta=sum_j |beta_j|^2>=0.

The first and last terms have even word parity, and rF is a nonzero odd
polynomial. TP therefore forces Re(gamma)=0. But direct multiplication gives

    F^2=I-[2c/(1-c^2)]r.

TP would then require delta r^2=[2c/(1-c^2)]r. The left side has nonzero
length-four coefficients unless delta=0; the right side has length at most
two and is nonzero because c!=0. This is impossible. Equivalently cancel the
non-zero-divisor r and compare the nonconstant polynomial delta r with a
nonzero constant.

Thus there is NO positive universal TP lift at L=2, even though the exact
linear scale-preserving TP lift exists at this same level. Rational instances
c=7/25 and c=161/289 are verified with exact free words in the checker.
This does not exclude a higher-degree or safe-rational positive lift; it does
not claim this particular product channel is the GYNI optimum. It identifies
why the prior conditional finite-realization theorem is useful in the tester
(direction-of-duality) argument but does not by itself construct a global
positive completion.

<a id="p2-r25"></a>

## 10. Convex averaging does not close a strictly positive value gap

A countable positive mixture of existing strict upper completions has scale
sum_m alpha_m c_m. If c_m>omega for every index with alpha_m>0 and the weights
sum to one, then its scale is still strictly greater than omega. Consequently
one cannot get an exact matching completion just by summably mixing the
current finite certificates. A telescoping subtraction would require a new
positivity argument; bounded traces supply none, by section 5.
