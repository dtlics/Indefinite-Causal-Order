# A finite SDP class of universal rational Laurent Choi kernels

This is a new exact ansatz and certificate recipe. Numerical probes
are discovery only; no new bound is claimed without rational repair/replay.

Let U=R0 R1 and fix rational 0<=r<1. The central Hermitian operator

    q_r(U)=(I+rU)(I+rU*)=(1+r^2)I+r(U+U*)

commutes with both reflections. It obeys q_r(U)>=(1-r)^2 I in every unitary
representation, including the scalar endpoint characters. Thus inverses exist
uniformly, with no removable-singularity or measure-zero proviso.

For a finite reduced word list U_L, use the rational Kraus features

    f_u(R)=u(R) q_r(R0R1)^-1.

For every flag (x,y), a PSD coefficient Gram H_xy defines a universal CP map
with product features f_u(R) tensor f_v(S). All features share a fixed central
denominator; independent coherent angle arguments are retained in the Choi
kernel, exactly as for the polynomial hierarchy.

<a id="p2-r06"></a>

## Winning numerator

Represent q_A q_B k_xy in the polynomial word basis, where

    k_xy=(I+(-1)^y R_x) tensor (I+(-1)^x S_y)/8.

Call this coefficient vector k'_xy. It is supported on local words of length
at most three. The Gram inequality H_xy>=k'_xy k'_xy^T therefore proves exact
CP dominance over the original winning map after multiplying both Kraus sides
by q_A^-1 q_B^-1. No approximation to the winning map is made.

## Exact marginal identities

Write the Laurent/group-algebra coefficients of q^2 as t_w. They are

    t_empty=alpha=1+4r^2+r^4,
    t_U=t_U*=beta=2r(1+r^2),
    t_U^2=t_U*^2=gamma=r^2,

with all other coefficients zero. For fixed x,u,u', require

    sum_(y,v,v':v'^*v=w) H_xy[(u,v),(u',v')]
       =A_x[u,u'] t_w                                    (1)

for every overlap word w, including the identity. Impose the exchanged version
for each y,v,v'. Since q is central, division by the Bob denominator q_B^2
turns (1) into the flag-wise NS identity. Exchange parties for the other side.
All these are finite, rational linear equations when r is rational.

Taking both output traces makes the polynomial numerator c q_A^2 q_B^2.
Its identity/identity coefficient is sum_xy Tr H_xy. Hence the channel scale is

    c=(sum_xy Tr H_xy)/alpha^2.                           (2)

This is NOT the maximum of a sampled-angle function. It is the exact scalar
trace-preservation coefficient, valid for every finite representation.

## Efficient exact affine projection

Reshape H locally as indices (x,u,u') versus (y,v,v'). Group the local indices
by overlap word w; let m_w be the group size and s_w its coefficient sum.
The Euclidean projection onto the subspace s_w=a t_w is

    a=[sum_w (t_w/m_w)s_w]/[sum_w t_w^2/m_w],
    each entry in group w -= (s_w-a t_w)/m_w.

Apply on Bob and Alice tensor factors; these two orthogonal projections
commute. They preserve global matrix transposition. The projection is exactly
rational for rational r, and hence can be replayed with common-denominator
integer arithmetic. The ordinary free-word SDP is the special case r=0.

## A full-rank NS repair direction

Adding a diagonal Gram identity alone does not preserve (1) when r!=0. A
replacement is explicit when

    mu=alpha-2beta-2gamma>0.

This covers the small positive r values suggested by the stored numerical
tails. For n=|U_L| and L>=4 choose epsilon=mu/(2n), and define a local Gram

    J=epsilon I_n + (mu/2)|empty><empty|
       +beta|empty+U><empty+U|
       +gamma|empty+U^2><empty+U^2|.

Then J>=epsilon I_n, while the sum of its Kraus adjoint-products is exactly

    epsilon n I+(mu/2)I
       +beta(2I+U+U*)+gamma(2I+U^2+U*^2)=q^2.

Therefore J_xy=J tensor J/4 in all four flags is a unit-scale, full-rank NS
rational-feature channel, with J_xy>=epsilon^2 I/4.

Starting from rational slack factors L_xy, set

    H0_xy=k'_xy k'_xy^T+L_xy L_xy^T,
    P=P_NS(H0), E=H0-P.

If e>=max_xy ||E_xy||, the repaired Gram

    H_xy=P_xy+(4e/epsilon^2)J_xy

satisfies exact NS and dominates the winning numerator. Its PSD proof is the
explicit inequality L L^T-E+(4e/epsilon^2)J_xy>=0. Exact Frobenius or row-sum
integer bounds certify e. Equation (2) supplies the repaired rational scale.
This repair is finite, dimension-independent, and valid at all endpoint
representations.

The common denominator can be generalized to any fixed strictly positive
central Laurent polynomial, with the same proportional-overlap equations.
For large r where the convenient displayed mu is not positive, positivity
of q^2-epsilon n I still permits a Laurent SOS factorization, but that
factorization must itself be explicitly certified before use.

## Relation to the observed geometric tails

The inverse of q_r has Fourier coefficients proportional to (-r)^|k|. This
makes the ansatz a controlled test of a common rational denominator, rather
than an inference that a diagonal Gram tail proves an infinite recurrence.
A scalar recurrence fit had large residuals; a one-pole denominator is only a candidate basis improvement.

The independent hierarchy-completeness theorem in
`hierarchy_completeness.md` does not assume this rational ansatz is optimal,
or that any rational kernel attains the unrestricted optimum.

## Certificate implementation and conventions

For the maintained degree-eight r=1/25 payload, the exact values live in [CERTIFIED_BOUNDS.json](../../CERTIFIED_BOUNDS.json). The independent standard-library checker uses affine isometries of the integers, explicit semantic indices and both projection orders; it imports no author verifier or numerical solver. It checks 38,148 marginal and 1,089 total-trace equations, including coefficients that vanish.

With unnormalised Choi vectors, Tr_out(|A>><<B|)=(B* A)^T. The physical trace of a scale-c Choi matrix is c d_AI d_BI; c itself is the TP scale. Full kernels retain coherent angle pairs. Real coefficient Grams do not require real physical representations.

The proof that every valid process pairs to one with the normalized NS completion is owned by [the universal word-channel theorem](../foundations/uniform_word_channel_theorem.md#4-why-every-valid-process-normalizes-this-channel). It is an affine-span identity and applies equally to these rational-feature channels. It does not require local implementability of the NS channel.

For r=1/25 the denominator is at least 576/625 at every representation, with endpoint values 676/625 and 576/625. The coefficient constants are alpha=393126/390625, mu=329276/390625 and epsilon=164638/6640625 at n=17. The independent checker reconstructs the target at denominator 64*25^8. Its exact integer residual uses the smaller valid upward-rounded Frobenius or maximum-row-sum bound per block, followed by the maximum over flags. The repair cost is exactly 4e/epsilon^2 and is checked against the repaired-minus-projected scale. Numerical clipping used only to propose factors is not a premise: their supplied rational product L L^T is positive exactly.

## Verification scope

The supplied independent result and factor archives support the exact finite certificate. The universal operator proof covers arbitrary finite representations, endpoint characters, unequal ranks and direct sums. It does not establish an optimal rational ansatz, attainment, or a matching physical value.
