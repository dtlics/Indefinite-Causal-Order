# Angle-uniform reflection-word channel certificates

This is a dimension-independent upper-bound construction. Each finite
word level is a sufficient SOS ansatz. The [completeness proof](../word-kernels/hierarchy_completeness.md) establishes convergence of the full hierarchy. A finite upper certificate alone does not identify the exact supremum.

## 1. Reduce instruments, not process dimensions

Use Liu–Chiribella Theorem 1 to replace arbitrary binary instruments by labelled
projective instruments, while allowing an arbitrary transformed valid process.
Set R_x=2P_(0|x)-I and S_y=2Q_(0|y)-I. These are Hermitian involutions; their
dimensions and Jordan angles are unrestricted. The Kraus operator of a winning
branch is

    K_xy=P_(y|x) tensor Q_(x|y)
        =[(I+(-1)^y R_x) tensor (I+(-1)^x S_y)]/4.

The winning CP map G has four orthogonal output-flag sectors (x,y), with
G_xy(rho)=K_xy rho K_xy^*/4. In a consistent Choi convention,

    GYNI score=Tr[W J(G)].

If using the fully transposed Choi convention, transpose BOTH W
and all Choi operators in this equation. Positivity, normalization and all
partial-trace identities below are unchanged.

<a id="p2-r04"></a>

## 2. A finite universal CP completion

Choose a finite list U of reduced words in two involutions, including the
empty word and each single letter. Reduction cancels adjacent equal letters;
dagger reverses a word. Let u(R) and v(S) denote their evaluations. For each
output flag (x,y), choose a real symmetric Gram matrix H_xy indexed by pairs
(u,v) in U×U and define

    J(F_xy)=sum H_xy[(u,v),(u',v')]
                  |u(R) tensor v(S)>><<u'(R) tensor v'(S)|.

If H_xy>=0, this is CP in every dimension. Let k_xy be the coefficient vector
of K_xy/2 in this word list: its four nonzero entries are

    k_xy[(R_x^a,S_y^b)]=(-1)^(a y+b x)/8, a,b in {0,1}.

The sufficient condition

    H_xy-k_xy k_xy^T>=0                                   (1)

therefore proves F_xy-G_xy is CP for every pair of reflections, without any
matrix-size or angle restriction.

## 3. Exact flag-wise no-signalling identities

For each x, each Alice word pair (u,u'), and every NONEMPTY reduced Bob word w,
impose

    sum_(y,v,v': reduce(v'^* v)=w)
       H_xy[(u,v),(u',v')]=0.                              (2)

For each y, each Bob word pair (v,v'), and every NONEMPTY reduced Alice word z,
impose

    sum_(x,u,u': reduce(u'^* u)=z)
       H_xy[(u,v),(u',v')]=0.                              (3)

These are coefficient identities; they are not tested on finitely many angles.
For a Kraus cross term, tracing Bob's quantum output gives the operator
(v'^* v)^T on Bob's input. Thus (2) gives exactly

    sum_y Tr_(B quantum output) J(F_xy)=J(A_x) tensor I_BI,

for some positive local Choi operator J(A_x), retaining Alice's setting flag x.
Likewise (3) gives

    sum_x Tr_(A quantum output) J(F_xy)=I_AI tensor J(B_y).

Positivity of these marginal maps follows from positivity of F, rather than
from a separately assumed positivity of their coefficient representations.

Taking both output traces, (2)-(3) kill every nonidentity overlap word.
Distinct reduced words satisfy u'^*u=empty iff u'=u. Consequently

    sum_xy Tr_outputs J(F_xy)=c I_AI tensor I_BI,
    c=sum_xy Tr H_xy.                                     (4)

For c>0, C=F/c is a CPTP no-signalling channel, INCLUDING its classical output
flags. All flag-wise marginal identities have been imposed before summing
the flags.

## 4. Why every valid process normalizes this channel

A valid bipartite process is normalized on product CPTP maps by definition.
It is also normalized on every CPTP no-signalling channel C.

To see this without an extra realizability assumption, let C_A,C_B be its
marginal channels and D_A,D_B fixed completely depolarizing channels. Define

    Z=J(C)-J(C_A) tensor J(D_B)
            -J(D_A) tensor J(C_B)+J(D_A) tensor J(D_B).

The two no-signalling identities imply Tr_AO Z=Tr_BO Z=0. Therefore
Tr(W Z)=0 by W=_AO W+_BO W-_AOBO W. The other three terms are product CPTP
channels and have process normalization 1,1,1. Hence Tr[W J(C)]=1.

No assertion that C is implementable by shared randomness, entanglement, or
a definite-order circuit is required. This is an affine-span consequence of
the process constraints.

By (1), F-G is CP. Positivity of W and (4) now prove the universal bound

    GYNI score=Tr[W J(G)]<=Tr[W J(F)]=c.                   (5)

Thus ANY exact Gram matrices satisfying (1)-(3) are a dimension-independent
certificate. The process normalization argument applies to the full output
ports, including the setting flags.

## 5. Exact coefficient repair

Numerical discovery searches for such matrices by minimizing sum Tr H_xy.
The discovery solver is not trusted as a certificate.

For exact repair, start from dyadic Gram factors L_xy and let

    H0_xy=k_xy k_xy^T+L_xy L_xy^T.

Arrange entries as a matrix indexed locally by (x,u,u') and (y,v,v'). For
each nonidentity reduced overlap word, its local index group contains all
settings and word pairs with that overlap. The groups are disjoint. Subtracting
the mean in each Bob group enforces (2); subtracting the mean in each Alice
group enforces (3). The two orthogonal projections act on separate tensor
factors and commute. They preserve simultaneous matrix transposition.

Call the resulting exact rational projection P_NS. If E=H0-P_NS(H0) and
delta>=max_xy ||E_xy||, then

    H_xy=P_NS(H0)_xy+delta I

satisfies (1)-(3). Adding diagonal Gram entries does not alter a nonidentity
overlap coefficient. The PSD proof is L_xy L_xy^T-E_xy+delta I>=0. Frobenius
and absolute row-sum bounds verify delta using integers only.


The [rational-kernel proof](../word-kernels/rational_kernel_ansatz.md) owns the rational generalization; [reproduction](../../REPRODUCIBILITY.md) owns its executable commands.

## Diagonal majorant identity

For a real coefficient vector e, put a_i=|e_i| and s=sum_i a_i. The diagonal matrix D=diag(s a_i) satisfies the exact sum-of-squares identity

    D-e e^T = sum_(i<j) a_i a_j
       (sign(e_i) basis_i-sign(e_j) basis_j)
       (sign(e_i) basis_i-sign(e_j) basis_j)^T.

Zero coefficients cause no exception. Diagonal nonnegative Grams in product-unitary words give a scaled NS channel even with arbitrary flag-dependent weights: summing Bob's output flag and quantum output leaves an Alice Choi matrix tensor the Bob input identity, and conversely. Their total scale is the sum of their coefficients. This is the exact positive error-channel construction used by the alternative-window checker.
