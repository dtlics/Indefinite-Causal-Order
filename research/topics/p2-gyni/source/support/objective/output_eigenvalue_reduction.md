# GYNI-specific output-eigenvalue reduction

Exact finite-angle equivalence. This preserves every process
normalization charge and all relevant angle coherences. It does not prove an
angle cutoff, finite attainment, or the unrestricted value.

<a id="p2-r08"></a>

## 1. A local output channel fixes the winning instruments

For the canonical local instruments, write R_x=2P_(0|x)-I. The output quantum
port contains the same angle sectors as the input and a classical setting flag
x. Define the flag-controlled output CPTP map

    D_A(X)_x=[X_x+R_x X_x R_x]/2.

Equivalently it dephases only the two GLOBAL eigenspaces of R_x. Each eigenspace
contains all K angle labels, so this does not measure the angle. For each
instrument branch,

    R_x P_(a|x)=(-1)^a P_(a|x),
    D_A(Ad(P_(a|x)))=Ad(P_(a|x)).

If W is any valid physical process, pulling it back through D_A and D_B gives
another positive normalized process: for arbitrary local CPTP maps M_A,M_B,

    <(D_A* tensor D_B*)W, J(M_A) tensor J(M_B)>
      =<W,J(D_A o M_A) tensor J(D_B o M_B)>=1.

The winning score is unchanged. D_A is self-adjoint and idempotent in Choi
coordinates, so the process can be taken block diagonal in the output
reflection eigenvalue at each setting flag. The setting control is on the
existing OUTPUT flag; no setting-controlled operation is assumed on the
process input.

## 2. Sixteen smaller PSD blocks

At angle theta_j use the real output basis

    v_(0|0)=|0>, v_(1|0)=|1>,
    v_(0|1)=(cos theta_j,sin theta_j),
    v_(1|1)=(-sin theta_j,cos theta_j).

A setting/angle-controlled output basis change maps these to computational
outcome labels a. After the dephasing, label the local classical output by
l=(x,a). In the zero-charge reduced space, each fixed l has local vector space

    H_l=direct_sum_j C^2_input, dimension d=2K.

The reduced process is now W_lm, sixteen PSD matrices of size d^2=4K^2.
Previously it was four matrices of size16K^2. Coherences j!=j' remain inside
EACH W_lm, including the angle-changing terms allowed by the rook constraint.

Let the local map on these classical-label Choi blocks be

    T(X)_j=sum_(x,a) (X_(x,a))_jj.

The sector-preserving CPTP condition is exactly T(X)_j=I_2. Define

    R=(1/4)T* T,
    D(X)=Tr(X)I/(8K).

The audited reduced-process projector has the SAME form

    P=R_A+R_B-R_A R_B-D_A+D_A R_B-D_B+R_A D_B.

Thus W is valid exactly when W_lm>=0, P(W)=W and Tr W=16. The affine projector
is

    P_aff(X)=P(X)+(16-Tr X)I/(64K^2).

The cone and this projector are angle-independent. The output basis change
commutes with R and D: sector-diagonal output partial traces are invariant
under output unitaries, and their adjoints place identity on the output. The
twirl has the same commutation. This proves exact correspondence with the
previous reduced cone after the objective-preserving twirl.

In fact each block has Tr W_lm=1. Take the local CPTP Choi operator I_d entirely
in a single classical label l, and likewise at Bob's label m. Their product
normalization gives this identity directly.

## 3. The objective becomes linear in the local angle vectors

Put

    nu_(a|x)=direct_sum_j v_(a|x)(theta_j), in C^(2K).

At setting pair (x,y), the only winning outcome block is
l=(x,y), m=(y,x), where

    G_lm=|nu_(y|x) tensor nu_(x|y)><same|/4.

All other objective blocks vanish. The qubit output is now classical, but the
angle output wire and the vectors nu retain their full quantum coherence.
It would be invalid to replace these coherent vectors by a probability
mixture over their angle components.

## 4. The existing game symmetry leaves three error orbits

Define errors e=a xor y and f=b xor x. The two game input-flip/output-flip
symmetries preserve e,f and connect all four setting pairs. At x=y=0 choose
four representative blocks H_ef on C^(2K) tensor C^(2K).

On the retained input space let

    A=direct_sum_j [cos(theta_j)Z+sin(theta_j)X],
    B=I_K tensor [[0,-1],[1,0]].

Then every block is reconstructed as

    W_(x,a),(y,b)=U_xy H_(a xor y),(b xor x) U_xy*,
    U_xy=(A^x B^y) tensor (B^x A^y).

Phases arising from the discarded output eigenvectors are constant within
an outcome block and cancel in conjugation. Party exchange makes H_10 the
swap of H_01, while H_00 and H_11 commute with the swap. Their PSD tests split
into symmetric and antisymmetric sizes

    d(d+1)/2 and d(d-1)/2, d=2K.

Thus there are two swap-split representative blocks and one full d^2 block.
The largest PSD matrix at K5 has size100, versus the prior size210 after
its party-swap reduction. The objective depends only on H_00.

## 5. Commutation with the complete physical CP lift

The previous exact lift fills every nonzero local charge (i,j), i!=j, by

    [Tr_output Z_(ii)/2] tensor I_(output j).

This block is invariant under the output reflection at sector j. Twirling Z
before lifting does not change Tr_output Z_(ii), so the lifted leakage block
is identical either way. The zero-charge block is unchanged by the lift and
receives the same coherent output conjugation on its (i,j) angle entries.
These facts hold independently at both parties, proving

    Lift o D_reduced = D_full o Lift

on every pair of phase charges and every setting flag. No peripheral charge
is deleted or assigned a nonphysical value.

## 6. Exact checks and discovery implementation

`check_exact_output_twirl.py` verifies with integers only:

- commutation with the audited reduced tangent projector
- trace preservation and each winning Kraus eigenidentity
- commutation with the full CP lift for K1,2,3
- all1,9,49 physical charge pairs and4,36,196 flag blocks respectively

`exact_output_twirl_checks.json` records all passes. The random test matrices
have off-angle entries; those entries are retained.


Discovery solvers are not required for the proof or supplied exact lower certificate.
