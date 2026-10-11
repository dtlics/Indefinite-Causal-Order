# C4-R03 — Stable endpoint polarization for the repeated-channel switch

Supplementary analytic proof. This is not a selected Lean endpoint and is not used by the main approximation lower-bound theorem. [Topic and related results](README.md).

## Statement

Let M,N>=1. Let a deterministic QC-CC circuit use exactly M A-slots and N B-slots after harmless padding. Suppose its full channel output has half-diamond error at most epsilon from S(A,B), uniformly over CPTP A,B. Symmetrize its slots separately, place A in one uniformly random A-slot and identity in the others, and place B in one uniformly random B-slot and identity in the others. This is a legal one-call-per-channel QC-CC circuit D.

Define lambda=1/M and mu=1/N. Then, for every A,B,

  (1/2)||D[A,B] - T_{lambda,mu}[A,B]||_diamond
    <= (2M-1)(2N-1) epsilon,

Here S is the full quantum-switch channel, Id is the identity channel, and the identity-diluted switch is

```text
T_{lambda,mu}(A,B)
  = lambda mu S(A,B)
    + lambda(1-mu) S(A,Id)
    + (1-lambda)mu S(Id,B)
    + (1-lambda)(1-mu) S(Id,Id).
```

This is the target in [the paper](../../../paper/main.tex), label `eq:dilution`. The estimate uses a full channel norm, so arbitrary control/target reference inputs are retained. The bound applies to classically adaptive call order; finite padded labeled slots and averaging permutations remain physically legal.

## Derivation

Put A(p)=(1-p)Id+pA, B(t)=(1-t)Id+tB, for 0<=p,t<=1. The circuit output F(p,t) has a bivariate Bernstein expansion with bidegree (M,N). Its coefficient F_{k,l} is the symmetrized circuit with k A-slots set to A and l B-slots set to B, all remaining slots identity.

For a univariate degree-at-most-m polynomial h, let

  L_m h = h(0)+h'(0)/m.

L_m extracts the first Bernstein coefficient (index 1). Consequently D= L_M^p L_N^t F. The switch polynomial G(p,t)=S(A(p),B(t)) is bilinear. Direct differentiation gives L_M^p L_N^t G=T_{1/M,1/N}.

The error E=F-G is Banach-valued, with sup_{[0,1]^2} ||E||_diamond <=2 epsilon. It remains to compute the norm of L_m on bounded real polynomials, and the same finite interpolation formula applies to an arbitrary Banach-valued polynomial.

## Sharp coefficient norm

For m>=2 take Lobatto nodes t_j=(1-cos(j*pi/m))/2, j=0,...,m. Let c_m=2 and c_j=1 for 1<=j<m. Exact endpoint differentiation gives

  L_m h = sum_j w_j h(t_j),
  w_0=1-(2m^2+1)/(3m),
  w_j=2(-1)^{j+1}/(m c_j t_j),  j>=1.

Here w_0<0 and sign(w_j)=(-1)^{j+1}. The polynomial H_m(t)=T_m(1-2t) has H_m(t_j)=(-1)^j, H_m(0)=1, and H'_m(0)=-2m^2. Thus

  sum_j |w_j| = -L_m H_m = 2m-1.

For m=1, L_1 h=h(1), whose norm is 1. Hence ||L_m||=2m-1 exactly, and the tensor-product functional has norm (2M-1)(2N-1). This proves the stated estimate. The bound is sharp if the only information about E is its bidegree and uniform norm: use E(p,t)=T_M(1-2p)T_N(1-2t) times a fixed vector. This does not assert that such an extremal error is realizable by a channel circuit.

## Scope and limitations

This avoids exponential full multiaffine-polarization losses because only the endpoint Bernstein coefficient (1,1) is needed. It does not create a dimension-growing lower bound: the target's switch weight is 1/(MN), while the transported error is O(MN epsilon). Any robust one-call witness must account for both factors.

If q is a worst-case total budget with adaptive order, padding to M=N=q is always safe, yielding factor (2q-1)^2. For a fixed padded budget M+N=q, use the sharper individual values.

The exact-simulation obstruction and finite certificate have separate owners: [P3](../p3-exact-switch-simulation/README.md). This supplementary argument does not claim a dimension-growing lower bound or a channel-realizable extremizer.
