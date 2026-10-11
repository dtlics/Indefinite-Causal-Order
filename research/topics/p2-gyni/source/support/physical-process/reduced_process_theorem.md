# Exact finite-angle reduced processes and explicit physical lift

This is a finite-angle equivalence, not an attainment theorem for
unrestricted GYNI. The proof retains all physical output-charge sectors through
an explicit completely positive lift; it does not discard those sectors.

<a id="p2-r01"></a>

## 1. Local sector-preserving channel space

Fix K angle sectors, each H_j=C^2, and the two classical setting flags x. Let
S=direct_sum_j (H_j^input tensor H_j^output). Its dimension is n=4K.
We work with Choi operators pinched in the two setting flags, so a local
operator is X=(X_0,X_1), with each X_x acting on S. Coherence between different
j is retained within each X_x.

Let T(X)_j=sum_x Tr_output [(X_x)_{jj}]. The sector-preserving CPTP maps are
exactly X>=0 with T(X)_j=I_2 for every j. They have a strictly positive
base point J0=I_S/4 in each flag. Thus their affine span is J0+ker T.

On local Choi operators define the Hilbert-Schmidt orthogonal projections

    R=(1/4) T* T,
    D(X)=Tr(X) I/(8K).

Here T* puts a matrix on each angle-diagonal input block, tensored with I_2 on
its output, and replicates it in both setting flags. Therefore TT*=4I,
R^2=R, D^2=D, RD=DR=D, and R(I)=I. The kernel of R is ker T.

## 2. Exact reduced-process cone

A reduced process Z consists of four flag blocks Z_xy on S_A tensor S_B.
It is valid exactly when

    Z>=0,
    Tr Z=16,
    P(Z)=Z,

where subscripts act on the named local Choi coordinates, including the flag,

    P=R_A+R_B-R_A R_B-D_A+D_A R_B-D_B+R_A D_B.       (1)

This is an orthogonal projector. Indeed decompose each local space into
range D, range(R-D), and ker R. Formula (1) keeps every tensor component
except ker R_A tensor ker R_B, ker R_A tensor range D_B, and
range D_A tensor ker R_B. Those are exactly the components that must vanish
for

    Tr[Z (J_A tensor J_B)]=1

on all sector-preserving CPTP J_A,J_B. The remaining constant is one because
J0_A tensor J0_B=I/16 and Tr Z=16. This also proves necessity, using the
strictly positive J0 to span arbitrary sufficiently small ker T variations.

The normalized white-noise point is Z0=I/(4K^2) in every flag block, and the
affine projector is

    P_aff(X)=P(X)+(16-Tr X) I/(64K^2).                (2)

Each PSD block has dimension16K^2. There are no optimization variables for
nonzero output charges, although the final physical process has all of them.

## 3. Local deterministic repair and its CP adjoint

Let H=direct_sum_j H_j. For an arbitrary local channel with Kraus operators
L_(x,a), define a sector-preserving repaired instrument using

    L'_(x,a,0)=sum_i Pi_i L_(x,a) Pi_i,
    L'_(x,a,i,j,r,t)=|i,t><j,r| L_(x,a) Pi_i /sqrt(2),
                 i!=j, r,t in {0,1}.

The output flag x is unchanged. The second family replaces output in sector
j!=i by I_2/2 in the original input sector i. The first family keeps every
sector-preserving part coherently. For each i,

    sum_(x,a,branches) L'^* L'
      =sum_i Pi_i [sum_(x,a) L_(x,a)^*L_(x,a)] Pi_i=I.

Thus this linear CP map E on Choi operators takes every CPTP instrument to a
sector-preserving CPTP instrument. It fixes every instrument whose Kraus
operators already preserve sectors, including the fixed GYNI instruments.
It can equivalently be realized by coherently copying the incoming sector,
then applying the channel and repairing the outgoing sector with that memory.

For a valid reduced process Z define

    W=(E_A* tensor E_B*)(Z).                         (3)

The adjoint is completely positive, hence W>=0. For every physical CPTP
instrument pair J_A,J_B,

    Tr[W(J_A tensor J_B)]
      =Tr[Z(E_A(J_A) tensor E_B(J_B))]=1.

Therefore W is a valid physical bipartite process. Since E fixes the winning
instruments, W and Z have exactly the same GYNI score.

## 4. Explicit all-charge formula

The zero local phase-charge block is S; each nonzero charge (i,j), i!=j,
has input H_i and output H_j. The local adjoint in (3) is:

- On zero charge, keep Z unchanged, including all angle coherences
- On charge (i,j), take Z's angle-diagonal (i,i) local block, trace its local
  output, divide by2, and tensor I_2 on the output H_j

Perform this independently for Alice and Bob. This reconstructs every pair
of local charges and all four setting flags. All coefficients are rational.
The trace of a local lift is K times the reduced trace, so Tr W=16K^2,
matching output dimensions4K at each party. Input dimensions are2K.

Conversely, compress any physical process to the zero/zero charge block.
It is PSD and normalizes every sector-preserving CPTP pair, so satisfies
(1)-(2). Its score is unchanged because the objective is entirely supported
on that block. Compression and (3) prove exact equality of the reduced and
full fixed-instrument optima, and the lift is a right inverse of compression.

## 5. Consequences and limits

- Numerical discovery can optimize only four16K^2 PSD blocks; the existing
  physical-game symmetry further leaves one representative and its
  party-symmetric/antisymmetric parts
- Exact rational certificates can certify Z alone and then apply the exact
  rational CP lift; peripheral charge-sector Gram factors need not be stored
- If a finite-angle optimum is algebraic, the lift preserves that algebraicity
- Nothing here implies a finite angle cutoff, unrestricted attainment, or an
  exact value of GYNI

The test implementation in reduced_process.py compares the lift against the
pre-existing full physical process projector for K=1,2,3, checks PSD and score
preservation, and compresses the earlier K6 strategy. The tests are numerical
validation, not a substitute for the CP/normalization proof above.

<a id="p2-r02"></a>

## 6. Compact semialgebraic finite-size characterization

Let alpha_K be the optimum when both parties use one common set of K canonical
angles, now allowed to vary in [0,pi/2], and optimize the reduced process Z.
The feasible process set is compact: Z>=0 and Tr Z=16 bound its operator norm,
and (1) is closed. Parameterize each angle by (c_j,s_j) with c_j,s_j>=0 and
c_j^2+s_j^2=1. Projector entries are c_j^2,c_j s_j,s_j^2. Therefore the joint
angle/process problem is a compact semialgebraic optimization with rational
coefficients. The PSD constraints can be written using principal minors.

It follows that alpha_K is attained and is a real algebraic number, and an
optimizer can be chosen with real algebraic process and projector entries.
Indeed the attainable score set is compact and semialgebraic over Q; its
maximum is an algebraic boundary point. A nonempty semialgebraic fiber over
that algebraic value has a point over the real algebraic numbers, by the
real-closed-field transfer principle. The physical lift preserves this field.

This statement does not identify alpha_K or provide a practical exact solver.
It does make a finite-attainment search precise: a matching finite process,
if found within this exhaustion, admits an algebraic representative. The
sequence alpha_K is nondecreasing by adding an unused angle with a valid input
embedding/output decoder. The earlier Jordan-grid approximation theorem gives

    sup_K alpha_K = omega_GYNI.

The conclusion is a compact algebraic finite-size exhaustion, not a proof that
the supremum stabilizes at any K. In particular, algebraicity of every alpha_K
does not imply algebraicity or finite attainment of its limit.

## 7. Unequal-sector generalization of the physical lift, including all endpoint characters and charges

Index the irreducible sectors by i, of dimensions d_i=2 in the interior and
1 for each scalar endpoint character. On an arbitrary flagged channel Kraus
operator K use the deterministic repair branches

    K_0=sum_i Pi_i K Pi_i,
    K_(i,j,r,t)=|i,t><j,r| K Pi_i /sqrt(d_i), i!=j.

Summing all branch adjoint-products gives sum_i Pi_i K^*K Pi_i. Thus a CPTP
channel remains CPTP. Every sector-preserving winning Kraus operator is
fixed, including its coherent entries across different sectors. The output
setting flag remains untouched.

Let E be this CP Choi supermap. The required physical process is

    W=(E_A^* tensor E_B^*)(Z).

It is positive and normalizes every arbitrary physical CPTP pair. On zero
charge it equals Z. On each nonzero local charge (i,j) it uses

    (Tr_(output i) Z_(ii)/d_i) tensor I_(output j).

Apply this formula independently at both parties: NONE of the peripheral
charges is dropped. The construction works for unequal sector dimensions
and all four scalar endpoint characters. Local input dimension is
2I+2|E|, and the setting-flag output dimension is twice that.
