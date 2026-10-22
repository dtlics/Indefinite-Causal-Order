# Adaptive acceptance under replacement noise

This method proves the acceptance estimate used by the [local-noise
converse](local-converse.md) and the [global-noise result](../global-noise.md).
It is a statement about acceptance events, with arbitrary intermediate
quantum memory; it assumes no preservation of a data register.

## Statement and normalization

Let $D=2m\geq8$, let $U$ be Haar distributed on $U(D)$, and set

$$
A=U(X\otimes I_m)U^\dagger,\qquad
B=U(Y\otimes I_m)U^\dagger,\qquad
\Omega_D(T)=\operatorname{Tr}(T)I_D/D.
$$

The same $U$ is used in both slots. Consider an ordinary two-slot
acceptance tester that calls $\operatorname{Ad}_A$ and
$\operatorname{Ad}_B$ once each, in either fixed order. It may prepare an
arbitrary query-memory state, retain arbitrary ancillas and references,
process the first output adaptively, and perform a final joint accept
measurement. Write $p_{11}$ for its Haar-averaged acceptance with both
ideal slots, and $p_{01},p_{10},p_{00}$ when the first, second, or both
slots are replaced by $\Omega_D$. Then

$$
\boxed{
 |p_{11}-p_{01}|,\ |p_{11}-p_{10}|,\ |p_{11}-p_{00}|
 \ \leq\ \kappa_D=\frac{3}{2D}.}
\tag{1}
$$

For a subnormalized initial preparation of trace $w$, every right-hand
side is $w\kappa_D$. Thus private classical initial-order choices share
one total initial weight, rather than each receiving a new constant.

All Choi matrices in this proof are **unnormalized**, so
$\operatorname{Tr}_{\mathrm{out}}J_{\mathcal G}=I_{\mathrm{in}}$ and
$J_{\Omega_D}=I_{\mathrm{in,out}}/D$. Label the ports

$$
(0,1,2,3)=(\mathrm{in}_1,\mathrm{out}_1,
             \mathrm{in}_2,\mathrm{out}_2).
$$

With fully transposed slot Choi matrices, their mixed-tensor signature is
$(+,-,+,-)$. The physical objectives are

$$
\begin{aligned}
M_{11}&=\mathbb E_U[J_A^T\otimes J_B^T],\\
\Delta_1&=M_{11}-\mathbb E_U[J_{\Omega_D}^T\otimes J_B^T],\\
\Delta_2&=M_{11}-\mathbb E_U[J_A^T\otimes J_{\Omega_D}^T],\\
\Delta_{12}&=M_{11}-J_{\Omega_D}^T\otimes J_{\Omega_D}^T.
\end{aligned}
\tag{2}
$$

There is no normalized-program-state factor $1/D$ or $1/D^2$ outside
these objectives.

## The four-port causal dual

An accepted tester $T$ is bounded by a deterministic tester:

$$
0\leq T\leq \Xi_{012}\otimes I_3,\qquad
\operatorname{Tr}_2\Xi_{012}=\rho_0\otimes I_1,\qquad
\operatorname{Tr}\rho_0=1.
\tag{3}
$$

For either signed objective $\sigma\Delta$, $\sigma\in\{-1,1\}$, a
sufficient dual is

$$
H\geq0,\qquad H\geq\sigma\Delta,\qquad
\operatorname{Tr}_3H=Z_{01}\otimes I_2,\qquad
\operatorname{Tr}_1Z=\kappa_D I_0.
\tag{4}
$$

Indeed, positivity and the directed trace constraints give

$$
\begin{aligned}
\operatorname{Tr}(T\sigma\Delta)
&\leq\operatorname{Tr}(TH)
 \leq\operatorname{Tr}[(\Xi\otimes I_3)H]\\
&=\operatorname{Tr}[\Xi(Z\otimes I_2)]
 =\operatorname{Tr}[(\rho\otimes I_1)Z]
 =\kappa_D\operatorname{Tr}\rho=\kappa_D.
\end{aligned}
\tag{5}
$$

In particular, the scalar cost is $\kappa_D$. The constraints trace the
**second output**, followed by the **first output**, with the intervening
input identities as in (4).

Let $Q_{ij}=|\Omega\rangle\langle\Omega|_{ij}\otimes I_{\{i,j\}^c}$,
where $|\Omega\rangle=\sum_a|a,a\rangle$, for opposite-sign ports.
Define the positive dominator

$$
P=\frac{4I}{5D^3}
  +\frac{Q_{01}+Q_{23}}{10D^2}
  +\frac{Q_{03}}{2D^2},\qquad
H_\sigma=P+\frac{\sigma\Delta}{2}.
\tag{6}
$$

The positivity proof below establishes $P\pm\Delta/2\geq0$ for all
three objectives in (2). It follows that $H_\sigma\geq0$ and
$H_\sigma-\sigma\Delta=H_{-\sigma}\geq0$.

The remaining constraints have direct partial-trace proofs:

$$
\begin{aligned}
\operatorname{Tr}_3P&=Z_P\otimes I_2,&
Z_P&=\frac{7I_{01}}{5D^2}+\frac{Q_{01}}{10D},&
\operatorname{Tr}_1Z_P&=\frac{3I_0}{2D};\\
R_{01}&=\frac{I_{01}/D-Q_{01}}{D^2-1},&&&
\operatorname{Tr}_1R_{01}&=0.
\end{aligned}
\tag{7}
$$

For $\Delta_1,\Delta_{12}$,
$\operatorname{Tr}_3\Delta=R_{01}\otimes I_2$; for $\Delta_2$ this
partial trace is zero. Thus take $Z=Z_P+\sigma R_{01}/2$ in the first
and double cases, and $Z=Z_P$ in the second. Both prefixes in (4) are
exact equalities, with $\kappa_D=3/(2D)$. Positivity of $Z$ also follows
from the positive operator $H_\sigma$ and its first trace equality.

## Exact moment identification

### Conditioning and the fourth moment

Condition on $B=\operatorname{diag}(I_m,-I_m)$. The conditional
anticommuting balanced reflection is

$$
A=\begin{pmatrix}0&V\\V^\dagger&0\end{pmatrix},
\qquad V\text{ Haar in }U(m).
$$

Its first unitary moment and invariance under $V\mapsto e^{i\theta}V$
give

$$
\mathbb E[A T A\mid B]
 =\frac{\operatorname{Tr}(T)I-\operatorname{Tr}(BT)B}{D}.
\tag{8}
$$

Before full slot transposition the channel difference from $\Omega_D$
has Choi matrix $-B^T\otimes B/D$. In the convention (2), therefore,

$$
\Delta_1=-\frac1D\mathbb E_B
 \left[B_0\otimes B_1^T\otimes
       |\overline B\rangle\!\rangle
       \langle\!\langle\overline B|_{23}\right].
\tag{9}
$$

Exchanging the slots gives $\Delta_2$. Thus only the central fourth
moment of one balanced reflection is needed.

Put $G=(D^2-1)(D^2-9)$. For ordinary four-copy permutations $P_\pi$,

$$
\mathbb E B^{\otimes4}=\sum_{\pi\in S_4}u_\pi P_\pi,
\qquad
u_\pi=\begin{cases}
(D^2-6)/G,&\pi\text{ has type }2^2,\\
-D/G,&\pi\text{ is odd},\\
3/G,&\pi\text{ has type }1^4\text{ or }3\,1.
\end{cases}
\tag{10}
$$

Here is an analytic derivation. For partitions $4,31,22,211,1111$, the
Schur-sector eigenvalues of the twirled fourth tensor power are

$$
\frac{3}{(D+1)(D+3)},\quad
-\frac1{D^2-1},\quad
\frac3{D^2-1},\quad
-\frac1{D^2-1},\quad
\frac3{(D-1)(D-3)}.
\tag{11}
$$

To obtain them, $\operatorname{Tr}B^j$ is zero for odd $j$, and is $D$
for even $j$. The character formula consequently reduces to

$$
s_\lambda(B)=\frac{\chi_\lambda(2^2)D^2}{8}
              +\frac{\chi_\lambda(4)D}{4}.
$$

Dividing by the hook-formula dimension $s_\lambda(I_D)$ gives (11).
Expanding the five central projectors gives (10). Explicitly, the $S_4$
character rows in class order $1^4,2\,1^2,2^2,3\,1,4$ are

$$
\begin{pmatrix}
1&1&1&1&1\\
3&1&-1&0&-1\\
2&0&2&-1&0\\
3&-1&-1&0&1\\
1&-1&1&1&-1
\end{pmatrix},
$$

with class sizes $1,6,3,8,6$. These finite rational identities give the
moment for all relevant $D$, rather than interpolating sampled matrices.

### Four-port diagram coefficients

Let $B_\pi=P_\pi^{\Gamma_{1,3}}$, with $P_\pi$ sending input slot $j$
to output slot $\pi(j)$. Enumerate permutations lexicographically from
index zero. Applying the fixed reshuffling in (9) to (10) gives

$$
\Delta_\ell=\sum_i d_i^{(\ell)}B_i,\qquad
d_i^{(\ell)}=\begin{cases}
1/G,&i\in\mathcal E,\\
-(D^2-6)/(DG),&i\in\mathcal C_\ell,\\
-3/(DG),&\text{otherwise},
\end{cases}
\tag{12}
$$

where

$$
\begin{aligned}
\mathcal E&=\{0,3,4,7,8,11,12,15,16,19,20,23\},\\
\mathcal C_1&=\{6,17,22\},\qquad
\mathcal C_2=\{1,17,22\}.
\end{aligned}
$$

The double case has the exact additional term

$$
\Delta_{12}=\Delta_1+
 \frac{I}{D^2(D^2-1)}-\frac{Q_{23}}{D(D^2-1)}.
\tag{13}
$$

Indeed, the difference is
$J_{\Omega_D}^T\otimes(\mathbb E J_B^T-J_{\Omega_D}^T)$, and the second
factor is $(I/D-Q_{23})/(D^2-1)$. This also proves the marginal identities
used in (7), since all slot Choi output traces are identities.

For a direct exact identification of the port convention, the replay
computes $h_i=\operatorname{Tr}(B_i^\dagger\Delta)$ by canonical Pauli
contractions and checks every equation

$$
\sum_j D^{\#\operatorname{cycles}(\pi_i^{-1}\pi_j)}d_j=h_i.
\tag{14}
$$

These are 24 polynomial identities for each of the three objectives after
clearing $D^2G$. Each $B_i$ commutes with the mixed Haar action, so its
trace contraction may be evaluated on the canonical
$X\otimes I_m,Y\otimes I_m$ pair before averaging. A closed matrix loop
has trace $(D/2)\operatorname{Tr}_2$ of its Pauli word; every erased slot
contributes its explicit factor $1/D$. This supplies the exact polynomial
right-hand sides without sampled unitaries. The Gram matrix in (14) is the Hilbert--Schmidt Gram of
the partially transposed permutations. It is invertible for $D\geq4$:
ordinary permutation operators are independent by acting on a tuple of
four distinct labels, and partial transpose is invertible. Therefore (14)
uniquely identifies the physical moment coefficients. Both (9)--(10) and
the independent Gram check use the actual unnormalized Choi convention.

## Positivity on the entire physical space

The small polynomial checks below are exhaustive; they do not assume a
list of numerical irreducible blocks. Work on
$V_0\otimes\overline V_1\otimes V_2\otimes\overline V_3$.

For each edge $e\in\{01,03,21,23\}$, let $T_e(X)$ place an
unnormalized cup on $e$ and a matrix vector $|X\rangle\!\rangle$ on
the remaining positive/negative pair, ordered positive first. Let
$\mathcal K=\sum_e\operatorname{im}T_e$. Split $X$ into its scalar and
traceless parts.

The scalar parts span the two full-cup vectors

$$
s_0=\Omega_{01}\Omega_{23},\qquad
s_1=\Omega_{03}\Omega_{21},
$$

with Gram matrix

$$
G_{\rm singlet}=\begin{pmatrix}D^2&D\\D&D^2\end{pmatrix}.
\tag{15}
$$

For traceless $X,Y$, direct index contraction gives

$$
\langle T_e(X),T_f(Y)\rangle
=(G_{\rm cup})_{ef}\operatorname{Tr}(X^\dagger Y),\qquad
G_{\rm cup}=\begin{pmatrix}
D&1&1&0\\1&D&0&1\\1&0&D&1\\0&1&1&D
\end{pmatrix}.
\tag{16}
$$

Its eigenvalues are $D+2,D,D,D-2$. The scalar images are orthogonal to
all traceless images. Thus for $D\geq8$, $\mathcal K$ consists of two
singlets and four independent traceless-matrix copies, of total dimension
$2+4(D^2-1)=4D^2-2$.

The candidate diagram algebra preserves this decomposition directly.
Every partially transposed permutation diagram factors into same-sign
permutations and opposite-sign cup contractions: first place its cups,
then permute the remaining same-sign through lines.
Same-sign swaps permute the cup edge while preserving the orientation of
$X$. On a traceless cup vector, $Q_f$ multiplies by $D$ for the same
cup, transfers to the new edge when the cups share one endpoint, and
annihilates the vector for disjoint cups because $\operatorname{Tr}X=0$.
Consequently every diagram acts on the four edge labels tensored with
the identity on the complete traceless-matrix space. It suffices to
evaluate its multiplicity Gram form on one Hilbert--Schmidt unit matrix
$X=|0\rangle\langle1|$. Equivalently these are the four adjoint
multiplicity copies. Positivity is tested by Gram forms, not by treating
the nonorthogonal cup vectors as an orthonormal coordinate basis.

On $\mathcal K^\perp$, every cup contraction vanishes. Every diagram
containing a top cup also contains a bottom cup, so its adjoint image
lies in a cup image and it kills $\mathcal K^\perp$. Only the four
all-through diagrams survive:

$$
I,\quad S_{02},\quad S_{13},\quad S_{02}S_{13}.
\tag{17}
$$

The swaps are commuting Hermitian involutions. Their four simultaneous
characters $(s,t)\in\{-1,1\}^2$ therefore exhaust the complement,
regardless of the dimensions of the character spaces. All four are
nonzero for $D\geq4$: choose distinct labels $0,1$ on the two positive
wires and $2,3$ on the two negative wires, symmetrize or antisymmetrize
each pair, and interleave the wires. Disjoint positive/negative label
sets kill every cup. Both $\mathcal K$ and its complement are reducing
for the Hermitian candidates, so no cross terms remain to be checked.

## The exact polynomial PSD certificate

Multiply each $H_\sigma$ by the positive common denominator

$$
L=10D^3(D^2-1)(D^2-9)=10D^3G>0.
\tag{18}
$$

For each of the three objectives and both signs, contract this scaled
diagram element against (15) and the four $T_e(|0\rangle\langle1|)$.
The resulting $2\times2$ and $4\times4$ Hermitian Gram forms have
integer-polynomial entries. There is an explicit exact rule for every
entry: join the diagram and bra/ket cup index constraints; pin the free
positive label to (0) and the free negative label to (1) in the
traceless sector; a contradictory $0=1$ class contributes zero, and
each unpinned connected index class contributes $D$.

All nonempty principal minors are checked, rather than only leading
minors. There are

$$
3\cdot2\left[(2^2-1)+(2^4-1)\right]=108
$$

such minors. For every rebuilt determinant $f(D)$, its complete
coefficient vector after $D=8+x$ has nonnegative integers and a strictly
positive constant. Hence $f(D)>0$ for every real $D\geq8$. This proves
positive semidefiniteness of both Gram forms on the entire interval;
division by the positive $L$ recovers the unscaled candidates.

The bulk tests also have an explicit compact formula. On a character
$(s,t)$, the scaled eigenvalue is

$$
8G+\sigma\left[
5D^3(1+st)-15D^2(s+t)
+\mathbf1_{\Delta=\Delta_{12}}5D(D^2-9)
\right].
\tag{19}
$$

The single-replacement bulk coefficients agree for the first and second
patterns. Thus two pattern types, two signs, and four characters give
16 distinct polynomial checks. Each full coefficient vector after
$D=8+x$ is nonnegative with strictly positive constant, proving
positivity on all four bulk character spaces. Equations (15)--(19)
therefore prove $P\pm\Delta/2\geq0$ on the full physical Hilbert space
for all three patterns. Together with (7), this completes (4)--(5) and
the acceptance theorem (1).

The complete finite data and independent reconstruction are
[`acceptance_correct_dual_sharp_certificate.json`](../checks/acceptance/acceptance_correct_dual_sharp_certificate.json)
and [`acceptance_correct_sharp_stdlib_replay.py`](../checks/acceptance/acceptance_correct_sharp_stdlib_replay.py).
The replay rebuilds all 72 objective Gram identities, 108 principal
minors, 16 bulk polynomials, and the causal prefix equalities using
standard-library integer-polynomial arithmetic. It recomputes the
determinants and shifted coefficients rather than trusting stored
Boolean flags, factorizations or matrix strings. No numerical
eigensolver, irreducible-block search or SDP solver is used. The data
and symbolic checks support this mathematical proof; this method is not
a Lean formalization.

## Subnormalized testers and the two uses of the estimate

If the preparation in (3) has $\operatorname{Tr}\rho=w$, the same trace
calculation (5) gives $w\kappa_D$. An initial known instrument may act
on a data input before deciding whether, and which, module to query.
On the maximally mixed input its first-query effect $E$ has launch
probability $w=\operatorname{Tr}(E)/D$; its prepared query-memory state
has this same trace. The effect precedes oracle access and is independent
of $U$. Input-dependent launch decisions are therefore included.
For private classical first-order labels, apply the result to their
subnormalized preparations and sum their weights. The Haar pair is
exchangeable up to irrelevant signs, so reverse order has the same
constant. This does not grant coherent unknown-module index access.

Two consequences explain the dependencies of the result:

1. For independent global replacement with rate $\gamma$ per call,
   write $t=1-\gamma$. The actual event probability is
   $p_\gamma=t^2p_{11}+t\gamma(p_{01}+p_{10})+\gamma^2p_{00}$.
   Applying (1) to all three patterns directly gives
   $|p_{11}-p_\gamma|\leq(1-t^2)w\kappa_D$.
   The double-replacement check is included in this constant; see the
   [global-noise theorem](../global-noise.md).
2. Known post-output unitary errors can be absorbed into the tester, and
   leave the full replacement channel unchanged. Compare any fixed
   post-output Pauli pair and the ideal pair to their common
   double-replacement reference. The triangle inequality gives
   $|p_{PQ}-p_{II}|\leq2w\kappa_D=3w/D$.
   Averaging the nonidentity Pauli-pair distribution supplies the
   homogeneous acceptance term in the [local-noise converse](local-converse.md).

The estimate uses a common full Haar frame and ordinary two-slot channel
access. Finite-design substitution and longer expected-query protocols
are handled by their separate moment-transfer and stopping arguments;
they are not extra conclusions of this four-port lemma.
