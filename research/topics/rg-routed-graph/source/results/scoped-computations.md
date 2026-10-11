# Scoped computations

[Topic index](../../README.md) · [Shared result index](../../../../RESULTS.md#rg--exact-native-routed-graph-universality)

Each result below has one owner. Exact scope and proof are updated here. Source-level mathematical arguments and finite certificates are distinguished from a new formal verification.

<a id="rg-067"></a>

## RG-067 — Serial endpoints on both phase circles

**Statement.** Exact coefficient/Gram calculations classify first and last serial supports over both specified unit-circle families.

**Status:** computed; independent audit pending. **Scope:** Computed result; independent mathematical audit remains pending. Discrete phase endpoints are specializations.

### Theorem

Let \(C_4,C_5\) be the independently audited phase-projector coefficient
tensors, \(J_r=C_r(I)\), and, for \(|z|=1\), put

\[
 K_{r,z}=I+(z-1)J_r,\qquad
 H_{r,z}(U)=[F(U)+(z-1)C_r(U)]K_{r,z}^{*}.
\]

Every \(H_{r,z}\) is normalized and complete. Its exact maximal reducing
first-query carriers are:

\[
\begin{aligned}
r=4,\ z\ne1:\quad &K_{4,z}(E_1,S_2,S_3,S_4)K_{4,z}^{*},
    &&\text{ranks }(2,4,2,2),\\
r=4,\ z=1:\quad &(S_1,S_2,S_3,S_4),
    &&\text{ranks }(4,4,2,2),\\
r=5,\ |z|=1:\quad &K_{5,z}(S_1,S_2,S_3,S_4)K_{5,z}^{*},
    &&\text{ranks }(4,4,2,2).
\end{aligned}
\]

The tuple notation denotes componentwise conjugation. All first carriers in
each tuple are mutually orthogonal. The corresponding total dimensions are
10, 12, and 12.

**All four maximal last-query carriers are zero for every phase in both
families.** There is no special unit-circle phase with a last endpoint or with
a full first endpoint. In the rank-four family, the identity phase is the sole
first-support rank-jump point.

The established QC-QC first/last-cover necessity therefore excludes QC-QC,
including ordinary fixed query order, for every restriction in both circles.
This is a statement about these complete four-query restrictions. It neither
constructs nor excludes a routed weak-loop host for either complete auxiliary
family, and does not address arbitrary joint extensions of the two records.

### 1. Coefficients and exact Gram matrices

Use the same actual-single defect definitions as in
[RG-067: Serial endpoints on both phase circles](scoped-computations.md#rg-067). All 256 matrix-unit tuples are retained. Let
\(T_{o,a,p}\) denote the integer coefficient \(4F_{o,a,p}\), and let
\(m_r(o,a)\in\{0,1\}\) be the audited laboratory-input/output mask for
\(C_r\). The identity projection is diagonal, with entries
\(j_r(p)=m_r(p,p)\). Thus the new integer Laurent coefficient is exactly

\[
  4H_{r,z;o,a,p}=T_{o,a,p}\,z^{m_r(o,a)-j_r(p)}.       \tag{1}
\]

Its Laurent degree is one in either direction. Identity specialization gives
the actual new singles and the actual omitted-query processes. Their first
and last defect coefficients have exponents between \(-2\) and \(2\).

For a defect coefficient \(16D_\ell(z)=\sum_e d_{\ell,e}z^e\), the last Gram
is computed as

\[
 G^{\mathrm{last}}(z)
   =\sum_{\ell,e,f}d_{\ell,e}d_{\ell,f}^{T}z^{e-f}.
\]

On \(|z|=1\) this equals \(256\sum_\ell D_\ell(z)D_\ell(z)^*\). The first
Gram instead uses \(d_{\ell,e}^{T}d_{\ell,f}z^{f-e}\). The coefficient
matrices are real integers, and reciprocity of the Gram coefficients is
checked. An a priori bound keeps every intermediate integer below \(2^{63}\).

### 2. Last supports: exact exclusion of every unit-circle zero

The last Grams split into fixed coordinate blocks of size at most five. Their
exact determinants are Laurent polynomials. With

\[
 t=z+z^{-1}\in[-2,2],
\]

every determinant becomes a real polynomial in \(t\). Apart from the following
two query/family combinations, every block determinant is a positive constant.

#### Rank-four family, query 2

The nonconstant scalar-block determinants are

\[
 -128(5t-18),\qquad -128(7t-22).
\]

Each of the two five-dimensional blocks has determinant

\[
 2^{33}(5t-18)(7t-22)^2(35t^2+452t-2836).             \tag{2}
\]

On \([-2,2]\), the first two linear factors are at most \(-8\). The quadratic
has positive derivative \(70t+452\), so its maximum on the interval is
\(-1792\), attained at \(t=2\). Consequently (2) and every scalar-block
determinant are strictly positive.

#### Rank-five family, query 4

The nonconstant scalar-block determinants are

\[
 -512(t-4),\qquad -1024(t-3),
\]

and the two two-dimensional blocks have determinant

\[
 -262144(9t-46).
\]

All are strictly positive on \([-2,2]\).

This proves that every last Gram is nonsingular throughout its phase circle.
As a separate exact machine certificate, the script converts each block
determinant to a polynomial in \(t\), checks positive endpoint values, and
uses rational Sturm root counting to verify that it has no root on
\([-2,2]\). No numerical root locations or numerical rank thresholds are used.

### 3. First supports: matching lower and upper bounds

For each candidate carrier \(Q(z)\) in the theorem, the checker expands
\(12Q(z)\) as an integer Laurent matrix and verifies exactly

\[
  G^{\mathrm{first}}(z)Q(z)=0,
  \qquad [Q(z),\alpha_{i,z}(e_{ab})]=0
\]

coefficientwise. On the unit circle, positivity of the first Gram converts
the first equality into simultaneous annihilation by **every** first-defect
coefficient. The candidate is an orthogonal projection because it is a
unitary conjugate of the known origin carrier. These are complete, reducing
lower carriers at all private dimensions.

For an exact upper bound the checker takes a principal minor of the first
Gram of size \(16-\operatorname{rank}Q(z)\). Pivot indices are selected once
from the exact \(z=-1\) Gram, then its symbolic determinant is computed for
arbitrary \(z\). After conversion to \(t\), rational Sturm counting verifies
no zeros anywhere on \([-2,2]\), with exactly one exception:

- Rank-four family, query 1: the principal minor is a positive constant times
  \((t-2)^2(15t-308)(961t-113678)\)
- Its only unit-circle zero is \(t=2\), equivalently \(z=1\)
- At \(z=1\), the original exact matrix-unit calculation gives first rank4

All other first-minor determinants are nonzero on the full interval. The
complete polynomials, coordinate indices, endpoint values, and exact root
counts are recorded in [phase_endpoint_circle_first_checks.json](../phase_endpoint_circle_first_checks.json). Matching
upper and lower dimensions establishes maximality of every carrier in the
theorem. Reduction imposes no further loss because it is verified on each
maximal candidate.

### 4. Reproduction and scope

Run, in this live research directory:

```
python phase_endpoint_exact.py
python phase_endpoint_circle.py
python phase_endpoint_circle_first.py
```

All three finish with `PASS`. Corresponding `_checks.json` files contain the
exact certificates; `.log` files contain execution summaries. The two circle
scripts reconstruct all defect coefficients from (1), rather than extrapolate
from the plus/minus data.

This closes the phase-endpoint construction lead for these two individual
circles. The task's native-interface and independent-private-ancilla conditions
are retained throughout. No claim is made about graph deletion, repeated
multiplicity classification, an arbitrary simultaneous auxiliary extension,
or the original universal routed-host problem.

### Discrete exact carriers and coefficient certificate

### Exact carriers

Let \(S_1,S_2,S_3=E_3,S_4=E_4\) be the previously audited canonical first
carriers of \(F\). The full new first-carrier tuples are

\[
  (S_{1,4},S_{2,4},S_{3,4},S_{4,4})
      =K_4(E_1,S_2,S_3,S_4)K_4,
\]
\[
  (S_{1,5},S_{2,5},S_{3,5},S_{4,5})
      =K_5(S_1,S_2,S_3,S_4)K_5.
\]

The first notation means componentwise conjugation, not conjugation of a
direct-sum matrix. In the standard binary basis,

\[
 J_4=\sum_{n\in\{0,2,8,9\}}|n\rangle\langle n|,
 \qquad
 J_5=\sum_{n\in\{0,4,6,8,12\}}|n\rangle\langle n|.
\]

In particular \(S_{1,4}=I_1\otimes|0\rangle\langle0|_2\otimes
|\Phi^-\rangle\langle\Phi^-|_{34}\). Other new carriers need not be cylinders
on their original physical query factor. The relevant condition is reduction
of the **actual new single** \(\alpha_{i,r}\), which is checked exactly.

### Definition and exhaustive coefficient certificate

For any one of the three normalized processes \(H\), define

\[
 \alpha_i(x)=H(I,\ldots,x,\ldots,I),\qquad
 B_i(x_{\bar i})=H(I_i,x_{\bar i}).
\]

The full first and last multilinear defects are respectively

\[
 D_i^{\rm first}(x)=H(x)-B_i(x_{\bar i})\alpha_i(x_i),
 \qquad
 D_i^{\rm last}(x)=H(x)-\alpha_i(x_i)B_i(x_{\bar i}).
\]

First supports obey \(D_i^{\rm first}Q=0\), last
supports obey \(QD_i^{\rm last}=0\), and in both cases \(Q\) must commute with
\(\alpha_i(M_2)\).

The checker uses all \(4^4=256\) tuples of the standard matrix units
\(e_{00},e_{01},e_{10},e_{11}\). This is a complex-linear basis of the full
four-query input space. For each tuple \(\ell\), the entries of \(4H_\ell\),
\(4\alpha_i(e_{ab})\), and \(4B_{i,\ell_{\bar i}}\) are integers. The
integer defect coefficient is computed as

\[
  16D^{\rm first}_{i,\ell}
       =4(4H_\ell)-(4B_{i,\ell_{\bar i}})(4\alpha_i(e_{ab})),
\]

with reversed multiplication for the last defect. Thus both products use the
new process's actual single and actual identity specialization, not the
original quartet singles.

The exact positive semidefinite Gram matrices are

\[
 G_i^{\rm first}=\sum_\ell (16D_{i,\ell}^{\rm first})^*
                                      (16D_{i,\ell}^{\rm first}),
 \quad
 G_i^{\rm last}=\sum_\ell (16D_{i,\ell}^{\rm last})
                                      (16D_{i,\ell}^{\rm last})^*.
\]

Their rational nullspaces give the exact common right/left defect kernels.
To enforce reduction, the code separately computes the nullspace of

\[
  G_{i,\mathrm{red}}=\sum_{a,b}
       \alpha_i(e_{ab})^* G_i\alpha_i(e_{ab}).
\]

This is the largest \(\alpha_i(M_2)\)-invariant subspace within \(\ker G_i\):
membership says every \(\alpha_i(e_{ab})v\) lies in the raw kernel; closure
under multiplication makes that space invariant, and closure under adjoints
makes it reducing. The checker verifies the matrix-unit multiplication and
adjoint laws of every actual \(\alpha_i\), then independently verifies all
256 defect-annihilation identities and all four commutators on the resulting
projection.

Integer arithmetic has a verified bound below \(2^{63}\). All nullspaces,
projectors, ranks, carrier identities, and commutators are then computed over
the rationals. No floating-point rank test or finite unitary sampling enters.

Because each defect is multilinear and each original query occurs once on
each side, coefficient equality also amplifies under arbitrary independent
private ancillas. Conversely, matrix units span the full input space, so the
common coefficient kernels are maximal, not only positive lower bounds.
