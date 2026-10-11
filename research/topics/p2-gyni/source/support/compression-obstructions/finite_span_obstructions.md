# Finite-span compression: exact obstructions, not a nonattainment theorem

The question is whether the three-dimensional reflection
operator system, two-dimensional irreducible fibers, and finite winning-Kraus
span force a uniform finite-angle cutoff for GYNI. They do not justify the
proposed generic CP/matrix-convex compression. The obstructions below are
exact. They neither prove that GYNI is unattained nor exclude an
objective-specific finite-dimensional optimizer.

<a id="p2-r22"></a>

## 1. Fixing just the two reflections already fixes their generated algebra

Choose K distinct interior angles alpha_j in (0,pi), and put

    R0=direct_sum_j Z,
    R1=direct_sum_j [cos(alpha_j) Z+sin(alpha_j) X],
    S_K=span{I,R0,R1}.

The system S_K has complex dimension three. Nevertheless

    C*(R0,R1)=direct_sum_(j=1)^K M_2.                    (1)

Indeed C=(R0R1+R1R0)/2 has the distinct eigenvalues cos(alpha_j), so polynomial
functional calculus in C gives every central sector projection. In each
sector, Z and the nonparallel second reflection generate M_2.

Suppose a proposed exact compression supplies UCP maps

    Phi:S_K -> M_d,
    Psi:M_d -> M_(2K),
    Psi(Phi(Ri))=Ri, i=0,1.

Write Xi=Phi(Ri). Positivity and unitality imply Xi=Xi* and -I<=Xi<=I.
Kadison-Schwarz for Psi gives

    I=Psi(Xi)^2 <= Psi(Xi^2) <= Psi(I)=I.

Thus equality holds. Each Xi lies in the multiplicative domain of Psi, so Psi
restricts to a *-homomorphism on C*(I,X0,X1), with image exactly the algebra
in (1). A C*-subalgebra of M_d surjecting onto K distinct M_2 summands must have
at least K source M_2 summands. Its faithful representation therefore needs

    d>=2K.                                              (2)

Consequently there is NO matrix-size bound depending only on dim S_K=3 for
such exact UCP factorizations.

The same conclusion holds for a unital complete-order embedding of S_K into
M_d: its inverse on the image has a UCP extension to M_d by Arveson's extension
theorem, reducing to the preceding argument. Thus even three-dimensional,
2-subhomogeneous reflection systems can require arbitrarily large exact
complete-order matrix realizations.

The multiplicative-domain fact used here is stated in Theorem8 of
[Choi–Johnston–Kribs](https://arxiv.org/pdf/0811.0947); the extension theorem is
[Arveson's original 1969 announcement](https://www.isibang.ac.in/~soumyashant/misc/collected-works-of-arveson/1960s/1969_On_subalgebras_of_Cstar_algebras.pdf).
The displayed inequalities contain the application-specific proof.

This obstruction applies to an exact local retraction fixing the operator
system pointwise. A transformation allowed to change both the reflections
and the process while preserving only the GYNI value is outside its scope.

## 2. Every distinct angle is exposed already at matrix level two

This gives an explicit matrix-convex obstruction without invoking envelope
terminology. Denote by A(alpha)=cos(alpha)Z+sin(alpha)X the second reflection.
For a target angle alpha define the 4 by 4 matrix pencil evaluated at beta:

    L_alpha(beta)=Z tensor Z+A(alpha) tensor A(beta).

Direct multiplication gives its spectral norm:

    ||L_alpha(beta)||=2 cos(|alpha-beta|/2),
                      alpha,beta in [0,pi].              (3)

For example, L^2 has eigenvalues 2+2cos(alpha-beta) and
2+2cos(alpha+beta), with the former no smaller on this interval. The spectrum
of L consists of the corresponding positive and negative square roots.
At beta=alpha, the maximally entangled vector (|00>+|11>)/sqrt(2) has eigenvalue2.

Given a finite list of angles excluding alpha, put

    g=1-max_j cos(alpha-alpha_j)>0,
    t=2-g/2.

Then t^2>4-2g, so the level-two pencil

    P=t I_2 tensor I-Z tensor R0-A(alpha) tensor R1       (4)

is strictly positive on every listed angle but has a negative expectation at
alpha, namely t-2=-g/2. Therefore omitting any distinct angle changes the
level-two positive cone. The four scalar corner states or a fixed finite
angle list cannot recover all matrix-order information.

There is an equivalent direct UCP-intertwiner proof. If reflections at alpha
were a matrix-convex combination of reflections at beta_j,

    R_x(alpha)=sum_j V_j* R_x(beta_j)V_j,
    sum_j V_j*V_j=I,

then

    sum_j [R_x(beta_j)V_j-V_jR_x(alpha)]*
          [R_x(beta_j)V_j-V_jR_x(alpha)]=0.

Every summand is positive, so each V_j intertwines both reflections. It also
intertwines their central anticommutators. Consequently

    [cos(beta_j)-cos(alpha)] V_j=0.

At least one V_j is nonzero; its angle must equal alpha. This applies to
arbitrary rectangular compression matrices and includes multiplicities.

Equations (3)-(4) concern preservation of an operator system, not the
existence of a special finite-angle maximizer of one chosen GYNI functional.
Matrix Caratheodory theorems require the matrix level of the represented point
to be fixed before counting support. They do not replace an unbounded process
matrix level by the vector-space dimension three.

<a id="p2-r23"></a>

## 3. Coherent Choi kernels restore arbitrarily large matrix corners

The original reflection algebra has irreducible fibers of dimension at most
two. The algebra relevant to the reduced process constraints and winning Choi
kernels does NOT inherit that bound.

In one fixed output-setting block, the local reduced Choi space is

    S=direct_sum_(j=1)^K(C^2_input tensor C^2_output).

Let D_j be its j-th sector projection. These projections are among the
normalization observables: T* applied to input identity on sector j gives D_j
in each setting flag. Work with that replicated version when both flags are
retained.

For setting0 and outcome0, P_(0|0)=direct_sum_j |0><0|, so its flagged Choi
operator is

    Q=|p><p|,
    p=sum_j e_j,
    e_j=|setting0> tensor |j,input0,output0>.

Each e_j is a unit vector. Keeping the setting flags explicitly does not
change the following identities:

    D_j Q D_k=|e_j><e_k|=:E_jk,
    E_jk E_lm=delta_kl E_jm,
    E_jk*=E_kj.                                         (5)

Thus the algebra jointly generated by the normalization observables D_j and
ONE winning Choi operator Q contains a full M_K corner. Its matrix levels are
unbounded as K grows, although Q has rank one and its Kraus operator belongs
to span{I,R0}. No rank or dimension estimate based solely on the winning span
removes this corner.

A normalized variant p=Q/K is a projection. If a UCP retraction preserves all
D_j and p, the same multiplicative-domain argument as in Section1 forces it
to preserve the entire M_K corner. Its compressed matrix dimension is at
least K. This makes the process-specific obstruction independent of the
reflection-algebra envelope argument.

The existence of this corner does NOT say that an optimal process must use
all of it. In fact the multiplicity-removal construction shows that
some large presentations are redundant. It says that uniform subhomogeneity
of the reflection algebra cannot be transferred to the full coherent Choi
normalization problem as an automatic compression theorem.

## 4. Where the Smith/Caratheodory shortcut fails

Smith's norm-stabilization lemma concerns a map whose range is a FIXED M_d:
its cb norm is determined at amplification d. It does not set d equal to the
number of operators spanning its domain. See
[Smith's original paper](https://doi.org/10.1112/jlms/s2-27.1.157), or the explicit
finite-matrix statement in Section2 of
[Johnston–Kribs–Paulsen](https://www.rintonpress.com/xxqic9/qic-9-12/0016-0035.pdf).

A positive reduced process Z can be read as a Choi matrix for a CP map between
local Choi matrix algebras of size4K (with setting blocks retained). Its range
level grows with K. Section3 shows concretely why the 2 by 2 irreducible
reflection fibers cannot simply replace that range by M_2. Restricting the
winning data to a few Kraus vectors does not by itself construct a positive,
normalization-preserving map into a fixed matrix range.

Likewise scalar Caratheodory applies only after an appropriate fixed
finite-dimensional convex representation has actually been proved. Coherent
angle kernels carry off-diagonal angle pairs and matrix-valued constraints;
they are not automatically ordinary probability measures on angles.

## 5. Precise remaining objective-specific question

A useful positive theorem would have to show that SOME GYNI-maximizing reduced
process can be replaced at equal score by one supported on at most a universal
number of angle sectors, while preserving positivity and every reduced
normalization equation. It must be allowed to alter the reflections/process
jointly; universal pointwise UCP retraction is too strong by Sections1-3.

No such objective-specific compression or finite cutoff is proved here.
Conversely none of the obstructions shows that the GYNI supremum fails to be
attained. They close the generic finite-winning-span/2-subhomogeneity shortcut
and identify the actual missing fixed matrix level.

## Verification

`check_obstructions.py` uses rational angle parameters and exact rational
arithmetic to verify the level-two separating pencils, including their
negative target expectation and strict positivity on all other listed
angles. It also checks the matrix-unit identities (5) exactly in the flagged
Choi space. These checks accompany the formulas above; no SDP solver is used.
