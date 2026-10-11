# Finite-Kraus universal NS kernels admit separate local feature spaces

This is an exact reduction for finite-Kraus universal completions.
It neither bounds the optimal Kraus rank nor asserts attainment. In particular,
it does not reduce an arbitrary infinite positive cross-kernel to a finite one.

<a id="p2-r10"></a>

## Statement

Let A and B each be the universal two-reflection algebra. For each output
setting pair (x,y), suppose a universal CP completion has finitely many Kraus
functions K_xy,r(R,S). They preserve the Jordan sectors (as do word, continuous
functional-calculus, and uniformly defined rational Kraus functions). Assume
its CP maps are NS in every finite representation, including direct sums and
all scalar endpoint characters. Keep all coherent angle pairs in that claim.

Fix ONE scalar character chi_B of B, for example S0=S1=+1, and define

    E_x = span over C { K_xy,r(R,chi_B) : y,r }.

Similarly, at one scalar Alice character chi_A define

    F_y = span over C { K_xy,r(chi_A,S) : x,r }.

Then each Kraus function belongs EXACTLY to the algebraic tensor product

    K_xy,r in E_x tensor F_y.                                      (1)

Consequently, the original completion has a positive finite Gram description
in separate local features selected from these endpoint slices. In particular

    dim E_x <= sum_y r_xy,     dim F_y <= sum_x r_xy.                (2)

The bounds depend on the Kraus counts. They are not uniform dimension or angle
cutoffs, and must not be substituted for one in a Smith/Caratheodory argument.
The chosen scalar character can be any endpoint at which the universally
specified functions are defined; a uniformly invertible denominator is defined
at every one of them.

## Proof

For any finite set of Alice representations, take their direct sum, retaining
all cross-angle Choi entries. On Bob, take a direct sum of an arbitrary test
representation and chi_B. Universal NS on that direct sum says that the Alice
marginal Choi kernel is the SAME on every diagonal Bob input sector, and is
independent of which Bob input unit vector is selected.

At the scalar sector it has the finite positive-kernel factorization

    A_x(R,R') = sum_y,r |K_xy,r(R,chi_B)>><<K_xy,r(R',chi_B)|.         (3)

At an arbitrary Bob representation S and a fixed input vector beta, exactly
the same kernel factors as

    A_x(R,R') = sum_y,r,eta |K_xy,r(R,S)_(eta,beta)> >
                              < <K_xy,r(R',S)_(eta,beta)|,          (4)

where eta ranges over a Bob output basis and the slices are Alice operators.
There are no omitted output flags; y is summed in both formulas.

For two factorizations of the same positive kernel, every feature in either
factorization belongs to the linear span of the features in any finite minimal
factorization. One elementary proof is to choose enough evaluation functionals
to separate a basis of the features in (3). Any evaluation combination which
annihilates those features has zero quadratic form in the kernel, and hence
annihilates EVERY feature in (4). This gives one constant-coefficient linear
combination valid at all further evaluation points. Applying the argument to
arbitrary finite direct sums establishes the global identity.

Thus every Bob matrix slice of K_xy,r lies in E_x. Exchange the parties to show
that every Alice matrix slice lies in F_y. For finite-dimensional function
spaces E,F, the intersection

    (E tensor all B-functions) intersection (all A-functions tensor F)
       = E tensor F

is exact: choose evaluation functionals dual to a basis of E, expand in that
basis, and apply the second inclusion to each coefficient. This proves (1).
Expanding each original Kraus function in product bases gives its coefficient
vector. The sum of their outer products is the required PSD Gram. The CP map,
winning domination, NS, and scale are unchanged.

## Consequence for a proposed joint rational denominator

Parameterize the interior reflections by rational tangent variables z,w. If
finitely many Kraus functions have rational entries with a common safe joint
denominator Q(z,w), the endpoint slices above are rational local functions.
Equation (1) supplies a representation with a denominator q_A(z) q_B(w), where
q_A and q_B can be chosen as common denominators of those endpoint slices.
Equality on the real open parameter rectangle is a rational identity.

Therefore a genuinely mixed irreducible denominator factor cannot remain in
a reduced rational expression for any Kraus entry of such a universal NS
completion. It cancels algebraically. A new finite-Kraus ansatz based only on a
nonseparable central denominator does not evade separate local rational feature
spaces. This rules out one proposed shortcut before numerical optimization.

This statement does not restrict the analytic denominator degree, the number
of local features, or the Kraus rank. Positive infinite-Kraus cross-resolvents
are outside its finite-rank hypothesis. Coherent matrix-valued local rational
features remain available, as do rigorously controlled infinite positive kernels.
