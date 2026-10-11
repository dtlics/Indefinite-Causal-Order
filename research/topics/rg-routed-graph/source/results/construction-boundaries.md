# Construction boundaries

[Topic index](../../README.md) · [Shared result index](../../../../RESULTS.md#rg--exact-native-routed-graph-universality)

Each result below has one owner. Exact scope and proof are updated here. Source-level mathematical arguments and finite certificates are distinguished from a new formal verification.

<a id="rg-022"></a>

## RG-022 — Whole-SCC coherent-boundary counterexample

**Statement.** An explicit valid routed host has a whole-SCC fragment whose host-occurring coherent-boundary prescription fails the claimed product-domain unitarity.

**Status:** scoped negative result. **Scope:** Refutes the local cap/fragment shortcut; does not refute the stronger global conditional fragment theorem.

### Results

1. **PASS:** the candidate fragment theorem is correct under its stated exact forward and reverse product-domain hypotheses and its independently checked internal weak-loop condition.
2. **New exact counterexample:** those exact domains, when defined using boundary tuples occurring in the host, do not automatically inherit even when the selected strongly connected branch component contains every branch of each of its vertices.
3. **Scope is essential:** the counterexample does not have *every* host vertex contained in one SCC. Its deterministic hub is split among singleton SCCs. Consequently it does not resolve the stronger globally whole-vertex hypothesis of the collapse theorem.
4. Neither result proves or refutes unrestricted routed-graph universality.

### 1. Primary-source audit of the conditional theorem

I checked the definitions against [Vanrietvelde et al., arXiv:2206.10042v3](https://arxiv.org/html/2206.10042v3), Definitions 3.2–3.7 and B.3–B.4, and Theorem 3.1. The paper's choice relation uses all branch choices, including unused coordinates. A branched route permits a single branch whose output index set is an arbitrary set of tuples. The output need not be a Cartesian product of individual wire index sets. Solid edges are tested against all consistent sections, and reverse dependence has the orientation used in the candidate. The superunitary conclusion includes separate local ancillary systems.

The proposed encoder and decoder therefore are actual native routed vertices. The encoder's output-choice coordinate is precisely one complete correlated input tuple. Its input-choice coordinate is singleton. The decoder is dual. Their statuses are constant. In the capped branch graph, the encoder has no incoming edge of any type and the decoder has no outgoing edge of any type. Hence caps cannot generate a cycle.

At fixed encoder choice, internal green dependence is exactly the stated fixed-boundary dependence; fixing the reverse decoder choice gives the red statement. Both exact-domain premises ensure that every fragment section is accepted by both caps and every choice assignment extends uniquely. Thus the cap construction preserves precisely the section set used for internal solid edges. The primary theorem applies directly, after which fixing the cap unitaries gives the claimed fragment map. Boundary dimension equality follows from unitarity.

Independent ancillas at different native vertices follow directly. If the intended statement allows a different private ancilla for every *branch* of one vertex, use the tensor product of those ancillas at that vertex; in branch b, act on its ancilla and apply identities to the remaining branch ancillas. This embeds the claimed branchwise family into the primary vertex-ancilla family without merging independent fillers into a joint arbitrary operation.

No correction to the theorem is required. The statement would become false if its two exact-domain premises were silently replaced by host reachability.

### 2. Exact host: four controlled input relabellings

All internal sector dimensions below are one. Let

\[
O=\{0,1\}^3,\qquad
w(a,b,c)=((1-b)c,(1-c)a,(1-a)b),
\]

and let the selector labels be \(s=0,1,2,3\), with

\[
t_0=000,\quad t_1=100,\quad t_2=010,\quad t_3=001,
\qquad x(s,o)=w(o)\mathbin\oplus t_s.
\]

Vertices are S, A, B, C, X, D. There is one external four-dimensional input at S, an external qubit input at each laboratory A, B, C, and one external 32-dimensional output at D. Every external index set is singleton.

Internal wires:

- S→X: selector index s in {0,1,2,3}
- X→A_i: index x_i in {0,1}
- A_i→X: index (x_i,o_i) in {0,1}²
- X→D: index (s,o) in {0,1,2,3}×{0,1}³

The branched native routes are:

- S has one branch, from its singleton input index to its four possible output indices s. Its full filler is U(4)
- Each laboratory A_i has branches A_i^0 and A_i^1. Branch A_i^x takes input index x and permits exactly the two output indices (x,0),(x,1). Including its external qubit, each branch has full U(2) freedom
- X has one branch X^{s,o} for each of the 32 pairs (s,o). Its input tuple is \((s,((x_i(s,o),o_i))_i)\), and its output tuple is \(((x_i(s,o))_i,(s,o))\). Every hub branch is singleton-to-singleton and has full U(1) freedom
- D has one branch accepting all 32 indices (s,o) and producing its singleton output index. Its full filler is U(32)

All routes are literally disjoint unions of rectangles. All native branches are nonzero and dimension-balanced. Every listed branch occurs in some consistent section. The global past and future both have dimension 32.

#### 2.1 Forward and reverse totality

The forward choices are s and six bits \(f_i(0),f_i(1)\). The section equations are

\[
x=w(o)\oplus t_s,\qquad o_i=f_i(x_i).
\]

For each fixed s, putting \(g_i(z)=f_i(z\oplus t_{s,i})\) reduces these to the ordinary Lugano fixed-point equations \(o_i=g_i(w_i(o))\). They have one solution for every tuple of local functions. Equivalently, this finite claim is verified by all 256 complete forward assignments in the attached exact checker. All wire indices are then fixed.

In reverse, only D has a nontrivial choice: it selects any (s,o). That fixes every hub and laboratory index and every branch status uniquely. There are exactly 32 reverse assignments and 32 consistent sections.

#### 2.2 Exact branch-graph certificate

There are no solid internal edges. For S→X, the hub branch fixes s. For either wire between X and A_i, the hub branch and laboratory branch fix its entire index tuple. For X→D, the hub branch fixes (s,o). All these fixed sectors are one-dimensional.

Every green edge has S or a laboratory branch as source, since no hub or D branch has a nontrivial outgoing choice. D's status is constant, so no green edge enters D. Every red edge points to D, since D supplies the only nontrivial reverse choice. Hence every closed walk is wholly green and confined to laboratory branches.

In fact every laboratory branch has green edges to both branches of each other laboratory. To see the edges from A_i^a, choose a selector with \(t_{s,i}=a\); the corresponding input symbol is the losing symbol of the unrelabelled Lugano function. Changing that branch's outgoing vote, while fixing suitable constant response functions at the other two laboratories, changes whether either other laboratory wins. Thus it changes both statuses at that other laboratory. The same argument applies to each pair by cyclic symmetry. There are no same-vertex green edges.

Therefore

\[
\mathcal C=\{A^0,A^1,B^0,B^1,C^0,C^1\}
\]

is one strongly connected component. It contains *all* branches of the three laboratory vertices. All remaining components are singletons. The exact checker finds 158 green edges, 38 red edges, no solid edges, and SCC sizes \(6,1,\ldots,1\), with 34 singleton components.

This is a valid routed graph, with the complete native filler family intact.

### 3. Failure of the host-occurring coherent boundary prescription

Open the three laboratory vertices as the fragment \(\Gamma_{\mathcal C}\). Their scalar incoming interface indices form x. Their scalar outgoing interface indices form ((x_i,o_i))_i, which can be identified with the pair (x,o). The three external incoming qubits remain part of the fragment input.

The host-occurring input set is

\[
R_{\mathrm{in}}^{\mathrm{host}}
=\bigcup_s\bigl(w(O)\oplus t_s\bigr)
=\{0,1\}^3\setminus\{111\},
\]

because \(w(O)=\{000,100,010,001\}\). Its host-occurring output set is

\[
R_{\mathrm{out}}^{\mathrm{host}}
=\{(w(o)\oplus t_s,o):s\in\{0,1,2,3\},\ o\in O\},
\]

which has exactly 32 elements.

But the opened fragment consists of three separated rectangular native vertices. It has exactly one section for **every** x in {0,1}³ and **every** complete six-bit forward choice tuple, with

\[
o_i=f_i(x_i).
\]

Thus its forward domain has 8×64=512 pairs, rather than \(R_{\mathrm{in}}^{\mathrm{host}}\times\{0,1\}^6\), which would have 448 pairs. The input 111 with all forward choices zero is an explicit forbidden-extra section. Similarly its reverse domain allows all 64 pairs (x,o), not just the 32 host-occurring outputs. Neither exact-domain premise holds with the host-occurring sets.

There is also a failure that cannot be repaired merely by dropping the “no sections outside” clause. Take the host-reachable input x=110 and choose all six forward bits zero. The open fragment has the unique output o=000. Yet (110,000) is absent from \(R_{\mathrm{out}}^{\mathrm{host}}\), since w(000)=000 and no selector shift equals 110. The coherent decoder proposed from the host output set rejects this section. Consequently the capped graph is not forward total even on the proposed input set.

A useful dimension check makes the obstruction especially transparent. The proposed coherent fragment input has dimension 7×2³=56, while the proposed coherent output has dimension 32. There can be no unitary between these spaces. The opened fragment itself is perfectly unitary on its actual practical spaces: input dimension 8×2³=64 and output dimension 64.

The internal dependence graph also changes on opening: at fixed x, all laboratory statuses are fixed, so the opened fragment has no internal green edges. In the host, the same six branches form the recurrent green component above. Whole-vertex closure of the *selected* component therefore does not preserve the internal branch graph either.

One can designate only A as an original unknown location and fix every B and C branch filler. The graph still has the same native certificate, so the failure is not cured by imposing at most one original query inside the selected component. This does not claim that the resulting one-query process lacks an ordinary comb realization.

### Stronger global hypothesis

The graph's X vertex has 32 branches in 32 distinct singleton SCCs. Hence it violates the requirement that **every vertex of the entire host** be contained in one component. S and D satisfy that requirement; the three laboratories satisfy it; X does not.

Accordingly this counterexample settles only the local implication:

> selected SCC contains whole vertices ⇒ its host-occurring boundary sets have the fragment theorem's exact product domains

That implication is false. The analogous claim with global whole-vertex closure remains open here. No conclusion about global coherent-DAG composition follows either way.



### 5. Reproduction and finite exploratory check

Run:

```
python /workspace/shared/conjectures/routed_graph_new/verify_fragment_counterexample.py
```

It checks complete forward and reverse assignments, all conditional wire-value sets entering the solid-edge criterion, all functional-dependence edges, SCCs, host and opened boundary sets, and both explicit mismatch witnesses. Output: [fragment_counterexample_checks.json](../fragment_counterexample_checks.json).

A separate exact census, `check_whole_scc.py`, reuses the existing binary three-party process-function enumerator and checks the laboratory SCCs of every valid generic hub graph. Among all 744 functions there are 488 with no recurrent laboratory SCC, 192 with a 2-branch SCC, and 64 with a 3-branch SCC. None has a nontrivial laboratory SCC containing whole vertices. This is a small-alphabet observation only; the four-context construction above shows why it cannot be extrapolated to a general obstruction.

The counterexample construction and its proof are the following proof. Its logical building block is the earlier exact generic hub construction in [RG-068: Classical three-party routes](positive-routes.md#rg-068); the new selector-context union and the boundary-domain mismatch are checked independently here. No novelty claim beyond the current research project is made.

### 6. Subsequent extraction progress

The failed cut-domain inference can be bypassed in some orientations using the published partial-exchange construction:

- [RG-024: Partial endpoint extraction](layer-structure.md#rg-024) proves actual first-use extraction for an earliest green single-query SCC containing the whole query vertex, and last-use extraction for the red latest dual. **Independent audit passed** in [RG-024: Partial endpoint extraction](layer-structure.md#rg-024)
- [RG-023: Lossless coherent-code DAG composition](layer-structure.md#rg-023) proves that already certified code unitaries on a physical DAG compose losslessly whenever the whole contraction is unitary. **Independent audit passed** in the same report
- [RG-024: Partial endpoint extraction](layer-structure.md#rg-024) proves the proper-subset extension for the reachable-reduced graph, giving positive first/last projections and native-rank bounds. **Independent audit passed** in [RG-024: Partial endpoint extraction](layer-structure.md#rg-024) after making reachability explicit
- [RG-025: Green whole-query group extraction](layer-structure.md#rg-025) proposes a genuine complete first-block factorization for a green earliest SCC containing several whole query vertices, with the dual red last-block statement. This would permit a legitimate application of the ≤2-query QC-QC theorem to the extracted block. Independent audit is pending

The green group-extraction result remains a candidate until reviewed. None of these arguments proves the missing red-first/green-last extraction, global whole-vertex collapse, or unrestricted routed universality.





**Reproduction limit:** supporting helpers were not supplied; the analytic argument remains available. See the [artifact map](../REPRODUCIBILITY.md#rg-022).

<a id="rg-045"></a>

## RG-045 — Static-query flags do not imply QC-QC

**Statement.** The actual reversed Lugano host has the proposed static flags but its original restriction is not QC-QC.

**Status:** scoped negative result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### Conclusion

Static, jointly commuting, past-supported native query branch flags do NOT imply QC-QC, last-query coverage, or absence of weak loops. The standard classical Lugano hub, reversed in time, already supplies a counterexample. This is an actual routed host with independent native branch fillers, not a canonical promotion whose routability is unknown.

### Native tensor and explicit route

Let

    w₁(p)=p₂(1−p₃),
    w₂(p)=(1−p₁)p₃,
    w₃(p)=p₁(1−p₂).

This is an orientation/relabeling of the standard binary Lugano process function. It satisfies the usual pairwise witness criterion: for distinct p,p′, some i has p_i≠p′_i and w_i(p)=w_i(p′). Equivalently it has one fixed point under every tuple of local binary functions.

Use the already proved generic classical hub route, and reverse every arrow and every route. Its past is the old output-record register p, its future is the tensor product of the old laboratory-past qubits, and each original laboratory retains two full native M₂ branches, indexed by b=w_i(p). Time reversal preserves bi-univocality and exchanges the two colors of weak loops, so this is a valid routed graph.

For arbitrary independent native matrices U_i^0,U_i^1, its contraction is

    G((U_i^0⊕U_i^1)_i)_{o,p}
      = product_i U_i^{w_i(p)}[o_i,p_i].               (1)

This is a multilinear native tensor on (M₂⊕M₂)^3 with boundary dimension8. Full independent private-ancilla validity follows from the actual reversed routed graph, rather than scalar tests.

### Static flags exactly as proposed

Let

    Π_{i,b}=sum_{p:w_i(p)=b}|p><p|.

For every native input tuple and arbitrary branch scalar z,

    G(...,U_i^0⊕zU_i^1,...)
      =G(...,U_i^0⊕U_i^1,...)[I+(z−1)Π_{i,1}].       (2)

The analogous identity holds for either branch and arbitrary native matrix coefficients. All Π_{i,b} are diagonal past projections and commute across parties. Thus (2) satisfies the strongest full-native fixed-auxiliary static-flag premise, including its complete tensor extensions.

The active projections are exactly

    E₁=I₁ P1₂ P0₃,
    E₂=P0₁ I₂ P1₃,
    E₃=P1₁ P0₂ I₃.

They are pairwise orthogonal, rank2, and leave a rank2 all-passive residual. Thus even static orthogonal active ideals with at most one active native branch per history are compatible with a genuine weak-loop routed host.

### The non-QC-QC original restriction

At native port i use the complete original-query embedding

    U_i^b=Z_i^b U_i.

Equation(1) becomes

    F_raw(U)_{o,p}=(-1)^{sum_i o_i w_i(p)} product_i U_i[o_i,p_i],

or

    F_raw(U)=W+sum_i(Z_i−I)W E_i,   W=U₁⊗U₂⊗U₃.

Normalize by the fixed unitary F_raw(I)* on the right. This is exactly the previously established three-qubit orthogonal-cylinder phase process used in the six-query no-endpoints construction. Its own phases are non-scalar and its cylinders proper/nonzero, so the exact last-row Gram formula gives T_i=0 for every original query. The established QC-QC last-row coverage theorem therefore excludes QC-QC.

The normalization conjugates the past flag projections if necessary; here the diagonal normalizer commutes with all E_i, so their static forms are unchanged.

### Implication for current research

The quartet’s exhaustive partial-promotion classification remains valid and valuable, but static native branch flags alone cannot bridge it to ordinary circuits. A host obstruction must distinguish its entangled serial codes from this routed classical-cylinder example, or exploit a stronger property that the reversed Lugano host fails. No argument may assume a latest red component containing a whole single original query: the recurrent red component here contains multiple original-query branches/vertices, precisely outside that endpoint theorem's hypotheses.

<a id="rg-046"></a>

## RG-046 — Routed process without serial endpoints

**Statement.** A routed six-query process has all first-query column and last-query row projections zero.

**Status:** scoped negative result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### 1. The routed building block

On H=(C2)^tensor3, use the orthogonal cylinders

    E1=I1 P1_2 P0_3,
    E2=P0_1 I2 P1_3,
    E3=P1_1 P0_2 I3.

With local Pauli Z phases, put

    Phi(W)=W+sum_i (Z_i-I)W E_i,
    D0=Phi(I),
    F(y)=Phi(y1 tensor y2 tensor y3)D0.

The retained computational-cylinder construction gives a valid routed
graph for this process on its original eight-dimensional boundary, using
each original query exactly once. See [RG-069: Exact tripartite orthogonal-support routes](positive-routes.md#rg-069)
and [RG-070: Coded-cylinder routes](positive-routes.md#rg-070). Its complete unitarity also follows
directly from orthogonality of the three right-support cylinders.

The exact last-query formula from [RG-016: Canonical last rows](serial-interfaces.md#rg-016)
gives, for every query i,

    L_i(F)=4I+8E_i > 0.

Thus every canonical output-last projection T_i(F) is zero. Moreover,
the coefficient matrices of F span M8: the product matrix units span M8,
Phi is an invertible Hilbert--Schmidt unitary on M8, and multiplication
by D0 is invertible.

Define the reversed process

    Fsharp(x)=F(x1*,x2*,x3*)*.

It is complex multilinear and independently ancillary-complete. Its
canonical first projections satisfy S_i(Fsharp)=T_i(F)=0. Its coefficients
also span M8. Reversing the valid routed graph realizes Fsharp: adjunction
exchanges forward and reverse univocality, reverses the solid arrows, and
exchanges the two dashed colors. A monochromatic weak loop remains weak.
Any fixed boundary normalizer is simply included as a boundary unitary.

### 2. Serial composition with disjoint queries

Use six independently variable original qubit queries and define

    G(x1,x2,x3,y1,y2,y3)=F(y)Fsharp(x).                 (1)

Both factors act on the same H, rather than on two independent boundary
registers. Connecting the unsectorized future boundary of the reversed
graph to the unsectorized past boundary of the forward graph gives a
routed realization of (1). There is no dependency returning from the
second graph to the first; hence no new cycle is created. All native
fillers remain freely variable, and composition preserves independent
complete unitarity. Each of the six original queries is used once.
The input and output boundary dimensions remain eight.

We claim that all twelve canonical endpoint projections vanish:

    S_i(G)=T_i(G)=0,       i=1,...,6.                  (2)

Here S denotes the common right kernel of the first-query defects and
T the common left kernel of the last-query defects. No statement about
individual branches of the realizing graph is inferred from (2).

### 3. Proof of all twelve zero projections

For an x-query, set all y-queries to identity. Any first-query column
of G is then a first-query column of Fsharp, and is therefore zero.
For a y-query, setting all x-queries to identity similarly shows that
any last-query row is a last-query row of F, hence zero.

Consider a y-query i and a hypothetical first projection S. Set the
other y-queries to identity, write alpha_i(a)=F(I,...,a,...,I), and
leave all x-queries variable. The defining first identity becomes

    [alpha_i(a), Fsharp(x)] S=0                       (3)

for every a and x. Since the Fsharp coefficients span M8, (3) holds
with Fsharp(x) replaced by any B in M8. Take a=Z and B=alpha_i(X).
The single map alpha_i is a unital *-homomorphism, so

    [alpha_i(Z),alpha_i(X)]=2 alpha_i(ZX)

is invertible. Equation(3) forces S=0.

Finally, for an x-query i and a hypothetical last projection T, set the
other x-queries to identity and write beta_i(a)=Fsharp(I,...,a,...,I).
The last identity gives

    T [F(y),beta_i(a)]=0.                            (4)

The F coefficients span M8, and choosing a=Z and the linear combination
F(y)=beta_i(X) makes this commutator invertible. Therefore T=0.
This proves (2), coefficientwise and without numerical tolerance.

### 4. Scope and use

The same argument works for any normalized routable process F on a
finite boundary whose coefficients span the entire boundary matrix
algebra, whose original qubit singles are homomorphisms, and whose
last-query projections all vanish. The displayed tripartite process is
an explicit instance.

Thus a future purported graph-wide serial-extraction theorem must cope
with a valid routed process having no nonzero first or last endpoint
column at all. In particular a positive partition supported on either
set of endpoint projections is a useful obstruction to the specified
QC-QC models, but cannot be necessary for arbitrary weak-loop routing.
This endpoint counterexample refutes the stated shortcut. The exact quartet host question is settled by [RG-001](obstruction.md#rg-001).

An exact matrix calculation is supplied separately in
`check_routable_no_serial_ends_round36.py`. It verifies full-rank defect
Grams using explicit context subfamilies; a full-rank subfamily suffices
to prove that the common kernel of all contexts is zero.





**Reproduction limit:** supporting helpers were not supplied; the analytic argument remains available. See the [artifact map](../REPRODUCIBILITY.md#rg-046).

<a id="rg-047"></a>

## RG-047 — Exposing individual table bits is impossible

**Statement.** The specified independently phase-addressable basis-bit coefficient action fails unitarity and cannot occur in any full-filler host.

**Status:** scoped negative result. **Scope:** The exact bit semantics are essential; this does not exclude arbitrary nonorthogonal encodings.

### 1. Fixed tensor and exact flag semantics

Use the retained quartet supports E_i and the safe orthonormal product basis, in this order:

    001−, 10+0, 0001, 11−+, 0100, 0110, 11+0, 11+1,
    0000, 001+, 0101, 0111, 10+1, 10−+, 10−−, 11−−.

Let W send the computational input label p to that normalized product word. Put

\[
V_o=I-2\sum_i o_iE_i,
\qquad
V_oW|p\rangle=\lambda(p,o)\bigotimes_iH^{\beta_i(p,o)}|a_i(p,o)\rangle,
\]

where every local ray lies in {0,1,+,−}, and beta_i is 0 for the Z basis and 1 for the X basis. Let

\[
\widetilde F(\mathbf U)=F_{\rm raw}(\mathbf U)W,
\qquad
(M_i(\mathbf U))_{o,p}=(-1)^{\beta_i(p,o)}\widetilde F(\mathbf U)_{o,p}.
\]

The flag-exposure hypothesis is **exactly** that a phase −1 on one freely phase-addressable routed sector of the proposed host changes its contraction from \(\widetilde F(\mathbf U)\) to \(M_i(\mathbf U)\), for every original query context. The sector can be on an auxiliary wire or auxiliary/native branch. Its location need not be specified. The coefficient-mask identification is part of the hypothesis and cannot be inferred merely from an informal claim that the circuit “knows the basis”.

### 2. Explicit failure of unitarity

Set

\[
U_1=(3I+4iX)/5,\qquad U_2=U_3=U_4=I.
\]

All original queries are unitary. For i=3 and i=4, direct exact computation gives

\[
\|M_i^\dagger M_i-I\|_{\rm HS}^2=2304/625>0.
\]

The Gram-defect entry at input-basis indices (0,14) is respectively

\[
+12\sqrt2\,i/25\quad\text{and}\quad-12\sqrt2\,i/25.
\]

There are exactly eight nonzero Gram-defect entries in each case; the entire list is in [basis_flag_obstruction_checks.json](../basis_flag_obstruction_checks.json). The unmasked \(\widetilde F\) is verified exactly unitary in the same calculation.

For the original normalized quartet, attach the fixed source coordinate change \(W^\dagger D_0\), where \(D_0=F_{\rm raw}(I)\). This right unitary conjugates the Gram defect and leaves its nonzero squared Hilbert–Schmidt norm unchanged. Thus the obstruction is not a choice-of-boundary-coordinate artifact.

### 3. Why this forbids the exposed flag in every valid full-filler host

A sector-diagonal phase on an internal wire is a unitary preserving its sector decomposition. It can be absorbed into the incident full native routed filler, by pre- or post-composition. The practical branch spaces and the route remain unchanged. Likewise a phase on a native branch is one of that branch's permitted full-unitary fillings.

Consequently a valid routed host must remain unitary when this phase is varied, with all original queries fixed to the displayed unitary context. Under the flag-exposure hypothesis its changed contraction is M_i. Section2 says that M_i is not unitary. This contradiction excludes the proposed exposed sector.

The conclusion holds for any auxiliary-node count, any topology, any placement of basis-rotation adapters, and any ancillary dimensions, provided the same coefficient-mask semantics hold. It does **not** rule out a quantum encoding that does not expose beta_i as such an orthogonal, independently phase-addressable sector. It also does not show that every possible realization must expose that bit.

### 4. Provenance and reproduction

[verify_basis_flag_obstruction.py](../verify_basis_flag_obstruction.py) is the small direct certificate. It imports only the Gaussian-rational quartet support matrices from [exact_fixtures.py](../exact_fixtures.py), builds the sixteen normalized product words, constructs the sixteen V_o matrices, identifies the exact local product rays, constructs the masks, and evaluates the two displayed Gram defects. No branch-graph theorem, native-algebra bound, numerical tolerance, or inverse unknown query is used to establish the numerical identities.

Run:

    python verify_basis_flag_obstruction.py

The original exploratory search is `safe_basis_native_phase_failure.py`; it found this same context for both flags. The scalar-hub forward/reverse and weak-loop checker is separately recorded in `safe_basis_scalar_hub_test.py`. Those checks are not needed for the graph-independent phase argument.

One exact positive observation is also recorded: the joint parity beta3 xor beta4 is independent of o in all 256 table entries. It equals one on source words 001−,10+0,11+0,11+1,001+,10+1 and zero on the other ten. Thus an arbitrary phase on the parity is simply a fixed diagonal input unitary and preserves unitarity in every query context. The checker verifies the input-only mask identity, not merely one numerical context. This shows why the individual-flag obstruction must not be broadened to every coarser encoding.





**Reproduction limit:** supporting helpers were not supplied; the analytic argument remains available. See the [artifact map](../REPRODUCIBILITY.md#rg-047).

<a id="rg-048"></a>

## RG-048 — Baseline orthogonality is not structural absence

**Statement.** An actual routed DAG has a jointly reachable branch pattern with zero joint coefficient at one baseline.

**Status:** scoped negative result. **Scope:** Exact hypotheses in the statement and proof; no wider realization claim.

### The failed inference

At the quartet's fixed auxiliary baseline, distinct active original-query
ideals have zero joint coefficients and orthogonal past projections. This
alone does not imply that those native branches never co-occur in a global
route section, nor that their projections remain orthogonal when auxiliary
fillers change. Individual branch-rank constancy does not supply either
conclusion.

### Actual routed DAG

Take boundary dimension eight: a control qubit and two laboratory qubits.
There are source S, auxiliary H, decoder D, and laboratories A and B. S,H,D
have one full M2 native branch each. A and B each have two full M2 branches,
indexed respectively by c,d in {0,1}.

The internal scalar-index wires form

    S --c--> A_c --c--> H --d--> B_d --d--> D.

S encodes the external control qubit into its two one-dimensional c sectors;
D decodes the two d sectors to the output control qubit. H is an arbitrary
full two-by-two matrix from the c sectors to the d sectors. A_c relays c and
acts on its external laboratory input/output qubit; B_d similarly relays d.
These are literal dimension-balanced rectangular native routes.

There are four consistent sections (c,d). The complete forward choices are
S's c and H's d; the complete reverse choices are D's d and H's c. All four
assignments in either direction give unique sections. Each co-occurring
endpoint-branch pair fixes its intervening one-dimensional scalar sector,
so there are no solid internal edges. Green edges are S→A_c and H→B_d;
red edges are A_c→H and B_d→D. The branch graph is acyclic.

Every native branch retains its independent full filler freedom. Its exact
contraction is the ordinary controlled-unitary circuit

    (D tensor I) [sum_d |d><d| tensor I_A tensor B_d]
    (H tensor I) [sum_c |c><c| tensor A_c tensor I_B]
    (S tensor I).

Thus independent ancillary completeness also follows directly, in addition
to the routed certificate.

### Orthogonal baseline flags despite joint route reachability

Fix S=D=I. Designate A0 as the first active branch and B1 as the second.
Their simultaneous coefficient, evaluated at identity laboratory matrices,
is

    C_11(H)=|1><1| H |0><0| tensor I4.

The route section c=0,d=1 is globally reachable in the full native graph.
Nevertheless at the perfectly allowed auxiliary baseline H=I,

    C_11(I)=0,
    Q_A=|0><0| tensor I4,
    Q_B=|1><1| tensor I4.

Both individual projections have rank four and are orthogonal. Replacing
only H by X makes the two input-side projections coincide and gives
`||C_11(X)||_HS²=4`. For the exact real rotation
`H=(3I+4XZ)/5`, that squared norm is `64/25`. Each individual branch rank
stays four throughout.

The baseline zero comes from a zero matrix entry of a fixed unitary filler,
not from a forbidden route or an unreachable native branch. This example
does not undermine the constant-status singleton or branch-centrality
proofs: neither proof infers graph reachability from fixed-context tensor
coefficients. It does block that tempting extra inference when trying to
turn the quartet's joint rank-budget identity into a global branch-graph
constraint.

The script and JSON with this prefix verify the route choices, branch graph,
and all three exact matrix contexts. This is a separate calibrated host,
not a realization of the quartet.

<a id="rg-049"></a>

## RG-049 — Tilted product geometry and the scalar-hub failure

**Statement.** Tilted rank-two carriers have useful product bases, but the proposed scalar hub fails weak loops and independent native unitarity.

**Status:** mixed positive geometry / negative construction. **Scope:** The exact ansatz and safe Pauli-product tests; the continuous strengthening is RG-050.

### 2. Rank-two tilted carriers can have orthonormal product bases

On factors34, let K=C-perp, where C=span{|01>,|−,+>}. K has exactly two product rays

\[
u=|+,0\rangle,\qquad v=|1,-\rangle,
\]

with overlap magnitude 1/2. Reflection in the Bell line satisfies

\[
(I-2|\Phi^+\rangle\langle\Phi^+|)u=v,
\qquad
(I-2|\Phi^+\rangle\langle\Phi^+|)v=u.
\]

Choose the relative ray q1=|0,u><0,u| on234. The actual represented carrier is

\[
Q_1=R_1(I_1\otimes q_1)R_1
=|00+0\rangle\langle00+0|+|101-\rangle\langle101-|.
\]

Likewise put g0=|0,0,1> and g1=|1,−,+> on134. Reflection in eta=(g0+g1)/sqrt(2) sends g0 to −g1 and g1 to −g0. With q2=|g0><g0|,

\[
Q_2=R_2(I_2\otimes q_2)R_2
=|0001\rangle\langle0001|+|11-+\rangle\langle11-+|.
\]

Take Q3=E3 and Q4=E4. Their product bases are {0100,0110} and {11+0,11+1}. The eight displayed words are mutually orthogonal and the four carrier projections are pairwise orthogonal.

A clean residual orthonormal product basis is

    0011, 00−0, 0101, 0111, 1000, 1001, 101+, 11−−.

Thus the sixteen words give a genuine full product-basis decoder on dimension16. No enlarged quantum boundary is required for this basis identification.

This does **not** make Q1 or Q2 a physical own-factor cylinder. Their spectator vectors depend on their own logical bit. In the generic rank-two Q1 family, product vectors must use a fixed own-qubit basis value unless the relative ray is an eigenray of the Bell reflection; those eigenrays are entangled. Hence an orthonormal product basis occurs precisely for relative ray u or v. The corresponding argument for Q2 gives precisely g0 or g1. This classifies the four rank-two product-code choices within these relative ray families.

Checker: `tilted_product_codes.py`; certificate `tilted_product_codes_checks.json`.

### 3. A new residual tradeoff

The classified simultaneous native tensor has all-passive coefficient F(b)R_Q, with R_Q=I−sum_i Q_i. A simple single-active product-code hub would instead give the ordinary passive product W(b)R_Q. These coincide for every b only if

\[
E_iR_Q=0\quad\text{for every }i.
\]

Necessity follows already by setting only query i to Pauli X:

\[
(F(I,\ldots,X_i,\ldots,I)-X_i)R_Q=-2X_iE_iR_Q.
\]

Sufficiency follows from the defining orthogonal-support formula. Since E_i is orthogonal to Q_j for j≠i, the condition is equivalent to E_i≤Q_i. For rank-two Qi it therefore forces Qi=Ei.

But E1 and E2 have no fully product vectors in their rank-two carriers. Thus rank-two product-code active blocks cannot simultaneously leave an ordinary product all-passive residual. For the product choices above, the squared Hilbert–Schmidt residual defects are exactly 6 at query1 and 4 at query2. This is an obstruction to the ordinary-residual architecture, not to a decoder implementing the genuinely non-product residual F(b)R_Q.

### 4. A phase-safe product basis from the alternative first-port ray

A stronger basis uses the other q1 product ray. In the listed order it is

    001−, 10+0, 0001, 11−+, 0100, 0110, 11+0, 11+1,
    0000, 001+, 0101, 0111, 10+1, 10−+, 10−−, 11−−.

Let W map the computational basis p to these normalized product words. For every o∈{0,1}⁴,

\[
V_o=I-2\sum_i o_iE_i,
\qquad
V_oW|p\rangle=\lambda(p,o)\bigotimes_i H^{\beta_i(p,o)}|a_i(p,o)\rangle.
\]

All 256 columns are product, all local rays lie in {0,1,+,−}, and lambda is a scalar phase. For fixed o, p↦a is bijective. The exact table is in [safe_basis_classical_test_checks.json](../safe_basis_classical_test_checks.json) and [safe_pauli_orbit_table.json](../safe_pauli_orbit_table.json).

The raw bit map o↦a(p,o) is a deterministic process function for every p. That fact is separate from the actual native hub's choices, which depend on the **basis** map beta. It does not supply a native-filler certificate.

### 5. The exact scalar-index hub

Vertices are a source S, four query vertices Q_i, one hub H, and a terminal D. Every internal sector is one-dimensional.

- S has one full U16 branch sending the scalar index p to H
- Query i has a full M2 branch for each globally occurring basis value beta. Its input tuples are (beta,a_i), its output tuples are (beta,o_i). Ports1/2 have only beta=0; ports3/4 have both beta values
- H has one scalar U1 branch for each (p,o). Its input tuple is (p,(beta_i(p,o),o_i)_i), and its output tuple is ((beta_i(p,o),a_i(p,o))_i,o)
- D has one full U16 branch accepting o and producing the original unsectorized output

Different hub input tuples are disjoint because they include p,o. Different output tuples are disjoint because o is recorded and p↦a is injective at fixed o. Every branch is square, positive-dimensional, and globally reachable.

Choose the query fillings U_i^beta=U_i H^beta and hub phases lambda(p,o). The resulting tensor is F_raw(U)W. The fixed source unitary W†D0, with D0=F_raw(I), then recovers the original normalized quartet. This statement only concerns the tied query fillers; the native blocks must remain independently variable to qualify as a valid routed host.

#### Both total choice domains pass

There are six independent query branch choice bits, indexed

    (Q1^0,Q2^0,Q3^0,Q3^1,Q4^0,Q4^1).

Forward choices are p and o_i=f_i(beta_i(p,o)). Exhaustive exact enumeration gives one section for all 16×64=1024 assignments. In reverse, D selects o and a_i=g_i(beta_i(p,o)); again all 1024 assignments give exactly one p and one section.

There are no solid edges: conditioning on any incident query/hub branch pair fixes its entire linking index value. Source/hub and hub/terminal links are fixed by the hub branch too.

#### Weak loops fail by a two-edge witness

Let h be the hub branch with p=001− (the first basis word) and o=0000. There is a closed walk

\[
Q_1^0\xrightarrow{\rm green}h\xrightarrow{\rm red}Q_1^0.
\]

Forward, fix source p=001−. Query choices 000000 give o=0000 and h occurs. Changing only Q1^0's outgoing bit gives choices 100000 and o=1000, so h disappears.

Reverse, fix terminal o=0000. Incoming choices 001001 give p=001−, so h occurs. Changing only Q1^0's incoming bit gives 101001 and p=10+0, so h disappears. The reverse orientation gives h→Q1^0, exactly as required for the displayed mixed cycle.

The full branch graph has 1292 green and 1300 red edges. Its SCC sizes are 262,1,1. It contains 1032 such green/red two-cycles. No strong-edge approximation is needed for the rejection.

Exact certificate: `safe_basis_scalar_hub_test.py` and `safe_basis_scalar_hub_test_checks.json`.

### 6. Actual independent native unitarity fails

At the tied identity-query context, the X-basis marker is a genuine central-projection candidate of rank6 at query3 and rank8 at query4. Their complements have ranks10 and8. These violate the audited exhaustive native-interface alternatives 2/14 (or a single whole M2).

There is also a direct exact witness, independent of that classifier. Take original query1 equal to (3I+4iX)/5 and all other original queries equal to identity. At query3 set the X-basis native branch to −H instead of H, leaving its Z-basis branch at I. Every supplied native matrix is unitary. The resulting matrix M satisfies

\[
\|M^\dagger M-I\|_{\rm HS}^2=2304/625.
\]

In the listed product-basis source coordinates its (0,14) defect entry is 12 sqrt(2) i/25. Flipping query4's X-basis branch instead gives the same norm and the opposite value at that entry. Conjugating by the fixed source normalizer preserves the nonzero norm.

Certificate: `safe_basis_native_phase_failure_checks.json`. The checker retains the phase table via the exact V_o columns; it does not discard negative amplitudes or replace nonorthogonal local rays by orthogonal flags.

### 7. Ordinary basis wrappers do not repair this skeleton

Replace a basis-conditioned query by a preadapter K_i^beta, one unbranched query Q_i, and a postadapter L_i^beta. Each adapter branch has full U2 freedom. The preadapter receives (beta,a), outputs a quantum qubit to Q_i, and bypasses beta to the postadapter. The query sends its quantum qubit to the postadapter, which outputs (beta,o) to H. The intended fixed preadapter is H^beta, and the postadapter is identity.

Both augmented choice tables remain the same: forward choices occur at L_i^beta and reverse choices at K_i^beta. However the preceding two-cycle becomes

\[
L_1^0\xrightarrow{\rm green}h\xrightarrow{\rm red}K_1^0
\xrightarrow{\rm solid}Q_1\xrightarrow{\rm solid}L_1^0.
\]

The solid edges have quantum dimension two for co-occurring branches. Thus this full-filler-preserving wrapper refinement fails too. Merely moving basis changes outside the native query does not solve the feedback problem.

### 8. Every safe Pauli-product OPB is excluded for this scalar-hub ansatz

Enumerate all 4⁴ initial product rays from {0,1,+,−}. Exactly 49 have all sixteen V_o images still in this product alphabet. They span the full sixteen-dimensional space. Marker invariance across those rays is false; for example the baseline query3 marker fails on ray 00+0 at o=0000.

A stronger finite necessary test avoids enumerating all complete bases. In any valid hub of this form the physical X-basis marker at query i=3 or4 must be one of

\[
K_i\in\{0,E_i,I-E_i,I\},
\]

by the audited native-interface classification. For a proposed basis ray psi, the marker's column must satisfy, for every o,

\[
1_{\{\beta_i(\psi,o)=1\}}\langle o|V_o\psi\rangle
=\langle o|K_iD_0\psi\rangle.                       \tag{*}
\]

This criterion is linear in the tested ray on the right and exact on the left. It is a necessary condition for each member of a putative OPB: if C_i is its branch-marked coefficient matrix and G0=D0W, then C_iG0†=K_i implies C_i=K_iD0W.

Among the 49 safe rays, the spans satisfying (*) at query3 have dimensions 12,12,13,13 for K3=0,E3,I−E3,I respectively. At query4 the dimensions are 13,13,12,12. Thus **even either port's marker condition alone prevents a sixteen-ray basis**. Imposing both markers leaves spans of dimension at most9 across all sixteen pairs. There is no need for an exhaustive maximal-clique search.

This excludes the entire scalar hub built from an OPB in the stated safe Pauli-product alphabet with independent Z/X M2 query branches. It does not exclude other product bases, different environment factorizations, coherent basis memory with different native interfaces, or arbitrary routed hosts.

Exact exhaustive certificates: [safe_pauli_marker_invariance.py](../safe_pauli_marker_invariance.py), [safe_pauli_allowed_markers.py](../safe_pauli_allowed_markers.py), and their JSON results.

### 9. Concrete remaining construction gap

The tilted rank-two geometry genuinely removes the old full-S1 product-envelope bottleneck. It supplies full-dimensional coherent product decoders. The phase-safe basis additionally supplies a product-valued reversible table with total forward and reverse classical choice relations.

The unsolved step is to factor that table's hub information flow so that quantum input information is not carried back through a branch that also records the same query's output. Full basis-conditioned native freedom cannot simply be retained, and moving its adapters outside the query creates a strong cycle. A successful architecture must preserve the original M2 (or classified active/passive) native interfaces while moving or compressing those input/output records in a way that removes the explicit mixed two-cycles. It must also implement the non-product all-passive coefficient of the tilted promotion, rather than silently replacing it by W(b)R_Q.

No valid host for the quartet has been obtained in this attempt. The failures above concern explicitly specified, newly tested architectures and do not prove nonroutability.





**Reproduction limit:** supporting helpers were not supplied; the analytic argument remains available. See the [artifact map](../REPRODUCIBILITY.md#rg-049).

<a id="rg-050"></a>

## RG-050 — Complete safe-product variety and scalar-hub exclusion

**Statement.** The complete complex safe-product variety excludes every deterministic one-term full product-basis scalar hub of the stated architecture.

**Status:** scoped negative result. **Scope:** Continuous rays are covered; does not classify arbitrary coherent encoders.

### 1. Result

Write a nonzero product ray as

    ψ = a ⊗ b ⊗ c ⊗ d,    a,b,c,d ∈ P¹(C),

and use 0=[1:0], 1=[0:1], +=[1:1], −=[1:−1]. Let `*` denote an arbitrary projective qubit, independently in each displayed component. Put

    h(a,c,d) = 2a₀c₀d₁ + a₁(c₀−c₁)(d₀+d₁).

The set of all ψ for which every one of the sixteen

    V_o ψ = (I − 2 Σᵢ oᵢEᵢ) ψ

is product has exactly the following irreducible components:

- One surface: b=0 and h(a,c,d)=0
- Nine projective lines: `0*01`, `1*−+`, `0*10`, `1*+−`, `01*0`, `011*`, `11+*`, `11*−`, `*1+0`
- One isolated point: `−1−1`

Here dimensions are complex projective dimensions: 2, 1, and 0 respectively. The surface spans a seven-dimensional vector subspace; the full variety spans C¹⁶. Its intersection with the original `{0,1,+,−}⁴` alphabet is exactly the previously found set of 49 rays. Most points of the surface and lines are genuinely continuous, so this is not a finite-alphabet enumeration.

Every full product basis drawn from this variety nevertheless fails the independent-native-filler requirement for the direct scalar orbit-table hub. The obstruction uses only port 3; port 4 gives an independent version. Arbitrary complex local frames do not repair it.

### 2. Exact necessity: first isolate the E₂-active rays

On factors 1,3,4 define the unnormalized products

    g₀ = |0,0,1>,       g₁ = |1,−,+>.

The support vector of E₂ is `v=2g₀+g₁`, with squared norm 8, and E₂ is its rank-one projector tensored with I₂. Thus

    E₂ψ=0  ⇔  h(a,c,d)=0.

Suppose E₂ψ≠0 and `(I−2E₂)ψ` is product. On factors 1,3,4, the difference between two product tensors is a nonzero multiple of v. The rank-two decomposition of v is unique in its product rays:

1. Its local ranks are 2 on all three factors
2. Any decomposition into two product tensors consequently has linearly independent factors in every slot
3. The span of the two spectator products is therefore the same as span{|0,1>, |−,+>} on 3,4
4. The latter two-dimensional space has exactly two product rays, because its two local pairs are linearly independent; in their local coordinates it is the diagonal matrix pencil diag(s,t), whose rank-one members have st=0
5. The remaining factor then fixes the corresponding first-qubit ray to 0 or 1

Hence `(a,c,d)` is g₀ or g₁. The second factor b is arbitrary. Conversely,

    (I−2E₂)(0b01) = −(1b−+)/2,
    (I−2E₂)(1b−+) = −2(0b01).

E₁,E₃,E₄ annihilate both entire families. Thus the E₂-active safe rays are exactly the two lines `0*01` and `1*−+`. No assumption of reality, normalization, Pauli coordinates, or finite alphabets entered this argument.

### 3. Complete classification on h=0

The projectors Eᵢ are pairwise orthogonal. Their reflections commute and their products are exactly the V_o. If E₂ψ=0 it stays zero throughout the orbit, so only the other three reflections need be considered.

#### 3.1 E₁ productness

Let q=c₀d₀+c₁d₁. The first reflection acts trivially when b₀q=0. When b=0 it always preserves products, since

    (I−2E₁)(a ⊗ 0 ⊗ c ⊗ d)
      = a ⊗ 0 ⊗ [d₁:−d₀] ⊗ [−c₁:c₀]

as unnormalized vectors. If b₀b₁q≠0, the two b-slices would have to be proportional for the result to be product. Their difference is a nonzero Bell tensor, which is not proportional to the initial product c⊗d. Therefore

    (I−2E₁)ψ is product  ⇔  b₀b₁q=0.

#### 3.2 b=0

E₃ and E₄ vanish. The preceding factorization proves all h=0 rays with b=0 are safe. This is the surface in the result.

#### 3.3 b=1

E₁ vanishes. On a,c,d, E₃ is the phase controlled by a=0,d=0; E₄ is the phase controlled by a=1,c=+. Their individual productness conditions are

    a₀a₁=0 or d₀d₁=0,
    a₀a₁=0 or c₀²−c₁²=0.

These conditions also suffice jointly: if a is a computational ray the two operations are local; otherwise d is computational and c is an X ray, so both operations only change a's relative phase.

Intersect with h=0:

- a=0 gives c=1 or d=0: `011*`, `01*0`
- a=1 gives c=+ or d=−: `11+*`, `11*−`
- With a₀a₁≠0, the four choices c∈{+,−}, d∈{0,1} give the remaining line `*1+0` and point `−1−1`

#### 3.4 b₀b₁≠0

Productness under E₁ forces q=0, so E₁ vanishes. A reflection in a three-factor product projector preserves an initial product exactly when either the projector annihilates it, or at least two of the three local factors equal the projector's support rays. This follows directly from a 2×2 flattening minor when two local perpendicular components are nonzero.

For E₃ and E₄ this specializes to

    E₃: a=1, or d=1, or (a=0 and d=0),
    E₄: a=0, or c=−, or (a=1 and c=+).

Together with q=h=0:

- a=0 leaves exactly c=1,d=0, giving `0*10`
- a=1 leaves exactly c=+,d=−, giving `1*+−`
- If a₀a₁≠0, the two conditions force d=1,c=−, contradicting q=0

These lines are safe including their b=0,1 endpoints. This completes necessity and sufficiency for all sixteen orbit elements, not just the four generators.

#### 3.5 Irreducibility and absence of omitted components

The two coefficient forms `2c₀d₁` and `(c₀−c₁)(d₀+d₁)` are coprime. Thus h, which is linear in the pair a₀,a₁, is primitive and irreducible over C by Gauss's lemma. The surface is irreducible. The nine displayed lines are distinct and none is contained in the surface or another line. The isolated point belongs to none of them or the surface. The case split covers every projective b and a; no affine chart, exceptional denominator, or rational-parametrization base point was discarded.

### 4. Exact architecture being excluded

This is the direct scalar product-orbit hub of [RG-049: Tilted product geometry and the scalar-hub failure](construction-boundaries.md#rg-049), now with an arbitrary complex orthonormal product basis `{ψ_p}` and arbitrary local unitary frames Bᵢ^β:

    V_o ψ_p = λ(p,o) ⊗ᵢ Bᵢ^{βᵢ(p,o)} |aᵢ(p,o)>.

Each query has an independent native M₂ branch for each occurring label β. Its prescribed original filling is `Uᵢ Bᵢ^β`. The hub has a single scalar term indexed by p,o, using the displayed input columns and the computational output indices o. Each reachable native branch must remain independently fillable; its scalar phase is in particular a permitted independent variation. The source/terminal are the fixed dimension-16 construction already described there.

The theorem allows arbitrarily many candidate labels, repeated frames, phases, general complex rays, and any safe product basis. Native validity itself cuts the reachable port-3 possibilities down to a single M₂, or an active/passive pair whose represented central projections have ranks 2 and 14.

The claim is not about a general scalar network with additional coherent sums per coefficient, arbitrary re-encodings of query outputs, a different external factorization, or a nonorthogonal quantum memory. Those do not automatically have this one-term product-orbit coefficient formula.

### 5. Full coefficient-marker rigidity

The already audited native original-query classification in [RG-009: Passive quotients and unique active serial ideals](native-interfaces.md#rg-009) and [RG-010: Joint native tensor from saturated phase ranks](native-interfaces.md#rg-010) says at port 3 that every reachable branch-central marker is one of

    K ∈ {0, E₃, I−E₃, I}.

More importantly, the active branch has the exact first-column coefficient, not merely an identity-context rank constraint. Let

    W(U)=⊗ᵢUᵢ,
    F_raw(U)=W(U)−2 Σᵢ P₁^{(i)}W(U)Eᵢ,
    D₀=F_raw(I),        F(U)=F_raw(U)D₀.

For an active port-3 branch the normalized coefficient is `F(U)E₃`. Since `[D₀,E₃]=0`, its coefficient in the raw source-basis coordinates is `F_raw(U)E₃`; the passive coefficient is its complement. Thus, for any one branch and any source vector ψ_p, the branch-marked coefficient must be

    C_β(U)ψ_p = F_raw(U)Kψ_p.                       (1)

The scalar orbit table instead marks the entire single p,o term. Its o-th row is

    1_{β₃(p,o)=β} <o|W(U)V_oψ_p>.

The o-th row of (1) is `<o|W(U)V_oKψ_p>`. Equality for all independent Uᵢ implies equality of their multilinear coefficient tensors:

    1_{β₃(p,o)=β} V_oψ_p = V_oKψ_p,
    1_{β₃(p,o)=β} ψ_p = Kψ_p.                      (2)

Only independent one-qubit unitaries are varied here. They linearly span the one-qubit matrix spaces; this is a coefficient identity, not permission to replace independent vertices by one unrestricted joint filler.

Equation (2) is substantially stronger than the old identity-context marker test. A branch label must be constant over the full o-orbit of a given source ray, and that ray must be an eigenvector of its represented marker. In particular every E₃-orthogonal ray must use the one passive M₂ branch throughout its orbit (or the one whole M₂ branch when the active ideal is absent).

### 6. No full product-basis scalar hub exists

Because the ψ_p span C¹⁶ and E₂≠0, at least one source ray has E₂ψ_p≠0. Section 2 forces it into `0*01` or `1*−+`.

Both families are annihilated by E₃. By (2), their entire orbits must therefore use the same passive port-3 frame. But reflection in E₂ exchanges their third-factor rays

    0  ↔  −.

These are distinct and nonorthogonal: their normalized overlap has squared magnitude 1/2. They cannot both be columns, even up to scalar phase, of one two-dimensional unitary frame. This contradiction excludes every full safe product basis in the stated architecture.

The same argument works at port 4: both families are annihilated by E₄, yet their fourth-factor rays change `1 ↔ +`, again with squared overlap 1/2. No larger boundary, shared ancilla, restricted filler family, or branch correlation has been assumed or introduced.

The obstruction already contradicts complete independent native unitarity. Checking forward/reverse univocality or weak-loop freedom cannot repair it. It excludes the continuous extension of this scalar-hub ansatz, while leaving the original universal realization problem open.

### 7. Reproducible exact checks

Run `python continuous_product_classification.py`. The checker:

- Verifies the supplied Eᵢ are orthogonal rank-two projections and D₀ is a Hermitian unitary
- Checks all sixteen images on every line by polynomial flattening minors
- Reduces every surface orbit minor modulo the exact ideal (h), including all exceptional parameter loci
- Verifies the E₁ factorization and the two complete E₂-active families symbolically for arbitrary complex b
- Verifies the raw normalization, port-3/4 active coefficients, and rowwise V_o formula with sixteen independent symbolic query matrix entries
- Compares the classification to all sixteen orbit images on a 1,296-point rational product grid
- Reproduces the prior 49 Pauli rays and exact span ranks

The necessity proof is the projective argument in Sections 2–3, not an inference from this supplementary finite grid. Results are in [continuous_product_classification_checks.json](../continuous_product_classification_checks.json); the stdout copy is `continuous_product_classification.log`.

<a id="rg-051"></a>

## RG-051 — Seven-context phase synthesis and legal record gadget

**Statement.** Exact seven-context scalar factorizations and a legal pre-existing-scalar-edge record gadget coexist with a failed naive quantum subdivision.

**Status:** conditional construction / negative subdivision. **Scope:** No generic quartet rewrite follows. The exact full-host target is excluded by RG-001; the positive scalar gadget remains reusable.

### Exact reduction obtained

The second maximal C7 laboratory-input context is entirely fixed-past: its
seven diagonal atom projections commute with every E_i. Let B denote its
seven-dimensional diagonal algebra. The full ten-dimensional real space of
complete diagonal laboratory-input tangent flags is the direct sum

    B + span{input bit1, input bit3, input bit4}.

The four C7 contexts admit exact scalar Laurent phase factorizations

    G_context(z,U)=F(U1 A1(z),U2,U3 A3(z),U4 A4(z)) B(z),

where B(z) is a fixed-past diagonal unitary and every Ai(z) is a diagonal
one-qubit unitary. Only query1 is used for context1, no query for context2,
queries1/3 for context3, and queries1/4 for context4. All exponent matrices
are explicit integers in [seven_context_synthesis_reduction_checks.json](../seven_context_synthesis_reduction_checks.json).
The identity holds coefficientwise in the original queries.

This isolates a precise phase-concentration problem with at most two physical
query-input phase locations per nontrivial context. It is NOT a native C7
realization: the same scalar z may appear repeatedly and inversely, and this
factorization must not be applied to arbitrary noncommuting private ancillary
matrices in place of the seven phases.

### A positive routed calibration

[seven_context_lugano_rewrite_check.py](../seven_context_lugano_rewrite_check.py) starts with the actual time-reversed
binary Lugano hub. Its source S has native M8 and emits the scalar index p;
its eight hub branches are scalar, and each laboratory has the original two
full M2 branches. The external boundary is dimension8.

For any seven-valued coarsening k(p) of the eight source labels (the test
merges p=000 and111), replace the scalar edge S→H by:

    S → splitter → record → merger → H,
                   splitter ─→ merger

The lower edge carries the residual scalar index p. The upper edges carry
k(p). Splitter and merger have eight singleton-to-singleton scalar branches;
the record has seven scalar branches. The splitter sends p to (k(p),p), and
the merger accepts precisely the correlated pairs (k(p),p). Every branch
retains its full native scalar freedom. No quantum multiplicity is promoted.

The checker exhausts all8 forward and64 reverse complete choices, computes
every conditional wire-value set and all three branch-edge types, and verifies
weak loops. Both the original and modified graphs have no internal solid
edges; every recurrent component is wholly red. The marked contraction is
exactly the original tensor multiplied on the past by z_{k(p)}. Thus a coarse
record on an ALREADY PRESENT scalar edge really can be exposed by a bypass
gadget without changing the laboratory interfaces.

### Calibration against the dangerous shortcut

The same checker replaces each recurrent M2 laboratory branch by two
successive full M2 branches joined by a dimension2 quantum sector. The
complete choice counts stay8 and64, and the tensor is still the complete
composition obtained by multiplying the two local fillers. Nevertheless the
naive subdivided graph acquires six solid edges and solid/red cycles, failing
weak loops. This is a graph-level obstruction to that subdivision, not to
the complete product tensor or to another possible routing of it.

This distinction is relevant when concentrating the C7 phase factors: ordinary
serial gate insertion inside a recurrent component cannot be assumed to
preserve the routed certificate.

### Precise missing rewrite

For one chosen quartet context, replace its exact distributed scalar phase
factorization above by ONE native C7 record vertex with coefficient branches
L_{P_k}, using a correlated residual-memory bypass. The rewrite must:

1. Use the record once and preserve its arbitrary independent private-ancilla
   branch fillers; canceling correlated scalar repetitions is insufficient
2. Preserve the classified original-query native ports, without exposing all
   sixteen computational input labels or splitting hidden multiplicities into
   independent branches
3. Supply an actual scalar record index k on a routed edge, rather than infer
   one from the completeness of the coefficient projection family
4. Keep quantum transport out of recurrent branch components and verify both
   complete choice domains and the resulting weak-loop graph

The Lugano bypass test proves this rewrite when the coarse record is already
a function of one genuine scalar edge. What is missing for the quartet is a
valid coarse-record encoder from the distributed laboratory-input context.
In contexts3/4 its five-dimensional record atoms merge a one-dimensional
computational sector with a four-dimensional coherent sector; a full M5
decoder or an independently phase-addressable fine computational refinement
cannot be silently substituted.

This remains a construction target, not a claimed general graph rewrite.
Records at different vertices are allowed to have noncommuting Heisenberg
representations; the four contexts are not assumed jointly accessible.

### Reproduction

- [seven_context_synthesis_reduction.py](../seven_context_synthesis_reduction.py): PASS
- [seven_context_lugano_rewrite_check.py](../seven_context_lugano_rewrite_check.py): PASS, including the intentional
  weak-loop failure of the quantum-subdivision calibration
- The corresponding JSON and log files contain exact data

The branch-edge conventions are those of [Vanrietvelde et al., Definitions
3.4–3.7 and Theorem3.1](https://arxiv.org/html/2206.10042v3).

<a id="rg-077"></a>

## RG-077 — Safe adapter algebras, phase obstruction and code rotation

**Statement.** Maximal safe finite-dimensional adapter algebras have the stated active-memory/scalar-payload form; exact examples exclude canonical phase freedom and direct code-rotation insertion.

**Status:** source-level result. **Scope:** Safety is relative to the specified memory observable. Does not grant arbitrary grouped interventions or a routed location for an abstract adapter.

### 2. Proof of the canonical-phase obstruction

The three-party example uses qubit memory R and qubit laboratories A,B,C. On R C let Phi and Psi project onto the Bell vectors (00+11)/sqrt(2) and (01+10)/sqrt(2), and put L=I-Phi-Psi. Its orthogonal supports on A B R C are

E_A=I_A tensor |0><0|_B tensor Phi,

E_B=|0><0|_A tensor I_B tensor Psi,

E_C=|11><11|_AB tensor P_+^R tensor I_C.

The rank-two projectors are pairwise orthogonal. Each is trivial on its own input. Hence the output-recording blocks V_abc=I-2aE_A-2bE_B-2cE_C give an ancillary-complete process by the orthogonal-support proof.

The proposed central phase operation becomes output multiplication by

D=x Phi+y Psi+z L.

At identity laboratory operations, its AB=11 block is

F_D=(I_R tensor |0><0|_C)D
     -(I_R tensor |1><1|_C)D(X_R tensor I_C).

The referenced helper check_new_cycle_phase_round5.py is described as checking symbolically on the phase torus that

Tr[(F_D†F_D-I)^2]=2-x/y-y/x=|x-y|²,

(F_D†F_D-I)^2=(|x-y|²/4) I_4.

Thus x=y is necessary. It is sufficient since Phi+Psi=(I+X_R tensor X_C)/2, so D commutes with X_R tensor I_C and all three original supports. At x=1,y=i,z=1 the squared Hilbert-Schmidt defect is exactly 2.

The same script verifies a safe adapter D0=P_+ tensor Z+P_- tensor I that moves Phi, and the order sensitivity of the two safe gate families. With A=H_R tensor I and B=P_+ tensor X+P_- tensor I, A,B,AB are safe, while BA has identity-context defect diag(-1,1,1,-1), of squared norm 4.

Thus those phases do not define unitary processes. This conclusion follows from the displayed exact defect identity and does not presume a routed realization for the phase-modified tensor.

The elementary adapter theorem itself is rigorous. For arbitrary D on R C, singleton parity erasure at C says exactly that

D(P_+ tensor I_C)D†=q_R tensor I_C.

The transformed supports remain orthogonal. The other two remain trivial on their own inputs, and this equation provides the corresponding property at C. This proves complete sufficiency as well as necessity. Choosing U_R carrying P_+ to q yields

D=(U_R tensor I_C)(P_+ tensor V_+ + P_- tensor V_-).

It is important that this safe set is an ordered product, not a group.

### 3. New dimension-independent classification of safe gate algebras

The following classification covers arbitrary finite memory and arbitrary payload dimension at least two.

**Theorem.** Let P be a nonzero, nonidentity projection on a finite-dimensional memory R, and let Q be a payload of dimension at least two. Say that a unital C*-algebra A contained in L(R tensor Q) is safe when

u(P tensor I_Q)u† belongs to L(R) tensor I_Q

for every unitary u in A.

Every safe A is contained in an algebra of the form

B(R_a,R_+,R_-)
 = [L(R_a) tensor I_Q]
   direct-sum L(R_+ tensor Q)
   direct-sum L(R_- tensor Q),                                  (1)

where R=R_a direct-sum R_+ direct-sum R_- is a P-reducing decomposition,

P|R_+=I,  P|R_-=0,

and P|R_a is nonzero and nonidentity if R_a is nonzero. The choice R_a=0 is allowed. Every algebra (1) is safe and maximal among safe unital C*-algebras. These are all the maximal safe algebras.

The word safe here is relative to this specified memory-observable condition. It is not a claim that these algebras furnish arbitrary routed-process decompositions.

#### Proof of containment

Form the memory-local orbit algebra

C=C*{u(P tensor I_Q)u† : u in U(A)}.

By the assumption C lies on R. Since U(A) is a group, every one of its elements normalizes C. This uses only already-safe operations and never assumes arbitrary joint laboratory unitaries are allowed.

Decompose the memory representation:

R=direct-sum_lambda (C^{n_lambda} tensor C^{m_lambda}),

C=direct-sum_lambda [M_{n_lambda} tensor I_{m_lambda}].

The unitary group of a finite-dimensional C*-algebra is connected. Its conjugation action cannot permute the finitely many minimal central projections of C. Thus every element of A commutes with those projections.

On one central block, A_lambda is a unital C*-algebra normalizing

M_n tensor I_{m dim Q}.

If H is Hermitian in A_lambda, its commutator derivation preserves M_n. Every derivation of M_n is inner, so

H=H_1 tensor I+I tensor H_2.

The same conclusion applies to H², since H² belongs to A_lambda. The component of H² traceless on both factors is

2 H_1^0 tensor H_2^0.

It must vanish. Therefore every Hermitian H acts on just one of the two factors, up to a scalar. A real linear space contained in the union of two linear subspaces lies entirely in one of them. Consequently

A_lambda is contained either in M_n tensor I or in I tensor M_{m dim Q}.  (2)

If n>1, the second alternative would commute with P on that block. Its orbit algebra would then be generated by one projection and would be commutative, contradicting the definition of C_lambda=M_n. Thus every n>1 block uses the first alternative: it acts on memory alone.

If n=1, P is either zero or identity on the corresponding memory multiplicity space. Arbitrary operations on that multiplicity space and Q are safe.

Combine all n>1 blocks into R_a, all scalar blocks with P=I into R_+, and all scalar blocks with P=0 into R_-. Equation (2) places A in (1). Each n>1 block has nontrivial P; otherwise its orbit could not generate M_n. Therefore P|R_a has both eigenvalues when R_a is nonempty.

#### Safety and maximality

Safety of (1) is immediate. Its active block rotates P inside memory only, while its other two blocks have P equal to a scalar identity or zero.

Suppose a larger safe algebra A' contains B from (1). Apply the containment theorem to A': it lies inside another algebra B' of form (1). Every central projection of B' is memory-local and commutes with B. But the memory-local commutant of B consists exactly of the scalars on each of the three nonempty original summands R_a,R_+,R_-. Hence each summand of B' is a union of complete original summands.

The original R_a cannot lie in a scalar-P summand of B', because P is nontrivial on it. Each nonzero original R_+ or R_- cannot lie in the active summand of B', since B already allows full payload operations there, whereas the active summand of B' acts as the identity on Q. Here dim Q>=2 is essential. Finally the P=1 and P=0 summands cannot merge into a scalar-P block. Thus B'=B and A'=B.

This proves maximality and exhaustiveness.

#### Checks and examples

For dim R=2 and rank P=1, either R_a=R or R_a=0. The theorem gives precisely the two qubit-memory algebras M2 tensor I and (C P direct-sum C P_perp) tensor M_dimQ.

For dim R=3 and rank P=2, there is also a mixed maximal algebra. Choose R_a of dimension two containing one P=1 and one P=0 direction, and let R_+ be the remaining P=1 direction. The algebra is

(M2 tensor I_Q) direct-sum M_dimQ.

This supplies independently variable memory rotation on one subspace and unrestricted payload processing on the other. Neither of the two qubit-only maxima describes this case.

### 5. Proof of the new code-rotating safe node

The independent admissible-node lane found a particularly useful adapter. Put

C_34=span{|0,1>,|-,+>},

Q=I_1 tensor |0><0|_2 tensor P_(C_34 perpendicular).

An arbitrary unitary on the two-dimensional C_34-perpendicular subspace, controlled by input2=0 and acting trivially on input1, fixes the actual supports E2,E3,E4. It can rotate Phi+ to the product vector q=|+,0>. The transformed E1 is then a product cylinder, and all four transformed supports have explicit coded-cylinder envelopes. This is a real, independently admissible node family, but neither safe-node admissibility nor the conjugation identity proves its location in the existing coded graph.

There is an exact obstruction to simply placing it inside one branch of that graph. In the bases input3=+/-, input4=0/1, write

chi=(|+,1>+|-,0>-|-,1>)/sqrt(3).

Then

C_34 perpendicular=span{q,chi},

Phi+=(q+sqrt(3) chi)/2.

The coded active-2 envelope found by the other lane is

F2=I2 tensor [P0_1 tensor I3 tensor P1_4
                +P1_1 tensor P-_3 tensor I4].

For fixed input1=0, its shared34 code is span{|+,1>,|-,1>}; for input1=1 it is span{|-,0>,|-,1>}. In either case,

F2 q=0,   ||F2 Phi+||²=1/2.

If a unitary W on this interface maps Phi+ to q and commuted with F2, these two quantities would agree by unitarity. Therefore [W,F2] is nonzero for every such rotation. This does not depend on choosing a particular rotation angle or its action on the other code basis vector.

More precisely, [F2,W]Phi+=-W F2 Phi+ on either fixed-label slice, so its norm is exactly 1/sqrt(2). Thus the full commutator has operator norm at least 1/sqrt(2). The exact audit script checks the two supporting projection norms.

The same chi also has a nonzero component in the coded residual sector: |-,0> for input1=0 and |+,1> for input1=1. Hence the adapter mixes active-1, active-2-envelope, and idle branches when input2=0. A unitary confined to an existing hub branch cannot realize that mixing. It changes the branch carrying the history of whether laboratory2 has been queried.

This is an obstruction only to the direct insertion in the displayed coded graph. A redesigned interface could change the history decomposition. In that case its two appearances of laboratory2 must satisfy the one-use fusion intertwiner, or a different explicit once-only realization must be supplied.

The rotation is not already one of the two U(3) code-preserving constructions. Those vary a gate on laboratory2's common code while preserving E1; this adapter instead rotates E1 and preserves actual E2. Treating them as the same operation would confuse the actual support E2 with its larger coded envelope F2.





**Reproduction limit:** supporting helpers were not supplied; the analytic argument remains available. See the [artifact map](../REPRODUCIBILITY.md#rg-077).
