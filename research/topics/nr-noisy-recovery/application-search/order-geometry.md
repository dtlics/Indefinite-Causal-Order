<a id="nr-r29"></a>

# Order-only activation bounds and modular-delivery accounting

[Investigation handoff](README.md) · [Application assessment](../architecture.md)

**Status and scope.** Secondary order-architecture detour, deprioritized for the original natural-black-box computing/QEC objective. Exact finite certificates have only the declared order-only scope. Supplied analytical derivations and scoped checks; not a new Lean audit or a publication-priority claim.

## 1. Conventions

Write

    Omega_d(X) = Tr(X) I/d,
    T_{a,b} = a id + b Omega_d.

These maps may be subnormalized. For a nonzero CP depolarizing map, b >= 0, a+b > 0, and a >= -b/d^2. Its normalized Choi state is isotropic, with Bell fidelity

    F = (a+b/d^2)/(a+b).

It is entanglement breaking exactly when a <= b/d, equivalently F <= 1/d. Its flagged success probability is a+b and is independent of the input.

Every channel slot has the standard paired-history implementation: the same labeled map appears in all histories, with its environment labels paired across those histories. Fresh environments or a classical mixture of valid tuples are allowed. An unspecified quantum shared bath or arrival-time-dependent substitution is not covered.

A 'bare binary tree' means recursively applying the ordinary two-slot switch to child channels, without intervening target encoders, decoders, or nontrivial target operations. Controls are initially independent of the payload/reference. They may be retained and measured at the end. A general once-each permutation experiment has one visit to each labeled device in every history, with arbitrary coherent amplitudes over permutations, but again no extra target operations between visits.

## 2. Analytical result: bare binary nesting does not activate EB depolarizing channels in d >= 3

### 2.1 Exact recursion

Switch T_{a,b} and T_{c,e}, initialize the control in plus, and measure it in X. The two subnormalized branches are

    a_+ = ac + be/(2d^2),
    b_+ = ae + bc + be/2,
    a_- = -be/(2d^2),
    b_- = be/2.

This follows by bilinearity, the ordinary composition rule, and the cross term of two completely depolarizing slots, Gamma(Omega_d,Omega_d)(X) = X/d^2. The identity/identity term has only a plus flag; mixed identity/depolarizer terms are also entirely plus.

For b,e > 0 set x=a/b and y=c/e. Then

    x_- = -1/d^2,
    x_+ = [xy + 1/(2d^2)]/[x+y+1/2].                 (1)

The control output is diagonal in the X basis because the cross map is Hermiticity-preserving. Inductively the entire collection of tree controls is classical in its product X basis, with one depolarizing CP map for each record. Thus a statement about every record also applies to the complete flagged channel, and arbitrary final receiver processing cannot restore entanglement.

### 2.2 EB closure theorem

For d >= 3 the interval

    -1/d^2 <= x <= 1/d

is preserved by (1). The denominator is positive. A separately fractional-linear function reaches its extrema at rectangle corners, since its derivative in either coordinate has sign independent of that coordinate. The minus branch is the lower endpoint. The plus branches at the four corners lie in the interval.

For example, put D=d^2 and L=-1/D. Then

    f(L,L) = (D+2)/[D(D-4)] <= 1/d,

where the inequality is equivalent to d^3-d^2-4d-2 >= 0, true for d >= 3. At T=1/d,

    f(T,T) = 3/[d(d+4)] <= 1/d.

The mixed corners are positive and at most 1/d.

**Theorem.** Any bare binary-switch tree of independently slotted entanglement-breaking depolarizing channels in dimension d >= 3 remains entanglement breaking, including all retained controls. No amount of nesting or receiver postselection activates entanglement in this class.

The leaf channels need not have identical strengths. The restriction to depolarizing channels and bare target processing is essential. This is stronger in its specific family than merely saying exact identity recovery is unavailable, but it does not imply that all higher-order processes or all encoded constructions fail.

For a general controller input independent of the target, the pure-state case is a diagonal filter of the uniform-controller output, because the controlled permutation is diagonal in the history basis. Mixed controller inputs follow by convexity. Such receiver-side filtering preserves separability. This does not grant initial payload/control entanglement or a clean information-bearing side channel.

### 2.3 Sharper bound for completely depolarizing leaves

Starting from x=0, the smaller invariant interval is

    L = -1/D,
    H = (D+2)/[D(D-4)],    D=d^2 >= 9.

Here f(L,L)=H. At the remaining corners the nonnegative differences are

    H - f(H,H) = 8(D-1)^2/[D(D-4)(D^2+8)],
    H - f(H,L) = 8(D-1)^2/[D(D-4)(D^2-4D+12)].

All plus corners are nonnegative, so the lower endpoint is preserved as well. Since F=(x+1/D)/(1+x) increases in x,

    F_branch <= 2/(d^2-2).                          (2)

This bound is reached by the four-leaf --+ tree. For d=3 it is 2/7 < 1/3; for d=4 it is 1/7 < 1/4. Greater tree depth does not improve this ceiling. Equation (2) is the raw depolarizing-branch fidelity; arbitrary receiver operations remain unable to exceed the separable Bell threshold 1/d, even though discarding and preparing a product state can exceed the smaller raw ceiling.

The qubit exception is structural: D-4=0, and the --+ branch can have b=0, hence be scalar identity.

### 2.4 A success-weighted robustness statement

Let m actual slots be within half-diamond distances epsilon_j of reference leaves satisfying the theorem. Slotwise contractivity and a hybrid give complete output trace distance at most E=sum_j epsilon_j. For any receiver acceptance/recovery procedure, with delivery probability s and conditional d-dimensional Bell fidelity F,

    s (F-1/d) <= E.                                  (3)

Proof: the witness P_accept tensor (Phi_d-I/d) has spectral width one, and expectation at most zero on the reference separable flagged output. Its expectation difference is at most trace distance. This treats failed branches rather than normalizing them away. Small deviations can produce weak accepted entanglement, but a large conditional fidelity at a meaningful yield consumes a nonzero perturbation budget.

## 3. Exact search over arbitrary permutations, not just binary trees

### 3.1 The coefficient matrices

Use the matrix-unit Kraus representation K_ab=|a><b|/sqrt(d) for each Omega_d. For two chronological permutation words pi,sigma, contract the matrix-unit indices of the forward word and conjugate word. Covariance gives

    F_{pi,sigma}(X) = A_{pi,sigma} X + B_{pi,sigma} Omega_d(X).

The coefficients are powers of d counting free index loops. The supplied scripts implement this as an exact union-find contraction. This uses the same foundational loop/permutation principle as Wilson and Chiribella [2], not a new theory of diagrammatic composition.

For control preparation amplitudes alpha and a rank-one final control effect beta, put z_pi=alpha_pi conjugate(beta_pi). The accepted map has

    a=z^dagger A z,  b=z^dagger B z,
    p=z^dagger G z,  G=A+B,
    F p=z^dagger H z,  H=A+B/d^2.                    (4)

Arbitrary subsets, mixed controls, and effects are obtained by diagonal congruences or sums of such terms. Numerical searches solve the generalized eigenproblem H z = F G z on G's positive support. Exact claims below instead use rational matrix inequalities.

### 3.2 Four-dimensional target: four or fewer slots are EB for every order superposition

For d=4 and m=2,3,4, the exact verifier proves

    B-dA >= 0,   H=A+B/d^2 >= 0.                    (5)

These inequalities establish separability of the FULL retained-control Choi output, not just low fidelity for a particular controller measurement. Indeed, let

    sigma_0=(I-Phi_d)/(d^2-1),
    sigma_{1/d}=Phi_d/d+(1-1/d)sigma_0.

Both are separable isotropic states. The control-target-reference operator decomposes as

    A tensor Phi_d + B tensor I/d^2
      = dH tensor sigma_{1/d}
        + (d-1)(B/d-A) tensor sigma_0.               (6)

Both controller coefficients are positive by (5). Independent preparation weights are congruences on those coefficients, preserving positivity. Arbitrary final joint processing of controller and target is local relative to the retained reference and cannot create entanglement.

For m=4 the verifier additionally proves

    (5/21)G-H >= 0.

Therefore every raw rank-one controller postselection has F <= 5/21 < 1/4. The numerical maximum equals 5/21, but the exact inequality, not the floating-point optimum, is the certified fact.

The matrices have dimensions 2, 6 and 24. Exact rational LDL elimination verifies (5); no SDP tolerance is used. One slot is trivially EB. The claim is limited to once-each coherent permutations without intermediate target processing, not to every circuit or encoding with four contacts.

### 3.3 Five slots suffice: explicit ten-history construction

Take five completely depolarizing ququart slots, labeled 1 through 5. Define two groups of chronological words:

    C = cyclic shifts of (1,2,3,4,5),
    C' = cyclic shifts of (5,1,4,2,3).

Prepare a uniform coherent superposition of these ten histories. Accept the normalized controller state with plus amplitudes on C and minus amplitudes on C'. Thus z_pi=+1/10 or -1/10 in (4).

Exact contraction gives

    a=153/6400,
    b=69/800,
    p=141/1280 = 0.11015625,
    F=25/94 = 0.2659574468... > 1/4.                 (7)

The accepted Choi state is entangled and, being isotropic, distillable with two-way assistance. It is NOT a high-fidelity pair without purification, nor is positive two-way assisted capacity a claim of positive unassisted capacity.

Together with (5), this proves that five is the minimum contact number for entanglement activation in the stated four-dimensional once-each order-only family. It is a finite, exact architecture separation, not an asymptotic query lower bound against all ordinary algorithms.

An alternative prepares all 120 histories uniformly and filters onto their permutation-sign superposition. It gives a=1/640, b=11/2560, p=3/512 and F=5/16. Its conditional fidelity is higher but its yield and control complexity are worse.

For comparison, the PUBLISHED six-cyclic-order construction [3] has p=7/32 and F=2/7 in d=4: six control paths, larger success, and larger fidelity than (7). Thus the minimal five-contact construction is not automatically the best practical source. Its contribution is the exact feasibility boundary and a different interference pattern.

### 3.4 Qubit endpoint: four-call exact recovery is optimal within the order-only flag-filter class

For d=2 with m fully depolarizing slots, perfect identity upon a controller flag requires b=0. Since B is positive, the accepted controller covariance must be supported on ker B.

Represent any preparation/filter choice by a positive matrix Z with

    0 <= Z <= diag(t),  t_pi >= 0, sum_pi t_pi=1.

A sum of accepted effects has the same representation. The perfect-identity condition is BZ=0. Permuting the identical slot labels acts transitively on the m! histories, preserves A,B and the objective Tr(AZ), and preserves positivity. Averaging any feasible solution over this action yields uniform t=1/m! without changing the objective. Therefore

    p_perfect <= Tr(P_ker(B) A)/(m!).               (8)

On the kernel, A is positive by complete positivity, so Z=P_ker(B)/m! attains the bound.

Exact nullspace computation gives:

    m=1,2,3: ker B = {0}, so no positive-yield exact identity flag;
    m=4: dim ker B=3; P A P has spectrum 9/16 (twice), 0 (22 times).

Hence

    p_perfect,max = [2*(9/16)]/24 = 3/64.           (9)

The familiar four-call --+ construction attains this. Searching all 24 orders, arbitrary preparation weights, and all accepted controller effects cannot improve its perfect-output yield in this class. This is not a theorem against intermediate target encoding, an arbitrary receiver decoder, multiple adaptive attempts, or other higher-order resources.

An interesting imperfect alternative uses all six permutations of three qubit depolarizers and the alternating-sign filter. It gives a=1/12, b=1/24, p=1/8, F=3/4. It activates entanglement, but exact four-call recovery can still be cheaper than purifying its mixed output. No practical dominance is claimed.

## 4. A modular way to transmit a larger register

### 4.1 The extra interface must be explicit

Suppose a physical square channel N acts on dimension D, potentially coupling all internal degrees of freedom. At each invocation the architecture supplies a known encoder C:2 -> D and decoder Dmap:D -> 2. The resulting input/output interface is

    L = Dmap o N o C,

a qubit CPTP channel. Its internal dimension and Kraus rank need not be known. Encoding may prepare local auxiliaries; decoding may trace them. They must not send an input-bearing clean helper across the communication cut.

The resource assumption is a native ability to coherently order the COMPLETE wrapped modules L, including their side records. A primitive switch of the bare N slots does not automatically provide this. In a distributed setting it requires the appropriate encoder/decoder ports at every coherently selected visit, not just at the outermost endpoints. This is a significant architecture condition, not a free mathematical relabeling.

### 4.2 Uniform calibration-free logical qubit source

For each of four labeled wrapped slots, choose an independent output Pauli P uniformly, keeping its choice fixed across coherent histories. For every L,

    (1/4) sum_P Ad_P o L = Omega_2.

For each individual Pauli realization, the four-channel qubit central-polynomial branch is already scalar identity. Multilinearity of the unnormalized branch therefore gives the exact averaged map

    H = (3/64) id_2.                                (10)

No Haar device distribution, common hidden axis, or calibration is required. The slots can differ. Known Pauli frames, the full coherent wrapper, and clean acceptance controls are resources that must be charged. This is an architectural corollary of the previous arbitrary-qubit result and established channel twirling, NOT a new distillation mechanism.

If the raw physical N is entanglement breaking across a network cut, then the wrapped L is also EB. Ordinary LOCC and such links cannot establish shared entanglement, while the extra coherent-placement resource supplies the heralded source. This remains a standard-network comparison, not proof against all ordinary coherent routings of a given apparatus.

### 4.3 Buffer successful pairs; do not postselect the entire unknown payload

Generate one Bell pair at a time using (10). Store successes. Only after collecting n pairs should the unknown, possibly entangled n-qubit payload be teleported. Failed attempts then destroy expendable candidate pairs, not the live input.

Expected contacts are

    E Q = 4n/(3/64) = 256n/3.

No (3/64)^n simultaneous-acceptance penalty is necessary. Clean endpoint storage is charged; it is not a noiseless path connecting endpoints. This is a heralded/two-way-assisted service, not an assertion of a positive unassisted capacity for the single-attempt flagged channel.

Exact binomial ledgers at failure probability at most 1%:

| Ideal pairs requested | Maximum attempts | Maximum contacts | Abort probability |
|---|---:|---:|---:|
| 1 | 96 | 384 | 0.00996292036 |
| 32 | 987 | 3,948 | 0.00989953164 |
| 100 | 2,648 | 10,592 | 0.00997196791 |

An early-stopping implementation saves calls. The expected-contact formula describes unrestricted waiting; the capped expectations are no larger. Arbitrarily long storage with no degradation is not silently inferred from these contact counts; a complete waiting-time/storage budget is separate.

### 4.4 A fully specified classical-flag-error ledger

This example handles CLASSICAL readout flips, not arbitrary controller decoherence.

Suppose each flag can be read nondestructively three times with independent 1% classical errors. Majority voting leaves

    eta=3(0.01)^2(0.99)+(0.01)^3=149/500000.

The complete ideal four-depolarizer flag instrument has the following coefficients a,b in units of 1/64, for binary records 000 through 111 (1=minus):

    a = [3,-2,1,-2,1,-2,3,-2],
    b = [16,8,8,8,8,8,0,8].

The desired flag is 110. With the effective independent classical sign errors, its reported acceptance is

    p_eta=(3+15 eta-8 eta^2-4 eta^3)/64,

and its Bell infidelity is

    e_eta=6 eta(3-2 eta)/(3+15 eta-8 eta^2-4 eta^3).

At the stated eta, p_eta=0.0469448326478460 and e_eta=0.0017849855782550. The averaged channel is depolarizing and the Choi errors Bell diagonal. A five-pair, single-error-correcting purification block has output error at most

    e5=1-(1-e_eta)^5-5e_eta(1-e_eta)^4
      =0.000031748141873359.

For 32 output pairs, collect 160 raw accepted pairs. At most 4,051 attempts (16,204 elementary contacts) succeed with probability above 99%, and the sum of corrected-pair infidelities is at most 0.00101594054. Adding a separately supplied 0.005 complete local-processing/storage budget yields total resource trace error and induced teleportation half-diamond error at most 0.00601594054.

Assumptions: independent attempts; ideal coherent order except the specified classical readout errors; ideal random Pauli wrappers or their error included in an allowed effective slot; no loss in this ledger; nondemolition readout with independent classical errors; common local error budget valid on delivered histories. Repeated measurement does NOT remove a coherent Z error that occurred on an order control before measurement. That error is indistinguishable from a genuine wrong flag and must be bounded separately. These are contracts, not achieved apparatus figures.

The five-pair purification/code correspondence and teleportation are established methods [6]. This is resource accounting for their composition, not a new QEC code.

## 5. Prior work and ordinary competitors

[1] Kechrimparis, Moran, Kwon, Probabilistic Channel Distillation via Indefinite Causal Order, Phys. Rev. Research 7, 043257 (2025), arXiv:2501.13696. https://arxiv.org/html/2501.13696v1 . Four-slot qubit recovery and higher-order channel distillation; multiqubit exact-universality limitation. Our all-depth EB depolarizing closure is a more specific strengthened obstruction derived here; novelty has not been exhaustively determined.

[2] Wilson and Chiribella, A Diagrammatic Approach to Information Transmission in Generalised Switches, arXiv:2003.08224v3 (2021). https://arxiv.org/html/2003.08224 . Loop-count/permutation analysis is prior work. The exact inequalities and order-pattern search here use this established foundation.

[3] Chiribella, Wilson, Chau, Quantum and Classical Data Transmission Through Completely Depolarising Channels in a Superposition of Cyclic Orders, PRL 127, 190502 (2021), arXiv:2005.00618v5. https://arxiv.org/html/2005.00618 . For m cyclic paths, accepted a=(m-1)/(m d^2), b=1/m; thus p=(d^2+m-1)/(m d^2), F=m/(d^2+m-1), entanglement iff m>d+1. This remains a stronger throughput comparator than the ten-path five-contact construction at d=4.

[4] Sazim, Sedlak, Singh, Pati, Classical communication with indefinite causal orders for N completely depolarizing channels, PRA 103, 062610 (2021), arXiv:2004.14339v2. https://arxiv.org/html/2004.14339 . Classical-capacity investigations already compare cyclic cosets and complete order sets. Do not claim first use of noncyclic order superpositions.

[5] Main et al., Distributed Quantum Computing across an Optical Network Link, Nature (2025), arXiv:2407.00835. https://arxiv.org/abs/2407.00835 . Heralded intermodule entanglement and gate teleportation motivate the service endpoint; they do not establish our noisy-module/coherent-order contracts.

[6] Bennett, DiVincenzo, Smolin, Wootters, Mixed State Entanglement and Quantum Error Correction, PRA 54, 3824 (1996), quant-ph/9604024. https://arxiv.org/html/quant-ph/9604024 . Finite-block purification and five-qubit code.

[7] Allard Guerin, Rubino, Brukner, Communication through quantum-controlled noise, PRA 99, 062317 (2019), arXiv:1812.06848. https://arxiv.org/html/1812.06848v2 . Definite-order coherent control can reproduce some purported communication advantages. Same-apparatus resource matching remains essential.

[8] Wang et al., Cyclic order superpositions enable quantum information transmission through completely depolarizing channels, Communications Physics (2026), arXiv:2510.07127. https://www.nature.com/articles/s42005-026-02698-1 . Photonic cyclic-order experiment on a qubit. Known randomized Pauli implementations and measured output-state fidelity do not establish inaccessible arbitrary-channel slots, our ququart result, or a fair all-apparatus comparator.

[9] Lee, Hann, Puri, Girvin, Jiang, Error Suppression for Arbitrary-Size Black Box Quantum Operations, PRL 131, 190601 (2023), arXiv:2210.10733. https://arxiv.org/html/2210.10733 . Ordinary error filtration with clean memory/routing is a relevant local-processor competitor.

## 6. Verification and priority boundaries

- `exact_certificates.py`: standard-library Fraction arithmetic; proves d4 m<=4 matrix inequalities and exact five/six-order coefficients.
- `qubit_optimum.py`: SymPy rational nullspaces; establishes the scoped perfect-heralding optimum 3/64 and the three-order alternating branch.
- `verify_extra.py`: exact SymPy recursion differences, small-d matrix-unit Kraus cross-checks, independent flag formulas, and additional finite checks.
- `explore_orders.py`: numerical generalized-eigenvalue search, m<=5 for five dimensions; six-order cases saved separately. These optimizer values are not substituted for exact certificates.
- `modular_protocol.py`: rational binomial tails and error budgets. The assumed storage/controller physical specifications are not verified by arithmetic.

Attribution discipline: the central-polynomial mechanism and Pauli twirling were already developed or published before this turn. Buffering heralded pairs is standard. The new investigation gives exact scoped architecture comparisons and a complete finite ledger; it does not prove a hardware runtime advantage or a new universal simulation lower bound. Neither pointwise input-output channel tomography nor a stated coherence time alone proves that a device supplies the required coherent slot pairing.

The most useful research conclusion is architectural: binary recursion on an unreduced noisy carrier can remain permanently entanglement breaking, while different order patterns or a native qubit-level interface escape the obstruction. A practical benefit must price those distinct interfaces and ordinary alternatives, rather than treating all of them as the same resource called 'a quantum switch'.
