<a id="nr-r30"></a>

# Finite game instantiations of existing query bounds

[Investigation handoff](README.md) · [Application assessment](../architecture.md)

**Status and scope.** Numerical and game corollaries, not an independent lower-bound method or a practical application obtained by increasing dimension. Supplied analytical derivations and scoped checks; not a new Lean audit or a publication-priority claim.


## Status and scope

These are finite-parameter consequences of the repository's stated C5 and C4 arguments, not new independent proofs of those arguments. The supplied `check_constants.py` verifies parameter substitutions in exact rational arithmetic; it does not verify the hidden-Haar recording theorem, the causal-comb argument, or physical implementations. The projection-game reformulation below is an additional deduction from the C4 proof's intermediate bounds.

Source inputs inspected:

- `dtlics/Indefinite-Causal-Order/research/topics/nr-noisy-recovery/noise-model-selection.md`, C5 complete-output bound (blob `a7c2e965f5d96177240e02a17873b6ce6bfc4082`).
- `dtlics/Indefinite-Causal-Order/paper/main.tex`, Appendix “Approximate full-switch simulation,” especially “Fixed mixtures, fresh labels, and a valid effect” (blob `f0907f179b62e8a6324addc60ff7823cc124bc94`).
- The same manuscript's finite-approximation upper bound, from channel programming.
- Bavaresco et al., *Simulating the quantum switch with quantum circuits is computationally hard*, arXiv:2409.18202v2, for the distinction between finite-query exact simulation and unlimited characterization.
- Pirandola et al., *Fundamental limits to quantum channel discrimination*, arXiv:1803.02834v4, for deterministic finite-error channel programming.

Both games grant ordinary algorithms arbitrary known quantum processing, finite quantum memory, entangled probes and allowed classical adaptation. Unknown environments and Kraus labels remain inaccessible; calibration calls count. A native standard switch is an additional stipulated resource.

## Game 1: the same noise-model decision at a finite large dimension

Let d = 2^768. A referee chooses a fair hypothesis bit:

- H: draw a Haar U once and provide repeated calls to the fixed channel Delta_U, the rank-one dephaser in U's columns.
- L: provide repeated calls to the known channel Lambda = (id + d Omega)/(d+1), where Omega(X) = Tr(X) I/d.

Each invocation has a fresh private environment. U is neither redrawn on each H call nor supplied as advice. The player returns the hypothesis bit. The score is the balanced-prior success, averaged over the hidden U in H.

### Switch strategy

Self-switch two independent invocations on target I/d and control |+>. For H, p_minus=0. For L,

    p_minus = (d-1)/(2(d+1)).

Repeat seven times. Return L if any minus occurs, otherwise H.

    P_H = 1,
    P_L = 1 - [(d+3)/(2(d+1))]^7,
    P_average = 1 - (1/2)[(d+3)/(2(d+1))]^7.

For d=2^768 this gives P_L > 0.99 and P_average > 0.996, using fourteen elementary channel calls. The respective values are just below 0.9921875 and 0.99609375; rounded numerical displays must not be mistaken for exact equality.

### Ordinary score bound

The source C5 endpoint bounds the learner's complete output distance under Delta_U versus Omega by

    B(q,d) = 18(2q)(2q+1)/d^(1/8)
             + 4q/sqrt(d-2q) + q^2/d.

Lambda and Omega have half-diamond distance at most 1/(d+1). An adaptive hybrid therefore gives

    TD(rho_H, rho_L) <= B(q,d) + q/(d+1),
    P_ordinary <= 1/2 + [B(q,d)+q/(d+1)]/2.

Set q=10^12. The required dimension conditions hold. To avoid numerical square roots, use

    sqrt(d-2q) >= 2^383.

Exact rational evaluation of the resulting upper bound gives

    P_ordinary < 0.500455.

Thus the finite comparison is:

- 14 switched calls: more than 99% correct under each hypothesis, and more than 99.6% balanced-prior success.
- Up to 1,000,000,000,000 ordinary calls: less than 50.0455% balanced-prior success.

No tomography-only restriction is used. This is a concrete corollary of C5, not an independent small-dimensional SDP certificate.

The larger uniform simplified bound from the source applies up to floor(2^(768/16)/100) = 2,814,749,767,106 calls, with success at most 0.53045. The direct substitution at 10^12 calls is sharper.

### Qualification

The large gap comes from a large target register and a generic hidden global basis. The theorem does not supply an efficient Haar-device synthesis, a native 768-qubit switch, or an astronomical lower bound for a two-qubit apparatus. Such implementation/circuit-size costs are outside this query theorem.

## Game 2: a perfect-completeness quantum-output game from C4

Let d=2^256 and r=2^120. The referee privately samples independent Haar unitaries U_1,...,U_r and V_1,...,V_r once, defining

    A = (1/r) sum_i Ad(U_i),
    B = (1/r) sum_j Ad(V_j).

These are fixed memoryless channels. A call samples a fresh hidden mixture index; individual components are not directly callable or replayable.

The referee prepares |+>_C and a maximally entangled state |Phi_d>_TR. It supplies C,T and the channel interfaces to the player, retains R, and accepts or rejects after the player returns C,T. No secret channel descriptions are released to the player.

For normalized Choi vectors |X>=(I tensor X)|Phi_d>, define

    |s_ij> = (|0>|V_j U_i> + |1>|U_i V_j>)/sqrt(2).

The verification measurement is {Pi, I-Pi}, where

    Pi = projector onto span{|s_ij>: all i,j}.

This is a fixed game rule as a function of the referee's sampled instance. It is not a test chosen after seeing the player's strategy.

### Perfect switch completeness

One switch, using one call to A and one to B, returns

    rho_switch = (1/r^2) sum_ij |s_ij><s_ij|.

Every component lies in the accepting subspace, so

    P_switch = 1

for every sampled instance, without postselection.

### Ordinary soundness from the C4 proof

Collect |s_ij> as columns of Z. Write

    W = Z Z^dagger,
    G = Z^dagger Z,
    zeta = ||G-I||_infinity,
    a = r^2/d.

The source proof gives E[zeta] <= a. It also constructs a counterfactual process in which mixture labels do not repeat. For every ordinary q-call strategy with q<=r,

    E Tr(W rho_fresh) <= 1/2 + (10/3)a.

Coupling the true label stream to that process changes the final state by at most

    c = q(q-1)/(2r)

in trace distance.

The new observation is the deterministic operator inequality

    Pi <= W + zeta I.

Proof: the positive eigenvalues of W are the positive eigenvalues of G. Each such eigenvalue lambda satisfies |lambda-1|<=zeta, hence 1<=lambda+zeta. On the kernel of W, Pi is zero. This proof does not require G to be invertible.

Consequently,

    E Tr(Pi rho_fresh)
       <= E Tr(W rho_fresh) + E zeta
       <= 1/2 + (13/3)r^2/d.

Because Pi is a valid effect, the coupling error adds at most c. Thus the game has the query-dependent inequality

    P_ordinary(q) <= min{1, 1/2 + 13r^2/(3d) + q(q-1)/(2r)}.

The expectation is over the fixed hidden Haar draws and the experiment's outcomes. It bounds all ordinary strategies under the source proof's access model.

### Finite substitution

Choose q=2^56=72,057,594,037,927,936. Then

    r^2/d = 2^-16,
    q(q-1)/(2r) = 2^-9 - 2^-65,

and

    P_ordinary
      <= 1/2 + 13/(3*65536) + 1/512 - 2^-65
       = 55563723352636915709 / 110680464442257309696
       < 0.502020.

The resulting game comparison is therefore:

- 2 switched calls: acceptance probability exactly 1.
- At most about 7.2e16 ordinary calls: acceptance probability below 0.502020.

It uses a 256-qubit target, a 256-qubit retained reference, and one control qubit. The referee's description and projection measurement can be enormously costly. No efficient referee, efficient native Haar ensemble, or ordinary noise-diagnostic application is claimed. It is a quantum-output verification game, not the control-bit model-validation game above.

The projection measurement reformulation gives perfect completeness without improving the source C4 trace-distance bound: the ideal and ordinary estimates have simply been redistributed into a perfect ideal score and a correspondingly larger ordinary ceiling.

## Why neither game has an unlimited-query constant gap

At fixed finite d, the manuscript's channel-programming construction supplies, for every epsilon>0, an ordinary simulator of the full switch using at most

    2 ceil[2 d(d-1)/epsilon]

channel calls and half-diamond error at most epsilon. Query cost is finite, although it can be very large. This simulator works uniformly over the input channels and all reference-entangled inputs.

For any referee effect 0<=E<=I, that distance changes its acceptance probability by at most epsilon. Thus Game 2 admits ordinary scores at least 1-epsilon for sufficiently many calls. Game 1 can likewise be approached to arbitrary accuracy; its distinct finite-dimensional channel hypotheses can be learned with finite-error tomography.

Therefore a fixed-dimension bounded-score game cannot have a gap bounded below by a positive constant against every finite ordinary query budget in this unrestricted repeated-access model.

The exact universal obstruction has different quantifiers:

    For each finite budget Q, no simulator reproduces the full switch
    exactly for every CPTP pair.

It does not assert a Q-independent positive approximation gap. A sequence of simulations can approach the switch arbitrarily closely without any finite member being exact. It also does not automatically prove that one particular verification game is never won perfectly at any finite budget: a game may test less than full channel equality.

Games with restrictions on locations, communication, query reuse, or independently refreshed devices are different access models. Their inequalities cannot be inferred from this no-finite universal-simulation statement.
