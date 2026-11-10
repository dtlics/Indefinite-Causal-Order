<a id="nr-r25"></a>

# Finite-family and product-local ordinary learning baselines

[Investigation handoff](README.md) · [Application assessment](../architecture.md)

**Status and scope.** Current negative boundaries for the main application search. The finite-family result is sample-efficient but can require exponentially expensive known processing; it is not a new threshold-search theorem. These are supplied analytic derivations and scoped computational checks, not a new Lean audit or a publication-priority claim. See [verification scope](checks/README.md).

## Status

This is a direct reduction to the published quantum threshold-search theorem of Badescu and O'Donnell, *Improved quantum data analysis*, TheoretiCS 3, article 7 (2024), Theorem 1.1, arXiv:2011.10908v4. It is not a new shadow-tomography theorem or a claim of publication priority. It was developed in this audit to check whether replacing an arbitrary Haar basis by a short-key or short-circuit family retains an unrestricted ordinary-query lower bound.

The result addresses query/sample cost. The known processing can be exponentially expensive in the key length. It is not a practical efficient-learning algorithm for an exponentially large candidate list.

## Proposition

Let d>=2. Let U_1,...,U_K be a known finite family of possible bases. The actual index k is unknown and fixed throughout the experiment. Suppose the black-box memoryless channel is promised to be either

E_{p,k}=(1-p)id+p Delta_{U_k},

for some k, or

M_p=(1-p)id+p Lambda, Lambda=(id+d Omega)/(d+1),

with known 0<p<=1. Device measurement outcomes and environments are not accessible. An ordinary quantum learner may retain entangled memory and implement arbitrary known quantum operations.

Then the decision problem has an ordinary protocol using

O(log^2(K+1)/p)

expected device calls at fixed confidence. A comparable fixed maximum budget follows by allocating a constant failure budget to acquiring sufficiently many accepted states. The cost of the postprocessing is not bounded by this statement.

## 1. One ordinary call gives a normalized Choi state

Let Phi_d be the normalized Bell projector. Define

Pi_k=sum_i (P_i^{U_k})^T tensor P_i^{U_k}.

The d summands are orthogonal rank-one projectors. Thus Pi_k is a rank-d projector, and Pi_k Phi_d=Phi_d. Directly,

J(Delta_{U_k})=Pi_k/d,
J(Lambda)=(Phi_d+I/d)/(d+1).

Consequently,

J(E_{p,k})=(1-p)Phi_d+(p/d)Pi_k,
J(M_p)=(1-p)Phi_d+p(Phi_d+I/d)/(d+1).

Preparing Phi_d and applying the unknown channel to one half costs one ordinary call. Repeating gives independent Choi states, conditional on the same fixed k.

## 2. Remove the common identity component without learning the hidden basis

Perform the known two-outcome projective measurement {Phi_d,Q}, where Q=I-Phi_d, retaining the state only for outcome Q. This is a coherent coarse-grained Bell-return test, not a complete Bell-basis measurement that resolves additional labels.

Under BOTH hypotheses, outcome Q has probability

r=p(1-1/d).

Conditioned on Q, the retained states are

sigma_k=(Pi_k-Phi_d)/(d-1),
sigma_0=Q/(d^2-1).

The hidden alternative is maximally mixed on an unknown (d-1)-dimensional subspace. The model is maximally mixed on the known full (d^2-1)-dimensional complement.

No hidden device outcome has been measured. The learner has measured a publicly specified observable of its own target/reference output.

## 3. Known tests for every candidate

For each candidate, define the known projector A_k=Pi_k-Phi_d. Then

Tr(A_k sigma_k)=1,
Tr(A_k sigma_0)=(d-1)/(d^2-1)=1/(d+1)<=1/3.

The learner does not know which A_k is the matching one. It does know the candidate list and can in principle implement every A_k. This does not grant the true hidden basis as free advice.

Use quantum threshold search with threshold theta=3/4, tolerance epsilon=1/4, and fixed failure delta. Its valid outputs are either an index j with Tr(A_j sigma)>1/2, or the conclusion that all expectations are <=3/4. Under sigma_0 only the latter is valid. Under any sigma_k, the latter is false, so a valid output identifies the alternative.

Theorem 1.1 requires O(log^2(K+1)) copies for these fixed constants, independent of the Hilbert-space dimension. Known operations can act jointly on copies. This is not the ordinary single-copy classical-shadows protocol.

## 4. Count rejected calls

To collect m accepted states requires mean m/r ordinary queries, i.e.

m/[p(1-1/d)] <= 2m/p.

A hard budget of C(m+log(1/delta))/r gives enough accepted copies with the desired probability by an ordinary binomial tail bound; aborted acquisition runs count as failed decisions. For fixed confidence the total is O(log^2(K+1)/p).

If p is unknown, a positive lower promise or a sequential stopping convention is necessary. Acquiring a fixed number of accepted states still has the displayed expected cost for every p>0. No uniform finite budget exists as p tends to zero and the hypotheses coincide.

## 5. Robust candidate cover

The argument also permits a known finite cover. Suppose the actual hidden-dephasing Choi state is within trace distance tau of one candidate. On the coarse-grained Q branch the success probability is unchanged because F_e=1/d for every dephaser; the normalized residual-state distance is at most d tau/(d-1)<=2 tau. The matching test then accepts with probability at least 1-2 tau. For sufficiently small constant tau, threshold search retains a constant gap.

For the weak channels, their prefilter distance scales by p and their filter probability scales by p, so the needed accuracy of the underlying dephaser cover remains constant, not proportional to p.

A promise that U is generated by an s-bit known description family gives K<=2^s and O(s^2/p) expected calls. A polynomial-size circuit family over a fixed finite gate alphabet has polynomial description length in n; enumerating it need not be computationally efficient. Continuous gate families can be discretized at a sufficiently accurate circuit norm, with a cover size determined by the number of parameters and the desired accuracy.

## Consequence for the application search

This rules out an information-theoretic exponential ordinary-query lower bound for this matched-dephasing test on a known polynomial-description-length family, under the unrestricted known-processing and collective-memory model. It does NOT rule out a computational separation from efficient ordinary learners, a huge processing/gate cost, finite parameter regimes where the polynomial bound is large, or other channel families/tasks with small normalized-Choi separation.

It does not contradict the Haar theorem: an arbitrary Haar basis cannot be replaced, at fixed accuracy, by a family with polynomial description length. Its required net can have log K scaling as a power of d. It is also consistent with the repository's careful statement that keyed pseudorandom constructions give computational hardness rather than the same unbounded-learner information-theoretic query bound.

This is the strongest additional baseline found in the present audit. It demonstrates why “sample once and keep fixed” is mathematically consistent with hardness, while the choice of physically motivated candidate family remains decisive.

## 1. The natural local-noise replacement for a hidden global basis is not comparably hard

Consider n independent qubits with unknown fixed unit vectors a_j. Let R_j=a_j dot sigma be their Hermitian Pauli-axis reflections. On qubit j, promise either

E_j=(1-p)id+p Delta_{a_j},

or the known local depolarizing map

M=(1-2p/3)id+(2p/3)Omega_2.

The full device is the tensor product over j, and a full-register invocation counts as one call. These channels have matching one-use average fidelities locally. Outcome records and the axes remain hidden. Ordinary quantum memory and entangled probes are allowed.

After k calls to the same subsystem,

E_j^k=(1+r)/2 id+(1-r)/2 Ad_{R_j}, r=(1-p)^k,

M^k=b id+(1-b)Omega_2, b=(1-2p/3)^k.

Let Phi be the Bell projector and Q=I-Phi the rank-three complementary subspace. Their normalized Choi states have

J(E_j^k)=(1+r)/2 Phi+(1-r)/2 |R_j>><<R_j|/2,

J(M^k)=(1+3b)/4 Phi+(1-b)/4 Q,

where |R_j>>/sqrt(2) is a unit vector in Q.

### A two-copy ordinary experiment

Prepare two independent Choi states by sending halves of Bell pairs through k-contact blocks of the actual channel. On each site's two Choi states, measure the fixed positive effect

T_j=(Q tensor Q)(I-SWAP)/2.

This requires only known Bell-subspace projectors and a SWAP test. It needs no hidden-axis description or device-outcome record.

For the structured channel, its nonidentity Choi component is the same rank-one state in both copies. The antisymmetric projection never clicks.

For the depolarizing channel,

Pr(T_j)=3(1-b)^2/16=:t.

The factor three is the dimension of the antisymmetric subspace of a three-dimensional error space. Errors across sites are independent by the product-channel promise. Therefore one complete experiment on n sites has

Pr(no click | depolarizing)=(1-t)^n,

Pr(any click | structured)=0.

All 2k full-register calls, two sets of retained reference systems, state preparations and joint measurements count. The experiment can use up to 4n qubits for its two Choi-state preparations. Restricting the ordinary learner's quantum memory would be a different task.

### Concrete numbers

Set n=32, p=0.01, k=280. Then

Pr(miss)=(1-3[1-(149/150)^280]^2/16)^32
        =0.009902805862335... <0.01.

Thus 560 ordinary full-register calls suffice for a worst-case 99%-accurate classification for every choice of hidden local axes. The exact rational inequality is checked by `check.py`.

### Relation to the natural switch test

On two k-contact blocks the structured self-switch always gives plus. The depolarizing self-switch gives minus with probability

p_minus_switch=[1-(1-4t)^n]/2.

Its one-trial miss probability is [1+(1-4t)^n]/2. For 0<=t<=3/16,

(1-t)^3 <= 1-2t,

and convexity of x^n on [0,1] gives

(1-2t)^n <= [1+(1-4t)^n]/2.

Hence three ordinary two-copy trials have no larger miss probability than one of these switch trials at the same block length. This is a concrete comparison of the natural tests, not a lower bound against every imaginable switched strategy. It prevents presenting their scalar signal as an exponential local-noise advantage.

Known Pauli-channel promises are even easier: Bell measurements sample Pauli error labels directly. A known classical error model does not require tomography merely to estimate a commutation sign.

