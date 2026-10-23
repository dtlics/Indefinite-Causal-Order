# Ordinary calibration of Pauli subspaces

<a id="nr-r06-pauli-subspace-calibration"></a>

This is a proof component of [NR-R06](../architecture-baselines.md#nr-r06).
It gives an ordinary estimator for a single commutation statistic,
with exact support and memory assumptions. It does not invoke a lower
bound for learning every channel eigenvalue.

Let the public Pauli-label space be
$\mathcal P_n=\mathbb F_2^{2n}$, with its nondegenerate symplectic
form $[a,b]$ and character $\chi(a,b)=(-1)^{[a,b]}$.
Two fixed stochastic Pauli channels $A,B$ have laws $p,q$.
Every call uses a fresh independent error label, including repeated
calls to the same channel. The task is to estimate

$$
 \eta(p,q)=\mathbb E_{a\sim p,\ b\sim q}\chi(a,b).
 \tag{SC1}
$$

The receiver has $n\ge1$ queried system qubits and $k\ge0$ additional
clean reference qubits. Known global Clifford preparation and readout,
reset, classical adaptation and binary linear algebra are allowed.
There is no supplied controlled unknown channel or unknown inverse.
Fix $0<\varepsilon<1$ and $0<\delta<1$. Logarithms in sample counts
are natural; binary ranks and entropy-free bit counts are integers.

**Weighted low-rank theorem.** If the support of either designated
law lies in an unknown linear Pauli subspace of rank at most $n+k$,
then an ordinary protocol estimates (SC1) within $\varepsilon$,
except with probability $\delta$, using polynomially many calls.
The weights are arbitrary, with no lower bound on a nonzero weight.
Writing $N=n+k$, a concrete bound is

$$
 O\!\left(
 (N+\ln(1/\delta))\frac N\varepsilon
 \left[N+\ln\frac{N+\ln(1/\delta)}{\delta}\right]
 +\varepsilon^{-2}\ln(1/\delta)\right).
 \tag{SC2}
$$

At fixed confidence this is $O(N^3/\varepsilon+\varepsilon^{-2})$.
In particular, rank at most $n$ needs no additional clean references.
The proof below includes all failure records and permits false
empirical constraints; it does not assume exact support recovery.

## Distribution-free empirical-span lemma

Let $\mu$ be any law on $\mathbb F_2^N$, take $m$ independent
samples, and let $W_m$ be their span. For $0<\alpha,\gamma<1$,

$$
 m\ge\frac{2N+8\ln(1/\gamma)}{\alpha}
 \quad\Longrightarrow\quad
 \Pr\{\mu(\mathbb F_2^N\setminus W_m)>\alpha\}\le\gamma.
 \tag{SC3}
$$

While the current span has outside mass greater than $\alpha$, the
next sample expands its dimension with conditional probability greater
than $\alpha$. Couple these increments from below to independent
Bernoulli$(\alpha)$ variables until that outside mass first drops to
$\alpha$; after that stopping time, fill the comparison sequence with
fresh Bernoulli variables. A failure trajectory never reaches the
stopping time and has at most $N$ expansions. Therefore its probability
is at most

$$
 \Pr\{\operatorname{Bin}(m,\alpha)\le N\}
 \le e^{-m\alpha/8}\le\gamma,
$$

because $m\alpha\ge2N$. This proves (SC3) without conditioning fresh
samples on the final successful-span event or assuming minimum masses.

## Random stabilizer probes and their hidden annihilator

First suppose $p$ has the rank promise. Enlarge the channel to
$A\otimes\operatorname{Id}_k$ on $N$ qubits. The actual error labels
have zero helper coordinates and lie in some unknown
$V\le\mathcal P_N$, with $r=\dim V\le N$. Set $T=V^\perp$;
then $\dim T=2N-r\ge N$.

Choose a uniform known Lagrangian $M\le\mathcal P_N$, of dimension
$N$. Prepare its stabilizer state, query $A$, and measure those
stabilizers. A known Clifford and terminal computational measurement
implement this experiment on the counted register. If error $a$
occurs, its syndrome is the linear functional
$\pi_M(a):x\mapsto[a,x]$ on $M$.

From $m$ observed syndromes form their empirical span $W_M$, and
compute its annihilator **inside $M$**:

$$
 K_M=\{x\in M:y(x)=0\text{ for every }y\in W_M\}.
 \tag{SC4}
$$

For every data set, $M\cap T\subseteq K_M$, because all actual labels
lie in $V$. The reverse inclusion can fail: empirical data can create
false constraints. Nevertheless, on the event in (SC3),

$$
 \Pr_{a\sim p}\{[a,x]=1\}
 \le\Pr\{\pi_M(a)\notin W_M\}\le\alpha
 \quad\text{for every }x\in K_M.
 \tag{SC5}
$$

Indeed, every functional in $W_M$ vanishes on $x\in K_M$.
One empirical-span event controls all $x$ simultaneously.

The required geometric fact is that independent uniform Lagrangians
$M_1,\ldots,M_K$ expose enough of $T$. Suppose the span $S_0$ of
the intersections seen so far is a proper subspace of $T$. Put
$A_0=T\setminus S_0$, $d=2^N$, and $Y=|A_0\cap M|$ for a fresh
uniform Lagrangian. Then $|A_0|\ge|T|/2\ge d/2$.
Every fixed nonzero label belongs to $M$ with probability
$1/(d+1)$: average the $d-1$ nonzero elements of $M$ over the
$d^2-1$ nonzero labels. For two distinct commuting nonzero labels,
the probability is

$$
 \frac1{(d+1)(d/2+1)}
 =\frac2{(d+1)(d+2)}
 \le\frac2{(d+1)^2};
 \tag{SC6}
$$

conditional on the first label, take the symplectic quotient by its
span. A noncommuting pair has inclusion probability zero. Thus, with
$\mu=\mathbb EY=|A_0|/(d+1)\ge1/3$,

$$
 \mathbb EY^2\le\mu+2\mu^2,\qquad
 \Pr(Y>0)\ge\frac{\mu^2}{\mathbb EY^2}
 \ge\frac{\mu}{1+2\mu}\ge\frac15.
 \tag{SC7}
$$

Each such event increases $\dim S_0$. At most $2N$ increases are
needed. The same stopped-process domination used in (SC3), now with
Bernoulli$(1/5)$, proves

$$
 K=\left\lceil5[4N+8\ln(4/\delta)]\right\rceil
 \quad\Longrightarrow\quad
 \Pr\{\operatorname{span}_i(M_i\cap T)\ne T\}\le\delta/4.
 \tag{SC8}
$$

The comparison binomial has mean at least $4N+8\ln(4/\delta)$, so its
probability of at most $2N$ successes is at most $\delta/4$.
This geometric statement depends only on the random settings, not on
conditioning them on successful syndrome learning.

## A computable space carrying almost all error mass

Use (SC8), and choose

$$
 \alpha=\frac{\varepsilon}{8N},\qquad
 m=\left\lceil
 \frac{2N+8\ln(4K/\delta)}{\alpha}\right\rceil.
 \tag{SC9}
$$

At each setting take $m$ fresh outputs, compute $K_{M_i}$, and form
$S=\operatorname{span}_i K_{M_i}$. A union bound makes (SC5) valid
for all settings except with probability $\delta/4$.
Independently of the data, (SC8) ensures $S\supseteq T$ except with
probability $\delta/4$.

Choose a basis of $S$ greedily from the individual $K_{M_i}$ bases.
Each selected vector remains in a specific source $K_{M_i}$; there
are at most $2N$ such vectors. On the simultaneous good event, (SC5)
and a union bound over this selected basis give

$$
 V'=S^\perp\subseteq V,\qquad
 \dim V'\le r\le N,\qquad
 p(V')\ge1-2N\alpha=1-\varepsilon/4.
 \tag{SC10}
$$

The containment follows from $S\supseteq V^\perp$. The mass bound
uses at most $2N$ constraints, not all exponentially many vectors of
$S$. In fact the mass bound holds on the empirical good event alone;
the geometric event supplies the dimension bound. False constraints
may remove low-probability errors, which is permitted by (SC10).

## Injective syndrome sampling on a known rank-at-most-$N$ space

For any known $V'\le\mathcal P_N$ of rank $r'\le N$, construct a
known Lagrangian $M_0$ disjoint from it. Symplectic elimination puts
$V'$, by a known Clifford frame, into the form

$$
 \operatorname{span}\{X_i,Z_i:1\le i\le s\}
 +\operatorname{span}\{Z_{s+j}:1\le j\le c\},
 \qquad 2s+c=r'.
 \tag{SC11}
$$

There are $\ell=N-s-c\ge s$ untouched qubits. Bell-pair each of the
$s$ symplectic-pair qubits with a distinct untouched qubit, put the
$c$ central qubits in $|+\rangle$, and stabilize the remaining
untouched qubits in a product state. This has a rank-$N$ stabilizer:
two Bell generators per pair, one central $X$ per central qubit, and
one generator per unused qubit. Any nontrivial Bell contribution has
a nonzero partner coordinate; any central $X$ lies outside the
central $Z$ span. Therefore its intersection with (SC11) is zero.
Undo the known frame to obtain $M_0\cap V'=\{0\}$.

The syndrome map $\pi_{M_0}|_{V'}$ is consequently injective.
One query of $A$ on this stabilizer state and its stabilizer readout
decode the realized $a$ whenever $a\in V'$. Use binary linear
algebra to invert on the known image; return a fixed default label
outside that image. Errors outside $V'$ can collide with its image,
but the coupling below already charges their entire probability.

Define the protocol on every record. If calibration produces
$\dim V'>N$, return the fixed estimate zero. For $k>0$, before a
decoded $N$-qubit label is used to probe $B$, return the system
identity label if any helper coordinate is nonzero; otherwise drop
its zero helper coordinates. Use the system identity for every other
decoding failure. On the good event $V'\subseteq V$, its labels
have zero helper coordinates, so correctly decoded events are
unaffected. Coupling the decoded system label $\widetilde a$ to the
actual $a$ whenever $a\in V'$ proves

$$
 \operatorname{TV}(\widetilde p,p)
 \le p(\mathcal P_N\setminus V')\le\varepsilon/4.
 \tag{SC12}
$$

All Bell pairs in this construction lie inside the counted $N=n+k$
register. For $k=0$, they use queried system qubits, not additional
clean references.

## Final scalar sampling and resource ledger

Freshly sample $\widetilde a$ as above. Prepare a known $+1$
product eigenstate of its system Pauli $P_{\widetilde a}$, query
$B$, and measure that Pauli. For a realized $b$, the outcome is
$\chi(\widetilde a,b)$; for identity, return the known value $+1$.
The bounded outcome $Y$ therefore satisfies

$$
 \mathbb EY=\eta(\widetilde p,q),\qquad
 |\eta(\widetilde p,q)-\eta(p,q)|
 \le2\operatorname{TV}(\widetilde p,p)\le\varepsilon/2.
 \tag{SC13}
$$

Take
$R=\lceil8\varepsilon^{-2}\ln(4/\delta)\rceil$
independent paired trials. Conditional on the calibration records,
fresh stationarity gives the same decoded law in every trial.
Hoeffding bounds deviation from (SC13)'s mean by $\varepsilon/2$
except with probability $\delta/2$. Together with the two
calibration failures, the total failure probability is at most
$\delta$. Calibration uses $Km$ calls to $A$; the final stage
uses $R$ calls to each channel, hence at most $Km+2R$ calls in
total, giving (SC2). Swap the channel roles when $q$ is designated.

If only the promise that *one* law is low-rank is supplied, run both
calibrations with $\delta/2$ in (SC8)–(SC9) and select any computed
space of rank at most $N$. At least the promised side
qualifies on its geometric good event. For either selected side, the
empirical good event alone gives the mass part of (SC10), which is
enough for the same decoding coupling. Even if the selected true support
has high rank, every actual error in its computed $V'$ has zero
helper coordinates, so the helper fallback preserves those correctly
decoded events. If neither qualifies, return zero. Combined calibration
failure is at most $\delta/2$; retain the final $\delta/2$ sampling
budget. This changes constants, not (SC2).

Sampling uniform Lagrangians, constructing their Clifford circuits,
spans, annihilators, bases, the known normal form and label inverses
all use polynomial binary linear algebra. The known Clifford gate
count is polynomial in $N$, as are classical computation and total
control count with the displayed query budget. Preparation, reset,
readout, control duration and errors remain physical costs; this is
not a claim that global Clifford gates are cheap native operations.

## Uniform subspaces of arbitrary ranks

<a id="nr-r06-uniform-subspace-cutoff"></a>

An exact uniform-law promise gives a broader ordinary algorithm with
no additional references. Let $p=\operatorname{Unif}(V)$ and
$q=\operatorname{Unif}(W)$, with arbitrary ranks $r,s$.
If the restricted pairing $V\times W\to\mathbb F_2$ has rank $h$,
character orthogonality gives

$$
 \eta=2^{-h}\ge0,\qquad
 h=r-\dim(V\cap W^\perp)\ge r+s-2n.
 \tag{SC14}
$$

For any integer cutoff $C\ge0$, the geometric proof extends to
$r\le n+C$: now $\dim T\ge n-C$,
$|T\setminus S_0|\ge2^n/2^{C+1}$, and the first moment is at least
$2^{-C}/3$. Equation (SC7)'s argument gives expansion probability
at least $\nu=2^{-C}/5$. If $T=\{0\}$, it is already fully known.
Choose

$$
 \begin{split}
 C&=\left\lceil\tfrac12\log_2(2/\varepsilon)\right\rceil,
 &\nu&=2^{-C}/5,\\
 K&=\left\lceil[4n+8\ln(8/\delta)]/\nu\right\rceil,
 &m&=n+\left\lceil\log_2(8K/\delta)\right\rceil .
 \end{split}
 \tag{SC15}
$$

Uniform error labels give uniform syndromes on $\pi_M(V)$.
If that syndrome space has dimension $h_M\le n$, failure of $m$
samples to span it means some nonzero functional on that space
vanishes on every sample. A union bound gives failure at most
$(2^{h_M}-1)2^{-m}\le\delta/(8K)$.
Across both channels and all $K$ settings, the total rank-failure
probability is at most $\delta/4$.

On this exact-span event the computed $K_M$'s equal their true
intersections. Thus their spans satisfy
$S_A\subseteq V^\perp$ and $S_B\subseteq W^\perp$.
The independent geometric comparison completes every annihilator
whose error rank is at most $n+C$, except with probability
$\delta/8$ per channel. Its binomial comparison has mean at least
$4n+8\ln(8/\delta)$ and needs at most $2n$ expansions.

If either computed span has dimension at least $n-C$, choose that
channel. It is complete on the good event: for example
$S_A\subseteq V^\perp$ and $\dim S_A\ge n-C$ imply $r\le n+C$,
exactly the range of the completeness guarantee. Hence $V=S_A^\perp$
is known. Draw $a$ uniformly from this known space **classically**,
then query $B$ on an eigenstate of $P_a$. Each bounded outcome has
mean (SC1); no further $A$ call is required. If $C\ge n$, every
actual rank is in the covered range and the nonpositive threshold
causes no problem.

If neither span reaches the threshold, both ranks exceed $n+C$
on the good event. By (SC14),
$\eta\le2^{-2C}\le\varepsilon/2$; return zero.
In the sampling branch,
$R_u=\lceil2\varepsilon^{-2}\ln(4/\delta)\rceil$
fresh outcomes estimate the mean within $\varepsilon$ except with
probability $\delta/2$. The rank failures, geometric failures and
final sampling failure sum to at most $\delta$. Calibration uses
$2Km$ calls; the final branch uses at most $R_u$ calls, for

$$
 O\!\left(
 \varepsilon^{-1/2}(n+\ln(1/\delta))
 \left[n+\ln\frac{n+\ln(1/\delta)}{\varepsilon\delta}\right]
 +\varepsilon^{-2}\ln(1/\delta)\right).
 \tag{SC16}
$$

This is an achievable upper bound at all ranks, not an ordinary
hardness result.

### Uniform affine cosets

For $p=\operatorname{Unif}(a_0+V)$, pair successive syndrome
observations and subtract them. The $m$ disjoint differences are
fresh uniform samples on $\pi_M(V)$, costing $2m$ calls per
setting. On exact rank recovery, any original observation supplies
the deterministic bit $[a_0,x]$ for each $x\in K_M$. Keep source
offsets when selecting an annihilator basis. Once $V^\perp$ is
complete, solve its known linear equations for any representative
of $a_0+V$; its affine law is then classically sampleable.
If recorded offset equations are inconsistent on a failed data set,
return the fixed estimate zero. On the good event they are consistent.

For a second affine law on $b_0+W$, averaging over $W$ first leaves
only labels $a\in(a_0+V)\cap W^\perp$. That intersection is empty or
a coset of $V\cap W^\perp$, occupying a $2^{-h}$ fraction of $V$.
The remaining phase has absolute value one. Consequently

$$
 |\eta|\le2^{-h}\le2^{\,2n-r-s}.
 \tag{SC17}
$$

The same high-rank zero return and finite failure ledger apply even
when $\eta$ is negative. Only calibration's factor-two call cost
changes.

## Verification scope and limits

The self-contained standard-library
[exact checker](../checks/architecture/verify_pauli_subspace.py)
replays finite symplectic geometry, empirical false-constraint and
uniform-law guards. Its public API is
$\texttt{verify\_pauli\_subspace()}$; its JSON CLI rejects optimized
Python that would remove assertions. The distribution-free, all-$N$
sample bounds and resource guarantees are proved above, rather than
inferred from finite enumeration.

The weighted theorem requires **exact** linear support rank at most
$n+k$. An arbitrarily small off-subspace contamination can remove
true annihilator constraints; this proof is not a robust-outlier
learner. Unknown SPAM, changing frames, drift, temporal bath memory
and unpriced global controls are outside its guarantee. High
$\eta$ does not by itself imply a low-rank exact support or the
uniform-subspace promise. The result supplies an ordinary scalar
estimator and closes those structured candidate families. It is
neither a decoder nor a demonstrated native advantage, and it does
not settle the general nonuniform high-rank scalar problem.
