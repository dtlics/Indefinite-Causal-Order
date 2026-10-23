# Ordinary tests for the structured commuting-burst memory

This is a proof component of [NR-R20](../memory-qualification.md#nr-r20).
It owns explicit qualification algorithms and a restricted lower bound.
The [general Pauli-subspace calibration method](pauli-subspace-calibration.md)
instead learns enough geometry to estimate commutation statistics for
arbitrary weighted laws. No lower bound here concerns arbitrary hidden
Haar bases or every ordinary adaptive receiver.

Let $G=\mathbb F_2^{2n}$ have symplectic form $[a,b]$, let $D=2^n$, and
let $L=L^\perp\leq G$ be an unknown fixed Lagrangian. Consider

$$
H_1:\ \mathcal E_1=(1-t)\operatorname{id}+t\mathcal P_L,\qquad
H_0:\ \mathcal E_0=(1-t)\operatorname{id}+t\Omega,\qquad
\mathcal P_L=D^{-1}\sum_{a\in L}\operatorname{Ad}_{P_a}.             \tag{O1}
$$

The physical Pauli axes are public. Every call redraws its error
independently; $L$ stays fixed. A supplied $0<t_{\min}\leq t$ suffices
for the finite guarantees. The algorithms see no error labels or
production flags. Take $0<\delta\leq1/4$. Fresh probes are measured
and reset; they do not preserve an unknown payload. Preparation,
readout, classical memory, reset and known controls are physical costs,
as specified in the [native screen](memory-native-cost.md).

## Zero-reference random-stabilizer rank test

Choose a uniformly random known Lagrangian $M$, prepare its pure
stabilizer state and measure its $n$ generators after one channel call.
Known global Clifford preparation and computational readout implement
this without additional references. The full syndrome is the linear
projection $\pi_M(a)(m)=[a,m]$. For $W=\pi_M(L)$ its laws are

$$
H_1:\ (1-t)\delta_0+t\operatorname{Unif}(W),\qquad
H_0:\ (1-t)\delta_0+t\operatorname{Unif}(\mathbb F_2^n),\qquad
\dim W=n-\dim(L\cap M).                                         \tag{O2}
$$

Any nonzero functional on the relevant support is one with probability
$t/2$. Failure of $N$ samples to span that support requires some
nonzero functional to vanish on every sample. A union bound gives

$$
\Pr[\text{failure to span}]\leq(2^n-1)(1-t/2)^N
 \leq2^n e^{-tN/2}.                                             \tag{O3}
$$

If $L\cap M\ne\{0\}$, the $H_1$ empirical rank is always below $n$.
Uniform $M$ has this property with probability at least $1/3$, for
every $L$. The total number of Lagrangians is
$\prod_{j=1}^n(2^j+1)$: counting a Lagrangian together with one of its
nonzero vectors gives the recurrence $N_n=(2^n+1)N_{n-1}$ by quotienting
by a fixed isotropic line. The $2^{n(n+1)/2}$ transverse Lagrangians are
graphs of symmetric binary matrices over a complementary Lagrangian.
Therefore

$$
\Pr[M\cap L=\{0\}]=\prod_{j=1}^n(1+2^{-j})^{-1}\leq2/3.          \tag{O4}
$$

Take independent settings and per-setting shots

$$
K=\left\lceil\frac{\ln(2/\delta)}{\ln(3/2)}\right\rceil,\qquad
N=\left\lceil\frac2{t_{\min}}
 \left(n\ln2+\ln\frac{2K}{\delta}\right)\right\rceil.              \tag{O5}
$$

Declare $H_1$ if any empirical rank is below $n$, and $H_0$ otherwise.
Under $H_0$, (O3) and the union bound make error at most $\delta/2$.
Under $H_1$, a false-$H_0$ outcome requires all settings to be transverse,
of probability at most $(2/3)^K\leq\delta/2$; sampling in a transverse
setting can only reduce that error. The hard call count is

$$
KN=O\!\left(\frac{n+\ln(K/\delta)}{t_{\min}}\ln\frac1\delta\right).
                                                               \tag{O6}
$$

This is one call per fresh probe, with no concatenation or recovery of $L$.

## Partial-Bell relation test with local target controls

Give the receiver $1\leq k\leq n$ clean reference qubits and put $m=n-k$.
On $k$ target sites $R$, prepare Bell pairs with that bank; on the other
$m$ sites $M$, prepare $|0\rangle$. Bell and computational readout
after one call reveal $r=(x_R,z_R)\in\mathbb F_2^{2k}$ and
$x=x_M\in\mathbb F_2^m$; $z_M$ remains hidden. The peak reference bank
is $k$, reset between calls. No global target Clifford is required
beyond the Bell-pair operations.

For $T$ calls, arrange referenced, observed local and hidden coordinates
as matrices $R,X,Z$ of sizes $2k\times T,m\times T,m\times T$.
Let $J_R$ be the referenced symplectic matrix and let $K_X$ span
$\ker X$. Reject $H_1$ if

$$
K_X^TR^TJ_RRK_X\ne0.                                           \tag{O7}
$$

Under $H_1$, all errors, including identity, are in $L$, so their full
Gram matrix is $R^TJ_RR+X^TZ+Z^TX=0$. Multiplying by $K_X^T,K_X$
eliminates the hidden terms. Thus (O7) never rejects, for every stream
and every $L$. Soundness extends to any Pauli law with commuting support.

For detection under $H_0$, introduce only for analysis the active
production set $A$ of size $B$. Conditional on $A$, active errors are
independent uniform vectors of $G$ and inactive columns are zero.
If $B\geq m+2$, then $\ker X_A$ contains independent $c,d$, chosen
from $X_A$ alone. Conditional on $X_A$, $R_Ac,R_Ad$ are independent
uniform vectors of $\mathbb F_2^{2k}$: each uniform row of $R_A$ maps
surjectively to its two products with $c,d$. Consequently

$$
\Pr([R_Ac,R_Ad]=1\mid X_A,A)=\frac{1-4^{-k}}2\geq3/8.            \tag{O8}
$$

The first vector is nonzero with probability $1-4^{-k}$; half of all
second vectors anticommute with each nonzero first vector. Extend
$c,d$ by zero outside $A$. They belong to $\ker X$, so this event
makes (O7) nonzero without the receiver identifying $A,c,d$.

Use a batch of

$$
T=\left\lceil\frac{8(m+2)}{t_{\min}}\right\rceil.                  \tag{O9}
$$

Then $B\sim\operatorname{Bin}(T,t)$ has mean $\mu\geq8(m+2)$, and
the multiplicative Chernoff inequality gives

$$
\Pr[B<m+2]\leq e^{-49\mu/128}
 \leq e^{-49(m+2)/16}\leq e^{-49/8}<1/9.
$$

One-batch rejection probability is therefore at least $(3/8)(8/9)=1/3$.
Use $b=\lceil\ln(1/\delta)/\ln(3/2)\rceil$ independent batches, reporting
$H_0$ on any rejection. The $H_1$ error is zero, the $H_0$ error is
at most $(2/3)^b\leq\delta$, and the hard call count is

$$
bT=O((n-k+2)t_{\min}^{-1}\ln(1/\delta)).                         \tag{O10}
$$

At $k=1$ this is $O(n/t)$ at fixed confidence with local target
controls. At $k=n$ it is $O(t^{-1}\ln(1/\delta))$: retaining labels
across calls avoids waiting for two active errors in the same trial.

The computation can stream. Keep at most $m$ independent $x$ pivots
with their accompanying $r$ values and reduce each new $(x,r)$ by the
same binary eliminations. A zero residual $x$ gives an $r\in R(\ker X)$;
all such residuals span that image, since each dependent column supplies
a standard kernel relation. Maintain their basis and symplectic
brackets. Until rejection it is isotropic and has dimension at most $k$.
A straightforward implementation uses $O(n^2)$ classical bits and
$O(n^2)$ bit operations per record. Erroneous Bell/syndrome records can
cause spurious rejection; arbitrary-SPAM robustness is not proved.

## Exact lower bound for a fixed probe layout

For this subsection only, $H_1$ draws $L$ uniformly from all Lagrangians
and then reuses it. Grant the receiver the independent production flags,
an enlarged experiment whose lower bound also holds without flags.
Keep one fixed stabilizer/Bell layout with $k<n$ references and $m=n-k$.
A fixed known global Clifford change of layout is allowed: uniformity
of the prior permits the same coordinates used above.

Every Pauli sends the fresh pure probe to one of $2^{n+k}$ known
orthogonal states, up to phase. The full distinguishable record is
$c=(r,y)$ with $r=(x_R,z_R)$ and $y=x_M$. Each output is diagonal in
this same basis; fresh-probe products remain diagonal in its product
basis even after mixing over $L$. Revealing all $c$ therefore dominates
arbitrary collective measurements and processing of these outputs.
Changing fixed stabilizer signs merely relabels records.

The class excludes changing layouts, nonstabilizer inputs and feeding
retained unknown outputs into later calls. These are allowed in the full
ordinary model and are not bounded here. The argument bounds the entire
fixed-probe experiment, rather than just a particular rank statistic.

Condition on $0\leq T\leq m$ burst calls and form observed $R,Y$ and
hidden $Z$. On $\operatorname{rank}Y=T$ the errors are independent and

$$
R^TJ_RR+Y^TZ+Z^TY=0.                                           \tag{O11}
$$

Each fixed ordered independent isotropic error tuple has $H_1$ probability

$$
c_T=D^{-T}\prod_{j=0}^{T-1}(2^{n-j}+1)^{-1}.                     \tag{O12}
$$

Successively quotienting by included isotropic lines gives probability
$(2^{n-j}+1)^{-1}$ that the next line is in a random Lagrangian of
the $2(n-j)$-dimensional quotient. Conditional on containing the tuple,
the independent draws give weight $D^{-T}$.

For full-column-rank $Y$, $Z\mapsto Y^TZ+Z^TY$ is onto alternating
$T\times T$ matrices: $Y^TZ$ can be any matrix and $A\mapsto A+A^T$
is onto that space in characteristic two. It has rank $T(T-1)/2$,
so (O11) has exactly $2^{mT-T(T-1)/2}$ solutions, independently of
$R,Y$. Every lift is an independent isotropic tuple. Under $H_0$
each record stream has probability $2^{-(n+k)T}$. The likelihood ratio
on the full-rank event is therefore constant:

$$
\ell_T=\prod_{j=0}^{T-1}(1+2^{j-n})^{-1}.                        \tag{O13}
$$

Both conditional record distributions on that event are the same
uniform law. The exact masses are

$$
g_0=\prod_{j=0}^{T-1}(1-2^{j-m}),\qquad
g_1=\prod_{j=0}^{T-1}\frac{1-2^{j-m}}{1+2^{j-n}}.
$$

Coupling their shared uniform component of mass $g_1\leq g_0$ gives

$$
\operatorname{TV}(P_1^T,P_0^T)\leq1-g_1
 \leq(2^T-1)(2^{-m}+2^{-n}).                                    \tag{O14}
$$

For the final inequality, the deficit of $(1-a)/(1+b)$ is at most
$a+b$, and the deficit of a product in $[0,1]$ is at most the sum
of deficits. Empty products include $T=0$.

For $Q$ total calls, the common flags contain $M\sim\operatorname{Bin}(Q,t)$
bursts. Condition on the flags; use (O14) on $M\leq h=\lfloor m/2\rfloor$
and the trivial bound otherwise. Since $h+1>m/2$, Markov gives

$$
\operatorname{TV}(P_1^{(Q)},P_0^{(Q)})
 \leq\frac{2Qt}{m}+2^{1-\lceil m/2\rceil}.                       \tag{O15}
$$

This yields a fixed-confidence $\Omega((n-k)/t)$ lower bound in this
class. It includes adaptive classical stopping under a mean budget:
if the maximum of the two hypothesis means is $q$, truncate at $Q$.
Both tail probabilities are at most $q/Q$. Pad the truncated
experiment with unused fixed-layout samples and use data processing:

$$
\operatorname{TV}(\text{full stopped transcripts})
 \leq\frac{2q}{Q}+\frac{2Qt}{m}+2^{1-\lceil m/2\rceil}.            \tag{O16}
$$

For $m\geq16$, $Q=\lceil m/(32t)\rceil$ and $q\leq m/(1536t)$,
this is at most $1/24+1/16+2/m+1/128<1/3$. Equal-prior success
$2/3$ needs total variation at least $1/3$, so such a mean budget
cannot suffice. The $H_1$ mean averages over its fixed random $L$;
a uniform worst-case mean guarantee is stronger and is also excluded.

Conditioning $L$ to have no nonzero Pauli of weight at most $w$
excludes prior mass at most
$\gamma\leq\sum_{j=1}^w3^j\binom nj/(D+1)$. Conditioning changes
any $H_1$ transcript law by at most $\gamma$; add that correction
to (O14)–(O16). For the explicit mean-budget constants above,
$\gamma\leq1/24$ still leaves the bound below $1/3$.

For $k\geq1$ and large $m$, (O10) matches this fixed-layout lower
bound's $m/t$ dependence at fixed confidence. It proves no optimality
against changing layouts, nonstabilizer inputs or coherent multiquery
strategies. An adaptively chosen Lagrangian can contain half of a
previously observed nonzero affine syndrome coset; treating every
adaptive intersection as exponentially rare is invalid.

## Reuse and verification scope

If one nonzero $b\in L$ is known, prepare a product $+1$ eigenstate
of $P_b$ and read its parity after a query. Minus probabilities are
$0$ and $t/2$, so $\lceil(2/t_{\min})\ln(1/\delta)\rceil$ calls
suffice. One usable known direction can remove the initial difficulty
without learning an entire basis or encoder.

The finite exact guards are the
[partial-Bell relations check](../checks/architecture/verify_memory_partial_bell.py)
and [fixed-layout likelihood check](../checks/architecture/verify_memory_fixed_probe.py).
They check small-instance soundness, uniform detection, streaming-kernel
equivalence and exact likelihood counts. The
[qualification guard](../checks/architecture/verify_memory_qualification.py)
checks finite syndrome laws and switched instruments. They support the
all-dimension proofs above; they do not establish a full ordinary lower
bound or a noisy-hardware advantage. Environment records and physical
control costs must be matched before using these as native comparators.
