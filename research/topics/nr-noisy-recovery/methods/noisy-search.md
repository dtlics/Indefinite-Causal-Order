# Depolarizing-noise search: ordinary flag simulation and counted restarts

[NR-R06 owner](../architecture-baselines.md#nr-r06) · [Application assessment](../architecture.md) · [Exact replay](../checks/architecture/verify_native_checks.py)

This is a proof component of NR-R06. Two known controlled-unitary
layers around ordinary depolarizing noise reproduce the full switched
channel, with the same control and noisy calls, including arbitrary
input/reference entanglement. Their real control and calibration costs
remain charged. A separate analysis of the proposal's untouched controls shows
that immediate and deferred measurement give the same instrument.
Counting rejected attempts and early aborts also gives the same
asymptotic search-cost order as bare ordinary restarted noisy Grover.
That latter comparison alone does not exclude finite constant gains.

The motivating primary proposal is
[Srivastava et al., arXiv:2401.05866v2 (May 2025)](https://arxiv.org/pdf/2401.05866v2),
Sections IV.1–IV.2. Its two measurement schedules and product-all-plus
readout are the scope of the comparison below. The discrepancy with
its displayed multi-iteration expressions is stated after deriving
the full instrument; no claim concerns an unmodeled controller.

<a id="nr-r06-noisy-search"></a>

## One block, including its control and reference

For integer $D\ge2$, define
$\Omega_D(X)=\operatorname{Tr}(X)I/D$ and
$\mathcal D_s=s\operatorname{Id}+(1-s)\Omega_D$, where $0\le s\le1$.
All maps act as identity on any passive reference $R$.
Switch two independent uses of $\mathcal D_s$, with an independent
control initially $|+\rangle$. Put $t=s^2$ and

$$
a=t+\frac{(1-s)^2}{2D^2},\qquad
b=\frac{1-t}{2}+s(1-s),\qquad
w=a+b=1-\frac{(1-s)^2(1-D^{-2})}{2}.
\tag{NS1}
$$

The complete output on every target–reference operator is

$$
\mathcal S(X)
=|+\rangle\langle+|_C\otimes\mathcal M_+(X)
 +|-\rangle\langle-|_C\otimes\mathcal M_-(X),
$$
$$
\mathcal M_+=a\operatorname{Id}+b\Omega_D,\qquad
\mathcal M_-=\frac{(1-s)^2}{2}
 \left(\Omega_D-\frac{\operatorname{Id}}{D^2}\right),\qquad
\mathcal M_++\mathcal M_-=\mathcal D_t.
\tag{NS2}
$$

To prove this, use Kraus operators
$K_0=\sqrt{s}I$ and
$K_{uv}=\sqrt{(1-s)/D}\,|u\rangle\langle v|$.
The diagonal order blocks are $\mathcal D_t(X)/2$. The cross block
is half of

$$
\mathcal X(X)=
\left(t+\frac{(1-s)^2}{D^2}\right)X
+2s(1-s)\Omega_D(X).
\tag{NS3}
$$

The two identity Kraus factors give $tX$; exactly one matrix-unit
factor gives $2s(1-s)\Omega_D(X)$; multiplying both matrix-unit
factors and summing their contracted indices gives
$(1-s)^2X/D^2$. Thus the order-basis matrix is
$\tfrac12\left(\begin{smallmatrix}\mathcal D_t&\mathcal X\\
\mathcal X&\mathcal D_t\end{smallmatrix}\right)(X)$.
Changing to the $X$ basis gives (NS2), including arbitrary reference
matrix units.

Both branches are completely positive. For the minus branch, the
unnormalized Choi matrix of
$\Omega_D-\operatorname{Id}/D^2$ is
$I_{D^2}/D-|\Gamma_D\rangle\langle\Gamma_D|/D^2$, where
$|\Gamma_D\rangle=\sum_j|jj\rangle$.
Its eigenvalue on $|\Gamma_D\rangle$ is zero and every orthogonal
eigenvalue is $1/D$. The branch effects are $wI$ and $(1-w)I$.
In particular, $1/2\le w\le1$ and $0\le a\le w$.

The control is already classical in the $X$ basis. An immediate $X$
measurement changes neither the joint $CTR$ state nor its retained
record. This is stronger than agreement of one target marginal.

## An ordinary circuit reproduces the complete depolarizing SWITCH

The compiler also preserves an arbitrary incoming state of C and
allows unequal known strengths $s_A,s_B\in[0,1]$.
Put $T=s_As_B$, $c=(1-s_A)(1-s_B)$ and
$\mathcal N=\mathcal D_{s_B}\circ\mathcal D_{s_A}=\mathcal D_T$.
The same Kraus contraction as in (NS3) gives the native cross map

$$
\mathcal X_{AB}(X)
=\left(T+\frac c{D^2}\right)X
 +(s_A+s_B-2T)\Omega_D(X).
\tag{NSP1}
$$

Thus an arbitrary input block $X_{ij}$ in the control basis has
diagonal outputs $\mathcal N(X_{ii})$ and off-diagonal outputs
$\mathcal X_{AB}(X_{ij})$. These statements include a reference.

Choose a known orthogonal unitary basis $\{V_v\}_{v=1}^{D^2}$ with
$\operatorname{Tr}(V_v^\dagger V_u)=D\delta_{vu}$, for example Weyl
unitaries, and put

$$
\lambda=\frac{(1-s_A)(1-s_B)}{1-s_As_B}\in[0,1].
\tag{NSP2}
$$

If both strengths are one, choose $\lambda=0$.
Sample $V=I$ with probability $1-\lambda$ and otherwise sample
uniformly from this basis. Apply the known
$C_V=|0\rangle\langle0|\otimes I+
|1\rangle\langle1|\otimes V$, make the two noise calls in ordinary
order, then apply $C_V^\dagger$. No extra helper, control measurement
or error-label record is used.

For a fixed $V$, depolarizing covariance makes both diagonal blocks
exactly $\mathcal N(X)$. Its off-diagonal block is

$$
T X+(1-T)\operatorname{Tr}(XV^\dagger)V/D.
\tag{NSP3}
$$

Orthogonality gives
$\mathbb E_v[\operatorname{Tr}(XV_v^\dagger)V_v]=X/D$.
Consequently the sampled circuit's off-diagonal output is

$$
\left(T+\frac{\lambda(1-T)}{D^2}\right)X
 +(1-\lambda)(1-T)\Omega_D(X)
=\mathcal X_{AB}(X).
\tag{NSP4}
$$

Here $\lambda(1-T)=c$ and
$1-T-c=s_A(1-s_B)+s_B(1-s_A)\ge0$, also proving
$0\le\lambda\le1$.
Every identity is componentwise on the reference matrix units.
Matching all four control blocks proves equality of the full $CTR$
channel for every input, including unknown quantum information in C.

For $D=2^n$, choose the Hermitian physical Pauli basis.
Then $C_V^\dagger=C_V$ and (NSP3) is the
[ordinary Pauli check (PM3)](../architecture-baselines.md#nr-r06-pauli-statistic-memory).
The implementation uses the existing control C, the same two noisy
calls, one classical $\lambda$ coin, at most $2n$ random bits and two
controlled-Pauli layers, each of at most $n$ elementary gates under
suitable connectivity. For equal strengths,
$\lambda=(1-s)/(1+s)$. In this case each nonidentity net Pauli
anticommutes with a uniform check with probability $1/2$, while
identity never does.

The checks surround the noise-only slots after the Grover operation;
no controlled unknown Grover oracle or inverse is supplied.
Known-unitary synthesis, connectivity, gate noise, retained-control
storage and duration remain real costs. The strengths or $\lambda$
must be supplied or calibrated: this is not an exact parameter-blind
compiler. A coin error $|\widehat\lambda-\lambda|$ causes at most that
half-diamond error, since the circuit is affine in the coin probability.
Its Pauli implementation specializes an existing check identity,
without a Bell bank or an additional clean control.

Calibration has an explicit dimension-independent sampling cost.
For a known pure input (a product input for qubits), the ordinary return probability is
$\mu_s=s+(1-s)/D$. From $m$ independent preparations/readouts,
invert this affine relation and clip the estimate to $[0,1]$.
Hoeffding gives simultaneous strength errors at most $\epsilon$,
except with probability $\zeta$, with
$m\ge2\epsilon^{-2}\log(4/\zeta)$ calls per channel.
Moreover, for $a,b\in[0,1]$,

$$
\left|\partial_a\frac{(1-a)(1-b)}{1-ab}\right|
=\frac{(1-b)^2}{(1-ab)^2}\le1,
$$

and likewise for $b$. The function extends continuously by zero at
$(1,1)$, so
$|\widehat\lambda-\lambda|\le|\widehat s_A-s_A|+
|\widehat s_B-s_B|$ globally.
For $L$ compiled blocks, the usual full-history hybrid bound is
$2L\epsilon$ on that good calibration event, or
$2L\epsilon+\zeta$ after averaging the failure event.
Preparation/readout accuracy, finite precision, calibration time,
reuse and drift must satisfy this premise; high-precision calibration
is not free.

Full channel equality preserves arbitrary subsequent processing,
adaptive flag decisions, coherent control reuse and reference
correlations. Under these available known controls, these particular
depolarizing SWITCH blocks give no extra noisy-query or full-output
capability. Their native routers can still have different physical
time and error costs. Correlated baths, inaccessible boundary controls,
other channel families and actual controlled/vacuum extensions need
their own analysis; this is not a uniform A/B-oracle simulation theorem.

## Every flag history and measurement timing

Let $\mathcal G_j$ be the target operation at iteration $j$. Introduce
one fresh switch control per iteration and never use an old control
to change a later operation. For a sign string
$\boldsymbol\sigma=(\sigma_1,\ldots,\sigma_k)$, its unnormalized
target–reference map is

$$
\mathcal I_{\boldsymbol\sigma}
=\mathcal M_{\sigma_k}\circ\mathcal G_k\circ\cdots
 \circ\mathcal M_{\sigma_1}\circ\mathcal G_1.
\tag{NS4}
$$

An induction using (NS2) proves that the full retained output is
$\sum_{\boldsymbol\sigma}|\boldsymbol\sigma\rangle
\langle\boldsymbol\sigma|_X\otimes
\mathcal I_{\boldsymbol\sigma}(X)$.
Equivalently, each measurement of an old control commutes with every
later channel acting on the target and new controls. Moving these
local instruments to the end therefore preserves **every** flagged
CP map, not only the all-plus probability. A final collective POVM
on the untouched controls is a classical randomized postprocessing
of their $X$ string. Forgetting all flags gives the ordinary sequence
$\mathcal D_t\circ\mathcal G_k\circ\cdots
\circ\mathcal D_t\circ\mathcal G_1$.

For a fixed common length, every retained subset or randomized
postprocessing of flags is CP-dominated by this ordinary flag-forgotten
map: the difference is the sum of the other CP branches. Consequently
its unnormalized correct-event mass, for any common positive final
test on target and reference, cannot exceed that ordinary run's mass.
Conditional fidelity may improve. Early aborts also change the cost,
so this fixed-length statement is not an exact restarted-rate ordering.

For a fixed Grover operator $G$, depolarizing maps commute with
$\mathcal G=\operatorname{Ad}_G$. Since $\Omega_D^2=\Omega_D$,

$$
\mathcal I_{+\cdots+}
=a^k\mathcal G^k+(w^k-a^k)\Omega_D.
\tag{NS5}
$$

The all-plus probability is $w^k$ and the normalized ideal-state
coefficient is $(a/w)^k$. The same result holds for immediate
postselection and terminal product-all-plus postselection.

This corrects the differing multi-step coefficients displayed for
those stated circuits in the primary proposal, v2, Eqs. (57)–(58).
For example, at $D=16,s=4/5$, (NS1) gives $a/w=8193/12545$.
The correct two- and three-step coefficients are
$67125249/157377025$ and $549957165057/1974294778625$;
the displayed denominators are respectively $157372673$ and
$1419655835905$. The replay derives the coefficients from raw Kraus
operators, without using either displayed recurrence.
This is a scoped disagreement about untouched old controls and the
specified product measurement. Interacting with old controls,
conditioning later operations on them or changing the physical
noise process requires a different calculation.

## All-attempt search and the early-abort cost

Start in the uniform superposition and search for one marked item.
One ideal Grover iteration uses one phase-oracle call, and

$$
\theta=\arcsin(D^{-1/2}),\qquad
P_k=\sin^2((2k+1)\theta).
$$

For a chosen integer $k\ge1$, abort immediately on the first minus
flag and restart from a fresh input. A completed attempt returns a
candidate. Its unnormalized correct-candidate probability and expected
number of executed Grover iterations are

$$
S_k=a^k(P_k-D^{-1})+w^k/D
    =a^kP_k+(w^k-a^k)/D,\qquad
C_k=\sum_{j=0}^{k-1}w^j.
\tag{NS6}
$$

An attempt reaches iteration $j+1$ with probability $w^j$, which proves
the cost formula. In particular, it is not legitimate to charge only
the accepted runs, or always to substitute $k$ for $C_k$.
Independent restarts have an amortized cost $C_k/S_k$ per correct
candidate. This becomes a recognized-success stopping algorithm only
with a supplied reliable candidate check; that access is specified
below. A deferred schedule with no early abort still has the same
$S_k$, but executes all $k$ iterations.

Put $p=1-t$ and $L=\max\{\sqrt D,pD\}$. Uniformly over these parameters,

$$
\boxed{\quad
\frac18 L\ \le\
\inf_{k\in\mathbb N,\ k\ge1}\frac{C_k}{S_k}
\ \le\ 16L .
\quad}
\tag{NS7}
$$

Any zero $S_k$ is assigned infinite cost.

For the lower bound, $C_k\ge kw^{k-1}$ and
$P_k\le\min\{1,(2k+1)^2/D\}\le\min\{1,9k^2/D\}$.
The sine inequality follows, for instance, by expanding the sine of
an integer multiple and applying $|\sin(m\theta)|\le m|\sin\theta|$.
With $f=a/w$,

$$
\frac{S_k}{C_k}
\le w\left[f^k\min\{1/k,9k/D\}+\frac1{kD}\right]
\le\frac4{\sqrt D}.
\tag{NS8}
$$

Here $\min\{1/k,9k/D\}\le3/\sqrt D$ and
$1/(kD)\le1/\sqrt D$.
For $p>0$, $b\ge p/2$ and $w\le1$, so
$f=1-b/w\le e^{-p/2}$. Therefore

$$
\frac{S_k}{C_k}
\le\frac{9ke^{-pk/2}+1}{D}
\le\frac{18/e+1}{pD}
<\frac8{pD}.
\tag{NS9}
$$

The middle inequality uses
$\sup_{x\ge0}xe^{-px/2}=2/(ep)$ and $p\le1$.
Equations (NS8)–(NS9) give
$C_k/S_k\ge\max\{\sqrt D/4,pD/8\}\ge L/8$ for every $k$,
including overshoot. At $p=0$ only (NS8) is needed.

For the upper bound, if $p\ge1/4$ or $D<16$, take $k=1$.
The identity
$P_1-D^{-1}=8(D-1)(D-2)/D^3\ge0$ and $w\ge1/2$ give
$S_1\ge1/(2D)$ and $C_1/S_1\le2D\le8L$.
Otherwise $D\ge16,p<1/4$. Define

$$
m=\min\{\sqrt D/4,1/(2p)\},\qquad k=\lfloor m\rfloor,
\tag{NS10}
$$

where $1/0=+\infty$. Then $m\ge1$, $k\ge m/2$ and $kp\le1/2$.
Bernoulli's inequality gives $t^k=(1-p)^k\ge1-kp\ge1/2$.
Also
$\theta\le\pi/(2\sqrt D)$ and
$(2k+1)\theta\le3\pi/8<\pi/2$.
Using $\sin x\ge2x/\pi$ on that interval and
$\theta\ge1/\sqrt D$ gives $P_k\ge k^2/D$.
Since $a\ge t$, (NS6) now yields

$$
S_k\ge a^kP_k\ge t^kP_k\ge\frac{k^2}{2D},\qquad
\frac{C_k}{S_k}\le\frac{2D}{k}
\le\frac{4D}{m}
=\max\{16\sqrt D,8pD\}\le16L.
\tag{NS11}
$$

This proves (NS7) without a numerical grid or a first-lobe restriction
on its lower bound.

## Ordinary restarts, verification and the remaining scope

An ordinary run with the same $k$ Grover iterations and serial noise
$\mathcal D_t$ has correct-candidate probability

$$
R_k=t^k(P_k-D^{-1})+D^{-1}
    =t^kP_k+(1-t^k)/D.
\tag{NS12}
$$

For $p\ge1/4$ or $D<16$, $R_1\ge1/D$.
Otherwise the same choice (NS10) gives
$R_k\ge t^kP_k\ge k^2/(2D)$.
Thus an ordinary restart has $k/R_k\le16L$ with an appropriate
common, known-noise round length. If the noise is not a supplied
parameter, its calibration or a noise-ignorant schedule has a cost.

A reliable bit-predicate port or separately justified verifier must
recognize whether a returned candidate is marked. Supply and count
the same check for both strategies. If it costs at most one additional
oracle call per completed attempt, the switched expected round cost is
$C_k+w^k\le2C_k$, and the ordinary cost is $k+1\le2k$.
Both have a verified expected-query upper bound $32L$.
The bare lower bound (NS7) continues to lower-bound the switched
verified cost. Allowing $k=0$ with this counted verifier costs $D$
queries per found item and does not violate that lower order.
Without the verifier, $C_0/S_0=0$ is not a meaningful search runtime.
A phase-only noisy oracle, particularly at $p=1$, does not automatically
provide a reliable predicate check.

Restarted noisy search is established prior:
[Vrana, Reeb, Reitzner and Wolf](https://arxiv.org/pdf/1307.0771),
Sections II.C–II.D, explicitly count candidate verification, and their
Theorem 3 addresses noise-ignorant schedules.
[Rosmanis](https://arxiv.org/abs/2309.14944) proves strong noisy-oracle
query bounds in a specified oracle/register model, including an error
flag variant. These are context, not imported lower bounds for an
arbitrarily controlled physical SWITCH. The lower bound (NS7) was
proved directly for the stated all-plus family.

The early-abort comparison leaves finite constant factors open.
Fixed-length correct-event dominance alone does not settle them.
Actual router/helper preparation, measuring versus storing controls,
noise-channel visits, source/reset, verification, classical feedback
and wall-clock latency must also be charged. Marginal depolarizing
fits do not supply independent physical slot dilations with the
same order records. The uniform cost bound (NS7) concerns the all-plus
policy. The full ordinary block simulation has the broader processing
scope proved above, conditional on its controlled-Pauli and helper
ports. Correlated baths and other oracle interfaces require a new
model. A useful new search proposal must specify those resources
and compare with restarted ordinary search before claiming a native
algorithmic advantage.

## Verification scope

The existing [native-check replay](../checks/architecture/verify_native_checks.py)
constructs finite raw switch Kraus operators and full target matrix-unit
maps. It compares immediate and deferred **every-flag** instruments,
retains a complex entangled reference, and checks the all-plus,
flag-forgotten ordinary, controlled-Pauli simulator, restart and
primary-discrepancy identities.
The arbitrary-$k$ induction, analytic cost bounds and physical access
qualifications above are proofs, not claims established by a finite
parameter scan. No new result ID, hardware implementation or
all-SWITCH-algorithm no-go is asserted.
