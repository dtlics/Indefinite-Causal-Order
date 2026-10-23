# Ordinary overlap certificates from product-probe records

This is an ordinary local-certification proof component of
[NR-R06](../architecture-baselines.md#nr-r06), with its
[Pauli entropy/capacity consequence](pauli-entropy-capacity.md)
owned by [NR-R20](../memory-qualification.md#nr-r20).
The [exact finite checker](../checks/architecture/verify_pauli_local_certification.py)
tests the conditional probe identities, correlated-law certificates,
readout-noise calculations and the rational population example.
Its finite cases do not prove the all-dimension capacity theorem.

Let a fixed stationary Pauli channel independently draw $a\sim p$
on every call, with arbitrary correlations between sites within $a$.
The target scalar is
$$
\eta=\mathbb E_{a,b\ \mathrm{iid}\ p}(-1)^{[a,b]}.
$$
All statements below assume trusted product state preparation,
single-qubit Pauli controls and readout, unless a specific calibrated
measurement-noise model is declared. The queried register contains
$n$ cleanly prepared data qubits; no additional clean reference qubits,
quantum helper or entangling gate is required. This is a diagnostic
experiment, not preservation of an unknown payload.

## A bounded OR certificate needs no error-weight promise

In one paired trial choose independent uniform axes
$k_i,\ell_i\in\{X,Y,Z\}$, prepare their positive product eigenstates
for two independent calls and measure in the same axes. Let
$I_i=1[u_i=-1]$, $W_i=1[v_i=-1]$, and put
$$
T=\sum_iI_iW_i,\qquad J=1_{\{T>0\}}.
\tag{O1}
$$
For a fixed realized error pair $a,b$, let
$K=|\operatorname{supp}(a)\cap\operatorname{supp}(b)|$.
At a common nonidentity site, exactly two of the three axes detect
each error, so the two independently chosen axes give
$\Pr(I_iW_i=1\mid a,b)=4/9$. At all other sites this probability is
zero. Axis choices at distinct sites are independent for this fixed
error pair; hence
$$
\Pr(J=1\mid a,b)=1-(5/9)^K.
\tag{O2}
$$
If $a,b$ anticommute globally, then $K\geq1$. Therefore
$$
\Pr(J=1)\geq\frac49\Pr([a,b]=1),\qquad
\boxed{\eta\geq1-\frac92\,\mathbb EJ.}
\tag{O3}
$$
The certificate is valid for arbitrary spatial correlations and
arbitrarily large error weights. It deliberately discards cancellations
of local commutation parity and can be vacuous on dense commuting
families.

Since $J\leq T$, (O3) is at least as strong as the untruncated
overlap certificate
$\eta\geq1-\frac92\mathbb ET=1-2\sum_iw_i^2$,
where $w_i=\Pr(a_i\neq I)$. Unlike the sum, $J\in\{0,1\}$ has a
dimension-independent range without assuming a maximum weight $k$.
One can still use label-sensitive additive local anticommutation
estimates where their stronger population certificate is useful.

For $N$ independent paired trials, Hoeffding gives the upper
confidence bound
$$
\mathbb EJ\leq\bar J+\sqrt{\frac{\ln(1/\delta_J)}{2N}}
\tag{O4}
$$
except with probability $\delta_J$. Insert this in (O3) and clip
the lower result to $[-1,1]$. A confidence subtraction of at most
$\varepsilon_\eta$ needs
$$
N\geq\frac{81}{8\varepsilon_\eta^2}\ln\frac1{\delta_J}.
\tag{O5}
$$
This is confidence padding relative to the empirical expression.
If the claim is instead that the reported lower certificate is within
$\varepsilon_\eta$ of the population lower certificate with high
probability, fluctuations and padding both count. Using a two-sided
event gives the sufficient
$N\geq81[2\varepsilon_\eta^2]^{-1}\ln(2/\delta_J)$.
These are conservative Hoeffding bounds, not optimum rare-event
sample counts.

## The same records estimate the identity probability

The known individual-population estimator is particularly simple:
$$
Z_A=(-1/2)^{\sum_iI_i}
 =\prod_i\left(1-\frac32I_i\right),\qquad
Z_B=(-1/2)^{\sum_iW_i}.
\tag{O6}
$$
For fixed $a$, each nonidentity site gives a minus outcome with
probability $2/3$; each identity site gives none. Thus the conditional
expectation of a local factor is 0 or 1, respectively. Independence of
the random axes conditional on $a$ proves
$$
\mathbb E[Z_A\mid a]=1_{\{a=0\}},\qquad
\mathbb EZ_A=\mathbb EZ_B=p_0.
\tag{O7}
$$
No spatial independence of $p$ was used. Both variables lie in
$[-1/2,1]$. This is exactly the $B=0$ instance of
[Flammia and O'Donnell, Quantum 5, 549 (2021), Theorem 22 and
its proof](https://arxiv.org/html/2105.02885), not a new measurement
proposal. Their Fact 17 supplies the conditional $2/3$ detection
law. Its additive estimation cost is independent of $n$, with
linear classical work in the number of recorded bits.

Using all $2N$ independent call records, define
$\bar Z=(2N)^{-1}\sum_j(Z_{A,j}+Z_{B,j})$. With probability at least
$1-\delta_0$,
$$
p_0\geq \bar Z-\frac32
\sqrt{\frac{\ln(1/\delta_0)}{4N}}.
\tag{O8}
$$
The paired OR outcomes and these identity estimates are correlated,
but a union bound does not require independence of the two confidence
events. Set $\delta_0=\delta_J=\delta/2$, use (O4), and let
$$
\ell=\max\left\{0,\bar Z-\frac32
\sqrt{\frac{\ln(2/\delta)}{4N}}\right\},\qquad
v=\max\left\{-1,1-\frac92
\left[\bar J+\sqrt{\frac{\ln(2/\delta)}{2N}}\right]\right\}.
\tag{O9}
$$
Clipping an upper mean at 1 is also allowed. With total failure at
most $\delta$, $p_0\geq\ell,\eta\geq v$. The already proved
Pauli entropy witness then gives the conservative certificate
$$
Q\geq
\max\{0,(\ell-\sqrt{1-v})n-1-3(1-\ell)\},
\tag{O10}
$$
using $h_2\leq1$ and $C_D<3$.

There are $2N$ ordinary channel invocations and $O(nN)$ local
preparation, readout and classical processing operations. No helper
is required even for $p_0$. The positive-rate conclusion is the
same asymptotic unassisted capacity lower certificate, with all its
stationarity, no-bypass and decoder limitations.

## Population example and finite-data distinction

Let $p_0=19/50$, and distribute the remaining $31/50$ uniformly on
the $3n$ weight-one nonidentity Paulis. Then $w_i=(31/50)/n$.
For every realized pair, $K\in\{0,1\}$, so $J=T$, and (O3)
gives
$$
\eta\geq1-\frac{2(31/50)^2}{n}.
$$
At $n=32$, the lower value is $0.975975$ and its complementary
square root is exactly $31/200=0.155$. Consequently the population
version of (O10) gives
$$
Q\geq\left(\frac{19}{50}-\frac{31}{200}\right)32
-1-3\frac{31}{50}
=\frac{217}{50}=4.34.
\tag{O11}
$$
The exact $\eta$ is larger,
$1-\frac43(31/50)^2/n$, because two distinct nonidentity labels
at the same site anticommute with probability $2/3$.
The 4.34 figure is an intentionally conservative population
certificate; finite data require (O9) and yield a generally smaller
certified rate. It is not an unconditional finite-sample guarantee
at the population endpoint.

This example has full linear Pauli span and sparse error events.
Known population-recovery methods already treat such errors.
The OR calculation is a direct ordinary scalar certificate; it
does not establish a new general $\eta$ estimator or a first
ordinary method for the family.

## Fixed physical readout floors are not absent

Even the identity channel illustrates the physical limit of the
ideal OR statistic. Suppose each local terminal readout bit is
independently flipped with probabilities $e_A,e_B$ in the two
calls, uniformly across sites. Ideal outputs are all plus. The
observed false-coincidence probability is exactly
$$
\mathbb E J_{\rm obs}
=1-(1-e_Ae_B)^n.
\tag{O12}
$$
At fixed $e_Ae_B>0$, it tends to 1 and makes the ideal certificate
vacuous, even on a perfect channel. Applying the noiseless formulas
to a general uncalibrated readout can also be unsound through false
negatives. Identity is a floor counterexample, not a universal
ordinary lower bound.

Calibrated symmetric bit flips can be inverted, but the estimator
and variance then change. For $e_A,e_B<1/2$, set
$$
U_i=\frac{\widetilde I_i-e_A}{1-2e_A},\qquad
V_i=\frac{\widetilde W_i-e_B}{1-2e_B},\qquad
\widetilde J=1-\prod_i(1-U_iV_i).
$$
Under independent readout noise conditional on all ideal outcomes,
$\mathbb E[\widetilde J\mid I,W]=1-\prod_i(1-I_iW_i)=J$.
Write $\tau_j=e_j(1-e_j)/(1-2e_j)^2$. For the identity channel,
the local corrected variables have mean zero and variance
$\tau_A,\tau_B$, giving the exact estimator variance
$$
\operatorname{Var}(\widetilde J)
=(1+\tau_A\tau_B)^n-1.
\tag{O13}
$$
This particular unbiased product inverse has exponential variance
at fixed nonzero readout noise. It is not a lower bound for every
ordinary calibrated protocol.

In fact a polynomial alternative is already available: use the
corrected additive statistic
$\widetilde T=\sum_iU_iV_i$, which estimates $\mathbb ET$.
The conditional readout variance and the law of total variance give
for identical channel laws
$$
\operatorname{Var}(\widetilde T)
=\operatorname{Var}(T)+
\frac23(\tau_A+\tau_B)\mathbb E\operatorname{wt}(a)
+n\tau_A\tau_B.
\tag{O14}
$$
There is no independence assumption between error sites here.
For a fixed ideal pair of measurement outcomes, distinct-site
readout noises are independent and
$\operatorname{Var}(U_iV_i\mid I,W)
=\tau_AW_i+\tau_BI_i+\tau_A\tau_B$.
Averaging $I_i,W_i$ gives (O14). General bounded-range
concentration remains polynomial in $n$, while a dilute
fixed-weight family has only a linear readout-floor contribution.
Median-of-means with a valid variance bound or bounded-range
concentration supplies confidence; empirical plug-in variance
is not automatically a guarantee.

The $p_0$ inverse has the analogous issue. Its corrected product
is $\prod_i(1-\frac32U_i)$. For identity noise with common
readout error $e$, its second moment is
$[1+\frac94\tau]^n$. This does not exclude a better $p_0$
protocol: the existing one-helper controlled-Pauli check and
trusted global-design survival methods have different resources.
Repeated/QND readout or fault-tolerant preparation can also alter
the effective floor, with their time, reset and control costs.

## Optional random-sign extension of the identity estimator

For the Pauli model, positive eigenstates suffice above. If each
input eigenvalue is independently randomized to $s_i=\pm1$ and
the output is relabeled $u_i=s_i m_i$, none of the Pauli formulas
change. This also makes (O6) an entanglement-fidelity estimator for
an arbitrary CPTP map $\mathcal E$, even without a Pauli model.
Indeed $1-\frac32 1_{\{u_i=-1\}}=\frac14+\frac34u_i$.
Expand the product over subsets. Averaging input signs kills all
off-diagonal input/output Pauli-support terms; averaging the
independent axes then yields
$$
\mathbb EZ=
\frac1{D^2}\sum_{P\in\mathcal P_n}
\frac1D\operatorname{Tr}[P\,\mathcal E(P)]
=F_e(I/D,\mathcal E).
$$
This is ordinary product-state fidelity estimation, consistent
with [Flammia and O'Donnell, Sec. 6.1](https://arxiv.org/html/2105.02885)
and [Flammia and Liu, PRL 106, 230501 (2011), channel
extension](https://arxiv.org/pdf/1104.4695). It does not extend
the OR commutation certificate to arbitrary non-Pauli maps.

The surviving interpretation is an ideal dimension-independent
ordinary sufficient certificate for spatially diluted overlap,
with explicit physical SPAM limits and calibrated polynomial
alternatives. It gives no hardness statement for high-weight
near-commuting laws, and no native switch advantage follows
from the entropy certificate alone.
