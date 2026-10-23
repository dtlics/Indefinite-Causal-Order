# Ordinary calibration of a publicly oriented Clifford burst channel

This ordinary-baseline proof component of
[NR-R06](../architecture-baselines.md#nr-r06) addresses the structured
burst-channel candidate. Its memory-capacity application is
[NR-R20](../memory-qualification.md#nr-r20), alongside the
[native control and noise-cost screen](memory-native-cost.md).
It reconstructs the relevant parameters when the Clifford **tableau is
public**. It does not require a circuit implementing the Clifford or its
inverse, a clean reference register, or purification of the mixed target.
Its dense controlled-Pauli gates and helper contrast remain physical
costs. An opaque unknown orientation is a different interface.

<a id="public-clifford-burst-calibration"></a>

## Channel, available controls and conditioning

On an $n$-qubit target, suppose the fixed repeatable channel is

$$
 \mathcal E=\alpha\operatorname{Id}+
 \beta\operatorname{Ad}_C\circ
       \left(\bigotimes_{i=1}^n\mathcal E_i\right)
       \circ\operatorname{Ad}_{C^\dagger},\qquad
 \beta=1-\alpha\ge\beta_{\min}>0.                 \tag{CB1}
$$

Each $\mathcal E_i$ is a one-qubit Pauli channel with unknown probability
law $p_i$ on $\{I,X,Y,Z\}$. The global no-burst/burst coin is redrawn
independently on every call. Conditional on a burst, the local errors are
independent with the same fixed laws $p_i$ on every call. This permits
the spatial correlations caused by the single global burst coin; it
does not cover an arbitrary correlated conditional burst law, persistent
event histories, or drift between probes.

The supplied symplectic tableau determines the physical Hermitian
Pauli $R_z=CP_zC^\dagger$ for every logical Pauli $P_z$. Its overall
sign is known and can be omitted for a commutation check. The protocol
has a clean reusable helper, controlled physical Pauli operations,
helper preparation/readout/reset, and the ability to query the channel
between the two controlled operations. These are assumptions about the
actual implemented channel and controls, not an inference that an
intended gate list identifies every unknown hardware error.

Write

$$
 \mathcal E_i^\dagger(\sigma)=\lambda_i(\sigma)\sigma,
 \quad \lambda_i(I)=1,
 \qquad
 f_z=\alpha+\beta\prod_i\lambda_i(P_z^{(i)}).
                                                        \tag{CB2}
$$

For two logical Paulis supported on disjoint sets $A,B$, let their
conditional product eigenvalues be $u,v$. The three means for those
Paulis and their product are

$$
 x=\alpha+\beta u,\qquad y=\alpha+\beta v,\qquad
 z=\alpha+\beta uv.
$$

The quantitative result assumes the supplied probes obey

$$
 d:=1-x-y+z=\beta(1-u)(1-v)\ge d_{\min}>0.       \tag{CB3}
$$

The cost depends on $\beta_{\min},d_{\min}$; these cannot be silently
treated as constants for an ill-conditioned instance.

## One-helper probes preserve the mixed target

For a physical Pauli $R$, put
$V_R=|0\rangle\langle0|\otimes I+|1\rangle\langle1|\otimes R$.
Prepare the helper in $|+\rangle$, apply $V_R$, query $\mathcal E$,
apply $V_R$ again, and measure helper $X$. For every realized physical
Pauli $P_a$,

$$
 V_R(I\otimes P_a)V_R
 =\bigl(|0\rangle\langle0|+
       (-1)^{[R,a]}|1\rangle\langle1|\bigr)\otimes P_a.
                                                        \tag{CB4}
$$

Indeed, the control-zero block is $P_a$ and the control-one block is
$RP_aR=(-1)^{[R,a]}P_a$. This proves the identity on every input,
including inputs entangled with a passive reference. For a mixed target
$I/2^n$, the complete output is specifically

$$
 \left[\frac{1+f_R}{2}|+\rangle\langle+|
       +\frac{1-f_R}{2}|-\rangle\langle-|\right]
       \otimes\frac{I}{2^n},\qquad
 f_R=\sum_a p(a)(-1)^{[R,a]}.                   \tag{CB5}
$$

Thus each helper outcome also leaves the target in $I/2^n$. The target
can be reused without target preparation, target readout or target
reset in this exact stationary Pauli model. No outcomes are discarded.
Fresh helper reset and fresh channel errors are still required.

Taking $R=R_z$ and using Clifford preservation of Pauli commutation gives
$f_R=f_z$ from (CB2). The identity fault contributes one; the conditional
product law factors over logical sites. No physical application of
$C$ or $C^\dagger$ enters the probe.

A weight-$w$ physical Pauli check factors into $w$ controlled one-qubit
Paulis with the same helper. The two checks therefore use at most
$2w\le2n$ elementary controlled-Pauli gates, plus helper rotations,
readout and reset. These counts do not include connectivity routing,
native decompositions, gate faults or the time needed to preserve the
helper while addressing a dense support.

If product target preparation/readout are available instead, prepare any
product $+1$ eigenstate of $R_z$ and measure its single-qubit factors
after the channel. Multiplying the outcomes also has mean $f_z$, since
$\mathcal E^\dagger(R_z)=f_zR_z$. This alternative uses a prepared
target and potentially dense readout parity. It is not needed for
(CB4)–(CB5).

## Burst fraction from three disjoint-support means

Expanding the expressions for $x,y,z$ yields

$$
 z-xy=\alpha\beta(1-u)(1-v)=\alpha d,
 \qquad \boxed{\alpha=\frac{z-xy}{1-x-y+z}}.     \tag{CB6}
$$

No local rate needs to be known to apply this identity. Suppose sampled
means $\widehat x,\widehat y,\widehat z\in[-1,1]$ each have error at
most $\delta$, where $\delta\le d_{\min}/6$. Then

$$
 |\widehat d-d|\le3\delta,\qquad
 \widehat d:=1-\widehat x-\widehat y+\widehat z
       \ge d_{\min}/2.
$$

The numerator error is at most $3\delta$, because
$|\widehat x\widehat y-xy|
 \le|\widehat x||\widehat y-y|+|y||\widehat x-x|
 \le2\delta$. Consequently

$$
 \left|\frac{\widehat z-\widehat x\widehat y}{\widehat d}
              -\alpha\right|
 \le\frac{3\delta+\alpha\,3\delta}{d_{\min}/2}
 \le\frac{12\delta}{d_{\min}}
 \le A_\delta:=\frac{14\delta}{d_{\min}}.        \tag{CB7}
$$

Define $\widehat\alpha$ by clipping this ratio to
$[0,1-\beta_{\min}/2]$. The interval contains the true $\alpha$ because
$\beta\ge\beta_{\min}$, so clipping cannot increase its error.
Moreover $\widehat\beta=1-\widehat\alpha\ge\beta_{\min}/2$.
The conservative constant $14$ will be used throughout.

## Local eigenvalues and valid probability laws

Measure the $3n$ logical one-site probes, in addition to the three
disjoint-support probes. Let $f_{i,\sigma}$ be their means and assume
all sampled means have error at most $\delta$. Set

$$
 \widehat\lambda_i(\sigma)
   =\frac{\widehat f_{i,\sigma}-\widehat\alpha}
          {1-\widehat\alpha}.
$$

Since $f_{i,\sigma}=\alpha+\beta\lambda_i(\sigma)$,

$$
 |\widehat\lambda_i(\sigma)-\lambda_i(\sigma)|
 \le\frac{\delta+2|\widehat\alpha-\alpha|}
              {\widehat\beta}
 \le L_\delta:=\frac{2(\delta+2A_\delta)}{\beta_{\min}}
 =K\delta,\quad
 K:=\frac2{\beta_{\min}}\left(1+\frac{28}{d_{\min}}\right).
                                                        \tag{CB8}
$$

The first inequality uses $|1-\lambda_i(\sigma)|\le2$.
Clipping each eigenvalue to $[-1,1]$ is optional and cannot worsen this
bound. Recover raw probabilities using

$$
 \begin{aligned}
 p_i(I)&=(1+\lambda_X+\lambda_Y+\lambda_Z)/4,\\
 p_i(X)&=(1+\lambda_X-\lambda_Y-\lambda_Z)/4,\\
 p_i(Y)&=(1-\lambda_X+\lambda_Y-\lambda_Z)/4,\\
 p_i(Z)&=(1-\lambda_X-\lambda_Y+\lambda_Z)/4.
 \end{aligned}                                           \tag{CB9}
$$

Each raw entry has error at most $3L_\delta/4$, so the total raw
$\ell_1$ error is at most $3L_\delta$. Project the raw vector onto
the probability simplex in $\ell_1$ distance. A minimizing vector
exists because the simplex is compact. Its distance from the raw vector
is no larger than the distance of the true probability vector. The
triangle inequality therefore gives valid reconstructed laws with

$$
 \|\widehat p_i-p_i\|_1\le6L_\delta.            \tag{CB10}
$$

This is a fixed four-outcome classical optimization, with no quantum
memory requirement.

## Commutation statistic and identity probability

Let $r=\bigotimes_i p_i$ and
$p=\alpha\delta_0+\beta C_*r$, where $C_*$ is the tableau's permutation
of Pauli labels. Build $\widehat p$ from the estimated mixture and
reconstructed local laws. Telescoping product measures gives

$$
 \|\widehat r-r\|_1
 \le\sum_i\|\widehat p_i-p_i\|_1\le6nL_\delta,
 \qquad
 \|\widehat p-p\|_1\le2A_\delta+6nL_\delta.     \tag{CB11}
$$

For the second inequality write the difference as
$(\widehat\alpha-\alpha)(\delta_0-C_*r)
 +\widehat\beta C_*(\widehat r-r)$ and use
$\|\delta_0-C_*r\|_1\le2$.

The target self-channel statistic is
$\eta(p)=\sum_{a,b}p(a)p(b)(-1)^{[a,b]}$.
Its kernel has magnitude one. Expanding the difference of two product
laws therefore yields

$$
 \boxed{|\eta(\widehat p)-\eta(p)|
       \le4A_\delta+12nL_\delta},\qquad
 \boxed{|\widehat p(0)-p(0)|
       \le2A_\delta+6nL_\delta}.                \tag{CB12}
$$

The second bound is conservative; a sharper coordinate bound is not
needed. No exponential table of probabilities is stored. In fact, put

$$
 h_i=1-4[p_i(X)p_i(Y)+p_i(Y)p_i(Z)+p_i(Z)p_i(X)].
$$

At one site, exactly the distinct nonidentity Pauli pairs anticommute,
so $h_i$ is the local mean commutation sign. Independence and
Clifford invariance then give the directly computable formulas

$$
 \eta(p)=1-\beta^2+\beta^2\prod_i h_i,
 \qquad p(0)=\alpha+\beta\prod_i p_i(I).         \tag{CB13}
$$

The same formulas apply to the reconstructed laws. Capacity/entropy
consequences of such certificates belong to
[the parent qualification result](../memory-qualification.md#nr-r20).

## Precision and finite sample budget

For desired statistic error $0<\varepsilon\le1$, take

$$
 \delta=\min\left\{\frac{d_{\min}}6,
       \frac{\varepsilon}{12nK+56/d_{\min}}\right\}.
                                                        \tag{CB14}
$$

Then (CB12) bounds the statistic error by $\varepsilon$ and the
identity-probability error by $\varepsilon/2$. There are at most
$m=3n+3$ mean settings. Every helper outcome is $\pm1$; Hoeffding's
inequality gives
$\Pr(|\widehat f-f|>\delta)\le2e^{-N\delta^2/2}$.
For total failure probability $0<\gamma<1$, use

$$
 N=\left\lceil2\delta^{-2}\log\frac{2m}{\gamma}\right\rceil
 \quad\text{calls per setting},\qquad Q\le mN.             \tag{CB15}
$$

A union bound proves the simultaneous event used in (CB7)–(CB12).
At fixed positive $\beta_{\min},d_{\min}$ this is
$O(n^3\varepsilon^{-2}\log(n/\gamma))$ channel calls. Each call
uses at most $2n$ elementary controlled-Pauli gates, so this gate-count
upper bound has an additional factor $n$. The statement is a sufficient
ideal-instrument budget, not a noise-robust native runtime bound.

## When square-root-size supports have constant conditioning

Suppose the two disjoint sets each contain at least $k_0\sqrt n$
sites, and the chosen axis at every selected site has defect

$$
 \frac{a}{\sqrt n}\le1-\lambda_i(\sigma_i)
       \le\frac{b}{\sqrt n},\qquad a,k_0>0.                \tag{CB16}
$$

For $n$ large enough that the upper defect is at most one, the selected
eigenvalues lie in $[0,1]$. Using $1-s\le e^{-s}$ gives
$u,v\le e^{-ak_0}$, hence

$$
 d\ge\beta_{\min}(1-e^{-ak_0})^2>0.             \tag{CB17}
$$

Thus square-root-size supports can supply a constant $d_{\min}$ for
the weak per-site regime. This requires a defect bound for the
**chosen logical axes**. A lower bound on total nonidentity probability
alone does not certify a predetermined axis: a pure $X$ error law has
$\lambda_i(X)=1$ even when its error probability is nonzero. Suitable
axis information can come from a declared model or a separately
budgeted preliminary calibration. The theorem itself uses the explicit
conditioning premise (CB3).

## Physical boundary and retained records

The ordinary protocol uses one helper and no reference bank, leaves
the exact mixed target reusable, and applies no Clifford synthesis.
It still needs dense helper-to-target coupling, sufficient connectivity,
accurate helper readout/reset, stable channel parameters and trusted
mean calibration. The finite budget (CB15) cannot be used unchanged
when check gates introduce unknown faults or a contrast that decays
with support size. Correcting a known contrast changes variance and
requires a calibration precision/failure budget; unknown SPAM can make
the means unidentifiable.

An extra routing register establishes storage capacity, not a prepared
Bell reference. Starting with an unlabelled maximally mixed $n$-qubit
target, a pure buffer
and a pure helper, preparing a pure target–buffer Bell state while
returning the helper clean requires exporting the target's $n$ bits of
entropy, or accounting for postselection. If individual target/buffer
reset, pairwise Hadamard/CNOT gates and readout are actually available,
an ordinary Bell source uses $n$ Hadamards and $n$ CNOTs after reset;
the inverse circuit and computational readout decode it. These are
conditional logical circuit counts, with native routing, entropy
removal and gate errors still priced.

Individual target reset is not required if addressed helper--target
SWAP and helper reset are available. Swap a helper initialized in
$|0\rangle$ into one target qubit, reset the helper, and repeat over
all sites. Each step puts that target qubit in $|0\rangle$ and exports
its prior state and correlations through the helper reset. After
$n$ swaps, even an initially correlated target is pure. Starting with
a clean helper, $n-1$ intermediate resets suffice; a final helper reset
returns it clean as well. Helper-to-target CNOT together
with Hadamards on both addressed qubits supplies reverse CNOT and the
usual three-CNOT SWAP. This is an $O(n)$ entropy-removal procedure,
with its control errors and reset time charged. Whole-register routing
or controlled-Pauli strings alone do not automatically supply these
addressed SWAP/Hadamard ports. A restriction to mixed targets must
therefore specify which actual controls or reset resources prevent
this ordinary preparation.

After the second check has compressed the sign into the helper, any
trace-preserving operation on the target alone leaves the helper
record law unchanged. This follows by partial-trace invariance under
a local trace-preserving map. A later unital target channel also keeps
$I/2^n$ fixed. Noise before or between the elementary controlled-Pauli
gates can change the extracted sign and must be modeled at that time.
Terminal target noise is therefore not, by itself, an exponential
readout cost for this ordinary helper protocol.

No matching statement is made for an unknown opaque tableau, an
arbitrary non-Pauli channel, a changing within-slot program or coherent
access unavailable to the ordinary hardware. The result identifies a
specific public-orientation closure and the remaining dense-check
resource question. A known propagation dictionary must be supplied
by the actual interface, rather than inferred from the efficiency of
some undisclosed Clifford implementation.

The relevant measured workload does not supply the full abstract port.
[Kurilovich et al., *Physical Review X* **16**, 021025 (2026)](https://doi.org/10.1103/1bl4-b2f7)
observe radiation-induced frequency shifts up to 3 MHz persisting about
1 ms, correlated with repetition-code detection events; modified echo
control suppresses much of their effect. These persistent phase/relaxation
dynamics do not establish fresh conditional product-Pauli bursts or a
hidden Clifford orientation.
[Hines et al., *PRX Quantum* **5**, 030334 (2024)](https://doi.org/10.1103/PRXQuantum.5.030334)
demonstrate BiRB on up to 27 qubits using product Pauli eigenstate probes
and public Clifford tracking, illustrating the ordinary alternative's
control assumptions. Neither experiment demonstrates quantum routing of
the complete burst-affected register. Within a declared circuit-level
Pauli model, a public suffix $S$ transports a fault by the known tableau
$SP_aS^\dagger=\pm P_{Fa}$; a separate unknown actual hardware transformation
cannot be inferred from an intended gate list.

The [exact standard-library replay](../checks/architecture/verify_public_clifford_calibration.py)
checks finite symplectic pairs, direct ordered PCS basis actions, every
logical probe of a two-qubit example, and rational sensitivity corners.
The general precision/sample guarantees and native-control premises are
the analytic argument above, not a consequence of those finite cases.
