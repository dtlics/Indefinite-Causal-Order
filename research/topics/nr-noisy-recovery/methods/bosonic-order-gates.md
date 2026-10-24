# Finite-gain bosonic order gates on unknown data

<a id="nr-r11-bosonic-order-gates"></a>

This proof component belongs to [NR-R11](../communication.md#nr-r11). The task is a heralded nonlinear sign gate

$$
G=\operatorname{diag}(1,1,-1)
\quad\text{on}\quad
\mathcal C=\operatorname{span}\{|0\rangle,|1\rangle,|2\rangle\}.
$$

The single input is unknown and may be entangled with a passive inaccessible reference. The output mode must remain available. A terminal homodyne reconstruction or destruction of the target does not provide this gate. Unlike a sign on the one-photon sector alone, this transformation is not a number rotation.

For the favorable two-order family defined below, including all number-resolved heralds and all helper outcomes, the exact success maximum per launched input is

$$
p_{\rm order}=\frac{3-2\sqrt2}{8}=0.0214466094\ldots .
$$

The ordinary KLM circuit achieves the same successful unknown-data map with probability $1/4$, using a supplied auxiliary photon, a vacuum mode, passive optics and number counting. Both protocols have real failed outputs. This compares accepted exact-gate yield; it does not order every possible utility of their full failure instruments or establish a hardware-rate comparison. The order family's no-count failure also prevents deterministic exact repetition on the same unencoded unknown qutrit.

## Primary device and ordinary-method scope

The following bounded source capsules delimit the physical application and closest prior; the subsequent optimization and failure proofs are derived here.

**Herald erasure.** [Zavatta et al., PRL 103, 140406 (2009), arXiv:0909.4450v1](https://arxiv.org/html/0909.4450v1) place one heralded PDC addition between two subtraction taps. Mixing subtraction herald modes, compensating delays and locking their relative phase produces a selected coherent order combination. The experiment tests thermal inputs through homodyne output analysis, with approximately 3% tap reflectivity and threshold SPCMs. It discusses finite tapping, multipair emission and unresolved photon number as imperfections. This is an ordinary chronological herald-erasure mechanism, rather than a demonstrated unknown-qutrit gate. Its mode selection, timing and phase requirements remain physical costs.

**Dynamic emitters.** [Luo et al., arXiv:2512.09711v2, 13 September 2026](https://arxiv.org/html/2512.09711v2), Fig. 1 and Eqs. (31)–(32), use dynamically coupled emitters in a chiral waveguide. Couplings depend on excitation number and temporal mode. Section II.6 discusses the absence of one universal deterministic coupling across the excitation sectors; Section IV treats superposition inputs with measured emitter heralds and mode-preserving approximations. The reported Fock-transfer fidelities therefore do not supply a deterministic unknown-qutrit creation/annihilation oracle. Drive waveforms, emitter preparation/reset, heralding, mode matching and loss must enter any replacement for the primitives below.

**Ordinary nonlinear sign gate.** [Knill, Laflamme and Milburn, Sec. V, Eqs. (17)–(22), arXiv:quant-ph/0006088v1](https://arxiv.org/html/quant-ph/0006088v1) give the retained-mode nonlinear sign construction. One auxiliary photon and vacuum enter a three-mode passive unitary; a selected auxiliary number record implements $G/2$ on arbitrary vacuum/one/two-photon superpositions. This is an analytic construction, not a measured rate. Its full output formula and failed records are retained below. Auxiliary-photon preparation and storage, optical synchronization, counting and restoration are resources. The source's subsequent qubit teleportation discussion is not automatically a qutrit teleportation protocol for this input.

**Closest prior.** [Costanzo et al., arXiv:1706.07018v1, Eqs. (3)–(5)](https://arxiv.org/html/1706.07018v1) already target this qutrit nonlinearity through superposed addition/subtraction. Their amplified vacuum-sign convention is equivalent to $G$ after number and global phases; the text proposes vacuum-heralded attenuation $t=1/(1+\sqrt2)$ to remove the amplification. [Fiurášek, arXiv:0910.4104v1, Eqs. (1)–(3), (8)–(10), (30)–(31)](https://arxiv.org/html/0910.4104v1) retains finite primitive attenuation and constructs finite-Fock diagonal gates by polynomial interpolation. Accordingly, neither this mechanism nor finite-Fock synthesis is claimed as new here. The result below is a scoped optimization and complete-record qualification of the specified two-primitive family, not a priority claim or an optimum over those broader constructions.

## BG1. Complete physical primitives and supplied coherent ports

For a two-mode squeezer with vacuum idler, put $u=\operatorname{sech}s$, $v=\sqrt{1-u^2}$, with $0<u<1$. Fix a common signal/idler mode and pump phase. Its exact expansion is

$$
|n,0\rangle\longmapsto
\sum_{\ell=0}^{\infty}\sqrt{\binom{n+\ell}{\ell}}
u^{n+1}v^\ell|n+\ell,\ell\rangle,
\qquad
A_\ell|n\rangle=
\sqrt{\binom{n+\ell}{\ell}}u^{n+1}v^\ell|n+\ell\rangle.
\tag{BG1}
$$

For a beam-splitter tap with vacuum auxiliary input, put $0<t<1$ and $r=\sqrt{1-t^2}$. A consistent beam-splitter phase convention gives

$$
|n,0\rangle\longmapsto
\sum_{k=0}^{n}(-r)^k\sqrt{\binom nk}t^{n-k}|n-k,k\rangle,
\qquad
B_k|n\rangle=(-r)^k\sqrt{\binom nk}t^{n-k}|n-k\rangle.
\tag{BG2}
$$

These are normalized full expansions: the tap uses the binomial identity, while the amplifier uses
$\sum_{\ell\ge0}\binom{n+\ell}{\ell}y^\ell=(1-y)^{-n-1}$ with $y=v^2$.
No-count events, all pairs and all number-changing rejected outputs are included. There is no truncation of the amplifier's physical output and no replacement by unbounded unnormalized $a$ and $a^\dagger$.

Optimistically supply an **independent two-level order control** $C$, its preparation, arbitrary POVM and actual readout, an outcome-dependent final number rotation $e^{i\theta N}$, ideal photon-number-resolved idler/tap detectors, and matched physical records between the two histories. The target's vacuum component does not itself carry an independent path-control qubit. Detecting a target output path destructively is not a nondestructive gate herald. An actual helper interaction/readout or a complete herald-erasure construction must be provided.

For $|c\rangle=\alpha|0\rangle+\beta|1\rangle$, the common fine number record $(\ell,k)$ has the control/target amplitude

$$
\alpha|0\rangle B_kA_\ell+\beta|1\rangle A_\ell B_k.
\tag{BG3}
$$

Every helper outcome and number record is part of the instrument. A measured helper row gives coefficients $c_0=\alpha\langle m|0\rangle$ and $c_1=\beta\langle m|1\rangle$. The optimization below even permits the helper POVM and final number rotation to depend on $(\ell,k)$. The physical premise requires pump, temporal, bath, number and other records to support the displayed cross term; discarding which-history copies does not establish it. No access to an inaccessible purifier or protected copy of the unknown data is supplied. Additional loss, modal mismatch or impurity requires its actual extra fields and instrument.

## BG2. Classification of every number-resolved exact-success record

An exact selected unitary subchannel has rank-one Choi operator. A positive sum of fine Kraus Choi operators can have that support only if each nonzero accepted fine Kraus is proportional to $G$. This remains true when number records or helper outcomes are grouped incoherently. A record with $\ell\ne k$ changes photon number and cannot implement $G$ with a final number rotation alone.

For $\ell=k=m$, set $q=ut\in(0,1)$ and use $\binom nm=0$ for $n<m$. Multiplying (BG1) and (BG2) gives, on $n=0,1,2$,

$$
K_m(n)=u(vr)^m q^n
\left[c_0\binom{n+m}{m}+c_1q^{-m}\binom nm\right].
\tag{BG4}
$$

The common tap phase $(-1)^m$ has been absorbed into the outcome phase. This expression retains both finite attenuation factors.

For $m=0$ both orders are the same attenuation; a nonzero selected row cannot obtain the required three magnitudes and nonlinear sign. For $m=1$, the vacuum amplitude requires $c_0\ne0$. Put $a=c_1/(c_0q)$ and $Q=qe^{i\theta}$. The one- and two-photon equations are

$$
Q(2+a)=1,\qquad Q^2(3+2a)=-1.
$$

Eliminating $a$ gives $Q^2-2Q-1=0$. Since $|Q|<1$, the only possibility is

$$
q=\sqrt2-1,\qquad \theta=\pi\pmod{2\pi},\qquad
\frac{c_1}{c_0}=-(2\sqrt2-1)=:-\kappa.
\tag{BG5}
$$

For $m=2$, the reverse word vanishes at $n=0,1$. Their matching forces $Q=1/3$, and the $n=2$ equation then forces $c_1/c_0=-5/3$. For every $m\ge3$ the reverse word vanishes throughout the code. Matching $n=1$ fixes $Q=1/(m+1)$, but the two-photon ratio becomes

$$
Q^2\binom{m+2}{m}=\frac{m+2}{2(m+1)}>0,
$$

and cannot equal $-1$. Thus only $m=1$ or $m=2$ can succeed. Their different required $q$ values prevent adding their probabilities at one fixed amplifier/tap setting. This covers all number records, not only the nominal one-pair flag. Coherent number erasure, additional intermediate gates and other primitives are outside this classification.

## BG3. Optimal helper and exact finite-gain maximum

Suppose a successful row requires $c_1/c_0=-k$, $k>0$, and let $p=|\alpha|^2$. Up to fixed phases, every such helper row is proportional to $(1/\sqrt p,-k/\sqrt{1-p})$. The total accepted POVM effect is at most identity. Therefore, including parallel accepted rows,

$$
\sum_j|c_{0,j}|^2
\le\frac{p(1-p)}{1-p+k^2p}
\le\frac1{(1+k)^2}.
\tag{BG6}
$$

The second inequality follows from the exact nonnegative remainder

$$
[1-p+k^2p]-(1+k)^2p(1-p)=[1-(1+k)p]^2.
$$

The bound is attained at $p=1/(1+k)$ with one rank-one projective helper row. The endpoint preparations cannot give a nonzero row with the required finite ratio. Mixed preparation cannot improve it: rank-one accepted Choi support imposes the target condition on each nonzero pure-component contribution, after which convexity applies.

For one pair, $(1+\kappa)^2=8$. Set $z=(\sqrt2-1)^2=3-2\sqrt2$ and $x=u^2$, so $t^2=z/x$ and $z<x<1$. Equations (BG4)–(BG6) give

$$
p_1\le\frac{(1-x)(x-z)}8\le\frac z8,
\qquad
z-(1-x)(x-z)=\left[x-\frac{1+z}{2}\right]^2.
\tag{BG7}
$$

Equality uses

$$
u^2=2-\sqrt2,\qquad t^2=1-\frac1{\sqrt2},\qquad
p=\frac1{2\sqrt2}.
$$

Prepare $\sqrt p|0\rangle+\sqrt{1-p}|1\rangle$ and measure the normalized row $\sqrt p\langle0|-\sqrt{1-p}\langle1|$. Then $c_0=p$, $c_1=-(1-p)$ and $uvr=\sqrt2-1$. Including the final phase, the accepted Kraus operator is

$$
K_{\rm success}=\frac{2-\sqrt2}{4}G,
\qquad p_1=\frac{3-2\sqrt2}{8}.
\tag{BG8}
$$

This is independent of the unknown input and preserves its full reference correlations on success.

For two pairs, (BG6) gives $9/64$ and $q=1/3$. Consequently

$$
p_2\le\frac9{64}x(1-x)^2\left(1-\frac1{9x}\right)^2
\le\frac9{64}x(1-x)^2\le\frac1{48}<\frac z8.
\tag{BG9}
$$

Here $1/9<x<1$, and

$$
\frac4{27}-x(1-x)^2=(x-\tfrac13)^2(\tfrac43-x)\ge0.
$$

The strict comparison is $(17-12\sqrt2)/48>0$, since $17^2-(12\sqrt2)^2=1$. An exact two-pair witness is $x=1/2$, $t^2=2/9$, with success $49/4608$. A tighter two-pair optimization is unnecessary for the global maximum: the classification in BG2 covers the remaining records and (BG9) already puts every two-pair success below (BG8).

## BG4. Threshold clicks and failed online data

Ordinary number-diagonal threshold photodetection sums distinct absorbed photon numbers incoherently. It does not supply the exact number-resolved gate. For example, the fine record $(\ell,k)=(2,1)$ maps vacuum through the addition-first word to

$$
-\sqrt2\,c_0uv^2rt\,|1\rangle,
$$

while the subtraction-first word vanishes on vacuum. Nonzero finite couplings and the required nonzero $c_0$ leave this contribution positive. Grouping it into a click/click success flag cannot cancel its Choi support against other positive fine contributions. Weak gain suppresses this contamination but does not make it zero at finite nonzero gain. Coherent erasure of the number record would be an additional resource.

The common no-idler/no-tap record is

$$
K_{00}=u q^N,\qquad
P_{\mathcal C}K_{00}^{\dagger}K_{00}P_{\mathcal C}
=u^2\operatorname{diag}(1,q^2,q^4).
\tag{BG10}
$$

The helper factors unchanged. This nonscalar effect means the rejected flag probability depends on the unknown state. There is no deterministic CPTP recovery of that flag preserving every code state and reference. To see this without assuming a particular decoder, suppose $\mathcal R(K\rho K^\dagger)=p(\rho)\rho$ for every code state. Linearity on mixtures of distinct pure states forces $p$ constant; tracing then forces $P_{\mathcal C}K^\dagger KP_{\mathcal C}=pP_{\mathcal C}$, contradicting (BG10). Equivalently this is the single-Kraus exact-code condition.

Forgetting the no-count flag does not correct the entire rejected instrument. If a common recovery made its complete rejected subchannel proportional to identity, the rank-one Choi support of that recovered subchannel would force the recovered no-count contribution to have the same support, giving the same contradiction. Probabilistic reversal, encoding, additional recovery and their costs remain possible. This obstruction rules out a free exact repeat on the unencoded unknown input; it is not a universal failure-utility theorem.

## BG5. Ordinary KLM full instrument

Write $b=2^{-1/4}$, $\gamma=1-\sqrt2$ and $c=(\sqrt2-1)b$. A real symmetric passive three-mode matrix from the KLM construction is

$$
U=\begin{pmatrix}
\gamma&b&c\\
b&1/2&\gamma/2\\
c&\gamma/2&\sqrt2-1/2
\end{pmatrix},\qquad U^TU=I.
\tag{BG11}
$$

Mode 0 contains the unknown qutrit; auxiliary modes 1 and 2 begin in $|1,0\rangle$. Define the creation polynomial

$$
P_n(z)=\left(\sum_{j=0}^2U_{j0}z_j\right)^n
\left(\sum_{j=0}^2U_{j1}z_j\right).
$$

For each detector record $(a,b')$ with $a,b'\ge0$ and $a+b'\le3$, put $h=n+1-a-b'$. The complete retained-mode Kraus formula is

$$
L_{a,b'}|n\rangle=
\begin{cases}
\displaystyle\sqrt{\frac{h!a!b'!}{n!}}
[z_0^h z_1^a z_2^{b'}]P_n(z)\,|h\rangle,&h\ge0,\\
0,&h<0.
\end{cases}
\tag{BG12}
$$

Thus all ten records and retained levels $0,1,2,3$ are specified, including every failed coherence. For arbitrary reference $R$, the recorded instrument acts as
$\sum_{a,b'}|a,b'\rangle\langle a,b'|\otimes(L_{a,b'}\otimes I_R)\rho(L_{a,b'}^\dagger\otimes I_R)$.
Equation (BG12) follows by expanding the transformed creation operators on the normalized input $(a_0^\dagger)^na_1^\dagger|0\rangle/\sqrt{n!}$; its factorials convert the monomials to normalized output Fock states. Unitarity of (BG11) gives completeness without dropping any outcome.

For $(a,b')=(1,0)$, the three coefficients are $(1/2,1/2,-1/2)$, so

$$
L_{1,0}=G/2,\qquad
L_{1,0}^\dagger L_{1,0}=I_{\mathcal C}/4,\qquad
\sum_{(a,b')\ne(1,0)}L_{a,b'}^\dagger L_{a,b'}=3I_{\mathcal C}/4.
\tag{BG13}
$$

This is an achievable ordinary gate at input-independent probability $1/4$, retaining all nine input/reference matrix units. Its failure is not harmless repetition either. Explicitly,

$$
L_{3,0}=\sqrt{3/8}\,|0\rangle\langle2|,
\qquad
L_{0,0}=b\sum_{n=0}^2\sqrt{n+1}\,\gamma^n|n+1\rangle\langle n|.
\tag{BG14}
$$

The former irreversibly removes two code sectors; the latter leaks $|2\rangle$ into $|3\rangle$. Neither is replaced by an artificial erasure of known data. The larger accepted yield is sufficient to close this proposed advantage on the declared exact-gate task, while leaving other full-instrument utilities to their own comparison.

## Resource ledger and executable scope

The ordinary auxiliary photon can be prepared offline, but its generation probability, purity, storage, synchronization, auxiliary vacuum mode, passive circuit, counters and restoration must be paid. One explicit ideal source ledger uses (BG1) on sacrificial vacuum, independently of the unknown data. Resolving exactly one idler photon gives a signal photon with probability $p_{\rm src}=x_0(1-x_0)\le1/4$, $x_0=u_0^2$, because $1/4-p_{\rm src}=(x_0-1/2)^2$. At $x_0=1/2$, one source opportunity followed, conditional on that herald, by one KLM gate opportunity has joint exact-gate probability $1/16>(3-2\sqrt2)/8$. This charges one amplifier call per overall attempt, as well as the extra passive modes and number counters. Source failures leave the data untouched only if the sacrificial preparation and failed outputs are isolated from its port; input waiting/delay, synchronization, storage and source-reset time must then be paid. This is an achievable ideal probability ledger, not a physical clock-rate comparison or equality of all resources.

The order family pays its amplifier pump, tap, both number records, independent helper preparation/readout, actual coherent routing or herald erasure, delay compensation, phase locks, modal selection and every failed launch. Availability of the ideal coherent port is an optimistic premise, not inferred from a scattering diagram. Extra deterministic emitter controls must satisfy their actual number-dependent, reset and output-mode constraints. Neither side receives a free bypass of the unknown data. Physical clock time, detector loss and imperfections require a specified device model before comparing useful gate rates.

The standard-library [exact replay](../checks/architecture/bosonic_order_gates.py) exposes `verify_finite_gain_ns()`, `verify_klm_qutrit()` and their aggregate `verify()`. The first checks the one-pair and two-pair successful maps on all nine matrix units each, nine no-count coherence ingredients, direct physical herald probabilities, helper/gain polynomial identities, threshold contamination and six higher-count ingredients. The second reconstructs all ten KLM Fock-record probabilities, the nine successful reference matrix units, and irreversible/leakage failure witnesses in exact arithmetic. Formula (BG12) supplies the full failed coherence maps analytically; the finite replay does not separately certify each failed cross coefficient. Active predicates run normally and under optimization.

The infinite primitive normalization, all-count classification, helper optimality, recovery impossibility and physical access/cost hypotheses are analytic arguments above. The finite replay is not a multimode device fit, a proof of a hardware rate, an optimum over arbitrary Gaussian or non-Gaussian gadgets, or a simulation theorem for every failure utility. A useful positive successor must supply a conditional operation outside this two-primitive polynomial family, or a better paid failed-output/recovery trajectory against ordinary herald-erased optics, KLM and available gate-teleportation methods. The present one-addition/one-subtraction exact NS candidate is closed on accepted yield and is not repeat-safe.
