# Known-reflection diagnostics: ordinary instruments and physical targets

This is a proof component of [NR-R06](../architecture-baselines.md#nr-r06).
It separates complete measured-output identities from the physical
preparation, measurement and many-body evolution ports they require.

<a id="nr-r06-reflection-diagnostics"></a>

### A measured reflection/noise switch on sector-diagonal inputs

Let \(V=V^\dagger=V^{-1}\) be a specified reflection on a finite-dimensional
target \(S\), \(P_v=(I+vV)/2\), and \(\mathcal E\) an arbitrary CPTP map
with actual Kraus operators \(K_j\). Use a plus order control, then read
that control in X. Fix the convention
\(L_{j,s}=(VK_j+sK_jV)/2\), \(s=\pm1\); a reversed convention only adds
an irrelevant measured-flag scalar. All target formulas below are tensored
with identity on a passive reference \(R\).

**Exact measured instrument.** Suppose the actual input satisfies
\([V\otimes I_R,\rho_{SR}]=0\). Then

\[
\sigma_s=\sum_{y=\pm1}(P_y\otimes I_R)
 (\mathcal E\otimes\mathrm{Id}_R)
 [(P_{sy}\otimes I_R)\rho_{SR}(P_{sy}\otimes I_R)]
 (P_y\otimes I_R). \tag{RI1}
\]

Indeed, \(P_yL_{j,s}P_v=(y+sv)P_yK_jP_v/2\), so only \(v=sy\) survives.
The input has no cross-sector terms. Resolving its two input sectors and
the two output sectors therefore gives (RI1), with all Kraus records
summed only after their fine maps have been compared. Positivity and
trace preservation give \(\sum_s\operatorname{Tr}\sigma_s=1\).

An ordinary circuit exactly realizes this whole measured-X/target/reference
instrument: perform an initial **Lueders** V measurement, retain its sign
v, use \(\mathcal E\) once, perform a final Lueders V measurement with
sign y, and report \(s=vy\). Initial measurement does not disturb the
unconditional sector-diagonal input, including correlations within either
degenerate eigenspace. The two measurements must preserve that within-sector
coherence; equal outcome probabilities alone are not sufficient. If the
input is known to occupy one eigensector \(v_0\), the first measurement is
unnecessary: \(\sigma_s=P_{sv_0}\mathcal E(\rho)P_{sv_0}\). Thus a known
stabilizer-sector input reduces the arbitrary-noise switch to one ordinary
final syndrome instrument, without a Pauli-noise assumption.

For the fixed, unreferenced input \(I/d\), (RI1) also reads

\[
\sigma_s=\frac{VE(I)V+E(I)+s[VE(V)+E(V)V]}{4d}
 =\frac1d\sum_yP_y\mathcal E(P_{sy})P_y. \tag{RI2}
\]

One may sample v with probability \(r_v/d\), \(r_v=\operatorname{Tr}P_v\),
prepare \(P_v/r_v\), call E once, and measure V at output. Zero-rank sectors
are omitted. A nondestructive Lueders output measurement matches the
retained target state. Destructive output measurement only matches the
joint \((s,y)\) probability law; it supplies no retained payload. For a
unitary E this includes the real unitary/reflection commutator fringe.
Choosing its supplied operation as W(t) covers the corresponding
four-point OTOC. This is a measured-instrument statement, not a general
OTOC learning or physical-rate theorem.

**State-dependent robustness.** Let \(\Delta_V(\rho)=\sum_vP_v\rho P_v\),
with reference identities implicit, and let \(\mathsf S_X\) denote the
complete native classical-X-flag/target channel. The same ordinary
measurement circuit on any input is
\(\mathsf O=\mathsf S_X\circ\Delta_V\). Contractivity gives

\[
\tfrac12\|\mathsf S_X(\rho)-\mathsf O(\rho)\|_1
 \le\tfrac12\|\rho-\Delta_V\rho\|_1
 =\|P_+\rho P_-\|_1
 \le\sqrt{\epsilon(1-\epsilon)},\quad
 \epsilon=\operatorname{Tr}(P_-\rho). \tag{RI3}
\]

The equality follows from the singular values of the off-diagonal block
matrix. For the last inequality, positivity factors its cross block as
\(A^{1/2}CB^{1/2}\), with \(\|C\|\le1\); Schatten Cauchy--Schwarz bounds
its trace norm by \(\sqrt{\operatorname{Tr}A\operatorname{Tr}B}\).
Any common flag-dependent recovery completed by its reject record remains
CPTP and contracts this distance. Consequently an all-launch score
\(q-\lambda bad\), \(\lambda\ge0\), differs by at most
\((1+\lambda)\|P_+\rho P_-\|_1\): its score observable ranges from
\(-\lambda\) to one. This is a state-dependent bound, not a diamond bound
or a yield-free conditional-fidelity assertion.

**Boundaries and cost.** For V=Z, E=Id and input \(|+\rangle\), native
always-plus output is \(|-\rangle\); the ordinary spectral circuit gives
\(I/2\). A Bell input likewise loses its intersector reference entanglement
under the initial measurement. These counterexamples do not affect (RI1),
which preserves arbitrary within-sector reference correlations. Even on
I/d, the full retained order control can contain coherences absent after
its X readout; no full-control simulation is claimed.

The [existing known-auxiliary compiler IQ1](../metrology.md#nr-r15-known-control-qec)
already gives an exact full-input/full-control/reference implementation
using two paid controlled-V placements around one common E. The present
lemma uses different, narrower spectral-access premises. Closest existing
owners are NR06 PM2--3 (Pauli eigenstate calibration/controlled-Pauli
payload checks), the scalar local-overlap estimator, and NR15 IQ1; none
is being reclassified as a new result ID or hardware advantage.

An executable V call alone does not provide its eigenspace preparation,
spectator-safe Lueders measurement, or their efficient synthesis. Pay
state preparation, both actual measurements where needed, ancillas,
leakage/readout/reset errors, classical records and the full deadline.
The reflected unitary and E must refer to the same actual chronological
module/dilation as the standard SWITCH; isolated reduced channels do not
supply a route with different bath histories. The algebra can include
retained environment outputs by extending V as identity there. An initial
interacting bath requires sector diagonality of the entire joint input,
not merely of its reduced S marginal, or an independently valid CPTP E.

The finite checker uses rational complex reflections, nonunital channels,
degenerate sectors and passive references, plus explicit scope witnesses.
Its fixtures do not prove the universal identities, certify inexpensive
spectral controls, or establish a native physical implementation.

<a id="nr-r06-forward-diagnostics"></a>

## Forward-only many-body diagnostics need the right observable

Two new 2026 physical ports make the ordinary baseline more concrete.
Neither supplies an executable coherent order router for two opaque
many-body operations. Large state dimension and difficult time reversal
alone do not establish that a useful diagnostic needs a large quantum
reference memory.

### Rydberg spreading with ordinary randomized quenches

[Toga et al., arXiv:2604.05038v1](https://arxiv.org/html/2604.05038v1),
Secs. II–IV, implement forward-only paired global-quench measurements
on Aquila. Their ledger is $2N_U N_S$ shots, with about 4 microseconds
coherence and 1 microsecond allocated to quenches. Nearby Hamiltonian
settings reuse calibration; larger changes require retuning. These
are intrashot limits, not a fresh two-query drift deadline. The
normalization and operator definitions need independent qualification.

The useful decision can be a specified spreading-front arrival threshold
under two proposed Hamiltonian settings. It must be fixed before scoring
either protocol. A SWITCH of a forward unitary $U$ and a local reflection
$V$ at maximally mixed input has control mean

$$C=\operatorname{Re}\operatorname{Tr}(VU^\dagger VU)/d.$$

This two-point statistic is different from the four-point OTOC of
$W(t)=U^\dagger WU$ and $V$. For example, for a CNOT evolution,
$V=X_{\rm control}$ and $W=Z_{\rm target}$, one obtains $C=0$ and
$\operatorname{Tr}[W(t)VW(t)V]/d=-1$. Routing the forward $U$ does not
supply an executable $W(t)$ module. An order proposal for the genuine
four-point target must establish that stronger physical port.

An ordinary reflection-eigenstate pilot already estimates $C$ with one
forward evolution when the required known preparation/readout is
available; it does not require a coherent copy of the many-body state.
Aquila's limited local addressing must be respected before declaring
that preparation free. Ordinary randomized quenches are instead a
demonstrated candidate baseline for its four-point diagnostic, with
design bias, reuse and all shots charged. Neither its raw estimator nor
its matching lightcone is used here as a rigorous normalization theorem.
For retained-output claims, a complete nondestructive measurement port
and unknown-output comparison remain separate requirements.

### Weak records from a retained interacting gas

[Altuntaş and Spielman, arXiv:2604.17719v1](https://arxiv.org/html/2604.17719v1),
Eq. (2) and the main experiment, measure symmetrized two-time density
correlations of a Bose gas by ordinary phase-contrast images. They infer
the dynamical structure factor and sound speed without reversing the
many-body evolution. Probe illumination totals 16.4 microseconds per
image; this is not the full image/trial clock. Each parameter setting
uses 128 preparations. In a displayed dataset the two probes
scatter about 0.01 and 0.125 photons per atom. The first probe leaves the
gas available for the second, with measurement backaction present.
Sign-weighting both weak-value subensembles retains all records;
stronger postselection increases conditional amplitude while degrading
signal-to-noise. These are spatially resolved classical records, not a
clean quantum reference of the gas.

A useful retained-system task is choosing probe strength and delay to
estimate a collective-mode dispersion within an allowed heating/loss
budget. The ordinary weak-record estimator already measures the stated
symmetrized observable. A proposed native antisymmetric-response or
four-point diagnostic must specify a different useful target and the
actual optical measurement dilation that accesses it. A classical
optical pilot can characterize imaging transfer noise, but does not
replace atomic quantum backaction.

<a id="nr-r06-rydberg-reflection-sector"></a>

## A reflection-sector guard for global Rydberg randomization

This is a conditional ideal-model benchmark, not a verdict about all
Aquila hardware or the paper's noisy data.

### Primary-source interface

[Toga et al., arXiv:2604.05038v1](https://arxiv.org/html/2604.05038v1),
Sec. II and Algorithm 1, specify global quenches from $|0\rangle^{\otimes N}$;
the local perturbation follows randomization. Figure 1's waveform shows
global $\Omega,\Delta$ and the later local detuning pulse $\Delta_0$.
Sec. III uses a chain with one spacing parameter $a$, but no complete
position/control-vector file was found in the inspected primary. Its
noisy model includes atom-distance and control noise, and the source
explicitly credits noise with improving agreement. Thus uniform
reflection-symmetric geometry and global Hamiltonian controls below
are declared ideal premises pending actual schedule verification.

### Exact support obstruction

Let $R$ reverse the order of the $N$ spins and take

$$H(t)=\Omega(t)\sum_jX_j-\Delta(t)\sum_jn_j+
       \sum_{j<k}J(|j-k|)n_jn_k.$$

This includes the full distance-dependent van der Waals couplings on
an equally spaced open chain; dropping longer-range couplings is not
needed. Relabelling $j\mapsto N+1-j$ leaves every term invariant, so
$[H(t),R]=0$ at every time. All products of these evolutions commute
with $R$. Since $R|0^N\rangle=|0^N\rangle$, every noiseless randomized
preparation lies in $P_+=(I+R)/2$.

Reversal fixes $2^{\lceil N/2\rceil}$ computational strings. With
$d=2^N$, the sector dimensions are

$$r_\pm=\tfrac12(d\pm2^{\lceil N/2\rceil}).$$

For $N=8$, $d=256$, $r_+=136$ and $r_-=120$. Any average preparation
$\bar\rho$ supported in $P_+$ obeys

$$\tfrac12\|\bar\rho-I/d\|_1\ge
  \left|\operatorname{Tr}P_-(\bar\rho-I/d)\right|=15/32.$$

Consequently this ideal ensemble cannot be a full-space state 1-design,
and cannot be a full-space state or unitary 2-design. Randomizing the
global amplitudes or adding more such quenches cannot remove the exact
support restriction. This does not prove the accessible ensemble is
Haar within its sector.

### Correct sector second moment

For the hypothetical Haar ensemble of pure states in $P_+$, the second
moment is $(P_+\otimes P_+)(I+\mathrm{Swap})/[r_+(r_++1)]$. Therefore

$$\mathbb E_+\langle A\rangle\langle B\rangle=
\frac{\operatorname{Tr}(P_+A)\operatorname{Tr}(P_+B)
      +\operatorname{Tr}(P_+AP_+B)}{r_+(r_++1)}.$$

The compressed term is not generally the full-space trace of $AB$.
An exact local witness does not even require sector-Haar mixing:
every supported state satisfies $\langle Z_1\rangle=\langle Z_N\rangle$.
Its squared mean contrast is zero. Full-space Haar states instead give

$$\mathbb E_{\rm Haar}(\langle Z_1\rangle-\langle Z_N\rangle)^2
  =2/(d+1)=2/257\quad(N=8).$$

For sector-Haar at $N=8$, each endpoint's variance and their covariance
are $72/[136\cdot137]=9/2329$. Full-space Haar has zero endpoint
covariance and endpoint variance $1/257$. A single scalar resembling a
participation ratio does not establish all these required moments.

There can be genuine four-point target bias. As a mathematical example,
take $U=P_{\rm sym}+iP_{\rm antisym}$ on the mirror endpoint pair and
identity elsewhere; let $W=Z_1$, $V=Z_N$, $A=U^\dagger WU$ and
$B=VAV$. This $U$ commutes with reversal and $B=RAR$. Every $R+$ input
has identical $A,B$ expectations, so a normalized cross/self-correlation
ratio is one when the denominator is nonzero. Yet the full-trace
OTOC $\operatorname{Tr}(AB)/d$ is zero. This is not a claim that the
example is one of the paper's compiled Rydberg pulse sequences.

### Physical next test and boundaries

Obtain the actual eight-site coordinates and every site-dependent
drive/detuning during randomization. Confirm which ideal generators
commute with reversal. Compare the endpoint mean-contrast second moment
with zero and $2/257$, using independent shot groups or a calibrated
shot-noise subtraction; uncorrected finite-shot variance is not the
state-ensemble moment. Retain missing atoms, asymmetric readout and
all postselection records. Fit ordinary dynamical and estimator bias
against exact eight-spin evolution before interpreting a lightcone.

Spatially asymmetric controls, position disorder or local records can
invalidate the support premise. Even reflection-covariant local noise
can transfer population between sectors: covariance of a channel is
weaker than preservation of $P_+$ support. For example, applying a
uniformly random single-site $Z_j$ to $|+\rangle^{\otimes N}$ is
reflection-covariant but, for even $N$, gives $P_-$ weight $1/2$.
Global common amplitude noise that still commutes with $R$ does not
have this effect. Noise-induced leakage also does not by itself certify
a pure-state 2-design or an unbiased OTOC estimator.

The test qualifies a real ordinary benchmark. It establishes no SWITCH
advantage: any comparison must still supply the native four-point port
and grant ordinary eigenstate/readout controls where executable. If
$S=W(t)$ is supplied as a reflection, an ordinary local-$V$ eigenstate
pilot uses one $S$ invocation and the same costly forward/backward
evolutions to sample $\operatorname{Tr}(VSVS)/d$. Uniform input mixing
and nondestructive retained-output readout remain physical premises.
