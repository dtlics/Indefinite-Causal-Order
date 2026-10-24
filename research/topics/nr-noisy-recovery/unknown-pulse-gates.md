# Unknown anticommuting pulse gates: exact-call gap and ordinary timing baselines

<a id="nr-r21"></a>

## NR-R21 — An exact physical-gate call gap does not imply shorter pulses

For a continuously unknown pair of anticommuting qubit axes, the exact
ordinary causal certificate below bounds completion by call two by
$13/20$, even with classical timing and order adaptation. An almost-surely
delivering exact ordinary protocol therefore needs mean at least $47/20$
calls, while a supplied native order route followed by terminal ordinary
repair uses $7/3$: an ideal gap of $1/60$.
This is a physical unknown-input gate target, not a tracked unknown frame.
The same target has an exact ordinary three-pulse implementation with
less interaction exposure than even the first native attempt.

The [NR-R17 owner](braided-magic.md#nr-r17) already contains the
quarter-braid gate mechanism, magic witness and protected-Ising router
obstruction. The distinct result here concerns continuously unknown
axes, classically chosen timed calls, a complete causal certificate and
ordinary timing/approximation baselines. It supplies neither a new
magic-generation mechanism nor a hardware advantage. No inspected
device supplies the complete promised interface.

## Access, output and unknown-frame promise

Let $A,B$ be unknown Hermitian involutions on a finite-dimensional data
space,

$$
A^2=B^2=I,\qquad AB=-BA.
$$

For a known angle $\theta$, a named pulse supplies
$R_A(\theta)=e^{-i\theta A}$ or $R_B(\theta)=e^{-i\theta B}$.
The same pair is repeatable throughout a job. The target, for
$0<\alpha<\pi/2$, is the physical unknown-input channel

$$
\mathcal U_\alpha=\operatorname{Ad}_{U_\alpha},\qquad
U_\alpha=e^{-i\alpha H},\qquad H=(A+B)/\sqrt2.
\tag{AP1}
$$

Every statement retains an arbitrary passive reference. No axis matrix,
common-frame key, oracle-related program or input-dependent advice is
supplied. The constructions do not learn the axes. The algebra implies an
encoded qubit with a multiplicity space: $B$ maps the $+1$ eigenspace of
$A$ unitarily onto its $-1$ eigenspace, so the two spaces have equal
dimension. Choosing paired bases identifies $A,B$ with two Pauli axes
tensored with an identity. This observation proves dimension-independent
identities; it does not grant the unknown encoding as a control.

Ordinary processing may use its actually supplied known operations,
ancillas, instruments and retained records. Separate timed pulses do not
automatically grant coherent selection between them, a do/don't-pulse
port, a simultaneous $A+B$ drive, a protected input-bearing bypass or a
known third axis. Conversely, a physical device that supplies any such
port must allow its ordinary use. Continuously variable angles are an
additional premise relative to fixed protected Ising exchanges.

An abstract pulse count charges each named invocation once. A physical
duration also charges its angle, start/stop transients, setup, idle
couplings and noise. Negative angles require signed control or their
actual positive-time replacements modulo $\pi$, whose global phase is
irrelevant only on the stated unconditionally applied data pulse.

## Exact ordinary synthesis without axis learning

Define principal angles

$$
h=\arctan\!\left(\frac{\tan\alpha}{\sqrt2}\right),\qquad
b=\arcsin\!\left(\frac{\sin\alpha}{\sqrt2}\right).
$$

Multiplying the involution exponentials gives

$$
R_A(x)R_B(y)R_A(z)
=\cos y\cos(x+z)I-i\cos y\sin(x+z)A
-i\sin y\cos(x-z)B-\sin y\sin(x-z)AB.
\tag{AP2}
$$

For $x=z=h/2$ and $y=b$, the $AB$ term vanishes and

$$
\sin b=\frac{\sin\alpha}{\sqrt2},\qquad
\cos b\sin h=\frac{\sin\alpha}{\sqrt2},\qquad
\cos b\cos h=\cos\alpha.
$$

Consequently the three ordinary pulses implement

$$
R_A(h/2)R_B(b)R_A(h/2)=U_\alpha.
\tag{AP3}
$$

This is an operator identity for every allowed pair, hence also for
reference-entangled inputs. Its chronological word is symmetric, so
the displayed convention creates no time-order ambiguity.
Exchanging $A,B$ gives another exact construction.

On this interval,

$$
\sin^2h=\frac{\sin^2\alpha}{1+\cos^2\alpha}
>\frac{\sin^2\alpha}{2}=\sin^2b,
\qquad 0<b<h.
\tag{AP4}
$$

Thus the ordinary word has integrated angle $h$ on one axis and $b$ on
the other. A native first attempt below uses $h$ on both. At angular
rates $\Omega_A,\Omega_B>0$, the achieved ordinary duration is
$h/\Omega_A+b/\Omega_B$, or the exchanged version. It is no larger on
either axis and strictly smaller on one than that native first attempt.
This is an achievable exposure comparison, not a time-optimal-control
theorem.

## Complete native flags and two different exact completion policies

Supply an independent clean order helper in $|+\rangle$ and a
nondestructive two-order route for $R_A(h),R_B(h)$. Its $X$ readout gives

$$
\begin{aligned}
K_+&=\cos^2h\,I-i\cos h\sin h(A+B)
       =\sqrt{1-q}\,U_\alpha,\\
K_-&=\sin^2h\,AB,\qquad q=\sin^4h.
\end{aligned}
\tag{AP5}
$$

The minus global phase depends on which route is called zero; its CP
map does not. Squaring the effects proves probabilities $1-q,q$ on
every input and reference. This is the timed extension of the owner's
[complete two-order branches](braided-magic.md#nr-r17), not a new
magic-generation primitive.

Two $\pi/2$ involution pulses apply $(AB)^\dagger$ up to a global phase
and restore the failed unknown input. Repeating after this actual
rollback, with ideal independent helper cycles, gives

$$
\begin{aligned}
\mathbb E N_{\rm attempts}&=(1-q)^{-1},&
\mathbb E N_{\rm rollbacks}&=q/(1-q),\\
\mathbb E Q_{\rm rollback}&=\frac{2(1+q)}{1-q},&
\mathbb E \Theta_A=\mathbb E\Theta_B
&=\frac{h+(\pi/2)q}{1-q}.
\end{aligned}
\tag{AP6}
$$

Here $\Theta_j$ is total absolute pulse angle. The two rollback calls
are full $\pi/2$ pulses, not short $h$ pulses. Routing, each helper
preparation/readout/reset, actual recovery and data waiting remain
additional costs. A known algebraic frame is not the physical output
channel (AP1) unless the endpoint accepts that frame and supplies the
operations needed to use it. In particular, tracking the unknown $AB$
action is not the same as an available known laboratory Pauli.

A stronger displayed policy uses only one native attempt. After its
minus flag, apply an exact ordinary three-pulse terminal repair and
stop. In (AP2) take

$$
x=h/2-\pi/2,\qquad y=\pi/2-b,\qquad z=-h/2.
$$

Its coefficients give $R_A(x)R_B(y)R_A(z)=U_\alpha AB$, which differs
from $U_\alpha(AB)^\dagger$ only by a global minus sign. Both corrected
branches therefore implement $\mathcal U_\alpha$, including their full
reference output, and

$$
\mathbb E Q_{\rm hybrid}=2+3q.
\tag{AP7}
$$

For signed angles priced by absolute exposure, the repair uses total
$A$ angle $\pi/2$ and $B$ angle $\pi/2-b$, hence total angle $\pi-b$.
Positive-time replacements have the same three named calls but may be
longer. This policy is not asserted optimal; for some angles the
ordinary three-pulse word alone is the better count.

At $\alpha=\pi/4$, $h=\arctan(1/\sqrt2)$, $b=\pi/6$, $q=1/9$.
The rollback policy uses mean $5/2$ calls, while the terminal-repair
policy uses $7/3$. The ordinary exact word uses three calls. At equal
unit angular rates its exposure is $h+\pi/6\approx1.139078$, whereas
rollback RUS uses
$[2h+\pi/9]/(8/9)\approx1.777528$.
Even the first native attempt has exposure $2h>h+\pi/6$.
These compare the displayed circuits, not the full ordinary
expected-query frontier.

For example, charge common setup $\tau_s$ per named pulse and native
per-attempt helper/router overhead $\tau_C$. At equal rate $\Omega$,
the displayed rollback policy can beat (AP3) in this ideal ledger only if

$$
\tau_s>
\frac{2}{\Omega}\left[
\frac{2h+\pi/9}{8/9}-h-\pi/6\right]
+\frac94\tau_C.
\tag{AP8}
$$

For the one-attempt hybrid, the corresponding necessary condition is

$$
\tau_s>\frac32\left[
\frac{h-b+(\pi-b)/9}{\Omega}+\tau_C\right].
\tag{AP9}
$$

Other overhead differences must be added rather than assumed equal.
Calibration compiled once per job, continuously present couplings and
reusable waveform preparation are not automatically per-activation
$\tau_s$. A capped rollback policy has reject probability $q^J$ after
$J$ attempts; the failed payload and every correction clock must remain
in its deadline instrument. Unresolved noise or a destructive flag
readout invalidates the exact retry maps.

## Achievable ordinary approximation at two and fractional mean calls

First consider only bare words $R_B(y)R_A(x)$, without ancillary
processing or intermediate measurements. Their normalized trace
overlap with $U_\alpha$ is

$$
f=\cos\alpha\cos x\cos y+
\frac{\sin\alpha}{\sqrt2}(\sin x\cos y+\cos x\sin y).
$$

Writing this as a bilinear form on unit vectors $(\cos x,\sin x)$ and
$(\cos y,\sin y)$ gives the real symmetric matrix

$$
M=\begin{pmatrix}
\cos\alpha&\sin\alpha/\sqrt2\\
\sin\alpha/\sqrt2&0
\end{pmatrix}.
$$

Its largest singular value is
$(\cos\alpha+\sqrt{1+\sin^2\alpha})/2$, attained by equal angles along
its top eigenvector. Thus the best entanglement fidelity **within this
bare two-pulse class** is

$$
F_{2,\rm bare}=\frac{1+\sqrt{1-\sin^4\alpha}}2.
\tag{AP10}
$$

This is an achievable comparator, not an arbitrary-ancilla or adaptive
two-call converse.

A different ordinary circuit chooses the two orders of equal pulses
with a fair classical bit and discards that internal bit:

$$
\mathcal R_h=\tfrac12\operatorname{Ad}_{R_B(h)R_A(h)}
            +\tfrac12\operatorname{Ad}_{R_A(h)R_B(h)}
=p\operatorname{Ad}_{U_\beta}+q\operatorname{Ad}_C,
\quad C=iAB,
\tag{AP11}
$$

where $q=\sin^4h$, $p=1-q$ and
$\tan\beta=\sqrt2\tan h$ for $0<h<\pi/2$.
The identity follows by summing the two complete flags (AP5), with the
target angle replaced by $\beta$. It is the explicit ordinary completion
used by the separate [final-flag comparison](methods/final-flag-completion.md).
It does not reproduce the native flagged service.

Its full all-input half-diamond error to (AP1) is exactly

$$
\epsilon_2(h,\alpha)
=\frac12\|\mathcal R_h-\mathcal U_\alpha\|_\diamond
=\frac{q+\sqrt{q^2+4p\sin^2(\beta-\alpha)}}2.
\tag{AP12}
$$

Here is a norm proof, rather than a fidelity substitution. Compose with
$U_\alpha^\dagger$ and use normalized Choi vectors. In the orthonormal
plane corresponding to $I,-iH$, the difference from the identity
channel has matrix

$$
\begin{pmatrix}
p\cos^2\delta-1&p\sin\delta\cos\delta\\
p\sin\delta\cos\delta&p\sin^2\delta
\end{pmatrix},
\qquad \delta=\beta-\alpha.
$$

Its trace is $-q$ and determinant $-p\sin^2\delta$, so its eigenvalues
are $(-q\pm\sqrt{q^2+4p\sin^2\delta})/2$.
Every real normalized eigenvector $(a,b)$ represents the unitary
$aI-ibH$. The remaining Choi direction is the unitary
$U_\alpha^\dagger C$, orthogonal to that plane, with eigenvalue $q$.
This signed sum of unitary channels bounds the diamond norm above by
the sum of the absolute eigenvalues. A normalized maximally entangled
encoded-qubit input attains exactly that trace norm, proving equality.
The multiplicity identity and any passive reference leave it unchanged.
Degenerate zero eigenvalues follow by the same decomposition or continuity.

At $\alpha=\pi/4$, take the exact ordinary angle $\tan h=2/3$. Then

$$
\epsilon_2=
\frac{16+\sqrt{51970-36504\sqrt2}}{338},
\qquad
0.10233<\epsilon_2<0.10234<1/9.
\tag{AP13}
$$

The inequalities can be checked by positive algebraic squaring; they do
not rely on a numerical optimum over angles. Choose exact Euler (AP3)
with probability $1/3$ and this two-call circuit with probability $2/3$,
discarding the internal choice. Its mean pulse count is $7/3$ and

$$
\mathcal O=\tfrac13\mathcal U_{\pi/4}+\tfrac23\mathcal R_h,\qquad
\tfrac12\|\mathcal O-\mathcal U_{\pi/4}\|_\diamond
=\tfrac23\epsilon_2<0.068227.
\tag{AP14}
$$

This approximation is not the native exact service. It is a stronger
ordinary benchmark at that mean than treating a two-call hard cap as
an expected-$7/3$ bound. If the endpoint requires retaining the random
choice, its recorded output must be compared separately.

## Prior mechanisms and actual selector access

[Zhao and Yuan, Quantum **5**, 534 (2021),
arXiv:2103.07988v2](https://arxiv.org/html/2103.07988v2),
Section 4.3 and Appendix D.2, already give exact anticommuting-sum
simulation through LCU. Their implementation uses coherent term
selection, preparation and amplification; the known-Pauli setting does
not supply controlled unknown pulses from ordinary opaque calls.
[Trillo, Dive and Navascués, PRL **130**, 110201 (2023),
arXiv:2205.01131v1](https://arxiv.org/html/2205.01131v1),
Eq. (1) and Proposition 1, give commutator/anticommutator outputs and
recursive repair for repeatable unknown qubit operations. The
[existing rewinding owner](obstructions.md#nr-r05) keeps its separate
stopping/loss analysis. Neither citation is claimed to establish this
task's ordinary optimum, and there is no new-mechanism or priority claim.

An actually supplied coherent selector can strengthen the ordinary
benchmark. Suppose one interval implements
$\operatorname{SELECT}\{e^{-i\beta A},e^{-i\beta B}\}$ at a common angle,
without assuming an identity bypass. With a clean helper and $X$
readout, $\tan\beta=\sqrt2$ gives

$$
L_+=\sqrt{2/3}\,U_{\pi/4},\qquad
L_-=-i\sqrt{1/3}\,D,\qquad D=(A-B)/\sqrt2,\quad D^2=I.
\tag{AP15}
$$

A three-pulse repair after minus is available from (AP2). With
$h=\arctan(1/\sqrt2)$ and $\beta=\pi/2-h$, take
$x=\pi/2-h/2$, $y=-\pi/3$ and $z=h/2$.
Their sums and differences are $x+z=\pi/2$, $x-z=\beta$;
(AP2) gives $-iA/2+iB/2+AB/\sqrt2=-iU_{\pi/4}D$.
Both branches then deliver the target up to a global phase, with mean
$1+(1/3)3=2$ named intervals in this selector model. All repair angles,
whose absolute total is $5\pi/6$, selector pulses and helper operations
remain charged. This different
port is neither implied by abstract order control nor an ordinary
restriction one may impose on a device that genuinely supplies it.
Selection among $I,A,B$ would be a still stronger LCU premise.

## Causal comparison and its limits

The exact Euler word, the restricted optimum (AP10), and the achievable
error (AP12) do not bound all ordinary causal processors with ancillas,
adaptive measurements, either call order and arbitrary pulse angles.
Nor does the existence of a three-call exact circuit prove that every
ordinary exact circuit has mean three. A finite Pauli-label prior is
unsuitable for that inference: ordinary Bell probing can reveal
orthogonal labels and permit subsequent known processing.

The following independent causal certificate supplies a converse for a
specified exact service. In the qubit subproblem, let
$A=\boldsymbol a\cdot\boldsymbol\sigma$ and
$B=\boldsymbol b\cdot\boldsymbol\sigma$ range over every unknown
orthonormal frame. The physical target is

$$
U=U_{\pi/4}=\frac I{\sqrt2}-\frac i2(A+B).
\tag{AP16}
$$

A query is one indivisible, uncontrolled application of
$e^{-iaA}$ or $e^{-ibB}$ on its oracle wire. Its real angle and type
are chosen classically before that call, possibly after earlier
records. Arbitrary known processing, ancillary memories, routing among
wires and instruments before, between and after calls are allowed.
There is no oracle-related advice or intra-call interaction. Coherent
angle or query-type selection, a controlled oracle and simultaneous
$A+B$ access are different interfaces. Known surrounding controls do
not become forbidden merely because they can route quantum states.

Exact success is a heralded subchannel proportional to
$\operatorname{Ad}_U$ for every frame and every input/reference, with
the physical gate delivered. An unspecified unknown $AB$ frame is not
an allowed output. Under this model, the probability of exact success
by call two obeys

$$
p_2\le\frac{13}{20}.
\tag{AP17}
$$

This is a uniform bound over real pulse angles and classical adaptive
records, not a grid optimization or the optimum value of $p_2$.
The [expected-query certificate in NR-R19](backaction.md#nr-r19)
has a different commuting promise and target and cannot be transferred
to this proof.

### Exact support and causal normalization

Use unnormalized vectorization $|X\rangle\rangle=\sum_{ij}X_{ij}|i,j\rangle$.
A successful two-query comb $C$ has port order
$(F,B_{\rm out},B_{\rm in},A_{\rm out},A_{\rm in},P)$.
For its fine Kraus vector $w$, the linked matrix is

$$
K_{fp}=\sum_{b_o,b_i,a_o,a_i}
w_{f,b_o,b_i,a_o,a_i,p}
(U_B)_{b_o b_i}(U_A)_{a_o a_i}.
\tag{AP18}
$$

Equivalently the Choi link uses the transposed oracle Choi matrices.
A qubit unitary Choi matrix has trace two, with no normalized-Bell
factor in this convention. The literal sequential vector
$w_{f,b_o,b_i,a_o,a_i,p}
=\delta_{f,b_o}\delta_{b_i,a_o}\delta_{a_i,p}$
links to $U_BU_A$ and fixes the normalization.
Positive causal completion gives $C_1,C_0\ge0$ with

$$
\operatorname{Tr}_F C\le I_{B_{\rm out}}\otimes C_1,\qquad
\operatorname{Tr}_{B_{\rm in}}C_1=I_{A_{\rm out}}\otimes C_0,\qquad
\operatorname{Tr}_{A_{\rm in}}C_0=I_P.
\tag{AP19}
$$

The dimensions of $C,C_1,C_0$ are $64,16,4$.

For fixed angles write $c_A=\cos a,s_A=\sin a$ and similarly for $B$.
Each output Pauli coefficient $k_o$ of a fine linked map is bilinear in
the sixteen features $(1,\boldsymbol b)_\mu(1,\boldsymbol a)_\nu$.
Rescale by the nonzero target coefficients:
$Z_0=k_0/(1/\sqrt2)$ and $Z_i=k_i/(-i/2)$.
Exact success forces

$$
Z_i=(a_i+b_i)Z_0,\qquad i=1,2,3.
\tag{AP20}
$$

Indeed the desired Choi matrix has rank one; each positive fine
contribution must have that support, since off-target positive terms
cannot cancel. There are 64 complex coefficient coordinates.
The [support replay](checks/architecture/anticommuting_pulse_support.py)
uses actual rational $SO(3)$ frames obtained from integer quaternions.
The resulting rational linear constraints have rank 59 modulo
1,000,003, with every denominator invertible there. Their rank over
$\mathbb Q$, $\mathbb R$ or $\mathbb C$ is therefore at least 59.
Five independent universal solutions are explicit: four invisible
maps with one $Z_o=\boldsymbol a\cdot\boldsymbol b$, and the proper map
$Z_0=1$, $Z_i=a_i+b_i$. Thus the universal kernel is exactly
five-dimensional. Every successful fine Kraus amplitude is constant
over the frame orbit; a hidden frame-dependent success amplitude is
not omitted.

For nonzero sines and cosines the transformation from physical query
coefficients to these Pauli features is invertible. In grouped order
$(F,P,B_{\rm out},B_{\rm in},A_{\rm out},A_{\rm in})$, put

$$
\begin{aligned}
e_I&=|I\rangle\rangle\otimes|I\rangle\rangle\otimes|I\rangle\rangle,\\
e_B&=\sum_i|\sigma_i\rangle\rangle\otimes
 |\sigma_i^*\rangle\rangle\otimes|I\rangle\rangle,\\
e_A&=\sum_i|\sigma_i\rangle\rangle\otimes
 |I\rangle\rangle\otimes|\sigma_i^*\rangle\rangle,\\
N_o&=\sum_i|\sigma_o\rangle\rangle\otimes
 |\sigma_i^*\rangle\rangle\otimes|\sigma_i^*\rangle\rangle,
\quad o=0,1,2,3,\quad \sigma_0=I.
\end{aligned}
$$

All sums in this display run over $i=1,2,3$.
Reorder these vectors into the causal port order. Their literal links are
$e_I\mapsto4c_Ac_BI$, $e_B\mapsto-4ic_As_BB$,
$e_A\mapsto-4is_Ac_BA$ and
$N_o\mapsto-4s_As_B(\boldsymbol a\cdot\boldsymbol b)\sigma_o=0$.
Consequently the exact-success support is spanned by $N_0,\ldots,N_3$
and

$$
E'=\frac{s_As_B}{\sqrt2}e_I+
       \frac{s_Ac_B}{2}e_B+\frac{c_As_B}{2}e_A,
\qquad E'\mapsto LU,\quad L=4c_Ac_Bs_As_B.
\tag{AP21}
$$

Writing a successful comb as a sum of fine vectors
$\lambda_jE'+\sum_o\eta_{jo}N_o$ gives
$p=L^2\sum_j|\lambda_j|^2$. The amplitude factor four and probability
factor sixteen follow from (AP18), without an extra Bell normalization.

### One uniform matrix sum of squares

The [exact certificate](checks/architecture/anticommuting_pulse_dual.json)
stores rational $Y,Z$ on ports
$(B_{\rm out},B_{\rm in},A_{\rm out},A_{\rm in},P)$ and
$(A_{\rm out},A_{\rm in},P)$ and a Gram matrix over $\mathbb Q(\sqrt2)$.
Set $W=(13/40)I_P$. The
[replay](checks/architecture/anticommuting_pulse_dual.py) reconstructs
and proves by exact positive LDL pivots that

$$
Y>0,\qquad
I_{B_{\rm in}}\otimes Z-\operatorname{Tr}_{B_{\rm out}}Y>0,\qquad
I_{A_{\rm in}}\otimes W-\operatorname{Tr}_{A_{\rm out}}Z>0.
\tag{AP22}
$$

These inequalities imply $Z,W\ge0$ as well.
Let $B_{\rm dual}=I_F\otimes Y$, and define
$H_{ij}=\langle e_i|B_{\rm dual}|e_j\rangle$,
$h_i=\langle e_i|B_{\rm dual}|N_0\rangle$,
$n=\langle N_0|B_{\rm dual}|N_0\rangle$, where
$(e_1,e_2,e_3)=(e_I,e_B,e_A)$.
These contractions are real and rational, as checked exactly.
The replay checks exact decoupling of each of these four vectors from
$N_1,N_2,N_3$. Their remaining triplet block is positive because
$B_{\rm dual}\ge0$.

Reduce nondegenerate angles modulo $\pi$ so that $c_A,c_B>0$; this
changes only the global phases of unconditional calls and still allows
negative tangents. Put

$$
x=\tan a,\quad y=\tan b,\quad
D=(1+x^2)(1+y^2),\qquad
v=(xy/\sqrt2,x/2,y/2)^T.
$$

Then $E'=(v_1e_I+v_2e_B+v_3e_A)/\sqrt D$ and $L=4xy/D$.
Congruence of the $(E',N_0)$ block by
$\operatorname{diag}(D,\sqrt D)$ reduces
$B_{\rm dual}$ minus the success objective to

$$
M(x,y)=
\begin{pmatrix}
Dv^THv-16x^2y^2&Dv^Th\\
Dh^Tv&Dn
\end{pmatrix}.
\tag{AP23}
$$

The stored $12\times12$ matrix $Q$ has strictly positive exact LDL
pivots and satisfies the polynomial identity
$M=R(x,y)^TQR(x,y)$.
The first column of $R$ is the eight monomials
$(x,y,xy,x^2,y^2,x^2y,xy^2,x^2y^2)$ followed by four zeros;
the second is eight zeros followed by $(1,x,y,xy)$.
The replay verifies every coefficient of all three independent matrix
blocks in $\mathbb Q(\sqrt2)$. This proves positivity for all real
$x,y$, not just sampled pulse angles. Together with triplet positivity,
it proves for every exact-success comb piece

$$
p\le\operatorname{Tr}[(I_F\otimes Y)C].
\tag{AP24}
$$

Combining (AP24), (AP19) and (AP22) gives $p\le\operatorname{Tr}W=13/20$
at fixed nondegenerate angles. The essential fact for adaptation is that
the same $Y,Z,W$ work for every angle.

### Endpoints, adaptive records and stopping

At $\sin a=0$ the first oracle channel reveals no $A$ information.
With $B$ fixed, varying $A$ around its perpendicular circle changes
the target channel while leaving that branch unchanged, so its
universally exact success is zero. At $\cos a=0$, replacing $A$ by
$-A$ changes its sole pulse by only a global sign. This is an allowed
frame change, but the two target channels are not proportional: their
nonzero identity coefficients fix the proportionality phase while
their $A$ coefficients have opposite signs. Exact success is again
zero. The same arguments apply to $b$ endpoints. Thus (AP24) holds
there by positivity without a singular change of variables.

Branches using no query, one query or twice the same axis likewise
have zero exact success: hold the queried axis fixed and vary the
missing axis. Hence successful completion by two calls must query
$A$ then $B$ or $B$ then $A$.

Let record $r$ determine the first angle and record $s$ after the first
query determine the second angle. Include all known preprocessing,
ancillas and intermediate outcomes in these records. Their positive
subcombs satisfy

$$
\begin{aligned}
\operatorname{Tr}_F C_{rs}&\le I_{B_{\rm out}}\otimes C_{1,rs},\\
\sum_s\operatorname{Tr}_{B_{\rm in}}C_{1,rs}
 &\le I_{A_{\rm out}}\otimes C_{0,r},\\
\sum_r\operatorname{Tr}_{A_{\rm in}}C_{0,r}&\le I_P.
\end{aligned}
\tag{AP25}
$$

The deficits permit branches that stop, continue beyond two queries,
fail or choose the same second query type. Applying the common
positive dual to each exact-success piece and summing gives

$$
\begin{aligned}
\sum_{rs}p_{rs}
&\le\sum_{rs}\operatorname{Tr}[
 (\operatorname{Tr}_{B_{\rm out}}Y)C_{1,rs}]\\
&\le\sum_r\operatorname{Tr}[
 (\operatorname{Tr}_{A_{\rm out}}Z)C_{0,r}]\\
&\le\operatorname{Tr}W=\frac{13}{20}.
\end{aligned}
\tag{AP26}
$$

Positivity of $Y,Z,W$ justifies each causal inequality, including
input-dependent instrument probabilities. For the reverse query
order rename $A,B$. The target is symmetric and the upstream price
is the same scalar $W=(13/40)I$. The two first-query-type branches
share the last normalization in (AP25), so their total has no extra
factor two.

For countable records the sums converge positively. For continuous
record and angle menus use the trace of the finite-dimensional Choi
instrument measures as a dominating positive scalar measure. Their
Radon–Nikodym densities are positive almost everywhere, and the common
dual inequalities integrate unchanged. A countable dense set of
frames selects one common full-measure record set on which rank-one
exactness holds; continuity of each fixed-record bilinear query
expression then supplies (AP20) for every frame. Standard measurable
physical instruments are assumed. Unbounded classical computations
or known gates add no oracle information; completed branches before
query three remain covered by the same positive subinstrument.

For an algorithm that delivers the exact physical target in finite time
almost surely on every frame and every input, let $Q_{\rm calls}$ count its queries
until delivery. It satisfies $Q_{\rm calls}\ge2$ almost surely. The
completed two-call branches form the successful subinstrument above,
so the tail-sum bound gives

$$
\mathbb E Q_{\rm calls}
\ge2+\Pr(Q_{\rm calls}\ge3)
=3-\Pr(Q_{\rm calls}=2)
\ge\frac{47}{20}.
\tag{AP27}
$$

An infinite expectation already satisfies the bound. Almost-sure
delivery is a service premise, not a claim that a controller looping
classically must physically execute infinitely many queries.
Comparison with the physical terminal-repair gate (AP7) at
$\alpha=\pi/4$ gives $47/20-7/3=1/60$. Neither value is asserted to be
the optimum ordinary or native expected cost.

The qubit theorem also yields a worst-case lower bound for a universal
algorithm in any even data dimension: restrict its promise to a known
embedding $A=(\boldsymbol a\cdot\boldsymbol\sigma)\otimes I_m$,
$B=(\boldsymbol b\cdot\boldsymbol\sigma)\otimes I_m$, initialize the
multiplicity and simulate it as allowed ancillary memory. This would
otherwise give a qubit algorithm violating (AP27). This is an
encoded-family worst-case reduction, not a claim about every
particular higher-dimensional encoding or known pair.
The certificate bounds neither optimal approximate channels nor
coherent angle/selector oracles, timing, noise or physical factory cost.

## Bounded NV physical screen and the next useful test

[Taminiau et al., Nature Nanotechnology **9**, 171–176 (2014),
arXiv:1309.5452v2](https://arxiv.org/html/1309.5452v2),
Methods and Supplement VII, IX and XIII, give
$H=P_0^e\otimes H_0+P_1^e\otimes H_1$, with
$H_0=\omega_L I_z$ and
$H_1=(\omega_L+A_\parallel)I_z+A_\perp I_x$.
Orthogonal normalized axes require $\omega_L+A_\parallel=0$;
equal angles in one common interval additionally require
$|\omega_L|=|A_\perp|$. Reported values
$\omega_L/(2\pi)=431$ kHz and
$(A_\parallel,A_\perp)/(2\pi)=(78.2,30)$ or $(32,44)$ kHz fail these tests.
The source uses 31.25 MHz electron control, $2\,\mu$s reinitialization,
and reports nuclear coherence under illumination of $51(7)\,\mu$s
and $0.35(9)$ ms. Its averaged fluorescence readout does not demonstrate
an individual ideal order flag. These couplings are continuously
present and electron pulses select their evolution; optical reset is
not required between every ordinary free-evolution window.
The inferred ideal electron $\pi$ duration is 16 ns, not a measured
all-in activation latency.

The same source already supplies
[conditional-dynamics context](architecture.md) for another
application; it is not a separate hardware realization of (AP5).
Its reported regime supplies neither the exact pair nor the large
nonamortizable setup assumed by (AP8)–(AP9). This does not exclude a
different engineered operating point. Such a point must first establish
its Hamiltonian Gram matrix and rates, then a full helper/data/bath
instrument, single-shot records, reset backaction and start/stop costs.
Equal-angle coherent selection, if engineered, must also be offered to
ordinary selector constructions such as (AP15).

## Quantized digital pulses: action and activation costs

<a id="nr-r21-sfq-activation"></a>

[Howe et al., PRX Quantum **3**, 010350 (2022)](https://arxiv.org/html/2111.12778v2),
Fig. 3, calibrate a Bloch-$\pi$ rotation with 352 Josephson pulse-generator
events at $2.685\,\mathrm{GHz}$. Their Eq. (7) estimates on-chip driver
dissipation per array event as $N_{JJ}I_c\Phi_0$, with $N_{JJ}=4650$ and
$I_c=3.05\,\mathrm{mA}$. Supplement XI uses two idle drive periods per
library waveform for phase changes. Its readout/reset context and
concatenated benchmarking support treating the $\ge15T_1$ reset as
between shots, rather than between coherent gates.
This is quantized voltage area, not quantized useful
qubit energy or a lower bound on total controller work.

The following is a derived ideal action diagnostic using that calibration,
not a fit to its noisy gates. Our $e^{-i\theta A}$ convention rotates the
Bloch vector by $2\theta$, so $n(\theta)=704|\theta|/\pi$ array events.
For $\alpha=\pi/4$, $h=\arctan(1/\sqrt2)$, $b=\pi/6$ and failure
probability $1/9$, the existing exact compiler formulas give:

| Policy | Named trains, or mean | Total action, or mean | Interpolated array events |
| --- | ---: | --- | ---: |
| Ordinary Euler | $3$ | $h+b$ | $255.256$ |
| Native first attempt only | $2$ | $2h$ | $275.846$ |
| Native with terminal repair | $7/3$ | $2h+(\pi-b)/9$ | $341.031$ |
| Native rollback/retry | $5/2$ | $(2h+\pi/9)/(8/9)$ | $398.327$ |

These rows grant ideal native flags, signed-axis control and a free helper.
The first attempt alone is not the completed exact service. Fractions of
an event are an interpolation: nearest integer words $[69,117,69]$ and
$[138,138]$ do not inherit the exact gate or failure probability.
At the representative clock, the interpolated Euler and terminal-repair
active times are $95.0675$ and $127.0134\,\mathrm{ns}$. A uniform
unavoidable setup $s$ per named train could reverse this comparison only if
$s>47.9189\,\mathrm{ns}+(3/2)H_C$, where $H_C$ is additional native-only
helper time per completed job. The reported two-period padding scale is
$0.7449\,\mathrm{ns}$ here, and is not an irreducibility theorem.
The source energy proxy is about $29.3271\,\mathrm{fJ}$ per whole array
event; do not multiply it by the junction count again. Driver/trigger,
attenuation, idle, helper, storage and actual recovery costs remain extra.

An $A/B/A$ word can also be scheduled as a single programmed waveform.
Legal removal or overlap of duplicated boundary padding strengthens the
ordinary comparison; it does not overlap active events when that changes
the word. Three named segments therefore do not establish three fresh
physical activations. At fixed event count, train starts/stops and idle
gaps must be measured separately from cached waveform preparation and
between-shot reset.

There is also an access test. If
$A_\phi=\cos\phi X+\sin\phi Y$ and
$B_\phi=-\sin\phi X+\cos\phi Y$, then
$(A_\phi+B_\phi)/\sqrt2=A_{\phi+\pi/4}$.
A supplied relative-phase setting addresses that bisector without
learning the common unknown $\phi$. The target still depends on $\phi$;
it has not become a known laboratory matrix.
[Liu et al., PRX Quantum **4**, 030310 (2023)](https://journals.aps.org/prxquantum/pdf/10.1103/PRXQuantum.4.030310),
Sec. II/Fig. 2, explicitly calibrate an equatorial phase family. This
supplies the access premise, not a measured midpoint-gate fidelity.
Howe's demonstrated integer grid has orthogonal delay three samples,
so the midpoint would require 1.5 samples and is not certified by that
grid. Combining the two experiments' access and count parameters is not
a same-device demonstration. If midpoint access is calibrated, the
ideal target needs one 176-event train and no uniform positive setup
penalty rescues the displayed native policies.

Liu's measured quasiparticle removal time $2.8(4)\,\mu\mathrm{s}$ also
precludes inferring a fresh independent activation-error model from its
aggregate benchmarks. That fit does not determine a coherent-order
cross-history instrument. Neither source demonstrates such an order
helper. A useful successor needs one device's target/reference and
leakage process at the actual phase grid, work and error versus starts at
fixed event count, and the same available phase, echo, selector and reuse
controls for ordinary operation. The
[standard-library ledger](checks/architecture/pulse_activation_ledger.py)
reproduces these scalar cost conversions; it certifies neither noisy
performance nor exact rounded gates or a native hardware advantage.

The useful device test is the native instrument plus terminal repair
against ordinary Euler, available selector/LCU controls and adaptive
ordinary processing on the same clock. Retain unknown data and
references, every failure, actual helper/readout errors, drift,
propagation, storage and deadline tails. Separate reusable job setup
from an unavoidable activation cost and amortize calibration over its
measured stability window. Interaction duration alone favors the
exhibited ordinary word; a hypothetical call-count difference is not a
physical timing, noise or fault-tolerant benefit.

## Exact replay scope

The standard-library [pulse checker](checks/architecture/anticommuting_pulse_gates.py)
replays full Euler/native/rollback matrix units at one
rational-trigonometric setting, including a dense complex frame change
and multiplicity. Its ordinary benchmark reconstructs finite CP and
Choi-plane identities, exact algebraic error enclosures and the
fractional mean-call ledger. General all-angle synthesis, the
dimension-independent diamond equality, time inequalities and physical
access qualifications are the analytic arguments above.

The same checked package replays the separate
[causal dual](checks/architecture/anticommuting_pulse_dual.py) and its
required [JSON](checks/architecture/anticommuting_pulse_dual.json) and
[support verifier](checks/architecture/anticommuting_pulse_support.py).
It checks 32, 16 and 4 positive causal LDL pivots, 12 positive Gram
pivots, 46 exact polynomial coefficients, the necessary-support rank
and 112 literal Pauli-link contractions, including the amplitude and
probability normalizations. The frame-support, common-adaptive-dual,
endpoint, stopping and encoded worst-case arguments are the proofs
above. No solver, floating tolerance, angle grid, physical NV fit,
coherent-router certificate or new Lean audit is involved. A certified
upper bound is not an assertion that the causal optimum equals it.
