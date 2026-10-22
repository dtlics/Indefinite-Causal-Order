# Purifying an unknown gate product under global replacement noise

<a id="nr-r02"></a>

**NR-R02.** A quantum switch improves a physical unknown gate product at fixed
noise and matched acceptance yield. The ordinary comparison includes every
adaptive protocol with at most **two total calls**, including repeated calls
to one device. A tighter exact certificate at dimension eight also gives
expected-query-cost and state-recovery corollaries without a hard query cap.
This result concerns full-register replacement noise; the local-noise model
of NR-R01 has different assumptions.

## Model and performance convention

Let $D=2m$ and draw a hidden frame $U$ from Haar measure on $U(D)$. Define

$$
A=U(X\otimes I_m)U^\dagger,\qquad
B=U(Y\otimes I_m)U^\dagger,\qquad W=BA.
$$

The balanced Hermitian involutions satisfy $AB=-BA$. The requested output is
the physical channel $\operatorname{Ad}_W$ on the supplied $D$-dimensional
input, including its entanglement with an inaccessible reference. The devices
are memoryless channels

$$
\mathcal E_g=(1-g)\operatorname{Ad}_A+g\Omega_D,
\qquad
\mathcal F_g=(1-g)\operatorname{Ad}_B+g\Omega_D,
\qquad
\Omega_D(\rho)=\operatorname{Tr}(\rho)I_D/D.
$$

Replacement affects the **entire physical register**. It is not independent
per-qubit noise or noise confined to a known logical factor. The same hidden
$A,B$ are used throughout one task, with independent replacement events.
Environments, Kraus labels, calibration data and prior unknown resource
states are unavailable.

An ordinary strategy may use arbitrary noiseless quantum memory, entangled
probes, data bypass, known gates, coherent routing in a fixed causal order,
instruments, heralding, and classical adaptive choice of the next device.
Its first choice may depend on an input measurement. The two-call theorem
allows either device twice, either ordering of distinct devices, and early
stopping. Individually callable boxes are supplied; a coherently indexed
combined oracle is an additional resource. The switch receives one use of
each device and coherent control of their order. All known processing is
ideal in the stated comparison.

Write $\Phi_D$ for a normalized maximally entangled state, and
$|w_U\rangle=(I\otimes W)|\Phi_D\rangle$. For a successful subchannel
$\mathcal S_U$, set

$$
\sigma_U=(\operatorname{id}\otimes\mathcal S_U)(\Phi_D),\quad
p_U=\operatorname{Tr}\sigma_U,\quad
q_U=\langle w_U|\sigma_U|w_U\rangle,
\qquad p=\mathbb E_U p_U,\quad q=\mathbb E_U q_U.
$$

For $p>0$, $F=q/p$ is the success-weighted mean conditional Bell fidelity.
Acceptance may depend on the input and frame. It need not define a
normalized conditional channel. If it is input independent, $F$ is the usual
conditional channel entanglement fidelity. A uniform-in-frame fidelity and
yield guarantee is covered by the averaged inequalities below.

## Switch map and exact error

Prepare the switch control in $|+\rangle$, use each device once, measure the
control in the $X$ basis, and accept its minus outcome. The payload is the
physical target output; its herald does not measure that payload. If $e_i,f_j$
are Kraus operators, the successful Kraus operators are
$(f_je_i-e_if_j)/2$.

For one ideal involution $H$ and one replacement, matrix-unit Kraus operators
$|a\rangle\langle b|/\sqrt D$ give

$$
\mathcal M_H(\rho)
=\frac{\Omega_D(\rho)}2-\frac{\operatorname{Tr}(H\rho)H}{2D}.
$$

For two replacements the successful map is
$(\Omega_D-\operatorname{id}/D^2)/2$. Bilinearity therefore gives

$$
\mathcal M_-
=(1-g)^2\operatorname{Ad}_W
+g(1-g)(\mathcal M_A+\mathcal M_B)
+\frac{g^2}{2}(\Omega_D-\operatorname{id}/D^2).
$$

The success probability is input independent. The frame-independent
Bell/Choi quantities are

$$
\begin{aligned}
p_S(D,g)&=1-g+\frac{1-D^{-2}}2g^2,\\
q_S(D,g)&=(1-g)^2+\frac{2g-3g^2/2}{D^2},\\
e_S(D,g)&=p_S-q_S=(1-2D^{-2})(g-g^2/2),\\
F_S(D,g)&=q_S/p_S.
\end{aligned}
\tag{1}
$$

The success formula allows arbitrary input-reference entanglement. The normalized
target Choi vector is an eigenvector of each positive Choi summand. Thus the
successful Choi state is $q_S|w_U\rangle\langle w_U|$ plus an orthogonally
supported positive remainder. Both successful maps have scalar input
marginals, so that remainder is $e_S$ times a channel. The triangle upper
bound and the Bell-input lower bound coincide:

$$
\frac12\|\mathcal M_-/p_S-\operatorname{Ad}_W\|_\diamond
=1-F_S=\frac{e_S}{p_S}.
\tag{2}
$$

No physical implementation of $W^\dagger$ is needed for this error statement.

## Exact dimension-eight frontier

**Theorem 1.** Let $D=8$ and $g=1/10$. Every ordinary strategy with at most
two total calls satisfies the affine inequality

$$
q-\lambda p\le a,
\qquad
\lambda=\frac{158531}{200000},\qquad
a=\frac{54081027}{2560000000}.
\tag{3}
$$

At success at least $p_S=11583/12800$, this gives

$$
F_{\rm ord}\le\lambda+\frac a{p_S}=\frac{102}{125}=0.816,
\qquad
F_S=\frac{10405}{11583}\approx0.89829923.
\tag{4}
$$

The switch's conditional half-diamond error is exactly $1178/11583$. Every
ordinary strategy at the required averaged yield has some frame whose
conditional Bell error is at least $23/125$. When ordinary success is input
independent, this also lower-bounds its worst-frame conditional channel
half-diamond error. The inequality is not a claim that every hard-coded
ordinary processor performs poorly on every individual frame.

### Certificate-to-comb proof

Use Choi wire order $(P,A_I,A_O,B_I,B_O,F)$ and unnormalized channel Choi
matrices $J$. The performance operators for an $\mathcal E$-then-$\mathcal F$
comb are

$$
\Omega_q=\mathbb E_U[J_W\otimes J_{\mathcal E}^T
\otimes J_{\mathcal F}^T]/D^2,
\qquad
\Omega_p=\mathbb E_U[I_{P,F}\otimes J_{\mathcal E}^T
\otimes J_{\mathcal F}^T]/D,
\tag{5}
$$

with factors placed on their named wires. A successful comb $C_s$ is bounded
by a deterministic comb $C\succeq C_s\succeq0$ whose causal normalization is

$$
\operatorname{Tr}_F C=R_2\otimes I_{B_O},\qquad
\operatorname{Tr}_{B_I}R_2=R_1\otimes I_{A_O},\qquad
\operatorname{Tr}_{A_I}R_1=I_P.
$$

The rational witness consists of Hermitian $Y$ on the first five wires,
$Z$ on the first three, and the scalar terminal operator $T=tI_P$, where
$Dt=a$. Its physical operator inequalities are

$$
\begin{aligned}
Y\otimes I_F&\succeq0,\\
Y\otimes I_F+\lambda\Omega_p-\Omega_q&\succeq0,\\
Z\otimes I_{B_I}-\operatorname{Tr}_{B_O}Y&\succeq0,\\
tI_{P,A_I}-\operatorname{Tr}_{A_O}Z&\succeq0.
\end{aligned}
\tag{6}
$$

Positivity gives

$$
\begin{aligned}
q-\lambda p
&\le\operatorname{Tr}[C_s(Y\otimes I_F)]
\le\operatorname{Tr}[C(Y\otimes I_F)]\\
&\le\operatorname{Tr}[R_2(Z\otimes I_{B_I})]
\le\operatorname{Tr}[R_1(tI_{P,A_I})]=Dt.
\end{aligned}
$$

This bounds all complex combs and arbitrary memory; no covariance or real
coordinate restriction is imposed on the strategy. Covariance only reduces
the search for the witness.

The [exact algebra checks](checks/algebra/) reconstruct (5) and all four
slacks from the rational witness in
`brauer_exact_certificate_D8_g1_10_heralded.json`. The mixed-tensor signature
is $(-,+,-,+,-,+)$. A basis consists of the $720$ permutation operators
partially transposed on the negative wires. Its Gram entries are
$D^{\#\mathrm{cycles}(\pi^{-1}\sigma)}$. Invariance lets each objective trace
be evaluated at the canonical $X,Y,Z$ frame; replay checks all $720$ Gram
equations for each objective, including adjoint indices.

Each slack is proved positive as an actual physical operator by rational
diagram algebra:

$$
S=X^\dagger X+R,\qquad
R=r_0I+\sum_{i\ne0}r_iB_i,\qquad
r_0>\sum_{i\ne0}|r_i|D^{c_i}.
\tag{7}
$$

A diagram with $c_i$ top cups has operator norm $D^{c_i}$. Exact pairing
composition reconstructs multiplication and closed-loop factors, so (7)
proves the PSD statements without a numerical representation, stored
multiplication cache, SDP solver, or eigensolver. The full replay also
rebuilds the causal slacks; checking unrelated PSD matrices would not prove
the comb bound. This is an exact arithmetic certificate, not a Lean
formalization.

### Initial instruments, repetitions and stopping

If an initial known instrument chooses first $\mathcal E$ or first
$\mathcal F$ with input effects $M_E,M_F$, then $M_E+M_F\preceq I$. Replacing
the final normalization by $M_r$ changes the telescope to $t\operatorname{Tr}M_r$.
The scalar terminal dual is essential here. Haar invariance under exchanging
$A,B$, and the phase equality $\operatorname{Ad}_{AB}=\operatorname{Ad}_{BA}$,
give the same witness for the opposite order. Summing the effects costs at
most $Dt$.

For histories with no access to one axis, condition mathematically on
$A=\operatorname{diag}(I_m,-I_m)$. The remaining axis is
$B=\left(\begin{smallmatrix}0&V\\V^\dagger&0\end{smallmatrix}\right)$ with
$V$ Haar in $U(m)$. Phase invariance removes the cross terms, giving

$$
\mathbb E_{B\mid A}|w_U\rangle\langle w_U|
=\frac2{D^2}\Pi_{\rm off}\preceq\frac2{D^2}I.
\tag{8}
$$

Every successful repeated-device or stopped output is independent of the
missing axis after this conditioning. It therefore obeys $q_{\rm rep}\le
\beta p_{\rm rep}$, where $\beta=2/D^2$. This includes arbitrary
postselection and memory. Global replacement noise contains no information
about the missing axis.

Keep the distinct-device success histories of any two-total-call strategy.
Whenever it would repeat or stop, **skip** that continuation, call the other
device on a dummy, and flag failure. The resulting one-use-each instrument
has exactly the original distinct-device success state. It never executes
a third call. Apply (6) to it. At $D=8$, $\lambda>\beta=1/32$, so adding back
the missing-axis branches cannot increase $q-\lambda p$. This proves (3)
for the full stated adaptive class.

### Deterministic corollary

On plus outcomes apply the known covariant CPTP map

$$
\mathcal N_D(\rho)=\frac{D\operatorname{Tr}(\rho)I-\rho}{D^2-1},
$$

the uniform mixture of nonidentity laboratory Weyl conjugations. Keep minus
outcomes unchanged. The resulting trace-preserving switch has

$$
F_{S,\mathrm{TP}}=q_S+\frac{g-g^2/2}{D^2-1}.
\tag{9}
$$

At $D=8,g=1/10$, a **separate** rational tree certificate gives

$$
F_{\rm ord,TP}\le\frac{813}{1000},\qquad
F_{S,\mathrm{TP}}=\frac{656731}{806400},\qquad
F_{S,\mathrm{TP}}-F_{\rm ord,TP}
\ge\frac{5639}{4032000}>0.
$$

The tree has branches $EE,EF$ after the first $E$, branch combs $C_h$, and
shared-prefix normalization

$$
\operatorname{Tr}_F C_h=R_{2,h}\otimes I_{B_O},\quad
\sum_h\operatorname{Tr}_{B_I}R_{2,h}=R_1\otimes I_{A_O},\quad
\operatorname{Tr}_{A_I}R_1=I_P.
$$

Its witness has $Y_{EE},Y_{EF}$ with common $Z,T$ and inequalities
$Y_h\otimes I\succeq\Omega_{q,h}$,
$Z\otimes I\succeq\operatorname{Tr}_{B_O}Y_h$, and the last inequality in
(6). The shared $Z$ enforces the shared first-query budget. The repeated-call
objective uses the same hidden $A$ in both slots. The separate
`brauer_exact_certificate_D8_g1_10_deterministic_tree.json` is a required
dependency of this corollary. Its five slacks pass the same exact replay.
The scalar terminal dual again covers input-dependent initial order choice.
The completed switch's half-diamond error is exactly $1-F_{S,\mathrm{TP}}$
by the same target/error Choi decomposition. The deterministic gain is small
and shrinks with dimension; it is distinct from the larger heralded gain.

## A uniform finite-noise theorem in every even dimension at least eight

**Theorem 2.** Let $g=1/10$, $D\ge8$ be even, $t=1-g$, $r=1-t^2$,
$\beta=2/D^2$, and $\kappa_D=3/(2D)$. Every ordinary two-total-call strategy
obeys

$$
q\le[\beta+(1-\beta)t^2]p+(1-\beta)t^2r\kappa_D.
\tag{10}
$$

Consequently, at $p\ge p_S(D,1/10)$,

$$
\begin{aligned}
F_{\rm ord}
&\le\beta+(1-\beta)t^2
\left(1+\frac{r\kappa_D}{p_S(D,1/10)}\right)
\le\frac{387509}{457600},\\
F_S&\ge\frac{162}{181},\\
F_S-F_{\rm ord}&\ge\frac{3992071}{82825600}>0.04819.
\end{aligned}
\tag{11}
$$

The switch yield is at least $11583/12800$ for every input and frame. This
fixed-ten-percent-noise statement does not use an ideal-preservation or
small-noise assumption. The sharper dimension-eight frontier (3) remains
available at $D=8$.

**Proof.** The [adaptive acceptance method](methods/acceptance.md) proves
that, for any one-use-each acceptance tester with arbitrary memory, its
Haar-average acceptance changes by at most $\kappa_D$ when the first, second,
or both ideal devices are replaced by $\Omega_D$. This is a tester statement
with the correct causal prefixes, not a parallel-probe bound. It scales by
the trace of a subnormalized initial branch. The proof uses explicit
four-port duals, a complete singlet/adjoint/bulk sector decomposition, and
exact polynomial positivity for every $D\ge8$. The
[acceptance checks](checks/acceptance/) verify the objective identities,
causal prefix identities and all sector positivity polynomials.

Prune repeated/stopped continuations as above and let $x$ be the retained
ideal-pair acceptance. If $p_z$ denotes retained acceptance in any of the
three replacement patterns, then $|x-p_z|\le\kappa_D$. Initial first-device
branch weights sum to at most one, so summing these tester bounds does not
multiply their cost. The retained noisy acceptance is at least
$t^2x+r(x-\kappa_D)=x-r\kappa_D$ and is no larger than the original $p$.
Thus $x\le p+r\kappa_D$.

Every erased-pattern output and every missing-axis history obeys (8).
The ideal retained good weight is at most $x$. Hence

$$
q\le\beta p+(1-\beta)t^2x
\le[\beta+(1-\beta)t^2]p+(1-\beta)t^2r\kappa_D,
$$

proving (10). For the uniform constants put $z=1/D\in[0,1/8]$. The ordinary
bound at switch yield is

$$
\frac{81}{100}+\frac{19}{50}z^2+
\frac{4617}{100}\frac{z(1-2z^2)}{181-z^2}.
$$

It increases with $z$: the derivative of the last rational factor has
positive numerator $181-1085z^2+2z^4$. Its maximum is the $D=8$ value in
(11). Meanwhile $F_S=(162+37z^2)/(181-z^2)$ has minimum $162/181$. This
proves all dimension-uniform constants.

### Eighty-percent order-control visibility

Let visibility $\nu$ multiply the order control's off-diagonal entries, with
all other operations unchanged. Then

$$
\mathcal M_-(\nu)=\nu\mathcal M_-+(1-\nu)\mathcal C_{\rm bare}/2,
\quad
p_\nu=\nu p_S+(1-\nu)/2,
\quad
q_\nu=\nu q_S+(1-\nu)F_{\rm bare}/2,
$$

where $F_{\rm bare}=(1-g)^2+(2g-g^2)/D^2$. Success remains input independent
and the accepted half-diamond error remains $1-q_\nu/p_\nu$. At $\nu=4/5$,
for every even $D\ge8$,

$$
p_\nu\ge\frac{13183}{16000},\qquad
F_S(\nu)\ge\frac{729}{824},\qquad
F_{\rm ord}(p\ge p_\nu)
\le\frac{35852083}{42185600}.
\tag{12}
$$

The accepted-fidelity gap exceeds $0.0348$. Equation (10) is evaluated at
the **new actual yield** $p_\nu$, so reduced acceptance is not ignored. At
$D=8$, (3) gives the stronger bound $8630061827/10546400000$ against switch
fidelity $46823/52732$. These numbers concern this visibility model; they
are not specifications for arbitrary faulty routing or local noise.

## Dimension-eight expected-query-cost corollary

**Corollary 3.** Retain $D=8,g=1/10$ and a single initially supplied unknown
input. Allow an arbitrary ordinary stopping protocol with finite expected
query count $c=\mathbb E N$, with no maximum-call cap. Every training and
failed-history call is charged. With $p,q$ averaged on the same Haar prior
and Bell input, define $C=c/p$ for $p>0$. Then

$$
q\le bp+kc,\qquad
b=a+3\lambda-2=\frac{1021671427}{2560000000},\qquad
k=1-\lambda=\frac{41469}{200000}.
\tag{13}
$$

Thus $F\le\min\{1,b+kC\}$. At the switch's yield-normalized cost,

$$
C_S=\frac2{p_S}=\frac{25600}{11583},\qquad
F_{\rm ord}\le\frac{8474194019647}{9884160000000}
\approx0.85735096<F_S.
\tag{14}
$$

Matching $F_S$ requires ordinary cost at least
$14802779861059/6148293465600\approx2.40762416$, over $1.08935C_S$.
This is a lower bound, not an achievable optimum.

**Proof.** Group accepted histories by $N=0,1,2,\ge3$, with probabilities
$p_0,p_1,p_2,p_T$ and good weights $q_0,q_1,q_2,q_T$. Put
$r_j=\Pr(N\ge j)$, averaged on the same test. Zero-call target averaging
gives $q_0\le\kappa_0p_0$, where $\kappa_0=1/63$; (8) gives
$q_1\le\beta p_1$ with $\beta=1/32$. Retain only successes that stop after
exactly two calls, flagging any request for a third call as failure. The
scalar terminal dual applies to the original initial querying effects,
whose total probability is $r_1$, so

$$
q_2-\lambda p_2\le ar_1.
$$

Repeated-axis two-call branches have nonpositive affine score and can be
added back. This truncation does not condition the Haar prior on reaching
two calls. Give the entire longer tail perfect fidelity, $q_T\le p_T$.
Counting all histories gives

$$
r_1\ge p_1+p_2+p_T,\qquad
c=\sum_{j\ge1}r_j\ge r_1+p_2+2p_T.
$$

The tail-sum identity is valid for unbounded integer stopping times with
finite expectation. Positivity and the preceding bounds yield

$$
q\le\kappa_0p_0+\beta p_1+\lambda p_2+p_T+ar_1.
$$

The exact constants obey $a\le k$, $2\lambda\ge1+\beta$, and $b\ge\kappa_0$.
Subtracting $kc$ and using $a-k\le0$ gives

$$
\begin{aligned}
q-kc
&\le\kappa_0p_0+\beta p_1+(2\lambda-1)(p_2+p_T)+(a-k)r_1\\
&\le\kappa_0p_0+(\beta+a-k)p_1+b(p_2+p_T)\le bp.
\end{aligned}
$$

This proves (13), including arbitrary nonuniform-budget mixtures and longer
ordinary filtration architectures. Their tails were already granted perfect
quality at the minimum possible three calls.

### Bell and finite pure-state recovery utilities

An accepted output earns $+1$ if a referee's target test passes and $-1$ if
it fails; erasure earns zero. All queries are charged. In the Bell test the
reference remains inaccessible to the worker and the reward is
$R_B=2q-p$.

For a test without an entangled input reference, the referee instead draws
one of the $72$ states in a complete set of nine three-qubit mutually
unbiased bases. It supplies the state without its classical label. On the
returned live payload it tests the projector onto $W|\psi\rangle$. The
ensemble is an exact complex projective two-design, so accepted pass mass
is $(8q+p)/9$ and reward is

$$
R_P=\frac{16q-7p}{9}.
$$

Its first moment is $I/8$, so the same expected query cost is used. The
referee knows the labels needed for its downstream test; that test is not
an operation available to the worker for heralding. The finite-ensemble
check constructs all $72$ projectors and verifies their first and second
moments exactly.

Since $q\le p$ and $b<7/16<1/2$, both rewards obey

$$
R_B,R_P\le\frac{q-bp}{1-b}
\le\frac{k}{1-b}c
=\frac{7692800}{22294617}c.
\tag{15}
$$

For $R_P$, the first inequality is equivalent to
$(7-16b)(q-p)\le0$; the Bell case uses $(1-2b)(q-p)\le0$. At expected budget
$c\le2$, every ordinary protocol therefore has reward at most
$15385600/22294617\approx0.69010380$. The two-call switch achieves

| Test | Switch reward, including erasures | Ordinary upper at $\mathbb E N\le2$ |
| --- | --- | --- |
| Bell target projector | $9227/12800=0.720859375$ | $15385600/22294617$ |
| Finite pure-state ensemble | $85399/115200\approx0.74131076$ | $15385600/22294617$ |

There is no yield floor or discarded failure cost in (15). The pure-state
reward gap is at least $43838959061/856113292800>0.05120$. The expected-cost
replay checks the source certificate and these exact arithmetic corollaries;
the finite-ensemble replay checks the separate two-design identity.

## Scope, baselines and verification dependencies

The large heralded gain is in accepted quality. At $D=8,g=1/10$ its correct
Bell mass is $q_S=10405/12800$, while bare composition has $10406/12800$.
Counting every erased output as an error does not give the large conditional
advantage. Equations (13) and (15) state the particular cost and utility
criteria under which all discarded attempts are nevertheless charged.

The number $c/p$ is yield-normalized query cost for a one-output heralded
transformation, not permission to retry on the same irreplaceable quantum
input. Refreshed-input selection and accessible-reference state preparation
are different models. There is no persistent many-output advantage claimed
after calibration of one fixed device pair: a learner may eventually
estimate its finite-dimensional gates and amortize synthesis across jobs.
The service/game interpretation uses a fresh hidden frame per one-shot task,
or charges all prior learning to the output being evaluated.

Explicit ordinary filters remain useful baselines. A two-rail filter on one
device followed by the other has success $11603/12800$ and fidelity
$1582871/1856480$. With early abort its expected cost per success is
$37203/11603\approx3.20633$. Filtering both devices has success
$134629609/163840000$, fidelity $7705052581/8616294976$, and early-abort
cost per success $624716800/134629609\approx4.64026$. These are feasible
protocols, not three/four-query optima. Corollary 3 already permits stronger
long-query competitors at the stated expected cost.

The theorem supplies a physical unknown-gate primitive. It does not establish
a fault-tolerance threshold, improved computation throughput, an advantage
under arbitrary local noise, a capacity theorem, or negligible routing and
control overhead. Coherent order access and a live nondestructive herald are
physical implementation requirements. Commutation-parity filtering and
superposed error mitigation are established mechanisms; the contribution
here is the scoped unknown-product transformation and its ordinary-strategy
converse, not priority for the filtering idea.

The required executable evidence is kept with the
[algebra checks](checks/algebra/) and [acceptance checks](checks/acceptance/):

- The dimension-eight heralded and deterministic rational JSON witnesses,
  their complete certificate-to-comb replay, exact diagram composition,
  objective contractions, Gram inversion and SOS checker support Theorem 1
  and the deterministic corollary. The deterministic tree JSON is required
  separately; the heralded certificate alone does not prove its tighter bound.
- The exact acceptance-objective, causal-prefix and sector-polynomial replay,
  together with [the physical acceptance proof](methods/acceptance.md),
  supports Theorem 2 and its visibility corollary in every even $D\ge8$.
- The expected-cost arithmetic replay depends on the heralded affine witness;
  the finite recovery-ensemble check supplies the two-design identity for
  (15). None of these corollaries depends on an exploratory optimizer run.

Numerical searches discover witnesses but do not replace these checks.
Repository validation checks structure and dependency consistency; it is not
a new Lean kernel audit or a proof of an unrecorded physical noise model.
