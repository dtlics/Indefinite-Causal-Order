# Entropy and capacity certificates for orthogonal random-unitary channels

This is the entropy proof component of
[NR-R20](../memory-qualification.md#nr-r20). The
[Pauli finite checker](../checks/architecture/verify_entropy_capacity.py)
guards the character identities, threshold inequalities, conditional
identity formula and a positive confidence example. The
[orthogonal-unitary checker](../checks/architecture/verify_orthogonal_entropy.py)
also checks the general Choi index identity on a non-Pauli unitary
basis, a dense change of frame, and target-state dependence.
Finite cases do not prove the all-dimension entropy or coding theorems.

Consider one fixed memoryless random-unitary channel in dimension
$D\geq2$, with $n=\log_2D$:
$$
\mathcal E_p(X)=\sum_{i=0}^{M-1}p_iU_iXU_i^\dagger,\qquad
U_0=I,\qquad
\operatorname{Tr}(U_i^\dagger U_j)=D\delta_{ij}.
$$
Orthogonality implies $M\leq D^2$; the probabilities may vanish.
Define the real commutator matrix and its independently sampled mean by
$$
C_{ij}=\frac1D\operatorname{Re}
\operatorname{Tr}(U_j^\dagger U_i^\dagger U_jU_i),\qquad
\eta=\sum_{i,j}p_ip_jC_{ij}.
\tag{EW1}
$$
The two quantities used below are $\eta$ and the identity-error
probability $p_0$. No uniform-support, low-rank, hidden-subgroup or
learning-complexity promise is imposed. In the $n$-qubit Pauli
specialization, $G=\mathbb F_2^{2n}$ and
$C_{ab}=(-1)^{[a,b]}$. The general statistic is the self-switch
helper mean when its target marginal is $I/D$; the input-independent
Pauli readout is a special case, as detailed below.

All capacities are unassisted asymptotic entanglement-transmission rates
in qubits per $D$-dimensional use, with the same fixed channel used
independently, arbitrary encoding/decoding and no clean input-bearing
bypass. The result is a sufficient capability certificate. It does not
construct the encoder, give a finite-block guarantee, or establish a
query advantage for the quantum switch.

## The universal entropy estimate

Let $q$ be any probability law on the orthogonal unitary family,
including a law with zeros.
Write
$$
c=q^{\mathsf T}Cq,\qquad e=1-c,\qquad
C_D=\frac{2-D^{-1}}{\ln2}.
$$
Here $-1\leq c\leq1$, and entropy is in bits. Then
$$
H(q)\leq
\min\left\{2n,\ (1+\sqrt{1-c})\,n+C_D\right\}.
\tag{EW2}
$$
If $q_0=0$, the first bound improves to $\log_2(D^2-1)$.

**The general spectral bound.** For nonnegative subweights $v_i$,
let $J_v$ be their unnormalized Choi mixture. In matrix-entry
coordinates,
$$
(J_v)_{ab,cd}
=\frac1D\sum_i v_i(U_i)_{ab}\overline{(U_i)_{cd}}.
$$
The normalized vectors $|U_i\rangle\!\rangle/\sqrt D$ are orthonormal,
so $\operatorname{Tr}(J_v^2)=\sum_i v_i^2$. Direct expansion of
the four indices gives
$$
v^{\mathsf T}Cv
=D\,\operatorname{Re}
\sum_{a,b,c,d}(J_v)_{ab,cd}(J_v)_{ca,db}.
$$
Indeed the inner matrix-entry product is
$(U_i)_{ab}\overline{(U_i)_{cd}}(U_j)_{ca}
\overline{(U_j)_{db}}$, whose sum is
$\operatorname{Tr}(U_j^\dagger U_i^\dagger U_jU_i)$.
The index map $(a,b,c,d)\mapsto(c,a,d,b)$ is a permutation.
Applying complex Cauchy–Schwarz to this **bilinear** sum yields
$$
|v^{\mathsf T}Cv|
\leq D\|J_v\|_F^2
=D\sum_i v_i^2.
$$
No identification with a sesquilinear inner product without its
required conjugation is used.

For Pauli operators there is the independent shorter proof:
their character matrix $H_{ab}=(-1)^{[a,b]}$ obeys
$H^2=D^2I$, hence $\|H\|_{\mathrm{op}}=D$, giving the same bound.

**Spectral tail bound.** For any threshold $\beta>0$, let
$$
T=\{i:q_i\leq\beta/D\},\qquad
v_i=q_i1_{\{i\in T\}},\qquad w=\sum_iv_i.
$$
The restricted self-bias satisfies
$$
v^{\mathsf T}Cv\leq D\|v\|_2^2\leq\beta w.
$$
Unitarity gives the nonnegative pair defect
$$
1-C_{ij}
=\frac{\|U_iU_j-U_jU_i\|_F^2}{2D}\geq0.
$$
Consequently $w^2-v^{\mathsf T}Cv$ sums a subset of the
nonnegative terms making up $1-c$, and is at most $1-c$.
For Paulis, one half of this defect is exactly the probability of
an anticommuting pair. No such binary-event interpretation is needed
for general unitary families.
Thus
$$
w^2-\beta w\leq1-c,\qquad
w\leq\frac{\beta+\sqrt{\beta^2+4(1-c)}}2
\leq\beta+\sqrt{1-c}.
\tag{EW3}
$$
For the Pauli specialization, no nonnegativity of the Fourier
transform of $q$, or realization as the Pauli characteristic function
of a quantum state, is assumed.

**Integrating the tails.** Draw $A\sim q$ and put
$X=-\log_2q_A$. Labels of zero probability never occur. For
$w(s)=\Pr[X>s]$, (EW3) with $\beta=D2^{-s}$ implies
$$
w(s)\leq\sqrt{1-c}+D2^{-s}.
\tag{EW4}
$$
Counting the at most $D^2$ possible labels also gives
$w(s)\leq D^22^{-s}$. The layer-cake identity
$H(q)=\mathbb EX=\int_0^\infty w(s)\,ds$ now yields
$$
\begin{aligned}
\int_0^n w(s)\,ds&\leq n,\\
\int_n^{2n} w(s)\,ds
 &\leq n\sqrt{1-c}+\frac{1-D^{-1}}{\ln2},\\
\int_{2n}^\infty w(s)\,ds&\leq\frac1{\ln2}.
\end{aligned}
$$
Adding these proves (EW2). This gives $H(q)\leq n+o(n)$ for every
sequence $c_n\to1$, with a dimension-independent finite-size offset.
It does not assert closeness to a commuting error algebra.

**The exact endpoint.** If $c=1$, every positive-weight commutator
norm in the pair defect vanishes. The support unitaries commute and
are normal, so they are simultaneously diagonalizable. Their
orthogonal linear span is contained in a $D$-dimensional diagonal
operator algebra. Hence there are at most $D$ support elements and
$H(q)\leq n$ exactly. If $q_0=0$, adding the identity preserves
commutation and orthogonality, so at most $D-1$ support elements remain:
$$
H(q)\leq\log_2(D-1).
\tag{EW5}
$$
The constant-offset bound (EW2) is deliberately not used in place of
this exact endpoint.

The simple strict constant
$$
C_D<3
\tag{EW6}
$$
will suffice for a rational numerical certificate. Indeed strict
convexity of $1/x$ on $[1,2]$ gives
$\ln2=\int_1^2x^{-1}\,dx>2/3$, while $2-D^{-1}<2$.

## The capacity certificate

Set $r=1-p_0$. If $r=0$, the channel is identity and $Q=n$.
Otherwise let $q_a=p_a/r$ for $a\neq0$, $q_0=0$. Since identity
commutes with every label,
$$
\eta=p_0^2+2p_0r+r^2c
     =1-r^2(1-c),\qquad
H(p)=h_2(r)+rH(q).
\tag{EW7}
$$
For this orthogonal random-unitary channel, the output of $I/D$ is
$I/D$, while its normalized Choi eigenvectors are the orthonormal
$|U_i\rangle\!\rangle/\sqrt D$, with eigenvalues $p_i$.
Consequently
$$
I_c(I/D,\mathcal E_p)=n-H(p).
$$
The direct quantum coding theorem gives
$$
Q(\mathcal E_p)\geq
\max\{0,\ n-h_2(r)-rB_n(c)\},
\tag{EW8}
$$
for either proved entropy upper bound $B_n(c)$ above, capped by
$\log_2(D^2-1)$.

In particular, $r\sqrt{1-c}=\sqrt{1-\eta}$ converts (EW2) into
the transparent universal certificate
$$
\boxed{
Q(\mathcal E_p)\geq
\max\left\{0,\ [p_0-\sqrt{1-\eta}]n
-h_2(p_0)-(1-p_0)C_D\right\}.}
\tag{EW9}
$$
No conditional division by $r^2$ is needed to evaluate (EW9).
The identity-mass-only bound
$$
Q(\mathcal E_p)\geq
\max\{0,n-h_2(r)-r\log_2(D^2-1)\}
\tag{EW10}
$$
is also valid and may be stronger in some parameter regimes. Take
the larger lower certificate. A positive result is sufficient,
not necessary, for positive capacity.

The only external coding dependency here is
[Devetak, IEEE Transactions on Information Theory 51, 44–55 (2005),
Theorem 5 and its direct coding proof](https://arxiv.org/pdf/quant-ph/0304127).
The entropy bounds above have complete Choi-index, spectral and
tail-integration proofs; they do not invoke an approximate-duality
conjecture.

## Finite confidence and physical measurement scope

Suppose a simultaneous confidence region has
$$
p_0\in[\ell,u]\subseteq[0,1],\qquad \eta\geq v,\qquad -1\leq v\leq1.
$$
Let $h_{\max}$ be the maximum of $h_2(x)$ on
$[1-u,1-\ell]$: it is 1 if that interval contains $1/2$, and
otherwise the larger endpoint value. Then the immediately valid
conservative certificate is
$$
Q\geq
\max\{0,\ [\ell-\sqrt{1-v}]n
-h_{\max}-(1-\ell)C_D\}.
\tag{EW11}
$$
It follows from (EW9) by separately worsening each term. A tighter
certificate minimizes the actual proved bound over the feasible
joint region. Point estimates near $r=0$, or an unbounded division
by a fitted visibility, are not confidence guarantees.

For the general random-unitary family, initialize a separately
prepared $|+\rangle$ control and target marginal $I/D$. The standard
self-switch of two independent calls then gives a $\pm1$ helper
outcome with mean (EW1). At another target state $\rho$ the mean is
instead
$$
\operatorname{Re}\sum_{i,j}p_ip_j
\operatorname{Tr}[\rho\,U_j^\dagger U_i^\dagger U_jU_i],
$$
which can depend on $\rho$. For example, in dimension 4 let
$X_4|k\rangle=|k+1\bmod4\rangle$ and
$Z'=\operatorname{diag}(1,1,-1,-1)$. The equal iid mixture of
$X_4,Z'$ has self-switch helper means 1 on $|0\rangle$, 0 on
$|1\rangle$, and $1/2$ on $I/4$. Thus a general experiment must
prepare or average to the declared maximally mixed target, rather
than import Pauli input-independence. The exact checker verifies
these full flagged probabilities within a 16-element non-Pauli
orthogonal unitary basis.

For Pauli errors, the unitary commutator is the scalar
$(-1)^{[a,b]}I$, so the helper mean is independent of the target.
In this specialization $p_0$ also has the established
reference-free product-probe estimator
$Z=(-1/2)^{\#\text{minus outcomes}}$ of
[Flammia and O'Donnell, Theorem 22](https://arxiv.org/html/2105.02885).
Its full proof, simultaneous confidence with an ordinary overlap
certificate and calibrated readout limits are in
[the local-certification method](pauli-local-certification.md).
No quantum helper is needed for that identity estimator; trusted
fresh product preparation and terminal local readout are needed.

For an arbitrary orthogonal unitary family containing identity,
$\operatorname{Tr}U_i=0$ for $i\neq0$, so
$p_0=F_e(I/D,\mathcal E_p)$. In qubit dimensions $D=2^n$,
randomizing the signs of the prepared
product eigenstates and relabeling the outputs makes the same
bounded product statistic an entanglement-fidelity estimator for
any CPTP map. The Pauli-transfer expansion proving this fact is
also given in the local-certification method. It supplies the
general family's $p_0$ measurement without assuming that its
unitaries are public Pauli operators. For other dimensions the
entropy theorem still holds, but this qubit product-probe protocol
is not being asserted: a conventional maximally entangled probe
and Bell-fidelity measurement can estimate $p_0$, with its
$D$-dimensional reference counted.

Separate independent batches of sizes
$2\varepsilon_\eta^{-2}\ln(4/\delta)$ and
$2\varepsilon_0^{-2}\ln(4/\delta)$, respectively, suffice by Hoeffding
for simultaneous additive confidence widths
$\varepsilon_\eta,\varepsilon_0$ with total failure at most
$\delta$. The first batch uses two primitive slots per trial.
In the qubit implementation, the product-fidelity batch uses one
per trial and has range
$[-1/2,1]$, so this shared Hoeffding budget is conservative.
These are ideal sample upper bounds, not an optimal resource
comparison. Global routing, helper lifetime, calibrated gates and
readout, loss and all rejected launches remain charged.

For independently calibrated helper visibility $\nu>0$, its observed
mean is $\nu\eta$, rather than $\eta$. A known $\nu$ costs a
$\nu^{-2}$ concentration factor; an uncertain visibility requires
minimization over its confidence interval. Unknown systematic
backgrounds or slot errors need explicit nuisance bounds. A temporal
joint law with the same one-time channel can have a different
self-commutation experiment: drawing the same label twice always
has sign $+1$. The capacity theorem and witness concern the fixed
iid channel, not an arbitrary quantum bath process inferred from
its one-use marginal.

Neither $Q>0$ nor a large value of (EW9) supplies an efficient
code, a near-commuting decoder, a fixed existing code's logical
failure probability or a finite-time memory service. It is an
operational existence certificate. Proving a native useful
qualification advantage still requires a full ordinary estimator
comparison and a coherent-order interface justified by hardware.

The family orthogonality and random-unitary structure are model
assumptions. They cannot be certified from $p_0,\eta$ alone.
For nonorthogonal unitaries, the Choi purity is not
$\sum_i v_i^2$, and the number or entropy of representation labels
can be enlarged without changing the channel. Diagonalizing a
general CPTP Choi state instead supplies orthogonal Kraus
operators that need not be unitary; the baseline
$\sum_{i,j}v_iv_j=w^2$ and its unitary commutator defect then
do not follow. The claims here do not cover arbitrary nonorthogonal
random-unitary representations or arbitrary CPTP maps.
The [bounded-overlap extension](unitary-error-overlap.md) supplies a
corrected bound under additional cardinality and coherence promises;
it does not cover arbitrary representations.
The ordinary local OR commutation certificate is likewise a
Pauli specialization, not a general-unitary consequence.

## A positive finite-confidence example with full support

For $n=32$, suppose simultaneous lower confidence bounds are
$p_0\geq19/50$ and $\eta\geq24/25$. Use
$\sqrt{1-\eta}\leq1/5$, $h_2\leq1$ and $C_D<3$ in
(EW11). No fitted entropy or floating-point root is needed:
$$
Q\geq
\left(\frac{19}{50}-\frac15\right)32
-1-3\left(1-\frac{19}{50}\right)
=\frac{29}{10}.
\tag{EW12}
$$
This certifies at least $2.9$ qubits per $32$-qubit use under
the stated channel and confidence model.

The confidence box is realized by a full-support channel, not only by
an exact commuting-support law. Let $L$ be any Lagrangian and take
$$
p=\frac{19}{50}\delta_0+
\frac{61}{100}\operatorname{Unif}(L)+
\frac1{100}\operatorname{Unif}(G).
$$
Every Pauli has positive probability, and
$$
\begin{aligned}
p_0&=\frac{19}{50}+\frac{61}{100D}+\frac1{100D^2}
       \geq\frac{19}{50},\\
\eta&=\left(\frac{99}{100}\right)^2+
2\frac{19}{50}\frac1{100}
+\frac2D\frac{61}{100}\frac1{100}
+\frac1{D^2}\left(\frac1{100}\right)^2\\
&=\frac{9877}{10000}+\frac{61}{5000D}
+\frac1{10000D^2}>\frac{24}{25}.
\end{aligned}
$$
The cross bias of a uniform Lagrangian and the full uniform label
law is $1/D$, and the full uniform self-bias is $1/D^2$,
which proves this expression directly.

For this same channel at $n=32$, the $p_0$-only bound (EW10)
is nonpositive. Indeed $p_0<39/100$ and
$\log_2(D^2-1)>63$, so even omitting its nonnegative
binary-entropy subtraction gives
$$
32-(1-p_0)\log_2(D^2-1)
<32-\frac{61}{100}\,63<0.
$$
Thus the example separates these two sufficient certificates.
It does not prove that no ordinary measurement can obtain the
additional information supplied by $\eta$.

## Counterexamples fixing the interpretation

These examples use the Pauli specialization $D=2^n$ with integer
$n$ and $G=\mathbb F_2^{2n}$. They are also admissible instances
of the general orthogonal-unitary model.

1. **No dimension-free closeness to commuting support.** Let $q$
   be uniform on $\{X_1,Z_1,\ldots,X_n,Z_n\}$. Only the ordered
   pairs $X_j,Z_j$ and their reversals anticommute, so
   $c=1-1/n\to1$. Any commuting family captures at most half
   the probability mass. Its distance to every commuting-support
   law is at least $1/2$, although $H(q)=\log_2(2n)$.
   The entropy certificate does not require algebraic TV closeness.

2. **The entropy correction must scale with $n$.** Fix a Lagrangian
   $L$, let $A$ be uniform on $L\setminus\{0\}$ and $B$ uniform
   on $G\setminus L$, and put $q=(1-\alpha)A+\alpha B$.
   The pair biases are $A^{\mathsf T}HA=1$,
   $A^{\mathsf T}HB=-1/(D-1)$, $B^{\mathsf T}HB=0$. Hence
   $$
   c=(1-\alpha)^2-\frac{2\alpha(1-\alpha)}{D-1},\qquad
   H(q)=\log_2(D-1)+\alpha n+h_2(\alpha).
   $$
   A fixed small anticommutation probability can therefore increase
   entropy above $n$ by a quantity linear in $n$.

3. **A tempting stronger coefficient is false.** For $n\geq2$, fix
   nonzero $u$, set $S=u^\perp\setminus\{0,u\}$, and put
   $q=\frac14\delta_u+\frac34\operatorname{Unif}(S)$.
   Its support excludes identity, $|S|=D^2/2-2$, and for $a\in S$
   the character sum over $S$ is $-2$. Thus
   $$
   c=\frac7{16}-\frac9{4(D^2-4)}\longrightarrow\frac7{16},\qquad
   H(q)=h_2(1/4)+\frac34\log_2(D^2/2-2)=\frac32n+O(1).
   $$
   This violates a universal bound
   $H(q)\leq(2-\sqrt c)n+O(1)$, whose limiting coefficient would
   be about $1.3386$, with an additive bound uniform near this
   value of $c$. There is also an exactly fixed-$c$ version:
   writing $M=|S|$, take
   $$
   q=\alpha_n\delta_u+(1-\alpha_n)\operatorname{Unif}(S),\qquad
   \alpha_n=1-\frac{3}{4\sqrt{1+2/M}}.
   $$
   Its bias is
   $c=1-(1-\alpha_n)^2(1+2/M)=7/16$ for every $n\geq2$,
   while $H(q)=\frac32n+O(1)$. This rules out even an
   additive constant depending only on that fixed $c$.
   No such sharpened conjecture is used.

4. **Two moments do not determine entropy or a decoder.** For fixed
   $p_0$, a point conditional law and a uniform law on
   $L\setminus\{0\}$ both have $c=1$ and $\eta=1$, yet their
   conditional entropies range from 0 to $\log_2(D-1)$.
   The witness supplies a lower capacity bound, not channel
   identification or an equality formula for capacity.

## Primary precedents and the strongest direct comparators

**The scalar and its state-distribution relatives.**
[Haug and Kim, PRX Quantum 4, 010301 (2023), Eq. (3)](https://arxiv.org/html/2204.10061)
average the Pauli commutator norm over independent Bell-difference
outcomes. If their state-generated Bell-difference law is $Q$,
the normalization is exactly
$\mathcal B=2\Pr_{Q,Q}(\text{anticommute})=1-Q^{\mathsf T}HQ$.
That is a close scalar precedent. It does not identify the
Bell-difference law, the squared Pauli-expectation distribution of
a state, and an arbitrary channel error law $p$.

More directly,
[Bittel, Eisert, Leone, Mele and Oliviero, Quantum 10, 2171 (2026),
Appendix A, Example 11, Eqs. (A28)–(A30)](https://arxiv.org/pdf/2504.12263)
use the arbitrary Pauli-channel scalar
$$
s=\sum_{P,Q}p_Pp_Q\operatorname{Tr}(PQPQ)=D\eta
$$
in a Haar-twirled channel-variance calculation, separately from
$\sum_Pp_P^2$. Their Theorem 80 concerns pure-state stabilizer
Rényi entropies and Bell magic, not the Shannon entropy of every
classical Pauli error law. The scalar itself is therefore not
claimed as new here.

**Classical bilinear-bias and entropy methods.**
[Ben-Sasson and Ron-Zewi, approximate duality, Theorem 2.10 and
Section 5.1](https://doi.org/10.1137/12089003X) concern binary
bilinear bias on uniform sets and extract dual subsets.
[Impagliazzo, Moore and Russell, An Entropic Proof of Chang's
Inequality](https://arxiv.org/abs/1205.0263) control independent
biased characters using entropy. These are relevant methodological
precedents. Neither statement is used as a substitute for the
arbitrary-weight threshold and tail-integral proof above.

**Detectable entropy and fidelity certificates.**
[Macchiavello and Sacchi, PRL 116, 140501 (2016),
Eqs. (3)–(5)](https://arxiv.org/html/1510.00219v2)
derive detectable capacity lower bounds by upper-bounding exchange
entropy with a joint-output measurement entropy. On a generalized
Pauli channel, Bell probabilities give the error law and the
hashing certificate $n-H(p)$. Their
[mixed-probe extension, PRA 97, 012303 (2018)](https://arxiv.org/html/1712.06867v1)
includes a correction determined by the specified noisy probe and
measurement. Unknown SPAM is not thereby removed.

The identity-mass-only formula (EW10) is also the
[Schumacher quantum-Fano bound, Sec. 6.2, Eq. (24)](https://arxiv.org/pdf/quant-ph/9604023)
applied to the maximally mixed input. It is the tight error-entropy
upper bound given only $p_0$, since uniform nonidentity error
probabilities attain it. A nonpositive lower capacity certificate
does not establish zero capacity.

**Scalar purity is an established comparator.**
[Zhang, Smith, Smolin et al., npj Quantum Information 10, 60 (2024),
Supplementary Theorem 1, Eq. (20)](https://arxiv.org/html/2308.07068)
give the maximum entropy at purity $P$ in dimension $m$:
the maximizing spectrum has one eigenvalue
$$
a=\frac1m+\sqrt{\frac{m-1}{m}\left(P-\frac1m\right)}
$$
and $m-1$ equal remaining eigenvalues. Consequently
$$
S\leq h_2(a)+(1-a)\log_2(m-1).
$$
For a Pauli Choi state, $m=D^2$,
$P=\sum_ap_a^2$, and its output entropy is $n$.
Thus subtracting this entropy upper bound from $n$ gives an
ordinary scalar-purity hashing certificate. Their shadow and
collective two-copy measurements have different reference, copy,
gate and statistical costs; a small number of settings is not a
dimension-independent shot guarantee.

For the full-support example above, even supplying its exact purity
alongside $p_0$ does not make this maximum-entropy hashing comparison
positive. To see this without numerical logarithms, set
$$
r=1-p_0,\qquad m=D^2-1,\qquad
R=\frac{\sum_{a\neq0}p_a^2}{r^2}.
$$
At $D=2^{32}$, $r>3/5$ and every nonidentity probability is
at most $31/(50D)$. Therefore
$$
\frac1m\leq R\leq\frac{31}{50Dr}
<\frac{31}{30D}<\frac1{20000}.
$$
Let
$$
\alpha=\sqrt{\frac{R-1/m}{1-1/m}},\qquad
q'=\alpha\delta_u+(1-\alpha)\operatorname{Unif}(G\setminus\{0\})
$$
for any nonzero $u$. Its conditional purity is exactly
$\alpha^2+(1-\alpha^2)/m=R$.
Since $m>2$, $\alpha^2<2R<1/10000$, so $\alpha<1/100$.
The law $p'=p_0\delta_0+r q'$ has the same $p_0$ and total
purity as the example. Entropy concavity gives
$$
H(p')\geq rH(q')\geq r(1-\alpha)\log_2m
>\frac35\frac{99}{100}\,63
=\frac{18711}{500}>32.
$$
Thus a maximum error-entropy bound using just these fidelity/purity
data cannot give a positive hashing certificate here, while (EW12)
does. This comparison neither upper-bounds the channel's actual
capacity nor excludes an ordinary way to estimate $\eta$.

For one qubit this comparison is exact at the level of data.
Every pair of distinct nonidentity Pauli labels anticommutes, so
$$
\eta=1-4(p_Xp_Y+p_Xp_Z+p_Yp_Z),\qquad
\sum_ap_a^2=\frac{\eta+1-4p_0+4p_0^2}{2}.
$$
Therefore $p_0,\eta$ supply no information beyond $p_0$ and
purity when $n=1$. For larger registers the equality fails:
equal mixtures of $X_1,X_2$ and of $X_1,Z_1$ both have
$p_0=0$ and purity $1/2$, but their self-biases are 1 and 0.
The commutation statistic then contains geometry beyond the
collision probability.

The mathematical distinction here is the orthogonal-random-unitary
Shannon upper bound, its arbitrary-Pauli-law specialization, and
the original-channel hashing consequence.
It is neither a first scalar measurement nor a first detectable
capacity witness. No novelty priority, ordinary-query lower bound
or native architecture advantage follows from this comparison.
