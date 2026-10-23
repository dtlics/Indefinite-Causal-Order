# Self-switch diagnostics do not supply a cheap decoder bootstrap

This proof component of [NR-R20](../memory-qualification.md#nr-r20)
concerns the fixed memoryless promise
$$
\mathcal E_{1,U}=\tfrac12\operatorname{id}+\tfrac12\Delta_U,
\qquad
\mathcal E_0=\tfrac12\operatorname{id}+\tfrac12\Omega_D,
\qquad D=2^n.
$$
It strengthens the [working-code verification argument](memory-code-verification.md)
for an explicit switch interface, including retained receiver-side quantum
programs and a high-prior mean cost. It also evaluates Petz and ordinary
code-projection constructions. It does not exclude every switch-assisted
decoder, framed switch slots or richer coherent access to the environment.
The [exact checker](../checks/architecture/verify_code_bootstrap.py)
guards the complete channel identities, code-projection formulas and
finite probability ledgers; it does not reprove C6 or a coding theorem.

## The complete self-switch has a high-case ordinary compiler

For this identity, allow any $0\le t\le1$ and put
$\mathcal E_t=(1-t)\operatorname{id}+t\Delta_U$.
For a nonnegative integer $k$,
$$
\mathcal E_t^k=(1-t)^k\operatorname{id}
 +[1-(1-t)^k]\Delta_U.
$$
This has a commuting Kraus representation using $I$ and the rank-one
projectors $P_i=|u_i\rangle\langle u_i|$. For any $k,l$, all Kraus
operators $A_i$ of $\mathcal E_t^k$ commute with all Kraus operators
$B_j$ of $\mathcal E_t^l$. The standard switch Kraus operators therefore are
$$
|0\rangle\langle0|_C\otimes B_jA_i+
|1\rangle\langle1|_C\otimes A_iB_j
=I_C\otimes B_jA_i.
$$
Consequently, as a complete channel,
$$
\boxed{\mathcal S(\mathcal E_t^k,\mathcal E_t^l)
 =\operatorname{id}_C\otimes\mathcal E_t^{k+l}.}       \tag{B1}
$$
This holds for arbitrary initial control, payload and reference
entanglement; it does not assume a plus control or maximally mixed input.
Serial execution costs $k+l$ production calls, exactly the number of
physical visits in the switched primitive.

Consider a training or decoding algorithm whose special primitives are
these unframed switches of production powers. Replace each by (B1),
retaining the control register. Known operations, measurements, adaptive
classical choices and quantum program registers outside these primitives
may be arbitrary. Complete channel equality makes the whole emulator
identical on the high case. No equality on the low case is asserted or
needed. A slot such as $V\mathcal E_tV^\dagger$, or known interventions
inserted inside a coherently reordered block, is outside this compiler.

## One successful unassisted code use gives a high-mean cost bound

Return to $t=1/2$. Training may leave a quantum program at the receiver
and select a classical block length $L$ and encoder description. Then
prepare a logical Bell pair $\Phi_2$ with an inaccessible reference,
encode one half, pass every input-bearing encoded system through the
$L$ production uses, and decode using the program. Count all oracle calls
inside training, encoding, storage and decoding. Rejections and
nontermination contribute zero to the joint Bell-pass statistic.

This is an unassisted block-storage model with a syntactically enforced
deployment interface: for every oracle instance and every finite execution
cutoff, only classical training metadata can reach the encoder; all
retained training quantum systems stay at the receiver. No quantum
entanglement is preshared between encoder and decoder, the reference is
inaccessible to the decoder, and no input-bearing system bypasses storage.
A receiver program may depend on the channel and training records but is
independent of the freshly prepared logical input. The classical length
is selected before that input; forward classical metadata is allowed.
Conditional on the fixed channel parameter $U$, future production calls
have fresh independent environments/error records. The retained program
is not entangled with those future records.

These restrictions apply also to the emulated low case and every
truncation; high-case equality alone would not imply them there.
A more general split quantum program would require an interface enforcing
separability for every oracle, rather than a promise verified only on the
high branch. Arbitrary adaptive two-way payload/feedback protocols are
outside this block-code converse.

For the low channel, the symmetric-extension argument in
[the verification method](memory-code-verification.md) proves
$$
F_0\le3/4                                                     \tag{B2}
$$
for every such logical-qubit code, uniformly in $L$, encoder and decoder.
A receiver-side quantum program is just an ancilla in its resulting CPTP
decoder map. This reasoning does not physically clone the program.
Classically correlated training choices are mixtures of codes to which
the same uniform ceiling applies. Shared encoder/decoder entanglement
would change that premise and is excluded.

Run the ordinary emulator, followed by one such Bell validation, and let
$F_h$ be its high-prior average joint Bell-pass probability. Its high
distribution is the original augmented protocol's distribution by (B1).
Its low behavior need not match that protocol, but (B2) still bounds
its accepted Bell statistic. Truncating or aborting a low decoder cannot
increase this statistic past the ceiling: its successful submap is bounded
by a TP completion, including a fixed failure output.

Use the parent's C6 shared-basis half-trace-distance bound. With
$$
q_*=\lfloor D^{1/16}/100\rfloor\ge1,\qquad
d_*=215/10000,
$$
every ordinary hard-$q_*$ primitive strategy has an output-probability
gap at most $d_*$ on the two hard priors. Let $N$ count the emulator's
primitive $A/B$ calls, and $c_h=\mathbb E_hN$.
Truncate before call $q_*+1$, outputting zero. Its high acceptance
decreases by at most
$\Pr_h[N>q_*]\le c_h/q_*$; its low acceptance remains at most $F_0$.
Thus
$$
F_h-F_0-c_h/q_*\le d_*.
$$
If a potentially unbounded protocol is used, assume it terminates almost
surely on the high prior. Add a finite overall step cap $M$, again
outputting zero. The extra high loss tends to zero as $M\to\infty$,
while the low procedure is finite regardless of its untruncated behavior.
Apply C6 at each finite $M$ and take the limit. Finite query mean alone
does not rule out an infinite zero-query computation.

It follows, without any finite-cost or termination assumption on the
untruncated emulated low case, that
$$
\boxed{c_h\ge q_*(F_h-3/4-d_*).}                       \tag{B3}
$$
In particular, $F_h\ge7/8$ implies
$$
c_h\ge \frac{207}{2000}\,q_* .                       \tag{B4}
$$
When a finite balanced-prior emulator mean $c_{\rm bal}$ is also defined,
$c_h\le2c_{\rm bal}$ gives $c_{\rm bal}\ge207q_*/4000$.
One consumable Bell validation suffices because the quantitative C6
probability-gap lemma is used; a single shot is not being claimed to
classify with success $2/3$.

For atomic production calls the ordinary simulator uses a fresh
Bernoulli$(t)$ coin, applying $A$ then $B$ only on the active branch.
The decision to invoke a call precedes that coin. Summing predictable
call indicators gives
$$
\mathbb E_hN_{\rm primitive}
=\mathbb E_h(N_A+N_B)+2t\,\mathbb E_hN_E.             \tag{B5}
$$
Here $N_E$ includes every visit in an emulated switch power and every
additional recovery or payload use; direct primitive accesses are charged
separately. At $t=1/2$ the atomic-production-only high mean equals the
primitive mean. Classical random lengths and adaptive program records
do not remove this cost.

## Self-adjoint noise is not a free Petz decoder

The physical channel obeys $\mathcal E_t^\dagger=\mathcal E_t$, so its
adjoint CP map is already available ordinarily. For a known rank-$K$
projector $P$, set $\sigma=P/K$, $\tau=\mathcal E_t(P)/K$.
The physical Petz map is
$$
\mathcal R_P(X)=
P\mathcal E_t\!\left(\mathcal E_t(P)^{-1/2}X
                         \mathcal E_t(P)^{-1/2}\right)P,       \tag{B6}
$$
with inverses on the output support, followed by the known inverse
encoder. The code-dependent inverse-root filter has not become known
merely because the middle adjoint is available. For $\sigma=I/D$,
Petz is just $\mathcal E_t$, so recovery after one noisy use is
$\mathcal E_t^2=\mathcal E_{2t-t^2}$, which further suppresses coherences.

The coherent algorithm of
[Gilyén et al., PRL 128, 220502 (2022), assumptions and Theorem 1](https://arxiv.org/html/2006.16924v2)
requires block-encoding circuits for $\sigma,\tau$ and a unitary
Stinespring circuit $U_{\mathcal N}$, including its inverse. With their
reciprocal-eigenvalue parameters $\kappa_x=1/\lambda_{\min}^+(x)$,
their gate bound is
$$
\widetilde O\!\left(\sqrt{d_E\kappa_\tau}
 [\kappa_\tau C_\tau+C_{\mathcal N}
 +C_\sigma\min\{\kappa_\sigma,d_E\kappa_\tau/\epsilon^2\}]\right).
$$
The $C$'s charge the supplied circuits. Opaque forward channel access,
even with $\mathcal E_t^\dagger=\mathcal E_t$, does not supply this
reversible environment interface. Copies of $\tau$ are available by
preparing $P/K$ and calling the channel; converting them to filters
has its own copy, precision and control costs. Granting the same coherent
interface to both competitors makes this an ordinary decoder baseline.
This upper-bound theorem is not a lower bound on every Petz algorithm.

More recent implementations also belong in the comparison.
[Biswas, Vaidya and Mandayam, PRR 6, 043034 (2024)](https://journals.aps.org/prresearch/pdf/10.1103/PhysRevResearch.6.043034)
give code-specific Petz circuits, including a low-ancilla sequence of
two-outcome measurements, but synthesize the recovery Kraus operators and
their polar factors; that sequence uses a weak-perturbation approximation.
[Utsumi and Nakata, Quantum 10, 2024 (2026)](https://quantum-journal.org/papers/q-2026-03-13-2024/)
give improved generalized Yoshida--Kitaev and Petz-like decoders with
QSVT-based fixed-point amplification. They assume known encoding/noise
descriptions and noiseless other operations. Their entanglement-transmission
guarantees require decoupling; costs depend on a nonzero spectral lower bound
and coherent Stinespring circuits, including conjugated or inverse operations.
Suitable encoders permit capacity-approaching rates, but opaque self-adjoint
channel access does not thereby supply an efficient decoder. The 2022 Petz
algorithm is one baseline, rather than the strongest general construction.

A direct filter implementation has a sharper scoped obstruction.
Assume $K<D$ and $\tau>0$, as holds almost surely for a fixed code
independent of a Haar hidden basis. Write
$w_i=\langle u_i|P|u_i\rangle$ and $S_2=\sum_iw_i^2$.
Since $\sum_iw_i=K$, $S_2\ge K^2/D$. Therefore
$$
\operatorname{Tr}[(I-P)\tau]=t(1-S_2/K)
 \le t(1-K/D),\qquad
\lambda_{\min}(\tau)\le t/D.                         \tag{B7}
$$
Also $\lambda_{\max}(\tau)\ge(1-t)/K+t/D$, by averaging its
restriction to the code. Its max/min ratio is consequently at least
$1+(1-t)D/(tK)$; the algorithmic reciprocal parameter is at least $D/t$.
Flat leverage scores $w_i=K/D$ attain these spectral values.

Even if the exact filter $F=a\tau^{-1/2}$ is free, its success operation
is contractive only when $a^2\le\lambda_{\min}(\tau)$.
Applying this filter, one ordinary $\mathcal E_t$ call and the code
projection gives the accepted map $a^2K\mathcal R_P$. Since Petz is TP
on the support of $\tau$, total success is input-independent and at most
$$
a^2K\le tK/D.                                       \tag{B8}
$$
For $K\ll D$ this particular routine has small yield. A failed unknown
payload cannot be retried by assuming fresh copies of it. Coherent
amplitude amplification needs additional reversible access. Neither
(B7) nor (B8) is a universal decoding lower bound; rank-deficient
outputs, larger codes and different algorithms need separate analysis.
The actual opaque-query obstruction for a working decoder in the
specified interface is (B3), not an inference from conditioning alone.

## A stronger ordinary heralded-output comparator

A known encoder already permits code-membership postselection without
Petz. Encode, use the memory once, undo the encoder, and accept when
the redundant input register returns to its initialized value.
This is ordinary syndrome postselection. On a logical Bell input its
acceptance $p$ and joint accepted Bell probability $q$ under the high
channel are exactly
$$
p_1=1-t+\frac tK S_2,\qquad
q_1=1-t+\frac t{K^2}S_2.                             \tag{B9}
$$
Indeed compressed dephasing Kraus matrices $V^\dagger P_iV$ have
trace $w_i$ and squared Hilbert--Schmidt norm $w_i^2$.
Under the low channel,
$$
p_0=1-t+tK/D,\qquad q_0=1-t+t/(KD).                  \tag{B10}
$$
Conditional entanglement fidelity is $q/p$, not $q$.

For a random rank-$K$ code independent of a fixed hidden basis,
unitary second moments give
$$
\mathbb ES_2=\frac{K(K+1)}{D+1},\quad
\bar p_1=1-t+t\frac{K+1}{D+1},\quad
\bar q_1=1-t+t\frac{K+1}{K(D+1)}.                    \tag{B11}
$$
To verify the moment directly, invariance makes
$\mathbb E(P\otimes P)=aI+b\,\mathrm{SWAP}$.
Its traces $K^2$ and $K$ determine
$a=K(KD-1)/[D(D^2-1)]$ and
$b=K(D-K)/[D(D^2-1)]$. A rank-one $P_i\otimes P_i$
has both contractions one, so summing $D(a+b)$ proves (B11).

In qubit dimensions $K=2^k$, uniform known Clifford encoding supplies
the same second moment; see
[Dankert et al., PRA 80, 012304 (2009)](https://arxiv.org/abs/quant-ph/0606161).
It uses a described Clifford circuit, $n-k$ redundant prepared qubits,
its inverse and syndrome readout, one production call and a failure flag.
These known gates, preparation, readout, resets and every rejected launch
are charged. No hidden-basis learning or inverse noise is used.
The guarantee is an encoder ensemble independent of the fixed channel,
not a guarantee when an adversary chooses the hidden basis after seeing
a fixed code.

For fixed $t<1$ and $K/D\to0$, both (B10) and the randomized instrument
in (B11) have conditional fidelity tending to one and yield tending to
$1-t$. The ensemble conditional fidelity is $\bar q/\bar p$; it need
not equal $\mathbb E(q/p)$ for a code chosen once.
Indeed $p_1\ge1-t$ also gives the per-code-average bound
$$
\mathbb E[1-q_1/p_1]\le
\frac{t(K^2-1)}{(1-t)K(D+1)}.
$$
Good heralded output therefore does not distinguish the two capacities
or supply a deterministic code exceeding (B2). Failure loses the input.
For example, completing failures by the maximally mixed logical state
has all-attempt Bell fidelity $q+(1-p)/K^2$, rather than $q/p$.
No optimality of this completion or of ordinary feedback is claimed.

The remaining useful-decoder question must identify an interface beyond
the high-case compiler, charge any environment/inverse or private
encoder access to both competitors, and demonstrate an all-attempt
service with finite payload, calibration and runtime costs.

## A framed qubit identity branch has a stronger ordinary helper echo

This is an online heralded state-recovery comparison, not a trained
decoder or an extension of (B1) to arbitrary framed slots. Fix one unknown
qubit axis $N=\mathbf n\cdot\boldsymbol\sigma$, $\|\mathbf n\|=1$,
and fresh independent noise calls
$$
\mathcal E_N=(1-t)\operatorname{id}+t\Delta_N
=a\operatorname{id}+b\operatorname{Ad}_N,\qquad
a=1-t/2,\quad b=t/2,\quad 0<t\le1.
$$
The axis stays fixed. All identities below preserve an inaccessible
payload reference.

For a known frame $V$ with Bloch rotation $R$, put
$c=\mathbf n\cdot R\mathbf n$ and
$W=(\mathbf n\times R\mathbf n)\cdot\boldsymbol\sigma$.
In $\mathcal S(\mathcal E_N,V\mathcal E_NV^\dagger)$, with a separately
prepared plus control and $X$ readout, only the two nonidentity Kraus
operators contribute to minus. Their commutator is $2iW$, so
$$
\mathcal F_-(\rho)=b^2W\rho W,\qquad
W^2=(1-c^2)I,\qquad
\mathcal F_-^2=b^4(1-c^2)^2\operatorname{id}.          \tag{F1}
$$
Thus two launches with the same frame give an exact identity branch
using four noisy calls. Choose a quarter rotation about a uniformly
random coordinate axis once per attempt and reuse it. Then $c=n_i^2$,
and the success obeys
$$
\frac{t^4}{24}\le
\frac{b^4}{3}\sum_i(1-n_i^4)^2\le b^4=\frac{t^4}{16}. \tag{F2}
$$
For the lower bound, with $x_i=n_i^2$,
$e_2=\sum_{i<j}x_ix_j$ and $e_3=x_1x_2x_3$,
$\sum_i(1-x_i^2)^2=2+2e_2^2+4e_3\ge2$.
The upper bound holds term by term.
Each launch needs a coherent-order router, an independently prepared plus
control and its $X$ readout/reset, as well as $V,V^\dagger$ around the
framed port. The two launches therefore use four physical memory visits
and four known frame gates. Early rejection can avoid the second launch,
but the first still consumes two visits. Those ports and control
coherences are not supplied by the averaged channel alone.

Suppose an ordinary interface supplies one clean helper and known
controlled $F_{\mathbf u}=\mathbf u\cdot\boldsymbol\sigma$ couplings
before and after an exposure, for a chosen known unit vector $\mathbf u$.
Prepare the helper in plus, apply the controlled involution, call
$\mathcal E_N$, apply the same controlled involution, and read the
helper in $X$. Let $s=\mathbf n\cdot\mathbf u$ and
$W_{\mathbf u}=(\mathbf n-s\mathbf u)\cdot\boldsymbol\sigma$.
The complete flagged instrument is
$$
\mathcal G_{\mathbf u,+}(\rho)
=a\rho+bs^2F_{\mathbf u}\rho F_{\mathbf u},\qquad
\mathcal G_{\mathbf u,-}(\rho)
=bW_{\mathbf u}\rho W_{\mathbf u}.                   \tag{F3}
$$
Indeed identity error always gives plus, while the noise Kraus operators
are $\sqrt b(N\pm F_{\mathbf u}NF_{\mathbf u})/2$.
Here $W_{\mathbf u}^2=(1-s^2)I$ and
$F_{\mathbf u}W_{\mathbf u}=-W_{\mathbf u}F_{\mathbf u}$.
Reset the same helper and repeat with the same $\mathbf u$. Then
$$
\begin{aligned}
\mathcal G_-^2&=b^2(1-s^2)^2\operatorname{id},\\
\mathcal G_+^2(\rho)
 &=(a^2+b^2s^4)\rho+2abs^2F_{\mathbf u}\rho F_{\mathbf u},\\
\mathcal G_+\mathcal G_-(\rho)
 &=\mathcal G_-\mathcal G_+(\rho)\\
 &=abW_{\mathbf u}\rho W_{\mathbf u}
   +b^2s^2F_{\mathbf u}W_{\mathbf u}\rho
                         W_{\mathbf u}F_{\mathbf u}.
\end{aligned}                                                    \tag{F4}
$$
These four branches sum to a TP instrument. Rejection after the first
plus can stop the attempt immediately.

Choose $\mathbf u$ once per attempt from nine unoriented axes: each
coordinate axis with probability $1/15$, and each of
$(\mathbf e_i\pm\mathbf e_j)/\sqrt2$, $i<j$, with probability $2/15$.
This distribution obeys
$\mathbb E s^2=1/3$ and $\mathbb E s^4=1/5$ for every $\mathbf n$.
For example, a signed coordinate pair contributes fourth-power sum
$(n_i^4+n_j^4)/2+3n_i^2n_j^2$; summing the listed weights gives
$(\sum_i n_i^4+2\sum_{i<j}n_i^2n_j^2)/5=1/5$.
The entire accepted map consequently is
$$
\mathbb E_{\mathbf u}\mathcal G_{\mathbf u,-}^2
=\frac{8b^2}{15}\operatorname{id}
=\frac{2t^2}{15}\operatorname{id}.                   \tag{F5}
$$
This exact success exceeds the actual native candidate's upper bound
$t^4/16$ for every $0<t\le1$, not merely its lower bound.
At $t=1/2$ it is $1/30$. The ordinary hard call cap is two, using
four controlled gates and one measured/reset helper. With early
rejection its mean noisy-call count is
$1+b\mathbb E(1-s^2)=1+t/3$.
All nine involutions are known one-qubit Cliffords, but a controlled
face-axis Clifford is an additional physical gate and need not cost
the same as a controlled Pauli. Uniform coordinate axes alone give
success at least $t^2/9$ with the same call cap.

The coefficient $8/15$ is minimax within this two-identical-echo family:
for any fixed $\mathbf u$, the spherical average over $\mathbf n$ is
$\frac12\int_{-1}^1(1-z^2)^2\,dz=8/15$.
No distribution over $\mathbf u$ can have a larger worst-case value,
and the nine-axis choice attains it everywhere. This is not an optimum
over all ordinary protocols.

Two clean helpers allow a stronger, differently priced comparison.
Coherently select one of $\{I,X,Y,Z\}$ before one exposure, undo it,
and project the four-branch label onto its uniform state. For every
Kraus matrix $K_j$ the success operator is
$$
\frac14\sum_P P^\dagger K_jP=\frac{\operatorname{Tr}K_j}{2}I.
$$
The accepted map for any qubit channel is therefore
$F_e(I/2,\mathcal E)\operatorname{id}$. For $\mathcal E_N$ it succeeds
with probability $a=1-t/2$, using one noisy call, two known Pauli
multiplexers and two helpers with preparation/readout.

These ordinary protocols retain input-bearing information in the helper
during exposure. They are valid only when that clean wire and the
stated couplings are available and charged. A clean helper with an
unrestricted target-helper SWAP would already give a deterministic
qubit bypass. A provider-fixed order control need not expose those ports.
Conversely, imposing the unassisted block-storage cut to prohibit the
ordinary bypass while granting every native helper coupling for free
would compare different resources. Faults, helper lifetime, routing,
loss and known gates require a matched hardware model.

All accepted identities are online state-recovery instruments. Failure
can destroy the supplied unknown state; they do not prepare a successful
channel before that state arrives. For independent re-preparable inputs,
the nine-axis echo's mean calls per accepted fresh state are
$15/(2t^2)+5/(2t)$, including rejected histories; the two-helper twirl
uses $1/a$ noisy calls on average. Retrying the same destroyed unknown
payload is not allowed. These costs do not establish unassisted capacity.

Controlled checks are established prior methods, including
[Gonzales et al., Pauli Check Sandwiching](https://arxiv.org/abs/2206.00215).
Higher-order Pauli-channel distillation is also prior work:
[Kechrimparis, Moran and Kwon](https://arxiv.org/html/2501.13696v1).
The comparison closes this particular framed qubit identity-branch
candidate with the supplied ordinary helper interface. It does not
simulate arbitrary framed switch instruments or prove an ordinary
compiler for every program trained with framed higher-order blocks.
