# A deployable code supplies an ordinary memory-qualification test

This is a proof component of [NR-R20](../memory-qualification.md#nr-r20).
At $D=2^n$, $n\ge1$, fix the memoryless production-channel promise

$$
\mathcal E_{1,U}=\tfrac12\mathrm{Id}+\tfrac12\Delta_U,
\qquad
\mathcal E_0=\tfrac12\mathrm{Id}+\tfrac12\Omega_D.
\tag{DC1}
$$

The capacity-existence decision and its ordinary query lower bound belong
to the parent result. Here the issue is qualification after an actual
encoder and decoder have become available. The comparison uses the
same physical channel calls and does not infer a working code from a
positive asymptotic capacity.

## Finite-block logical fidelity has a low-channel ceiling

A fixed classical code description $c$ specifies CPTP maps

$$
\mathcal A_c:\mathcal L(\mathbb C^K)\longrightarrow
\mathcal L((\mathbb C^D)^{\otimes L}),\qquad
\mathcal B_c:\mathcal L((\mathbb C^D)^{\otimes L})
\longrightarrow\mathcal L(\mathbb C^K),\quad K\ge2.
$$

This is a standard unassisted block code: every system carrying the
unknown logical input traverses the $L$ channel uses. Encoder ancillas
may be discarded; decoder ancillas are freshly prepared and independent.
There is no protected input-bearing bypass or preshared quantum
assistance between encoder and decoder. The $K$-dimensional verification
reference is inaccessible to the decoder. A heralded decoder is completed
to a TP map, with failures included in the output statistic. Two-way
assisted protocols and arbitrary postselected conditional fidelities
are different models.

Let $\Phi_K=|\Phi_K\rangle\langle\Phi_K|$, where

$$
|\Phi_K\rangle=K^{-1/2}\sum_{i=0}^{K-1}|i\rangle_R|i\rangle_A,
\qquad
F(c,\mathcal E)=\operatorname{Tr}\!\left[
\Phi_K(\mathrm{Id}_R\otimes
\mathcal B_c\circ\mathcal E^{\otimes L}\circ\mathcal A_c)(\Phi_K)
\right].
$$

The low channel has the elementary symmetric two-output extension

$$
\mathcal J_0(\rho)=\tfrac12\rho\otimes I_D/D
+\tfrac12 I_D/D\otimes\rho.
\tag{DC2}
$$

This is CPTP, and both reduced channels are exactly $\mathcal E_0$.
Apply $\mathcal J_0^{\otimes L}$ after the single encoder and apply
the same decoder separately to its two output banks. The resulting
state $\omega_{RB_1B_2}$ has both $RB_i$ marginals equal to the
logical channel's normalized Choi state. Put

$$
P_1=\Phi_{RB_1}\otimes I_{B_2},\qquad
P_2=\Phi_{RB_2}\otimes I_{B_1}.
$$

The two marginals therefore give

$$
2F(c,\mathcal E_0)
=\operatorname{Tr}[(P_1+P_2)\omega]
\le\|P_1+P_2\|_\infty=1+K^{-1}.
\tag{DC3}
$$

To prove the norm explicitly, define isometries from $\mathbb C^K$
into $R\otimes B_1\otimes B_2$ by

$$
V_1|x\rangle=K^{-1/2}\sum_i|i,i,x\rangle,\qquad
V_2|x\rangle=K^{-1/2}\sum_i|i,x,i\rangle.
$$

Then $P_j=V_jV_j^\dagger$ and

$$
V_1^\dagger V_2=I/K,\qquad
(P_1+P_2)(V_1\pm V_2)=(1\pm K^{-1})(V_1\pm V_2).
$$

The plus and minus image spaces are orthogonal, both have dimension
$K$, and their complement is the kernel. This proves (DC3), hence
the uniform ceiling

$$
\boxed{F(c,\mathcal E_0)\le b_K:=\frac{K+1}{2K}}
\quad\text{for every such code and every }L.
\tag{DC4}
$$

The proof uses a symmetric extension. Its connection to antidegradable
channels is established by
[Myhr and Lütkenhaus, Lemma 5](https://arxiv.org/html/0812.3667).
It does not require entanglement breaking: the low Choi state has Bell
overlap $1/2+1/(2D^2)>1/D$, exceeding the maximum for a separable
state. It also avoids inferring a finite-block bound merely from
$Q=0$.

## A supplied working code can be tested directly

Prepare $\Phi_K$, apply the code to one half, decode, and measure
the projector $\Phi_K$ on the reference and decoded output. The
Bernoulli mean is exactly $F(c,\mathcal E)$. If the supplied high code
satisfies

$$
F(c,\mathcal E_{1,U})\ge b_K+\gamma,\qquad\gamma>0,
$$

threshold the empirical mean at $b_K+\gamma/2$. For

$$
N=\left\lceil2\gamma^{-2}\ln(1/\beta)\right\rceil,
\qquad0<\beta<1,
\tag{DC5}
$$

independent fresh trials, Hoeffding's inequality bounds each low-code
false acceptance and good-high-code false rejection by $\beta$.
The code is frozen throughout validation. Conditional on that code
and the fixed $U$, the channel uses and trial preparations are
independent; a point estimate on a changing or memory-bearing device
does not justify this confidence bound.

Validation costs exactly $NL$ production calls, $N$ executions of
the encoder and decoder, logical Bell preparation/readout and resets,
and the protected verification reference. For $K=2^k$, the Bell
projection can use $k$ paired Clifford checks. These costs can be
large even when the call multiplier $N$ is constant. No estimate of
$U$, process tomography or basis diagonalization is required once
the working code is supplied.

In particular, a logical-qubit code with

$$
K=2,\qquad F(c,\mathcal E_{1,U})\ge7/8
$$

has gap $\gamma=1/8$ above the low ceiling $3/4$. Threshold $13/16$
and

$$
N=\lceil128\ln12\rceil=319
\tag{DC6}
$$

give each validation error at most $1/12$.

A logical-qubit reference can also be replaced by trusted preparation
and return measurements on the six Pauli eigenstates. For a TP qubit
map with Bloch action $r\mapsto Tr+t$, their average return probability
is $\mu=1/2+\operatorname{Tr}(T)/6$, whereas
$F_e=(1+\operatorname{Tr}T)/4$. Thus

$$
\mu=(2F_e+1)/3.
\tag{DC7}
$$

The low/high bounds become $5/6$ and $11/12$. Threshold $7/8$
and $\lceil288\ln(1/\beta)\rceil$ fresh tests give the same error
guarantee, using $L$ production calls per test. This trades the
retained reference for more trials and trusted logical preparation
and readout. It does not remove SPAM calibration. The average-fidelity
identity is established; see
[Nielsen, *Physics Letters A* 303, 249–252 (2002)](https://arxiv.org/abs/quant-ph/0205035).

## Learning and running the code obey the original query ledger

Suppose ordinary training makes a random number $N_{\rm train}$ of
production calls, then outputs a classical code description $c$ and
block length $L(c)$. Freeze it, discard quantum training memory, and
validate using fresh channel uses. Training may be adaptive, and it
may fail; a failure still supplies some TP fallback code for testing.
All training attempts and rejected outcomes are charged.

Assume under the Haar high prior that training produces a code with
$F(c,\mathcal E_{1,U})\ge7/8$ with probability at least $2/3$.
For every low-channel training outcome, (DC4) still bounds its selected
code by $3/4$. Conditional fresh-shot concentration is unaffected by
how that classical code was selected. With the 319-shot test,

$$
\Pr[\mathrm{reject}\mid0]\ge11/12,\qquad
\Pr[\mathrm{accept}\mid1]\ge(2/3)(11/12)=11/18.
$$

Its balanced-prior success is therefore at least

$$
\frac12\left(\frac{11}{12}+\frac{11}{18}\right)
=\frac{55}{72}>\frac23.
\tag{DC8}
$$

The expected production-call cost is exactly

$$
\mathbb E N_{\rm train}+319\,\mathbb E L(c),
\tag{DC9}
$$

where expectations use the balanced Haar promise prior, including
training randomness. Conditional on the realized code, validation
makes exactly $319L(c)$ calls. Taking total expectations proves the
ledger even if training length or output block length has rare long
branches. It requires finite expected cost and the parent result's
stopping/truncation scope; it does not replace a mean by a hard cap.

For

$$
q_*:=\left\lfloor D^{1/16}/100\right\rfloor\ge1,
$$

the parent NR-R20 expected-cost reduction at $t=1/2$ now implies

$$
\boxed{\mathbb E N_{\rm train}+319\,\mathbb E L(c)>q_*/12.}
\tag{DC10}
$$

This is a corollary of the existing C6 bound, not a new optimal exponent.
If training or code execution also uses the underlying dephaser ports,
use the parent's full mixed primitive-call ledger instead; those
additional accesses cannot be omitted.

Setting training to zero also gives a precise orientation-blind
finite-block consequence: a fixed $U$-independent code attaining
$7/8$ Bell fidelity on at least two-thirds of Haar $U$ must have
$L>q_*/(12\cdot319)$. This does not exclude small codes for known
or structured $U$, another channel family, or weaker fidelities
that do not cross the ceiling. Universal coding under channel
uncertainty is possible asymptotically, as established by
[Bjelaković, Boche and Nötzel](https://arxiv.org/html/0811.4588).
That existence theorem does not supply an $n$-uniform short block or
an efficient deployed decoder for this promise.

## Consequence for an architecture claim

An efficient working-code interface gives an ordinary qualifier whose
cost is a constant number of executions of that code at fixed
confidence. If an encoder/decoder is supplied through private hardware
or $U$-correlated classical advice, that is additional interface
information; the no-advice C6 lower bound cannot simultaneously be
applied as though the code had been learned for free. If the code is
learned from the stipulated ordinary channel interface, (DC10) charges
that learning and its finite block length.

Capacity screening before code construction can still have operational
value. [Pfister et al., *Nature Communications* 9, 27 (2018)](https://arxiv.org/html/1611.05411)
study one-shot capacity estimation and verification, including comparison
of physical and encoded channels. Their protocols do not provide an
ordinary polynomial-query discriminator for every hidden-basis promise.
The present result likewise does not establish that every code-free
capacity decision is useless. A native application must identify the
decision made before deployment and price the later encoder, decoder,
calibration and verification access.

The all-$K$ broadcast, projector and statistical arguments above are
analytic. Finite isometry/projector checks in the parent
[memory-qualification replay](../checks/architecture/verify_memory_qualification.py)
guard their transcription, not the general coding theorem or a
hardware implementation. This component adds neither a formal Lean
endpoint nor a claim about two-way-assisted capacity, arbitrary
adaptive communication codes or unmodelled temporal noise.
