<a id="nr-r01"></a>

# NR-R01 — Physical Bell-frame restoration with a quantum switch

A quantum switch has a constant advantage in an explicitly specified quantum recovery game with local noise, fresh private frames, and the same mean query budget as an ordinary receiver. The guarantee averages over the sampled frame; it is not a guarantee for every fixed frame.

The proof combines analytic operator arguments with exact rational and polynomial certificates. This new recovery theorem has not been formalized in Lean or externally peer reviewed. [Checks and their scope](checks/README.md) describe the executable evidence. The detailed operator and source arguments have separate owners: [local converse](methods/local-converse.md) and [design transfer](methods/design-transfer.md).

## Theorem

For every integer $n\geq 8$, put $D=2^n$. In the recovery game defined below, choose a fresh private frame from a public finite circuit ensemble whose standard sixth-twirl channel has unhalved diamond error at most $1/(2000D^{10})$ from Haar measure. Then:

| Receiver | Mean module calls | All-round expected score |
| --- | ---: | ---: |
| Standard quantum switch | $2$ | At least $1427/2000=0.7135$ |
| Any ordinary variable-length receiver | At most $2$ | At most $55706889062400/80664000728557\approx0.6906040930$ |

The certified score gap is at least

$$
\frac{3693750914850839}{161328001457114000}
\approx 0.0228959070>0.022.
$$

An ordinary receiver may use arbitrary noiseless quantum memory, known processing, encodings, entangled probes, postselection, data bypass, classical adaptive module selection, and arbitrarily many calls on rare histories. Its **actual** mean call count includes calibration and rejected histories. There is no lower bound on its acceptance probability and no bound on its computation or memory beyond the well-defined quantum operations in the model.

If only the switch control's off-diagonal coherence is reduced by a factor $\nu\geq0.97$, with all other operations unchanged, the switch score remains at least $0.70135$. Its gap from the same ordinary upper bound is at least

$$
\frac{17336156971469039}{1613280014571140000}
\approx0.0107459070.
$$

This visibility statement concerns the specified control-dephasing model, not arbitrary routing or physical gate errors.

## Source, noise and receiver interface

Write $X_1=X\otimes I_{D/2}$, and similarly for $Y_1,Z_1$. For each task the source samples one private $U$, fixed throughout that task, and defines

$$
A_U=UX_1U^\dagger,\qquad
B_U=UY_1U^\dagger,\qquad
C_U=iB_UA_U=UZ_1U^\dagger.
$$

Thus $A_U,B_U,C_U$ are Hermitian involutions, $A_UB_U=-B_UA_U$, and $C_U^2=I$. The channel of $C_U$ is the channel of the desired product $B_UA_U$.

The public frame distribution $\mu_n$ satisfies

$$
\begin{aligned}
\mathcal T_{\mu,t}(T)
  &=\mathbb E_{U\sim\mu}
      U^{\otimes t}T(U^\dagger)^{\otimes t},\\
\|\mathcal T_{\mu_n,6}-\mathcal T_{\mathrm{Haar},6}\|_\diamond
  &\leq\epsilon_n,\qquad
\epsilon_n\leq\frac1{2000D^{10}}.
\end{aligned}
$$

This is the additive diamond norm of the **standard six-copy twirling channel**, without a factor $1/2$. It is not merely an entrywise moment or spectral-norm requirement. The distribution and construction may be public, but the selected circuit word and seed are not given to the receiver.

The supplied memoryless modules are

$$
\begin{aligned}
\mathcal E_U&=\Lambda_n\circ\operatorname{Ad}_{A_U},&
\mathcal F_U&=\Lambda_n\circ\operatorname{Ad}_{B_U},\\
\Lambda_n&=\operatorname{Dep}_{\eta_n}^{\otimes n},&
\operatorname{Dep}_\eta(T)&=(1-\eta)T+
                  \eta\operatorname{Tr}(T)I_2/2,\\
\eta_n&=\frac43\left[1-(9/10)^{1/n}\right].
\end{aligned}
$$

There is one independent local noise site on every qubit **after each complete global module**. Each invocation has fresh noise and exposes no error label. The identity-Pauli weight of a complete module is $z=9/10$, so the joint identity-error weight of two calls is $r=z^2=81/100$. This is the actual local channel, not an approximation by global depolarization.

The source prepares

$$
|\Phi_D\rangle_{RQ}=D^{-1/2}\sum_i|i\rangle_R|i\rangle_Q,
\qquad
|\Phi_{C_U}\rangle=(I_R\otimes C_U)|\Phi_D\rangle,
$$

and gives the receiver only $Q$ and the two callable modules. The **original reference $R$** is inaccessible to the receiver and remains untouched until verification. After the receiver delivers a physical register $Q'$ and an accept/reject bit, an accepted return is tested by the fixed projector

$$
\Phi_D=|\Phi_D\rangle\langle\Phi_D|_{RQ'}.
$$

The verifier neither corrects $R$ using the frame nor changes or relabels this test. The frame-aware source has no online influence after issuance. No clean unscrambled copy of the challenge payload, $U$ description, seed, correlated program, free training invocation, or source assistance is supplied. A metadata instruction to track a frame cannot substitute for the physical return under this test. Standard Bell preparation and verification need $O(n)$ known gates and no unknown $C_U$ gate at verification.

The score is $+1$ for an accepted verification pass, $-1$ for an accepted verification failure, and $0$ for rejection. Every round counts. This utility prefers a known erasure to an undetected wrong return; it is not itself a probability or a capacity.

Ordinary module identity is chosen classically. Known coherent routing among registers is permitted. A free coherent indexed oracle combining the modules, a specified vacuum-sector extension, or exposed noise environments would be a different interface. Different tasks use independent private frames, and the next task begins after delivery of the preceding output. Persistent-frame calibration amortization and joint access to future tasks' devices are not included.

## Bell recovery and actual expected cost

Fix $U$, and let $M_U$ be the receiver's accepted decoder subchannel, with Kraus operators $K_j$. Define

$$
p_U=\operatorname{Tr}M_U(I/D),\qquad
q_U=\frac1{D^2}\sum_j
       |\operatorname{Tr}(C_UK_j)|^2.
$$

Since $C_U=C_U^\dagger$, cyclicity of trace gives

$$
\langle\Phi_D|
 (\operatorname{id}\otimes M_U\circ\operatorname{Ad}_{C_U})(\Phi_D)
 |\Phi_D\rangle=q_U.
$$

Thus $q_U$ is both the accepted standard Bell-pass weight in this task and the accepted target-goodweight for $M_U$ approximating $\operatorname{Ad}_{B_UA_U}$ on a standard Bell input. Acceptance is $p_U$, and $0\leq q_U\leq p_U$. With frame averages $p,q$, the all-round score is exactly

$$
\mathsf S=2q-p.
$$

The initially supplied $Q$ has marginal $I/D$ for **each** $U$. Every event $N\geq j$, including all preceding adaptive operations and private memory, is a CP effect on the initial $Q$. Its probability is therefore exactly its local Bell-input probability at that $U$. Summing the nonnegative tail probabilities proves that the actual query cost

$$
c=\mathbb E[N]=\sum_{j\geq1}\Pr(N\geq j)
$$

is the cost used by the converse. For unbounded stopping this uses Tonelli's theorem, not an optional-stopping assumption. All training and rejected histories are included. Finite $c$ excludes infinitely many calls with positive probability; a branch delivering no output can be valued as rejection.

## Haar prefix bound and the uniform intercept

The [local converse](methods/local-converse.md) proves the following homogeneous two-call inequality, first for Haar $U$. If an ordinary at-most-two-call accepted subinstrument has first-query launch probability $w$ on $I/D$, then

$$
q-rp\leq a_{D,n}w,\qquad
a_{D,n}=\frac{3r(1-r)}D+
 \frac{4\mu_{\rm err}}{(1-D^{-2})^2}+\frac{128}{D^2}.
\tag{1}
$$

Here $\mu_{\rm err}$ is the largest **joint Pauli-pair weight** other than $(I,I)$. It is neither a marginal error weight nor the total error probability. For the prescribed local channel,

$$
\mu_{\rm err}=\frac{27}{100}
          \left[(10/9)^{1/n}-1\right]
 \leq\frac3{100n}.
$$

The inequality follows from $(1+1/(9n))^n\geq10/9$. A single nonidentity Pauli at one physical site in one module, with no errors elsewhere, maximizes that nonidentity joint weight.

The operator proof of (1) includes every mixed-tensor sector, not sampled spectra. Its ideal fidelity moment has the exact decomposition

$$
\Omega_f=|w_0\rangle\langle w_0|+R_0,
\qquad
0\leq R_0\leq\frac{128}{D^5}I,
$$

Here $w_0=(v_{\rm EF}-v_{\rm FE})/[D(D^2-1)]$ for the two unnormalized causal wiring kets defined in the method proof, each of squared norm $D^3$ and with mutual inner product $D$. Orthogonality of the Pauli-shifted wiring kets, a successful comb trace bound $D^3w$, and the proper four-port causal acceptance dual yield the three terms of $a_{D,n}$. The complete spectral, Weyl-dimension and affine argument is in [the method proof](methods/local-converse.md). In particular, the launch factor $w$ is preserved across input-dependent initial order branches; the intercept is not charged separately to every later branch.

For $n\geq8$, $D\geq256$, (1) holds with the uniform bound

$$
\begin{aligned}
A&=\frac{4617}{2560000}
 +\frac3{200}\left(\frac{65536}{65535}\right)^2
 +\frac1{512}\\
 &=\frac{2749735788563}{146597076480000}
 \approx0.0187570984.
\end{aligned}
\tag{2}
$$

This includes repeated calls, early stopping, arbitrary encodings and data bypass. The missing-axis bound used to restore those branches is $q\leq\beta p$, $\beta=2/D^2\leq r$. With no queried axis the smaller bound is $q\leq\kappa_0p$, $\kappa_0=1/(D^2-1)$. Both are integrated Haar statements; their use under finite designs is justified below by moment transfer, rather than by asserting a Haar conditional distribution under a finite prior.

## From two-call prefixes to every finite-mean receiver

Group accepted histories by $N=0,1,2,\geq3$, with probabilities $p_0,p_1,p_2,p_T$ and goodweights $q_0,q_1,q_2,q_T$. Let $r_1=\Pr(N\geq1)$ and $k=1-r=19/100$. The Haar inequalities are

$$
q_0\leq\kappa_0p_0,\qquad
q_1\leq\beta p_1,\qquad
q_2-rp_2\leq Ar_1,\qquad
q_T\leq p_T.
$$

To obtain the third inequality, retain only the original protocol's accepted histories that stop at exactly two calls, and truncate when it requests a third. At a branch that would repeat a device, replace the repeated second call, before execution, by a dummy call to the unused device and mark failure; pad earlier-stop querying branches similarly. No third call is appended. The original same-axis successes have nonpositive affine score and can then be restored in the bound. This preserves the original first-query launch weight. No future query output or posterior conditioning on reaching the prefix is used.

Every long accepted branch may be perfect in this relaxation. Distribution-free counting gives

$$
c\geq r_1+p_2+2p_T,\qquad
r_1\geq p_1+p_2+p_T.
$$

Subtract $kc$, use $A\leq k$, and then replace $r_1$ by its lower bound in the term with coefficient $A-k\leq0$. This yields

$$
q-kc\leq
 \kappa_0p_0+(\beta+A-k)p_1+b(p_2+p_T),
\qquad
b=3r+A-2.
$$

The exact conditions $b\geq\kappa_0$ and $2r\geq1+\beta$ bound each coefficient by $b$. Consequently

$$
q\leq bp+kc,\qquad
b=\frac{65786478674963}{146597076480000}
  \approx0.4487570984.
\tag{3}
$$

This proof charges all failed and training histories and permits arbitrary finite expected length. It does not restrict learning on long branches or assume any maximum number of queries.

## Efficient finite frames and resource-scaled approximation

A $j\leq2$-call prefix has balanced degree at most $(2j,2j)$ in $U,U^*$ for acceptance, and at most $(2j+2,2j+2)$ for target goodweight. Exact sixth moments therefore transfer the integrated prefix inequalities. The conditional missing-axis Haar proof need not hold under a finite design, and is not reused as such.

For the standard-twirl diamond error $\epsilon_n$, the [mixed-norm transfer proof](methods/design-transfer.md) gives

$$
|\Delta q_j|,|\Delta p_j|
 \leq\epsilon_nD^{4j+2}r_1.
$$

The factors come from conversion of the mixed-tensor twirl by partial transposes, the unnormalized objective trace bound, and positivity of a comb with trace at most $D^{j+1}r_1$. Arbitrary memory is absorbed into the external comb. Fixed physical Pauli postprocessing is a convex mixture of fixed unitary conjugations on slot legs and preserves this estimate; local-noise covariance is not assumed.

Combine accepted one- and two-call histories into one padded two-slot subinstrument, without changing their actual cost. Put

$$
\delta=\epsilon_nD^{10}\leq\frac1{2000},\qquad
e=(1+r)\delta\leq\frac{181}{200000}<\zeta:=\frac1{1000}.
$$

Its combined goodweight loses at most $\delta r_1$, and its weighted acceptance loses at most $r\delta r_1$. Thus the additional intercept is $er_1$, not an uncharged additive error per execution. The zero-query target bound loses at most $\epsilon_nD^2p_0$. The coefficient conditions

$$
A+\zeta<k,\quad
2r\geq1+\beta,\quad
b+\zeta\geq\kappa_0+\epsilon_nD^2
$$

hold already at $D=256$ and remain valid for larger $D$. Repeating the stopping algebra under the **actual** frame distribution gives

$$
q_{\mu_n}\leq\widetilde b\,p_{\mu_n}+kc_{\mu_n},
\qquad \widetilde b=b+\zeta<\frac12.
\tag{4}
$$

No assertion is made that an unbounded-query transcript, output or cost distribution matches Haar. Long paths use only positivity and counting under their actual probabilities. A computationally unbounded receiver may know the whole finite support and learn the selected label on a rare long path; that path has already been allowed perfect goodweight and charged at its full cost.

The corrected finite-gate random-circuit theorem of Brandão, Harrow and Horodecki supplies the required ensemble with $O_G(n^2)$ ideal nearest-neighbor gates for fixed design order six and polynomially many private random bits. The alphabet is fixed, finite, inverse-closed, algebraic and universal. Reversing and inverting the word gives $U^\dagger$, so $A_U,B_U,C_U$ have polynomial ideal circuit descriptions. The norm conversion and finite-bit sampling allowances are part of [the source proof](methods/design-transfer.md); [references](references.md) identify the precise primary results. No computational-security assumption is involved. The gate-set constants are unspecified, so this is an asymptotic circuit-size result, not a practical depth estimate.

## Score comparison and switch implementation

Since $q\leq p$ and $\widetilde b<1/2$,

$$
(2q-p)(1-\widetilde b)-(q-\widetilde b p)
  =(1-2\widetilde b)(q-p)\leq0.
$$

Equation (4) therefore implies

$$
\mathsf S_{\rm ord}\leq\frac{kc}{1-\widetilde b}.
$$

At actual mean cost $c\leq2$, this is precisely

$$
\mathsf S_{\rm ord}\leq
L:=\frac{55706889062400}{80664000728557}
\approx0.6906040930.
$$

For the switch, prepare the order control in $|+\rangle$, route $Q$ through the two modules in the two orders, measure the control in the $X$ basis, and accept the minus outcome. The identity-error pair contributes exactly the target channel, so $q_{\rm sw,Haar}\geq r=0.81$. The exact Haar acceptance identity for physical Pauli noise is

$$
p_{\rm sw,Haar}
 =\frac{1+r}{2}-\frac{1-r}{2(D^2-1)}\leq0.905.
$$

Hence $\mathsf S_{\rm sw,Haar}=2q-p\geq0.715$. Only this second-moment acceptance identity and positivity are needed; full fourth-moment formulas for $q$ are not required.

Here is a direct proof of the acceptance identity. For an unweighted
physical Pauli-error pair $P,Q$, the successful Kraus operator is
$K_{PQ}=(QBPA-PAQB)/2$, so

$$
p_{PQ}=\frac12-\frac1{2D}
 \operatorname{Re}\operatorname{Tr}(APBQPAQB).
$$

The identity pair has interference trace $-D$ and acceptance one.
For $Q\ne I$, condition on $B$ and use

$$
\mathbb E[A T A\mid B]
 =\frac{\operatorname{Tr}(T)I-\operatorname{Tr}(BT)B}{D},
$$

proved by writing $A$ in off-diagonal blocks with Haar $V$ in the
eigenbasis of $B$. Take $T=PBQP$ and contract against $QB$.
Since $\operatorname{Tr}Q=0$, the expected interference trace becomes
$(\operatorname{Tr}BQ)^2/D$. The balanced-reflection second moment on
the traceless matrix space gives
$\mathbb E(\operatorname{Tr}BQ)^2=D^2/(D^2-1)$.
If $Q=I$ and $P\ne I$, instead condition on $A$ and apply the same
formula to $B(PA)B$, contracted against $AP$. It gives the identical
value with $A,P$ in place of $B,Q$. Thus every nonidentity pair has
average acceptance $1/2-1/[2(D^2-1)]$. Mixing identity-pair mass $r$
and the remaining mass $1-r$ proves the displayed formula. This proof
keeps the physical local Pauli law; it does not replace it by global
depolarization.

The accepted two-slot switch process is positive and has external trace at most $D^3$: inserting two completely depolarizing channels makes its accepted probability equal to its trace divided by $D^3$, which is at most one. The same two-slot objective estimate therefore applies to the switch, although it is not a fixed-order causal comb. Both $q$ and $p$ change by at most $\delta\leq0.0005$ under the approximate frame source. Thus

$$
\mathsf S_{\rm sw,\mu_n}\geq0.715-3\delta
 \geq\frac{1427}{2000}=0.7135.
$$

Subtracting $L$ proves the main exact gap. No acceptance denominator, retry of a damaged input, or omission of rejected rounds occurs in this comparison.

## Specified order-coherence loss

Let $\nu\in[0,1]$ multiply only the switch control's off-diagonal terms. For any pair of channels the accepted map is exactly

$$
M_-(\nu)=\nu M_-+\frac{1-\nu}{2}\mathcal C_{\rm diag},
\qquad
\mathcal C_{\rm diag}=
 \frac{\mathcal F_U\circ\mathcal E_U+
       \mathcal E_U\circ\mathcal F_U}{2}.
$$

Each definite composition is trace preserving and has target goodweight at least $r$, so its Bell score is at least $2r-1=0.62$. Linearity gives

$$
\mathsf S_{\rm sw,Haar}(\nu)\geq0.31+0.405\nu.
$$

Subtracting the same $3\delta\leq0.0015$ source allowance, $\nu\geq0.97$ yields

$$
\mathsf S_{\rm sw,\mu_n}(\nu)\geq
\frac{14027}{20000}=0.70135.
$$

The resulting exact gap is the visibility bound in the theorem. In a phase-flip-channel convention, $\nu=0.97$ means phase-flip probability $0.015$; it does not mean three percent arbitrary physical gate error.

## Corollary: a secret pure-state recovery test

Instead of the Bell resource, independently choose a secret pure state $|\psi\rangle$ from an exact projective two-design, supply $C_U|\psi\rangle$, and test the physical return against $|\psi\rangle$ after delivery. The receiver gets neither the state label nor a clean copy before committing its output and flag. The verifier needs the state label, not $U$ or $C_U$.

For every CP accepted map, including input-dependent acceptance,

$$
s=\frac{Dq+p}{D+1},\qquad
\mathsf S_\psi=2s-p=
 \frac{2Dq-(D-1)p}{D+1}.
$$

For each $U$, the ciphertext ensemble has marginal $I/D$; the same prefix-effect and Tonelli argument identifies its actual expected cost. Here

$$
\widetilde b<\frac{255}{512}
 \leq\frac{D-1}{2D}.
$$

Consequently the nonnegative combination

$$
\mathsf S_\psi=
 \frac{q-\widetilde b p}{1-\widetilde b}
 +\left(\frac{2D}{D+1}-\frac1{1-\widetilde b}\right)(q-p)
 \leq\frac{kc}{1-\widetilde b}
$$

gives the same ordinary upper bound. Also

$$
\mathsf S_\psi-(2q-p)=\frac{2(p-q)}{D+1}\geq0,
$$

so the switch lower bounds, including the stated visibility case, remain valid. Uniform stabilizer states give an efficiently sampled and verified exact two-design; a uniform Clifford preparation and its inverse specify the state test. This Clifford sampling is only for $|\psi\rangle$, not for the hidden frame $U$: Clifford frames alone do not provide the required sixth design. This is a corollary of NR-R01, not a second canonical recovery theorem.

## Scope and dependencies

The scrambled Bell input is already maximally entangled. The task restores a **specified standard Bell alignment**, rather than creating entanglement or proving a generic distribution rate. Keeping the original reference passive is essential:

$$
(I\otimes C_U)|\Phi_D\rangle
 =(C_U^T\otimes I)|\Phi_D\rangle.
$$

If the frame-aware source could correct $R$ online, $C_U^T$ on $R$ would restore the standard pair with zero receiver queries. Frame-dependent reference corrections, alternative reference registers and verification relabeling are outside the theorem.

All guarantees average over **fresh sampled frames**. Local-noise success can be frame- and input-dependent; the unscrambled frame $U=I$ excludes the corresponding worst-frame claim. Both unknown axes and the absence of free frame-correlated training are essential. Reusing a frame over many outputs permits amortized calibration and needs a separate theorem. [Obstructions](obstructions.md) record these and other interface restrictions.

The rate $\eta_n=\Theta(1/n)$ keeps a module's identity-Pauli mass at $0.9$. This is not a fixed-local-error-rate fault-tolerance threshold. The switch has $2n$ physical post-module noise sites; the ordinary mean budget gives at most $2n$ in expectation. Noise is not charged at every compiled elementary gate. State preparation, one scrambling operation, device configuration, transfer and verification are common exogenous resources, outside the receiver's oracle-call budget. No wall-clock, unrestricted batch-throughput, cryptographic-security or communication-capacity advantage follows.

The [global-noise result](global-noise.md) uses distinct assumptions and has its own owner. [References](references.md) distinguish the existing parity-filter and error-filtration mechanisms from this combined mean-cost recovery statement. [Checks](checks/README.md) specify which exact identities and certificates are replayed, and which analytic and representation-theoretic arguments remain mathematical proof inputs rather than Lean-checked claims.
