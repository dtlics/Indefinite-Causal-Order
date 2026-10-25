<a id="nr-r06-thermal-return-cadence"></a>

# Thermal return, ordinary checking cadence and the full SWITCH instrument

This proof component belongs to the [NR-R06 required-gate/full-instrument comparison](../architecture-baselines.md#nr-r06-required-bosonic-entanglers). It gives a source-backed ordinary benchmark, exact abstract-channel comparisons and a sufficient cold-regime dominance theorem. No physical native-order advantage is established.

Two declared models below answer different questions. The code/vacuum uniform-reset semigroup gives an analytic ordinary cadence baseline. The full two-rail generalized-amplitude-damping (GAD) model gives the complete abstract SWITCH instrument and receiver optimum. Their rates and coefficients are not identified with each other or fitted to the measured device. Within each section, notation is local: the first section uses q for code population and u for no-loss survival; the GAD sections use u for equilibrium excitation and q for launched Bell-good mass.

## Primary pins

[Huang et al., Nature Physics (2026)](https://www.nature.com/articles/s41567-026-03211-9) and its [detailed preprint](https://arxiv.org/html/2504.12099v1) supply the measured nonlinear service. Preprint III/IV/Fig. 3 describe coupler-mediated logical square-root-iSWAP, ancilla vacuum-selective mapping/readout, and Bell storage with CPMG/repeated checks. Supplement IV identifies loss-to-vacuum followed by thermal code reentry as undetected dephasing, mitigated by retaining all-good check records. Supplement III checker numbers use final data postselection. Supplement VII gives a 150 ns gate flux pulse (50 ns plateau and two 50 ns edges); phase corrections are extra. No complete check/readout/reset/release clock was found. Published and preprint headline fidelities differ; do not mix versions.

## One physical decision and one cost

Decide how often to check an encoded payload after the required calibrated logical entangler and before a fixed release deadline T. The proposed qualification experiment injects data entangled with a separately characterized reference, retains the output, and records every erasure/readout/reset/abort event. Prepared-state tomography does not characterize this arbitrary-input/reference service.

Compare the minimum **mean complete laboratory time per accepted output**, E[cycle time]/p_accept, subject to a declared bound on the normalized accepted output's entanglement infidelity relative to the required target and a fixed release deadline. Also publish input-dependent acceptance and the full rejected output instrument; state fidelity after selection alone cannot establish a general service. For an unknown customer input, rejection is terminal failure: the throughput score averages independent fresh service/qualification attempts and grants no retry or recreation of that input. Early aborts can reduce the mean clock only when the same facility is granted to both sides. Include preparation, calibrated entangler and phase corrections, CPMG, check backaction, readout, helper decay, reset, release and all failed trials. Paid reusable calibrations are available to both sides.

This is a useful distinction from absorbing-vacuum models: terminal good occupancy does not certify a no-loss history. It does not yet make order interference useful.

## Strong ordinary controls, including a deferred marker

The ordinary side receives the actual repeated source check/readout records and CPMG controls. It also receives any coherent prefix marker actually qualified by the same ancillary coupling. For code projector P and Q=I-P, the ideal M=P tensor I + Q tensor X on a clean helper records one bad midpoint without changing a good unknown payload/reference. Execute M once, do not overwrite the flag, finish the service, and read helper plus terminal code occupancy once at the end. A classical midpoint readout/reset is not intrinsically required. Tables S2/S3 give two-photon ancilla T1 entries of 7 and 14/31 microseconds; retained-flag lifetime needs qualification.

Repeated controlled-X markers into the same two-level helper store parity, not a permanent OR: two bad samples can erase its flag. An exact update that preserves the sampled data and maps both helper values to 1 on bad occupancy is not unitary. More samples may use additional coherent storage, a larger helper, or measured records/reset; those are physical costs, not an automatic requirement for the one-midpoint case. Neither endpoint nor midpoint sampling detects a loss-and-return wholly between samples.

## A declared thermal-semigroup ordinary baseline (own derivation; not a device fit)

Take code dimension d, vacuum e, loss jumps sqrt(a)|e><i| and return jumps sqrt(b/d)|i><e| for each code basis i. Rates a,b are nonnegative; return discards the old payload and prepares tau=I/d. Ignore other errors only for this analytic baseline. Starting in the code, the terminal accepted map is

K_t(rho) = s(t) rho + [q(t)-s(t)] tau Tr(rho),
s(t)=exp(-a t),
q(t)=b/(a+b)+a exp[-(a+b)t]/(a+b),

with q=1 if a=b=0. The population equation is q'=-a q+b(1-q); the traceless code component decays as exp(-a t), proving the map.

For m equally spaced ideal code tests over storage time T, retaining every good result composes K_(T/m) m times:

K_acc(rho)=u rho+[p_m-u] tau Tr(rho),
u=exp(-a T), p_m=q(T/m)^m.

The accepted Choi entanglement fidelity is F_m=u/p_m+(1-u/p_m)/d^2. Thus accepting more returned trajectories raises yield but worsens this conditional quantum-output metric. For a,b>0, p_m tends to u and F_m tends to 1 as m grows; p_m-u = u*a*b*T^2/(2m)+O(m^-2). Finite check time, error, reference noise and thermal behavior during checks must be inserted before optimizing an actual cadence. With a noiseless, noninteracting helper, two ideal tests at T/2 and T have precisely the same accepted map as one deferred midpoint M plus the final code test (m=2): final helper projection onto 0 extracts the midpoint P on both sides of the density operator and commutes past every subsequent data-only channel.

## Exact bridge obstruction and next experiment

Adjacent square-root-iSWAP gates generally fail to commute, so their order superposition does not automatically implement the required clean target W. Two identical ideal calls commute, but two coherently selectable, independently noisy module/bath services are not supplied by repeating one calibrated pulse. A SWITCH claim additionally needs both chronological products of the same two physical dilations, a common target, retained environment/reset records, and a measured selector/readout clock.

The next discriminating experiment is therefore the ordinary full-instrument cadence sweep above, including a **single coherent midpoint flag with final readout** if qualified, against repeated recorded checks at the same release deadline and error threshold. Measure within-interval loss/return, accepted reference preservation, and complete mean clocks. Only a measured residual error/cost gap after these controls justifies engineering an order selector.

## Verification scope

The companion exact rational guard verifies the literal Lindblad generator on every operator matrix unit at code dimensions 2, 3 and 4, using separate loss/return rate bases. It verifies reset idempotence, formal accepted-map composition coefficients and deferred-marker Kraus amplitudes, plus the helper parity warning. It refuses optimized Python and imports quietly. The continuous-time formulas remain the analytic ODE/exponential proof above. These finite identities do not fit or certify a source-device instrument. The closest existing comparison is the required-TIP deferred midpoint marker and returned-leakage discussion.

## Full two-rail thermal GAD instrument and terminal recovery

This is a fixed-channel, all-launched calculation, not a source device
model. Each supplied module is F=G_(u,x) tensor G_(u,x), where
x=exp[-(gamma_down+gamma_up)Delta], u is the stationary excited population,
v=1-u, and G has Kraus operators

 sqrt(v)diag(1,sqrt(x)), sqrt[v(1-x)] sigma_-,
 sqrt(u)diag(sqrt(x),1), sqrt[u(1-x)] sigma_+.

A and B are identical modules with independent channel reservoirs. The
native protocol is the abstract SWITCH of these two channels, with actual
Kraus-pair operators (F_j F_i +/- F_i F_j)/2. It is not a claim that a
common-clock thermal bath implements this abstract supermap. The logical
payload has a fresh independent balanced control |+>; payload-control
preencoding, additional channel uses and changed native schedules are not
part of the optimized receiver benchmark below. The logical
code is {|10>,|01>}; all final even outputs and all control/marker outcomes
are retained as observed flags. Maps below are valid on arbitrary logical
input/reference. p,q,bad and utility use a normalized logical Bell input,
target identity, p=sum Tr K^dagger K/2, q=sum |Tr K|^2/4, bad=p-q.

Write B=u v(1-x)^2. One interval followed by final odd projection gives

 E(rho)=x rho+B Tr(rho)I, p_1=x+2B.

Thus E^n has p_n=(x+2B)^n, q_n=(p_n+3x^n)/4 and
bad_n=3(p_n-x^n)/4 exactly. For n>2 this represents retention of every
intermediate odd condition; repeatedly toggling a single marker qubit
does not implement a sticky bad record. The present n=2 ordinary protocol
needs only one coherent midpoint marker, initialized 0 and flipped on
even parity, without midpoint readout or reset.

For the full ordinary instrument, put
a0=v+u x, a1=u+v x, e00=v(1-x)a0, e11=u(1-x)a1,
t00=v(1-x^2)(v+u x^2), t11=u(1-x^2)(u+v x^2), and p1=x+2B.
Its four observed maps are

 marker0/odd: E^2(rho),
 marker1/odd: B(1+x^2-2B)Tr(rho)I,
 marker0/even: p1 diag(e00,e11)Tr(rho),
 marker1/even: diag(t00-p1 e00,t11-p1 e11)Tr(rho),

where even matrices use {|00>,|11>}. Every rejected candidate is a
replacement map: it contains no information about the original logical
input. After any terminal trace-nonincreasing CP recovery such a map has
q=p/4. It cannot contribute positive utility q-lambda*bad at lambda>=1.

The abstract SWITCH has full odd-flag maps that are logical Pauli channels,
M_s(rho)=sum_a w_(s,a) sigma_a rho sigma_a, with

 w_(+,I)=x^2+B(1+6x+x^2)/4+B^2/2,
 w_(+,X)=w_(+,Y)=B(1+6x+x^2)/4,
 w_(+,Z)=B(1+x)^2/4;

 w_(-,I)=B(1-x)^2/4-B^2/2,
 w_(-,X)=w_(-,Y)=B(1-x)^2/4,
 w_(-,Z)=B(1+x)^2/4.                                  (T1)

One derivation uses the one-qubit crossed-order kernel C_G. Its population
coefficients are a0^2,a1^2 and 2sqrt(x)(1-x)v,2sqrt(x)(1-x)u; its coherence
coefficient is x+B. The two-qubit crossed kernel factors C_G tensor C_G.
Its odd compression is (x+B)^2 rho+2xB(XrhoX+YrhoY), while the ordinary
two-interval odd map is x^2 rho+B(1+x)^2Tr(rho)I. Taking their half-sum
and half-difference gives T1. In particular all displayed weights are
nonnegative for physical u,x; B<= (1-x)^2/4 suffices for the minus-I term.

The remaining native even maps are replacement maps as well. Define
c00=2v sqrt(x)(1-x)a0^2 and c11=2u sqrt(x)(1-x)a1^2. Then

 native +/-/even: (1/2)diag(t00 +/- c00,t11 +/- c11)Tr(rho). (T2)

Their total probabilities, added to the odd maps, sum to one. They have
q=p/4 after any terminal CP recovery and are optimally rejected for
lambda>=1. No parity reject has been normalized away.

The flags are already classical in the retained output, rather than an
optional measurement that might hide a better joint receiver. For matched
Kraus families of identical independent channels, K_+(i,j)=K_+(j,i) and
K_-(i,j)=-K_-(j,i). Pairwise cancellation gives
sum_(i,j) K_+(i,j)rho K_-(i,j)^dagger=0 for every input/reference. Each
fixed pair also has one definite net ladder-change parity on the odd
input code, shared by both order terms; its odd/even output cross blocks
vanish. Thus retained control and target are a direct sum of the four
X/parity flag blocks. Arbitrary joint control-target TNI recovery reduces
to independent CP recoveries on these orthogonal blocks. Ordinary output
is likewise classical: the first F already makes odd/even parity blocks
incoherent, the marker stores that parity, and the second F creates no
parity coherence. The native cancellation uses A=B as full channels;
equal T1 alone does not establish it for unequal modules.

General terminal recovery on an odd Pauli flag reduces exactly to Pauli
correction or rejection for this Bell-utility objective. For recovery
operators R_alpha define f_a=sum_alpha |Tr(R_alpha sigma_a)|^2/4.
Pauli Parseval and trace-nonincreasingness give f_a>=0 and sum_a f_a<=1.
For flag probability p=sum w_a the utility is
sum_a[(1+lambda)w_a-lambda p]f_a. Hence its optimum is

 max{0,(1+lambda)max_a w_a-lambda p}.                    (T3)

The bound is attained by a single best Pauli correction or rejection;
continuous filters do not improve it. Plus has best correction I; minus
has best correction Z. Ordinary marker0/odd has best I, with
p_O=(x+2B)^2, q_O=(p_O+3x^2)/4. Its other flags are already disposed of
above. Thus the formulas compare the full instruments with arbitrary
terminal TNI CP recovery under the stated channel/control inventory.

A finite exact counterexample to dominance by the one-marker ordinary
protocol is u=x=9/25 and lambda=3/2. All individual GAD Kraus amplitudes
are rational, with sqrt(u)=sqrt(x)=3/5 and sqrt(v)=sqrt(1-x)=4/5.
Then B=36864/390625. Ordinary marker0/odd has

 p_O=45947208609/152587890625,
 q_O=26318345121/152587890625,
 q_O-(3/2)bad_O=-3124950111/152587890625.

Its best complete policy rejects every flag, utility zero. Native plus/
odd also has negative best utility, -13218092127/152587890625. Keeping
only minus/odd and correcting by logical Z instead gives

 U_N=1042255872/152587890625=0.0068305280827392 per launch >0. (T4)

Its q and bad are unnormalized launched masses. This is an exact finite-
channel comparison, not a weak-noise coefficient or an accepted-only
fidelity claim. It proves no dominance against all ordinary controls.
More markers, changed encodings, interventions inside an interval, extra
queries, and noisy/finite controls are different resources. In particular
frequent ideal parity records can suppress the leave-and-return noise.
Native order-coherent thermal-module access and the ordinary parity-marker
entanglers, storage, final measurements and recovery are supplied ports
whose physical cost is not established here.

The ideal ordinary marker flips on BOTH |00> and |11>, namely all of
P_even. The separately audited Huang vacuum-selective |00> pulse is only
a motivation for testing one of these states; it does not certify the
full parity gate or higher-leakage coverage. The native order-coherent
GAD-contact port is likewise unprovided. A measured joint upward/downward
thermal-rate fit is needed to assign any device to the cold or warm
regime; a fridge temperature or T1 alone does not establish u.

One bounded stronger-cadence example exposes that resource dependence.
At u=x=1/2 and lambda=3, the same balanced two-module native protocol has
optimal p=23/512, q=18/512 and utility 3/512 by keeping minus/odd with Z;
the best one-midpoint-marker policy is zero. Four equal subintervals of
the same total thermal duration have z=1/sqrt(2), u(1-u)=1/4 and odd
success per subinterval z+(1/2)(1-z)^2=3/4. Keeping every parity test gives
p_4=81/256, q_4=273/1024, bad_4=51/1024 and utility 15/128, twenty times
the native value. These exact launched masses use three intermediate
parity records, e.g. three fresh coherent markers measured at the end,
plus the final parity record. They require access inside each supplied
Delta module (or a finer-duration channel alphabet), extra entanglers,
marker storage/readout and their physical clock/noise. They do not follow
from a fixed opaque F_Delta query port, do not establish universal m=4
dominance, and do not grant free measurement/reset or a reusable sticky
single marker.

## A sufficient cold-regime dominance theorem

This is an analytic consequence of the identical-contact, identical-rail
thermal GAD model, not a fitted temperature statement about the source.
Each of the two independent contacts is G_x,u tensor G_x,u, with x in
[0,1], excited equilibrium population u in [0,1], and total time 2Delta.
The logical input is the odd code {|10>,|01>}. Full quantum-output
utility uses the normalized logical qubit Choi input: U=q-lambda*bad,
bad=p-q. Every failed launch is retained in the instrument. The formulas
below optimize arbitrary terminal trace-nonincreasing CP recovery on
all accessible target/control outputs, under the full-instrument
Pauli/replacement reduction proved in the accompanying derivation.
The native protocol has a fresh balanced |+> control independent of the
payload; preencoded control/payload inputs or extra calls are not included.

Write c=u(1-u), r=1-x, B=c r^2. Let [g]_+=max(0,g). The native accepted
odd X-control blocks have best target-good coefficients

 q_+=x^2+B(1+6x+x^2)/4+B^2/2,
 b_+=B(3+14x+3x^2)/4,
 q_-=B(1+x)^2/4,
 b_-=3B(1-x)^2/4-B^2/2.

The plus block uses identity; the minus block uses logical Z. All even
blocks are replacement maps and have no positive utility for lambda>=1.
Thus the optimal native utility is U_N=[g_+]_++[g_-]_+, where
g_+=q_+-lambda*b_+ and g_-=q_--lambda*b_-.

The ordinary single coherent midpoint bad-prefix marker, with final odd
test, has one nonreplacement block and its optimal utility is U_O=[g_O]_+,
where q_O=x^2+xB+B^2, b_O=3B(x+B), g_O=q_O-lambda*b_O.
All other ordinary marker/parity blocks are replacement maps.

Claim: if c<=1/8, then U_O>=U_N for every lambda>=1. This is a
sufficient cutoff; it is not asserted optimal. For a positive-temperature
qubit with u<=1/2, it includes u<=(1-1/sqrt(2))/2, approximately 0.1464.

First, g_O>=g_+ throughout the cold regime. At lambda=1,

 g_O-g_+=B[1+x^2-5B]/2>=0,
 b_+-b_O=B[(3+2x+3x^2)/4-3B]>=2Bx>=0.

The first inequality uses B<=1/8; the second uses the universal
B<=(1-x)^2/4. Increasing lambda therefore preserves g_O>=g_+.

Second, even without the cold restriction, g_O>=g_++g_- for lambda>=1.
At lambda=1 the gap is B(1-x)^2-3B^2>=0, and its lambda derivative is

 b_++b_--b_O=B[3-2x+3x^2-7B]/2
                 >=B(5+6x+5x^2)/8>=0.

It remains to handle a positive minus block when the plus block is
discarded. If g_->0 at lambda>=1, then x>1/5. Indeed

 q_--b_-=B[-1+4x-x^2+B]/2,

and B<=(1-x)^2/4 makes the bracket nonpositive for 0<=x<=1/5.
For x>1/5 put t=(1-x)^2/x<=16/5. In the cold regime,

 q_O-q_-=x^2-B(1-x)^2/4+B^2
              >=x^2[1-t^2/32]>=17x^2/25>0.

The positive-fidelity utility cutoffs R_O=q_O/b_O and R_-=q_-/b_- obey
R_O>R_- whenever B>0 and x<1 in this remaining case. After multiplying
their positive denominators, the numerator of R_--R_O is

 N=3B(x+B)(1+x)^2-q_O[3(1-x)^2-2B]
  =(1-x)^2*x^2[14c-3+14c^2*t+2c^3*t^2]
  <=-(51/100)(1-x)^2*x^2<0.

The last inequality substitutes c<=1/8,t<=16/5 in an increasing polynomial:
-5/4+(7/32)(16/5)+(1/256)(16/5)^2=-51/100.
For 0<=lambda<=R_-, the linear function g_O-g_- is nonnegative at both
endpoints: at zero by q_O>=q_-, and at R_- by R_O>=R_-.
Therefore g_O>=g_- whenever g_->0.

If both native blocks have positive utility, use the second inequality;
if only the plus or only the minus is positive, use the first or third;
if neither is positive there is nothing to show. B=0 and x=1 reduce
directly to equality with no returned trajectories. This proves the
stated all-lambda>=1 dominance, including arbitrary retained control and
flag recovery within the identical GAD model.

For larger c this proof does not assert dominance. Warm rational examples
in the accompanying full-instrument calculation give positive heralded
native-minus utility when the single-midpoint comparator rejects every
output. More ordinary checks can change that comparison and require
their additional coherent memory or actual readout/reset clocks. No
general ordinary-control or hardware separation follows from this cutoff.

## Replay and remaining experiment

The existing NR-R06 fault-simulation job imports three exact standard-library
guards: `thermal_cadence_guards.py`, `dualrail_thermal_guards.py` and
`thermal_cold_cutoff_guards.py`. They check finite rational generator and
composition identities, full flagged maps and retained-control cross blocks,
the warm counterexamples, stronger-cadence arithmetic and cold-proof
coefficient/envelope ingredients. They do not evaluate a continuous-time
device, establish the all-parameter inequalities by sampling, or certify
physical routing, marker access, rates or clocks. The continuous-time,
joint-recovery and all-lambda proofs are the analytic arguments above.

The next useful source experiment measures the full accepted/rejected
reference instrument and upward/downward rates during storage and checks,
qualifies both even states of the coherent parity marker, and prices the
single-marker and repeated-record cadence frontier at one release deadline.
An implementation of this abstract-channel comparison additionally needs
two fresh independently noisy selectable dilations, a common required ideal
operation and a measured selector clock. A live or shared-bath order
experiment instead needs its own complete retained-output comparison.
Without those ports and a residual benefit over the strongest
paid ordinary cadence, the warm abstract example is not an architecture gain.
