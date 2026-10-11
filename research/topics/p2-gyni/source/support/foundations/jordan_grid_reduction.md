# A quantitative Jordan-grid reduction for unrestricted binary GYNI

**Structural reduction; the exact GYNI value is not determined.**
This note supplies an explicit finite-dimensional SDP approximation with a
dimension-independent error estimate. It neither treats a numerical plateau as
an optimum nor claims finite-dimensional attainment of the unrestricted
supremum. The original bipartite process model and all four unrestricted port
dimensions are retained before the reduction.

<a id="p2-r03"></a>

## 1. Source premise and canonical grid

The external premise is Liu–Chiribella Theorem 1: arbitrary process/instrument
correlations admit equal-rank labelled projective instruments. Its construction
uses pure orthogonal setting flags and fixed local pre/post channels.
See [the theorem and Appendix F](https://arxiv.org/html/2403.02749v3).

Consequently each party can use, on some even-dimensional H,

    M_(a|x)(rho)=P_(a|x) rho P_(a|x) tensor |x><x|,
    P_(0|x)+P_(1|x)=I, rank P_(a|x)=dim(H)/2.

For integer L>=1, set K=L+1, h=pi/(2L), and theta_j=j h, j=0,...,L.
The FIXED canonical local instrument acts on H_L=C^K tensor C^2, with

    P_(0|0)^L=I_K tensor |0><0|,
    P_(0|1)^L=sum_j |j><j| tensor |v_j><v_j|,
    |v_j>=cos(theta_j)|0>+sin(theta_j)|1>,
    P_(1|x)^L=I-P_(0|x)^L,

and outputs the postmeasurement system together with |x><x|. Its input
dimension is 2K and output dimension is 4K. Both parties use this same fixed
instrument; only the valid process W is optimized. Denote its maximum GYNI
score by g_L. This is one ordinary finite SDP, not a see-saw optimization.

### Quantitative theorem

For every finite-dimensional bipartite quantum process and arbitrary local
binary-input/binary-output instruments,

    score <= g_L + (1+sqrt(2)) pi^2/(16 L^2).               (1)

Conversely g_L<=omega_GYNI because its fixed instruments are allowed in the
original problem. Hence

    0<=omega_GYNI-g_L <= C/L^2,
    C=(1+sqrt(2))pi^2/16.                                  (2)

On the nested grids L=2^k, g_L is nondecreasing. Certified SDP upper values
plus C/L^2, and certified feasible lower values, give a convergent enclosure
of the unrestricted supremum. Taking running minima makes the upper
enclosures monotone if desired.

The following proof retains coherence BETWEEN distinct Jordan-angle sectors.
It never selects a single sector or assumes those sectors form a classical
mixture.

## 2. Equal-rank Jordan normal form

For P=P_(0|0), Q=P_(0|1), the two-projector decomposition splits H into
one- and two-dimensional invariant subspaces. On every nontrivial two-block,
a basis change puts the projectors in the form

    P=|0><0|, Q=|v(theta)><v(theta)|, 0<theta<pi/2.

The one-dimensional joint eigenspaces can also be paired. Equal ranks of P
and Q imply dim(H_10)=dim(H_01). Their half-dimension ranks additionally imply
dim(H_00)=dim(H_11). Pair 11 with 00 to obtain theta=0 blocks, and 10 with 01
to obtain theta=pi/2 blocks. Thus H is exactly a direct sum of two-dimensional
angle blocks. The simultaneous basis change is absorbed into the process by
fixed local unitaries.

## 3. Unbiased angle rounding and its channel error

For each block angle theta in [theta_j,theta_(j+1)], independently round it to
the lower or upper grid endpoint with probabilities chosen so E theta'=theta.
Writing delta=theta'-theta,

    E delta=0, E delta^2<=h^2/4.

This randomness is independent of the actual setting x. Setting-zero
projectors do not change. Let P be the setting-one projector before rounding,
P' its random block-diagonal replacement, and D=P'-P. On a two-block,

    ||P''(theta)||=2,
    (P(theta')-P(theta))^2=sin^2(delta) I.

The second-order Taylor estimate and the variance bound give, uniformly in the
number of blocks and their multiplicities,

    ||E D||<=h^2/4,  ||E D^2||<=h^2/4.                    (3)

Consider the instrument channel with its outcome explicitly recorded. A
Stinespring isometry is

    V|psi>=sum_(a=0,1) P_a|psi> tensor |a>_C tensor |a>_E.

Tracing E makes C classical. The setting flag can be appended without
changing any norm. For Delta V=V'-V,

    ||E Delta V||=sqrt(2)||E D||<=sqrt(2)h^2/4,
    E Delta V^*Delta V=2 E D^2 <=h^2 I/2.

Expand the averaged channel around V. The two cross terms have diamond norm
at most 2||E Delta V||. The remaining CP map has diamond norm at most
||E Delta V^*Delta V||. Partial trace is contractive. Therefore

    ||E Instrument(theta')-Instrument(theta)||_diamond
       <= (1+sqrt(2))h^2/2.                               (4)

This estimate applies to the WHOLE direct sum, including all coherences
between different blocks. Bounding individual blocks and discarding those
coherences would not suffice.

## 4. Why an arbitrary valid process cannot amplify this error

Fix the other party's setting and its complete instrument. Contracting it
with W produces a one-slot quantum tester for the party being changed. Its
positive outcome operators sum to rho_in tensor I_out, with Tr rho_in=1.
This follows directly from positivity and normalization of the original
process for every local CPTP map.

Such a tester is realized by preparing a purification of rho_in and measuring
the channel output together with the retained reference. Thus the total
variation between its joint classical outputs under two instrument channels
is at most half their diamond distance. This argument does not assume a
definite order for the original two-party process.

By (4), replacing one party's setting-one instrument changes a fixed-setting
winning probability by at most

    (1+sqrt(2))h^2/4.

Only half the uniformly weighted GYNI settings use that party's setting one.
Telescoping the replacements for Alice and Bob therefore changes the average
score by at most

    (1+sqrt(2))h^2/4=C/L^2.                               (5)

The rounded average is a valid instrument. Equivalently, it is the average
of finitely many rounded projective strategies. The bilinear Born rule makes
the independently rounded two-party score the average of their scores.

For completeness, the same argument bounds each conditional joint
distribution's total-variation error by (1+sqrt(2))h^2/2. A convex mixture of
the compressed processes below realizes the averaged behaviour on the same
fixed grid ports. Thus the approximation is not limited to the one score.

## 5. Multiplicity removal with a VALID process extension

Fix one rounding outcome. Group identical angles to write

    H = direct_sum_j (C^2 tensor C^(r_j)),
    P_(a|x)=direct_sum_j(P_(a|x)(theta_j) tensor I_(r_j)).

Let r=max_j r_j and embed H isometrically in H_L tensor C^r, retaining angle
j, qubit coordinate, and multiplicity label. Call this isometry J. Every grid
projector tensor I_r preserves the embedded subspace and intertwines with the
rounded original projector.

One must NOT simply zero-pad W. Instead enlarge the local ports by composing
the original process with these fixed local channels:

    E(rho)=J rho J^*,
    D(sigma)=J^* sigma J +Tr[(I-JJ^*)sigma] tau,

where tau is any fixed old-input-space density operator. On the output, D
acts on the postmeasurement quantum system and leaves the setting flag
untouched. Both E and D are CPTP. Hence every enlarged CPTP operation is sent
to an old CPTP operation, and pulling the process back by E,D yields a valid
enlarged process W_tilde. On the chosen grid instruments the leakage term is
zero and the probabilities are reproduced exactly.

Both enlarged local instruments now factor as the fixed grid instrument
tensor the identity channel on the multiplicity register. Plug those identity
channels into W_tilde. The resulting W_L is positive: in Choi form it is a
partial expectation of W_tilde against the identity-channel Choi vectors.
It is normalized because every new local CPTP map tensor id_r is CPTP in the
enlarged ports. Thus W_L is a valid process on input dimension 2K and output
dimension 4K at each party.

The grid-angle register remains. Cross-angle coherences are untouched.
Only the multiplicity register, on which BOTH instruments act identically,
is absorbed into the process. Unequal and zero multiplicities are handled
by the CPTP extension, not by assuming a rectangular original Hilbert space.

Every rounded strategy therefore has score at most g_L. Averaging and (5)
prove (1). Conversely the canonical grid strategy is admissible, proving (2).

## 6. Explicit finite SDP and effective interpretation

In the port order A_I,A_O,B_I,B_O, let M^L,N^L be the fixed transposed Choi
operators just defined, and

    G_L=(1/4)sum_(x,y) M^L_(y|x) tensor N^L_(x|y).

The SDP is

    maximize Tr(W G_L)
    subject to W>=0, Tr W=(4K)^2,
       _BIBO W=_AO BIBO W,
       _AIAO W=_AIAO BO W,
       W=_AO W+_BO W-_AOBO W.

Its matrix dimension is 64K^4. Pinching the two output setting flags preserves
both validity and the objective; this gives four PSD blocks of size 16K^4.
The instrument coefficients are algebraic numbers at the chosen roots of
unity. The affine space has a strictly positive normalized white-noise
process, so the usual finite SDP dual has no missing Slater premise.

For target additive error epsilon, choosing L>=sqrt(C/epsilon) bounds every
input port by 2(L+1) and every output port by 4(L+1). This is an approximation
cutoff, not an exact finite-dimensional attainment theorem. The SDP can be
very large; existence of the effective reduction does not make its execution
cheap. It does, however, replace an unproved dimension cutoff by an explicit
error-controlled statement.

## 7. What remains open

Neither the limit of this SDP family nor a matching exact GYNI strategy has
been evaluated analytically here. A small grid value by itself is a LOWER
bound; only its certified dual upper value plus C/L^2 is an unrestricted
upper bound. The fixed-grid SDP is exact for its named canonical instruments,
whereas (2) is the additional theorem that controls the missing dimensions.

The labelled-projective modelling reduction is an external premise. The argument above is analytical; finite numerical examples do not establish its uniform quantifiers or publication priority.

## Exact full-grid dual certificate

Let P0 be the trace-zero full-process orthogonal projector, S an exact PSD Gram, Gtilde the rational objective and delta>=||P0(Gtilde+S)||. Then

    Y=Gtilde+S-P0(Gtilde+S)+delta I

lies in ker P0 and dominates Gtilde. At local quantum input dimension d, normalized white noise is I/d^2 and process trace is 4d^2. The integer implementation's replacement coefficients have denominator 4d^4, use Python integers, and include all phase-charge sectors. Pinching phase symmetries retains coherent |j,j> labels in the zero sector; it does not justify replacing the complete PSD process by a clique sum. The reduced-cone version of this certificate is owned by the fixed-support separation proof.
