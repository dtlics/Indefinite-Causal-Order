<a id="p2-r26"></a>

# Exact strict improvement after adding one endpoint angle

This is a scoped physical separation, not the exact unrestricted
GYNI value and not a universal dimension lower bound.

Let S5 be the five canonical Jordan angles with the rational tangent pairs in
`Radau5_fixed_upper165.json`. Let S6 be the SAME five pairs followed by[1,0],
which adds theta=pi/2. Let g(S) be the optimum over valid physical processes
for those fixed labelled projective instruments.

Two exact rational certificates prove

    g(S5) <= 0.622165000000592
           <0.62216529991079 <= g(S6) <= omega_GYNI.

The displayed endpoints are outward-rounded from exact fractions, and the exact strict difference
between the certified new lower and old upper is approximately
2.999101998040136e-7. `endpoint_strict_support_improvement.json` checks equality
of the original five pairs, checks the added endpoint, and compares the two
fractions without floating arithmetic.

Consequently a universal NS completion extending this five-angle completion
at its certified scale cannot exist, regardless of polynomial degree or
whether an infinite kernel is allowed. Such a completion would contradict the
six-angle physical process. This rules out the SPECIFIC same-scale matching
candidate investigated here. It says nothing about the best value over other
five-angle sets, a finite cutoff, or unrestricted nonattainment.

<a id="p2-r07"></a>

## Lower certificate

`endpoint_lower1653.json` and `endpoint_lower1653_data.json.gz` reconstruct a positive reduced
process with trace16 and all audited reduced affine identities. Its exact
rational CP-adjoint lift includes EVERY physical output-charge sector. Local
input/output dimensions are12/24. The projectors are exactly rational.

Replay:

    OPENBLAS_NUM_THREADS=1 python \
      ../physical-process/certify_reduced_process.py \
      --verify endpoint_lower1653.json endpoint_lower1653_data.json.gz

This is the existing reduced-process verifier and existing CP-lift theorem.
The new output-eigenvalue discovery shortcut is not a certificate dependency.

## Upper certificate for the five fixed angles

Let P0 be the exact orthogonal projector onto trace-zero reduced processes,
K=5, and let G be the exact rational winning Choi operator at S5. The saved
integer factors define L L*. Starting with H=G+L L*, the verifier computes

    E=P0(H), delta>=max_flag ||E_flag||,
    Y=H-E+delta I.

Then P0(Y)=0 and Y-G=L L*-E+delta I>=0. Every normalized reduced process Z has
trace16 and white-noise point Z0=I/(4K^2), so

    <G,Z> <= <Y,Z> = <Y,Z0> = Tr(Y)/(4K^2).

All identities and the PSD repair are reconstructed with integers/rationals.
The Frobenius and absolute-row-sum bounds certify delta. No solver or floating
spectrum is trusted by replay. The upper certificate's total repair cost is
approximately5.90e-13.

Replay:

    OPENBLAS_NUM_THREADS=1 python certify_fixed_angle_dual.py \
      --verify Radau5_fixed_upper165_factors.json.gz

The mathematical dependency is only the already-audited reduced physical cone
and its CP lift. In particular, this is NOT an unrestricted upper certificate;
its G and its process ports are those of S5.

## Status of the matching attempt

The numerical finite-grid completion's free NS defect was verified to lie in
the finite-support vanishing ideal. That algebraic divisibility was necessary
for the proposed extension but did not ensure positive extendibility. The
subsequent physical endpoint separation establishes a genuine obstruction to
same-scale extension of this candidate. The targeted finite-level iteration's
nonzero residual was not used as an infeasibility proof.

The [reproduction guide](../../REPRODUCIBILITY.md) gives the maintained exact replay commands.
