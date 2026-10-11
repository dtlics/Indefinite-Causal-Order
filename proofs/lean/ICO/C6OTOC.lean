import ICO.C6OTOCClock
import ICO.C6SwitchTest

/-! Exact private clock-phase averaged four-point OTOC, including the actual
control measurement probability of the quantum switch. -/
namespace ICO.C6OTOC
open Matrix QIT ICO.SwitchObservable ICO.SwitchExperiment ICO.C6OTOCClock
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
set_option Elab.async false
variable {d : ℕ} [NeZero d]

theorem four_trace_cycle (B A : CMatrix (ZMod d)) :
    (B*A*Bᴴ*Aᴴ).trace = (A*Bᴴ*Aᴴ*B).trace := by
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm B (A*Bᴴ*Aᴴ)

theorem sum_four_trace_clock (U B : CMatrix (ZMod d)) :
    (∑ k : ZMod d, (B*rotatedClock U k*Bᴴ*(rotatedClock U k)ᴴ).trace) =
      (d : ℂ) * ∑ i : ZMod d,
        (B*basisProjection U i*Bᴴ*(basisProjection U i)ᴴ).trace := by
  simp only [four_trace_cycle]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, sum_rotatedClock_twirl]
  simp [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, MatrixMap.ofKraus,
    Matrix.sum_mul, Matrix.trace_sum]

theorem raw_clock_interference (U V : CMatrix (ZMod d)) :
    rawInterference (rotatedClock U) (rotatedClock V) =
      (d : ℂ)^2 * rawInterference (basisProjection U) (basisProjection V) := by
  unfold rawInterference
  rw [Finset.sum_comm]
  simp only [sum_four_trace_clock, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hh (i : ZMod d) :
      (∑ l : ZMod d, (rotatedClock V l*basisProjection U i*
        (rotatedClock V l)ᴴ*(basisProjection U i)ᴴ).trace) =
        (d : ℂ) * ∑ j : ZMod d,
          (basisProjection V j*basisProjection U i*
            (basisProjection V j)ᴴ*(basisProjection U i)ᴴ).trace := by
    rw [← Matrix.trace_sum, ← Matrix.sum_mul, sum_rotatedClock_twirl]
    simp [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      MatrixMap.ofKraus, Matrix.sum_mul, Matrix.trace_sum]
  simp only [hh, ← Finset.mul_sum]
  ring

/-- Average over two independent, uniformly chosen private clock exponents.
The additional factor d normalizes the trace to infinite temperature. -/
def phaseOTOC (U V : CMatrix (ZMod d)) : ℝ :=
  (∑ k : ZMod d, ∑ l : ZMod d,
    (rotatedClock V l*rotatedClock U k*(rotatedClock V l)ᴴ*
      (rotatedClock U k)ᴴ).trace.re) / ((d : ℝ)^2 * d)

theorem phaseOTOC_eq_interference (U V : CMatrix (ZMod d)) :
    phaseOTOC U V = interference (basisProjection U) (basisProjection V) := by
  have h := congrArg Complex.re (raw_clock_interference U V)
  simp only [rawInterference, Complex.re_sum, Complex.mul_re, Complex.mul_im,
    pow_two, Complex.natCast_re, Complex.natCast_im, zero_mul, mul_zero, sub_zero, add_zero] at h
  unfold phaseOTOC interference rawInterference
  rw [h]
  simp only [ZMod.card, Complex.re_sum]
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  field_simp

theorem phaseOTOC_born (U V : Matrix.unitaryGroup (ZMod d) ℂ) :
    (ICO.C6SwitchTest.plusProbability U V : ℝ) =
      (1+phaseOTOC (U : CMatrix (ZMod d)) (V : CMatrix (ZMod d)))/2 := by
  rw [phaseOTOC_eq_interference]
  exact switch_plus_probability _ _ _ _

#print axioms phaseOTOC_eq_interference
#print axioms phaseOTOC_born
end
end ICO.C6OTOC
