import ICO.CircuitComb
import ICO.ReverseIntegral

/-! # Plugging two oracle matrices into an open circuit

The contraction matrix inserts the two actual oracle matrices into six open
wires. The normalized Choi overlap with the reverse product is exactly the
rank-one test used by the Haar reverse bound.
-/

open scoped ComplexOrder MatrixOrder
open Matrix QIT MeasureTheory ICO.CausalReverse ICO.ReverseIntegral ICO.ReverseFidelity

namespace ICO.CircuitOutput

set_option maxHeartbeats 1500000
noncomputable section

universe u
variable {A : Type u} [Fintype A] [DecidableEq A]

/-- Insert `U : a → b` and `V : c → e`, leaving input `P` and output `f`. -/
def oraclePlug (U V : CMatrix A) : Matrix (A × A) (SixWires A) ℂ :=
  fun pf i => if pf.1 = i.1.1.1.1.1 ∧ pf.2 = i.2 then
    U i.1.1.1.2 i.1.1.2 * V i.1.2 i.1.1.1.1.2 else 0

def targetVector (T : CMatrix A) : A × A → ℂ := fun pf => T pf.2 pf.1

/-- The unnormalized output Choi matrix of the plugged network. -/
def outputChoi (C : CMatrix (SixWires A)) (U V : CMatrix A) : CMatrix (A × A) :=
  oraclePlug U V * C * (oraclePlug U V).conjTranspose

theorem outputChoi_pos {C : CMatrix (SixWires A)} (hC : C.PosSemidef)
    (U V : CMatrix A) : (outputChoi C U V).PosSemidef :=
  hC.mul_mul_conjTranspose_same (oraclePlug U V)

/-- Normalizing both the circuit Choi state and unitary target gives `d⁻²`. -/
def outputOverlap (C : CMatrix (SixWires A)) (U V T : CMatrix A) : ℝ :=
  ((Fintype.card A : ℝ) ^ 2)⁻¹ *
    tracePair (outputChoi C U V) (rankOneMatrix (targetVector T))

theorem tracePair_sandwich_rankOne {I J : Type u}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (L : Matrix I J ℂ) (C : CMatrix J) (v : I → ℂ) :
    tracePair (L * C * L.conjTranspose) (rankOneMatrix v) =
      tracePair C (rankOneMatrix (L.conjTranspose.mulVec v)) := by
  rw [rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
  simp only [Matrix.conjTranspose_conjTranspose, tracePair]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem oraclePlug_adjoint_target (U V : Matrix.unitaryGroup A ℂ) :
    (oraclePlug (U : CMatrix A) (V : CMatrix A)).conjTranspose.mulVec
      (targetVector ((U : CMatrix A) * (V : CMatrix A))) = reverseAmplitude U V := by
  ext i
  simp [oraclePlug, targetVector, reverseAmplitude, Matrix.mulVec,
    dotProduct, Matrix.conjTranspose_apply, Fintype.sum_prod_type, apply_ite, ite_and,
    mul_comm, mul_left_comm, mul_assoc]

/-- The operational overlap is the rank-one reverse test, with all Choi
normalization factors explicit. -/
theorem outputOverlap_eq_reverse_score (C : CMatrix (SixWires A))
    (U V : Matrix.unitaryGroup A ℂ) :
    outputOverlap C (U : CMatrix A) (V : CMatrix A)
      ((U : CMatrix A) * (V : CMatrix A)) =
      tracePair C (rankOneMatrix (reverseVector U V)) := by
  unfold outputOverlap outputChoi
  rw [tracePair_sandwich_rankOne, oraclePlug_adjoint_target]
  unfold reverseVector
  rw [rankOne_real_scale, tracePair_real_smul_right]
  simp only [inv_pow]

/-- The actual double-Haar output overlap of a causal comb obeys the reverse
bound. This theorem still takes a causal comb; circuit realizability is a
separate, explicit theorem in `CircuitComb`. -/
theorem causal_outputOverlap_bound [Nontrivial A]
    (C : CMatrix (SixWires A)) (C₂ : CMatrix (FirstFourWires A))
    (hC : C.PosSemidef) (hC₂ : C₂.PosSemidef)
    (hcausal : partialTraceB C = Matrix.kronecker C₂ (1 : CMatrix A)) :
    (∫ U : Matrix.unitaryGroup A ℂ,
      ∫ V : Matrix.unitaryGroup A ℂ,
        outputOverlap C (U : CMatrix A) (V : CMatrix A)
          ((U : CMatrix A) * (V : CMatrix A))
        ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) ≤
      (C.trace.re / (Fintype.card A : ℝ) ^ 3) *
        ((Fintype.card A : ℝ)⁻¹ +
          (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1)) ^ 2 := by
  simp_rw [outputOverlap_eq_reverse_score]
  exact causal_reverse_score_bound C C₂ hC hC₂ hcausal

/-- A final outcome inherits the reverse-overlap bound from its completed
parent, without being required to satisfy a causal normalization equation. -/
theorem outcome_outputOverlap_bound [Nontrivial A]
    (Cout C : CMatrix (SixWires A)) (C₂ : CMatrix (FirstFourWires A))
    (hparent : Cout ≤ C) (hC : C.PosSemidef) (hC₂ : C₂.PosSemidef)
    (hcausal : partialTraceB C = Matrix.kronecker C₂ (1 : CMatrix A)) :
    (∫ U : Matrix.unitaryGroup A ℂ, ∫ V : Matrix.unitaryGroup A ℂ,
      outputOverlap Cout (U : CMatrix A) (V : CMatrix A)
        ((U : CMatrix A) * (V : CMatrix A))
      ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) ≤
      (C.trace.re / (Fintype.card A : ℝ) ^ 3) *
        ((Fintype.card A : ℝ)⁻¹ +
          (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1)) ^ 2 := by
  simp_rw [outputOverlap_eq_reverse_score]
  rw [← tracePair_reverseTest_eq_average]
  exact outcome_reverse_test_bound Cout C C₂ hparent hC hC₂ hcausal

end
end ICO.CircuitOutput


