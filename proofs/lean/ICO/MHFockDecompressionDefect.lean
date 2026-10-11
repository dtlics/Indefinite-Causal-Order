import ICO.MHFockDecompression
import ICO.MHDecompressionDefect
import ICO.MHWReachability

/-! Actual forward and inverse decompression defects with arbitrary entangled
spectator memory. The loss is the missing squared mass of the W query. -/
namespace ICO.MHFockDecompressionDefect
open Matrix QIT ICO.MHFockDecompression ICO.MHDecompressionDefect ICO.MHRectangularAction
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHWEmbedding ICO.MHWDomainProjection
  ICO.MHWReachability ICO.MHPurifiedOracle ICO.MHTernaryCompression
  ICO.MHFockLabels ICO.MHFockOracle ICO.MHWRecordSwap ICO.MHFockSwap
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
variable {A μ : Type*} [Fintype A] [DecidableEq A] [Fintype μ] [DecidableEq μ]
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem bij_recordW {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) :
    bijProjection T*recordW hT=recordW hT := by
  ext o i
  rw [bijProjection,Matrix.diagonal_mul]
  by_cases hz : recordW hT o i=0
  · rw [hz,mul_zero]
  · simp [recordW_output_bij hT o i hz]

theorem bij_recordW_inverse {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) :
    bijProjection T*(recordW hT).conjTranspose=(recordW hT).conjTranspose := by
  ext o i
  rw [bijProjection,Matrix.diagonal_mul]
  by_cases hz : (recordW hT).conjTranspose o i=0
  · rw [hz,mul_zero]
  · simp [recordW_inverse_output_bij hT o i hz]

def spectatorUnitary {E : Type*} [Fintype E] [DecidableEq E]
    (U : Matrix.unitaryGroup E ℂ) (μ : Type*) [Fintype μ] [DecidableEq μ] : Matrix.unitaryGroup (E×μ) ℂ :=
  ⟨Matrix.kronecker (U : CMatrix E) (1 : CMatrix μ),
    Matrix.kronecker_mem_unitary U.property (1 : Matrix.unitaryGroup μ ℂ).property⟩
theorem memory_defect (inverse : Bool) {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (x : EuclideanSpace ℂ (InputCutoff (α := A) T×μ))
    (hx : rectAct (Matrix.kronecker (bijProjection T) (1 : CMatrix μ)) x=x) (hn : ‖x‖≤1) :
    ‖rectAct (Matrix.kronecker (if inverse then queryMatrix.conjTranspose else queryMatrix) (1 : CMatrix μ))
      (rectAct (Matrix.kronecker (fockD hT) (1 : CMatrix μ)) x)-
      rectAct (Matrix.kronecker (fockD hT) (1 : CMatrix μ))
        (rectAct (Matrix.kronecker (if inverse then (recordW hT).conjTranspose else recordW hT) (1 : CMatrix μ)) x)‖^2 ≤
      1-‖rectAct (Matrix.kronecker (if inverse then (recordW hT).conjTranspose else recordW hT) (1 : CMatrix μ)) x‖^2 := by
  let U : Matrix.unitaryGroup (A×Environment A) ℂ := if inverse then queryUnitary⁻¹ else queryUnitary
  let W : CMatrix (InputCutoff (α := A) T) := if inverse then (recordW hT).conjTranspose else recordW hT
  have hU : (U : CMatrix (A×Environment A))=if inverse then queryMatrix.conjTranspose else queryMatrix := by
    cases inverse <;> rfl
  have hB : bijProjection T*W=W := by
    cases inverse
    · exact bij_recordW hT
    · exact bij_recordW_inverse hT
  have hP : bijProjection T*(W.conjTranspose*W)=W.conjTranspose*W := by
    cases inverse
    · exact bij_mul_recordGram hT
    · change bijProjection T*((recordW hT).conjTranspose.conjTranspose*(recordW hT).conjTranspose)=_
      rw [Matrix.conjTranspose_conjTranspose,← Matrix.mul_assoc,bij_recordW]
      simp [W]
  have hUW : (U : CMatrix (A×Environment A))*fockD hT*(W.conjTranspose*W)=fockD hT*W := by
    cases inverse
    · exact fockD_forward_domain hT
    · simpa only [U,W,Bool.true_eq,if_true,Matrix.UnitaryGroup.inv_val,Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose] using fockD_inverse_domain hT
  have hh := defect_norm_sq_le (spectatorUnitary U μ)
    (Matrix.kronecker (fockD hT) (1 : CMatrix μ))
    (Matrix.kronecker W (1 : CMatrix μ)) (Matrix.kronecker (bijProjection T) (1 : CMatrix μ))
    (by simp only [Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,← Matrix.mul_kronecker_mul,
      fockD_gram,Matrix.mul_one])
    (by simp only [Matrix.kronecker,← Matrix.mul_kronecker_mul,hB,Matrix.mul_one])
    (by simp only [Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,← Matrix.mul_kronecker_mul,
      hP,Matrix.mul_one])
    (by dsimp only [spectatorUnitary]
        simp only [Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,← Matrix.mul_kronecker_mul,
          hUW,Matrix.mul_one]) x hx hn
  simpa only [spectatorUnitary,hU,W] using hh

#print axioms memory_defect
end
end ICO.MHFockDecompressionDefect