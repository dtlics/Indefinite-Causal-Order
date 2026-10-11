import ICO.MHRotatedDecompressionDefect
import ICO.MHDecompressionInitial

/-! A complete physical query followed by its actual changing-memory
isometry has the same decompression defect as the recording query. -/
namespace ICO.MHDecompressionStep
open Matrix QIT ICO.MHDecompressionKnown ICO.MHDecompressionInitial ICO.MHRotatedDecompressionDefect
  ICO.MHRotatedTrajectory ICO.MHRectangularAction ICO.MHDecompressionDefect
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockKnownOperation ICO.MHWDomainProjection
  ICO.MHTernaryCompression
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
variable {A μ ν : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]

theorem physicalKnown_isometry (K : Matrix (A×ν) (A×μ) ℂ) (hK : K.conjTranspose*K=1) :
    (physicalKnown K).conjTranspose*physicalKnown K=1 := by
  simp only [physicalKnown,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,
    Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul,hK,Matrix.mul_one,Matrix.one_kronecker_one,Matrix.submatrix_one_equiv]

def physicalStep (K : Matrix (A×ν) (A×μ) ℂ) (C D : Matrix.unitaryGroup A ℂ) (inverse : Bool) :
    Matrix ((A×Environment A)×ν) ((A×Environment A)×μ) ℂ :=
  physicalKnown K*Matrix.kronecker (physicalRotated C D inverse : CMatrix (A×Environment A)) (1 : CMatrix μ)

def recordingStep {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : Matrix (A×ν) (A×μ) ℂ) (C D : Matrix.unitaryGroup A ℂ) (inverse : Bool) :
    Matrix (InputCutoff (α := A) T×ν) (InputCutoff (α := A) T×μ) ℂ :=
  known T K*Matrix.kronecker (rotatedW hT C D inverse) (1 : CMatrix μ)

theorem step_defect {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : Matrix (A×ν) (A×μ) ℂ) (hK : K.conjTranspose*K=1)
    (C D : Matrix.unitaryGroup A ℂ) (inverse : Bool)
    (x : EuclideanSpace ℂ (InputCutoff (α := A) T×μ))
    (hx : rectAct (Matrix.kronecker (bijProjection T) (1 : CMatrix μ)) x=x) (hn : ‖x‖≤1) :
    ‖rectAct (physicalStep K C D inverse) (rectAct (memoryD hT μ) x)-
      rectAct (memoryD hT ν) (rectAct (recordingStep hT K C D inverse) x)‖^2≤
      1-‖rectAct (recordingStep hT K C D inverse) x‖^2 := by
  have he : physicalStep K C D inverse*memoryD hT μ-memoryD hT ν*recordingStep hT K C D inverse=
      physicalKnown K*(Matrix.kronecker (physicalRotated C D inverse : CMatrix (A×Environment A)) (1 : CMatrix μ)*memoryD hT μ-
        memoryD hT μ*Matrix.kronecker (rotatedW hT C D inverse) (1 : CMatrix μ)) := by
    simp only [physicalStep,recordingStep,Matrix.mul_sub,Matrix.mul_assoc]
    have hh := memoryD_known hT K
    rw [← Matrix.mul_assoc (memoryD hT ν) (known T K),← hh,Matrix.mul_assoc]
  rw [← rectAct_mul,← rectAct_mul,← rectAct_matrix_sub,he,rectAct_mul,
    rectAct_norm _ (physicalKnown_isometry K hK),recordingStep,rectAct_mul,
    rectAct_norm _ (known_isometry T K hK),rectAct_matrix_sub,rectAct_mul,rectAct_mul]
  exact rotated_memory_defect hT C D inverse x hx hn

#print axioms step_defect
end
end ICO.MHDecompressionStep