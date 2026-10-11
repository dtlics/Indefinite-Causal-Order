import ICO.MHRecordingChoiceOperators
import ICO.MHRotatedTrajectory

/-! Actual forward/inverse recording covariance with arbitrary entangled
memory, using the same before/after rotations as the physical trajectory. -/
namespace ICO.MHChoiceMemoryCovariance
open QIT ICO.MHRecordingChoiceOperators ICO.MHRotatedTrajectory ICO.MHFockTrajectory
  ICO.MHFockKnownOperation ICO.MHInverseCovariance ICO.MHWRestricted
  ICO.MHBoundedRecording ICO.MHFockRotation
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 512
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem choice_restricted_covariance (C D : Matrix.unitaryGroup α ℂ)
    {q T : ℕ} (hq : q+1≤T) (hqd : q<Fintype.card α) (inverse : Bool) :
    ‖(fockQ C D T : CMatrix (InputCutoff (α := α) T))*choiceRestrictedV hq inverse-
      (fockQuery (after C D inverse) T : CMatrix (InputCutoff (α := α) T))*choiceRestrictedV hq inverse*
      (fockQuery (before C D inverse) T : CMatrix (InputCutoff (α := α) T))*
      (fockQ C D T : CMatrix (InputCutoff (α := α) T))‖≤
      16*Real.sqrt ((2*(q:ℝ)*(q+1))/Fintype.card α) := by
  cases inverse
  · exact restrictedV_covariance C D hq hqd
  · exact inverse_restricted_covariance C D hq hqd

theorem tensor_identity_covariance {H μ : Type*} [Fintype H] [DecidableEq H]
    [Fintype μ] [DecidableEq μ] (Q V D C : CMatrix H) :
    Matrix.kronecker Q (1 : CMatrix μ)*Matrix.kronecker V (1 : CMatrix μ)-
      Matrix.kronecker D (1 : CMatrix μ)*Matrix.kronecker V (1 : CMatrix μ)*
      Matrix.kronecker C (1 : CMatrix μ)*Matrix.kronecker Q (1 : CMatrix μ)=
      Matrix.kronecker (Q*V-D*V*C*Q) (1 : CMatrix μ) := by
  simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.mul_one]
  ext o i
  simp only [Matrix.kroneckerMap_apply,Matrix.sub_apply,sub_mul]

theorem choice_memory_covariance (C D : Matrix.unitaryGroup α ℂ)
    {q T : ℕ} (hq : q+1≤T) (hqd : q<Fintype.card α) (inverse : Bool)
    (μ : Type*) [Fintype μ] [DecidableEq μ] :
    ‖Matrix.kronecker (fockQ C D T : CMatrix (InputCutoff (α := α) T)) (1 : CMatrix μ)*
        Matrix.kronecker (choiceRestrictedV hq inverse) (1 : CMatrix μ)-
      Matrix.kronecker (fockQuery (after C D inverse) T : CMatrix (InputCutoff (α := α) T)) (1 : CMatrix μ)*
        Matrix.kronecker (choiceRestrictedV hq inverse) (1 : CMatrix μ)*
      Matrix.kronecker (fockQuery (before C D inverse) T : CMatrix (InputCutoff (α := α) T)) (1 : CMatrix μ)*
      Matrix.kronecker (fockQ C D T : CMatrix (InputCutoff (α := α) T)) (1 : CMatrix μ)‖≤
      16*Real.sqrt ((2*(q:ℝ)*(q+1))/Fintype.card α) := by
  rw [tensor_identity_covariance]
  exact (tensor_identity_norm_le _).trans (choice_restricted_covariance C D hq hqd inverse)

#print axioms choice_memory_covariance
end
end ICO.MHChoiceMemoryCovariance
