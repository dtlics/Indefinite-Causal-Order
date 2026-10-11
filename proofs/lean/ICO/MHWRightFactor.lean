import ICO.MHWRightSector

/-! Exact normalized creation factorization in a full coherent length sector. -/
namespace ICO.MHWRightFactor
open QIT ICO.MHSymmetric ICO.MHWOccupation ICO.MHOccupationCovariance ICO.MHWRightSector
  ICO.MHFockNodup ICO.MHWRecordEntries ICO.RecordingCopyIdentity ICO.MHOccupationCounts
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1800000
variable {α : Type*} [Fintype α] [DecidableEq α]

def sectorBij (n r : ℕ) : CMatrix (RightSector (α := α) n r) :=
  Matrix.blockDiagonal (fun p : TensorPowerProfile (α×α) n => bijRightProjection p r)

def sectorCreator (n r : ℕ) : Matrix (RightSector (α := α) n (r+1)) (RightSector (α := α) n r) ℂ :=
  Matrix.blockDiagonal (fun _ : TensorPowerProfile (α×α) n => occupationRightCreator (α := α) r)

theorem sectorCreator_tensor (n r : ℕ) : sectorCreator (α := α) n r=
    Matrix.kronecker (occupationRightCreator (α := α) r)
      (1 : CMatrix (TensorPowerProfile (α×α) n)) := by
  ext o i
  simp only [sectorCreator,Matrix.blockDiagonal_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Matrix.one_apply,mul_ite,mul_one,mul_zero]

theorem rightSector_factor (n r : ℕ) :
    rightSectorW (α := α) n r=
      (((Real.sqrt ((Fintype.card α : ℝ)-n-r))⁻¹ : ℝ) : ℂ) •
        (sectorBij n (r+1)*sectorCreator (α := α) n r) := by
  simp only [rightSectorW,sectorBij,sectorCreator,← Matrix.blockDiagonal_mul]
  simp_rw [rightWOccupation_factor]
  ext o i
  simp only [Matrix.blockDiagonal_apply,Matrix.smul_apply,smul_eq_mul]
  split_ifs <;> simp

theorem rightSector_image_factor (n r : ℕ) (hsize : n+r≤Fintype.card α) :
    Matrix.blockDiagonal (fun p : TensorPowerProfile (α×α) n =>
        rightWOccupation (r := r) p*(rightWOccupation (r := r) p).conjTranspose)=
      (((((Fintype.card α : ℝ)-n-r)⁻¹ : ℝ) : ℂ) •
        (sectorBij n (r+1)*(sectorCreator (α := α) n r*(sectorCreator (α := α) n r).conjTranspose)*sectorBij n (r+1))) := by
  simp only [sectorBij,sectorCreator,Matrix.blockDiagonal_conjTranspose,← Matrix.blockDiagonal_mul]
  simp_rw [rightWOccupation_image _ hsize]
  ext o i
  simp only [Matrix.blockDiagonal_apply,Matrix.smul_apply,smul_eq_mul]
  split_ifs <;> simp

theorem actual_right_image_factor {n r T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (hi : n+r≤T) (ho : n+(r+1)≤T) (hsize : n+r<Fintype.card α) :
    (basisEmbedding (rightSectorEmbed (α := α) ho)).conjTranspose*
        (recordRightW hT*(recordRightW hT).conjTranspose)*basisEmbedding (rightSectorEmbed ho)=
      (((((Fintype.card α : ℝ)-n-r)⁻¹ : ℝ) : ℂ) •
        (sectorBij n (r+1)*(sectorCreator (α := α) n r*(sectorCreator (α := α) n r).conjTranspose)*sectorBij n (r+1))) := by
  rw [rightSector_image hT hi ho hsize,rightSector_image_factor n r hsize.le]

end
end ICO.MHWRightFactor
