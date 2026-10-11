import ICO.MHBoundedRecording
import ICO.MHCovarianceNorm

/-! Actual two-record sector covariance and its quantitative fresh-oracle
version. The basis is `((query,left occupation),right occupation)`. -/

namespace ICO.MHSectorCovariance

open QIT ICO.MHSymmetric ICO.MHCreationCovariance ICO.MHRightCovariance
  ICO.MHOccupationCovariance ICO.MHBadInsertion ICO.MHERecordingApprox
  ICO.MHBlockNorm ICO.MHCovarianceNorm ICO.RecordingProcess
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 1800000

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def tensorUnitary (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ) :
    Matrix.unitaryGroup (a × b) ℂ :=
  ⟨Matrix.kronecker (U : CMatrix a) (V : CMatrix b), Matrix.kronecker_mem_unitary U.property V.property⟩

theorem unitary_norm_le (U : Matrix.unitaryGroup a ℂ) : ‖(U : CMatrix a)‖ ≤ 1 :=
  isometry_matrix_norm_le _ (Matrix.mem_unitaryGroup_iff'.mp U.property)

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Sector (n r : ℕ) := Input (α := α) n × TensorPowerProfile (α × α) r

def sectorV (n r : ℕ) : Matrix (Sector (α := α) (n + 1) r) (Sector (α := α) n r) ℂ :=
  Matrix.blockDiagonal (fun q : TensorPowerProfile (α × α) r => fullInsertion (n := n) q)

def sectorE (n r : ℕ) : Matrix (Sector (α := α) (n + 1) r) (Sector (α := α) n r) ℂ :=
  Matrix.kronecker (symmetricInsertion (α := α) n) (1 : CMatrix (TensorPowerProfile (α × α) r))

theorem sectorE_block (n r : ℕ) : sectorE (α := α) n r =
    Matrix.blockDiagonal (fun _q : TensorPowerProfile (α × α) r => symmetricInsertion (α := α) n) := by
  ext ⟨o, q⟩ ⟨i, p⟩
  simp [sectorE, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.blockDiagonal_apply']

theorem sector_difference_norm_le (n r : ℕ) (hsize : n + r < Fintype.card α) :
    ‖sectorV (α := α) n r - sectorE (α := α) n r‖ ≤
      Real.sqrt ((2 * (n + r : ℝ) * (n + r + 1)) / Fintype.card α) := by
  rw [sectorV, sectorE_block, ← Matrix.blockDiagonal_sub]
  apply blockDiagonal_norm_le _ _ (by positivity)
  intro q
  exact insertion_difference_norm_le q hsize

def queryTurn (D : Matrix.unitaryGroup α ℂ) (n r : ℕ) : Matrix.unitaryGroup (Sector (α := α) n r) ℂ :=
  tensorUnitary (tensorUnitary D (1 : Matrix.unitaryGroup (TensorPowerProfile (α × α) n) ℂ))
    (1 : Matrix.unitaryGroup (TensorPowerProfile (α × α) r) ℂ)

def inputTurn (C D : Matrix.unitaryGroup α ℂ) (n r : ℕ) : Matrix.unitaryGroup (Sector (α := α) n r) ℂ :=
  tensorUnitary (tensorUnitary C (symmetricRotation (leftEdgeUnitary C D) n))
    (symmetricRotation (rightEdgeUnitary D⁻¹ C⁻¹) r)

def outputTurn (C D : Matrix.unitaryGroup α ℂ) (n r : ℕ) : Matrix.unitaryGroup (Sector (α := α) n r) ℂ :=
  tensorUnitary (tensorUnitary (1 : Matrix.unitaryGroup α ℂ) (symmetricRotation (leftEdgeUnitary C D) n))
    (symmetricRotation (rightEdgeUnitary D⁻¹ C⁻¹) r)

theorem normalized_left_covariance (C D : Matrix.unitaryGroup α ℂ) (n : ℕ) :
    Matrix.kronecker (D : CMatrix α) (1 : CMatrix (TensorPowerProfile (α × α) (n + 1))) *
      symmetricInsertion (α := α) n * Matrix.kronecker (C : CMatrix α)
        (occupationRotation (leftEdgeUnitary C D) n) =
    Matrix.kronecker (1 : CMatrix α) (occupationRotation (leftEdgeUnitary C D) (n + 1)) *
      symmetricInsertion (α := α) n := by
  have he : symmetricInsertion (α := α) n =
      (Real.sqrt (Fintype.card α) : ℂ)⁻¹ • occupationLeftCreator (α := α) n := rfl
  rw [he]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  exact congrArg (fun M => (Real.sqrt (Fintype.card α) : ℂ)⁻¹ • M)
    (occupationLeftCreator_covariance C D n)

theorem sectorE_covariance (C D : Matrix.unitaryGroup α ℂ) (n r : ℕ) :
    (queryTurn D (n + 1) r : CMatrix (Sector (α := α) (n + 1) r)) * sectorE (α := α) n r *
      (inputTurn C D n r : CMatrix (Sector (α := α) n r)) =
    (outputTurn C D (n + 1) r : CMatrix (Sector (α := α) (n + 1) r)) * sectorE (α := α) n r := by
  change Matrix.kronecker (Matrix.kronecker (D : CMatrix α) 1) 1 *
      Matrix.kronecker (symmetricInsertion (α := α) n) 1 *
      Matrix.kronecker (Matrix.kronecker (C : CMatrix α) (occupationRotation (leftEdgeUnitary C D) n))
        (occupationRotation (rightEdgeUnitary D⁻¹ C⁻¹) r) =
    Matrix.kronecker (Matrix.kronecker (1 : CMatrix α) (occupationRotation (leftEdgeUnitary C D) (n + 1)))
      (occupationRotation (rightEdgeUnitary D⁻¹ C⁻¹) r) *
      Matrix.kronecker (symmetricInsertion (α := α) n) 1
  simp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one]
  erw [normalized_left_covariance]
  rfl

/-- Approximate unitary covariance of the actual unrestricted fresh insertion
on both record registers, with the published factor two. -/
theorem sectorV_covariance_norm (C D : Matrix.unitaryGroup α ℂ) (n r : ℕ)
    (hsize : n + r < Fintype.card α) :
    ‖(queryTurn D (n + 1) r : CMatrix (Sector (α := α) (n + 1) r)) * sectorV (α := α) n r *
      (inputTurn C D n r : CMatrix (Sector (α := α) n r)) -
      (outputTurn C D (n + 1) r : CMatrix (Sector (α := α) (n + 1) r)) * sectorV (α := α) n r‖ ≤
      2 * Real.sqrt ((2 * (n + r : ℝ) * (n + r + 1)) / Fintype.card α) :=
  approximate_intertwine _ _ _ _ _ _ (sector_difference_norm_le n r hsize)
    (unitary_norm_le _) (unitary_norm_le _) (unitary_norm_le _) (sectorE_covariance C D n r)

end
end ICO.MHSectorCovariance

