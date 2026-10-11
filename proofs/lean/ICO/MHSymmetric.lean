import QIT.Symmetry.UnitaryTwirl
import ICO.RecordingPureCorrespondence

/-!
# Symmetric occupation registers for the Ma–Huang oracle

Occupation profiles include arbitrary repeated labels. The embedding below
uses QIT's normalized symmetric profile vectors, rather than identifying
multisets with sets. Tensor rotations preserve this entire symmetric space.
-/

namespace ICO.MHSymmetric

open QIT
open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section
set_option maxHeartbeats 1000000

variable {a : Type*} [Fintype a] [DecidableEq a]

def occupationEmbedding (n : ℕ) : Matrix (TensorPower a n) (TensorPowerProfile a n) ℂ :=
  fun w p => tensorPowerProfileUnitVector p w

theorem occupationEmbedding_gram (n : ℕ) :
    (occupationEmbedding (a := a) n).conjTranspose * occupationEmbedding (a := a) n = 1 := by
  ext p q
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    occupationEmbedding, Matrix.one_apply] using tensorPowerProfileUnitVector_inner p q

theorem occupationEmbedding_projection (n : ℕ) :
    occupationEmbedding (a := a) n * (occupationEmbedding (a := a) n).conjTranspose =
      symmetricProjectionMatrix n := by
  rw [symmetricProjectionMatrix_eq_sum_rankOne_profileUnitVector]
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, occupationEmbedding,
    Matrix.sum_apply, rankOneMatrix_apply]

theorem symmetricProjection_occupationEmbedding (n : ℕ) :
    symmetricProjectionMatrix n * occupationEmbedding (a := a) n = occupationEmbedding (a := a) n := by
  rw [← occupationEmbedding_projection, Matrix.mul_assoc, occupationEmbedding_gram,
    Matrix.mul_one]

def occupationRotation (U : Matrix.unitaryGroup a ℂ) (n : ℕ) :
    CMatrix (TensorPowerProfile a n) :=
  (occupationEmbedding (a := a) n).conjTranspose *
    (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) * occupationEmbedding (a := a) n

theorem occupationRotation_intertwine (U : Matrix.unitaryGroup a ℂ) (n : ℕ) :
    (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) * occupationEmbedding (a := a) n =
      occupationEmbedding (a := a) n * occupationRotation U n := by
  rw [occupationRotation, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    occupationEmbedding_projection, symmetricProjectionMatrix_mul_unitaryTensorPowerMatrix,
    Matrix.mul_assoc, symmetricProjection_occupationEmbedding]

theorem occupationRotation_gram (U : Matrix.unitaryGroup a ℂ) (n : ℕ) :
    (occupationRotation U n).conjTranspose * occupationRotation U n = 1 := by
  have hU : (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)).conjTranspose *
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) = 1 :=
    unitaryTensorPowerMatrix_star_mul_self U n
  have hGram :
      ((unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) * occupationEmbedding (a := a) n).conjTranspose *
      ((unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) * occupationEmbedding (a := a) n) =
        (1 : CMatrix (TensorPowerProfile a n)) := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)).conjTranspose,
      hU, Matrix.one_mul, occupationEmbedding_gram]
  calc
    _ = (occupationRotation U n).conjTranspose *
        ((occupationEmbedding (a := a) n).conjTranspose * occupationEmbedding (a := a) n) *
        occupationRotation U n := by rw [occupationEmbedding_gram, Matrix.mul_one]
    _ = (occupationEmbedding (a := a) n * occupationRotation U n).conjTranspose *
        (occupationEmbedding (a := a) n * occupationRotation U n) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [← occupationRotation_intertwine]; exact hGram

def symmetricRotation (U : Matrix.unitaryGroup a ℂ) (n : ℕ) :
    Matrix.unitaryGroup (TensorPowerProfile a n) ℂ :=
  ⟨occupationRotation U n, Matrix.mem_unitaryGroup_iff'.mpr (occupationRotation_gram U n)⟩

/-- Prepend a single-particle amplitude to a tensor word. -/
def prepend (n : ℕ) (v : a → ℂ) : Matrix (TensorPower a (n + 1)) (TensorPower a n) ℂ :=
  fun o i => v o.1 * if o.2 = i then 1 else 0

theorem tensor_prepend (U : Matrix.unitaryGroup a ℂ) (n : ℕ) (v : a → ℂ) :
    (unitaryTensorPowerMatrix U (n + 1) : CMatrix (TensorPower a (n + 1))) * prepend n v =
      prepend n ((U : CMatrix a) *ᵥ v) * (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) := by
  ext o i
  rcases o with ⟨x, w⟩
  change (∑ s : a × TensorPower a n, (U : CMatrix a) x s.1 *
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) w s.2 *
        (v s.1 * if s.2 = i then 1 else 0)) =
    ∑ t : TensorPower a n, ((∑ z, (U : CMatrix a) x z * v z) *
      if w = t then 1 else 0) *
        (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) t i
  simp [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm]

/-- The bosonic creation map in the symmetric tensor-word representation.
The occupation-basis coefficient will be `sqrt(count + 1)`. -/
def creationWord (n : ℕ) (v : a → ℂ) :
    Matrix (TensorPower a (n + 1)) (TensorPower a n) ℂ :=
  (Real.sqrt (n + 1) : ℂ) •
    (symmetricProjectionMatrix (n + 1) * prepend n v * symmetricProjectionMatrix n)

theorem creationWord_covariance (U : Matrix.unitaryGroup a ℂ) (n : ℕ) (v : a → ℂ) :
    (unitaryTensorPowerMatrix U (n + 1) : CMatrix (TensorPower a (n + 1))) * creationWord n v =
      creationWord n ((U : CMatrix a) *ᵥ v) *
        (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) := by
  simp only [creationWord, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    unitaryTensorPowerMatrix_mul_symmetricProjectionMatrix]
  rw [Matrix.mul_assoc _ (unitaryTensorPowerMatrix U (n + 1) : CMatrix (TensorPower a (n + 1))),
    tensor_prepend]
  simp only [Matrix.mul_assoc]
  rw [unitaryTensorPowerMatrix_mul_symmetricProjectionMatrix]

end
end ICO.MHSymmetric


