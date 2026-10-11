import ICO.MHSymmetric

/-! Exact covariance of symmetric creation maps, in occupation coordinates
and in the left query/record coupling used by Ma–Huang. -/

namespace ICO.MHCreationCovariance

open QIT ICO.MHSymmetric
open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section
set_option maxHeartbeats 1000000

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem occupationEmbedding_adjoint_projection (n : ℕ) :
    (occupationEmbedding (a := a) n).conjTranspose * symmetricProjectionMatrix n =
      (occupationEmbedding (a := a) n).conjTranspose := by
  have h := congrArg Matrix.conjTranspose (symmetricProjection_occupationEmbedding (a := a) n)
  simpa only [Matrix.conjTranspose_mul, symmetricProjectionMatrix_conjTranspose] using h

theorem occupationRotation_left_intertwine (U : Matrix.unitaryGroup a ℂ) (n : ℕ) :
    occupationRotation U n * (occupationEmbedding (a := a) n).conjTranspose =
      (occupationEmbedding (a := a) n).conjTranspose *
        (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) := by
  rw [occupationRotation, Matrix.mul_assoc, Matrix.mul_assoc, occupationEmbedding_projection,
    unitaryTensorPowerMatrix_mul_symmetricProjectionMatrix, ← Matrix.mul_assoc,
    occupationEmbedding_adjoint_projection]

def creationOccupation (n : ℕ) (v : a → ℂ) :
    Matrix (TensorPowerProfile a (n + 1)) (TensorPowerProfile a n) ℂ :=
  (occupationEmbedding (a := a) (n + 1)).conjTranspose * creationWord n v * occupationEmbedding (a := a) n

theorem creationOccupation_covariance (U : Matrix.unitaryGroup a ℂ) (n : ℕ) (v : a → ℂ) :
    occupationRotation U (n + 1) * creationOccupation n v =
      creationOccupation n ((U : CMatrix a) *ᵥ v) * occupationRotation U n := by
  unfold creationOccupation
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, occupationRotation_left_intertwine,
    Matrix.mul_assoc (occupationEmbedding (a := a) (n + 1)).conjTranspose
      (unitaryTensorPowerMatrix U (n + 1) : CMatrix (TensorPower a (n + 1)))
      (creationWord n v), creationWord_covariance]
  simp only [Matrix.mul_assoc]
  rw [occupationRotation_intertwine]

def basisVector (z : a) : a → ℂ := fun x => if x = z then 1 else 0

theorem mulVec_basisVector (A : CMatrix a) (z : a) :
    A *ᵥ basisVector z = fun x => A x z := by
  funext x
  simp [Matrix.mulVec, dotProduct, basisVector]

theorem prepend_expansion (n : ℕ) (v : a → ℂ) :
    prepend n v = ∑ z, v z • prepend n (basisVector z) := by
  ext o i
  simp [prepend, basisVector, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    ← Finset.sum_mul]

theorem creationWord_expansion (n : ℕ) (v : a → ℂ) :
    creationWord n v = ∑ z, v z • creationWord n (basisVector z) := by
  rw [creationWord, prepend_expansion, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro z _
  simp only [creationWord, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1
  exact mul_comm _ _

theorem creationWord_basis_covariance (U : Matrix.unitaryGroup a ℂ) (n : ℕ) (z : a) :
    (unitaryTensorPowerMatrix U (n + 1) : CMatrix (TensorPower a (n + 1))) *
      creationWord n (basisVector z) =
        ∑ w, (U : CMatrix a) w z •
          (creationWord n (basisVector w) * (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n))) := by
  rw [creationWord_covariance, mulVec_basisVector, creationWord_expansion, Matrix.sum_mul]
  simp only [Matrix.smul_mul]

variable {α : Type*} [Fintype α] [DecidableEq α]

def leftEdgeUnitary (C D : Matrix.unitaryGroup α ℂ) : Matrix.unitaryGroup (α × α) ℂ :=
  ⟨Matrix.kronecker (C : CMatrix α) (D : CMatrix α).transpose,
    Matrix.kronecker_mem_unitary C.property (Matrix.transpose_mem_unitaryGroup_iff.mpr D.property)⟩

theorem leftEdgeUnitary_apply (C D : Matrix.unitaryGroup α ℂ) (x y u v : α) :
    (leftEdgeUnitary C D : CMatrix (α × α)) (x, y) (u, v) =
      (C : CMatrix α) x u * (D : CMatrix α) v y := rfl

/-- The left query/record creation operator before the common `1/sqrt d`
normalization. This is the exact symmetric-tensor version of `E^L`. -/
def leftCreator (n : ℕ) :
    Matrix (α × TensorPower (α × α) (n + 1)) (α × TensorPower (α × α) n) ℂ :=
  fun o i => creationWord n (basisVector (i.1, o.1)) o.2 i.2

theorem leftCreator_left_entry (n : ℕ) (D : CMatrix α)
    (o : α × TensorPower (α × α) (n + 1)) (i : α × TensorPower (α × α) n) :
    (Matrix.kronecker D (1 : CMatrix (TensorPower (α × α) (n + 1))) * leftCreator (α := α) n) o i =
      ∑ y : α, D o.1 y * creationWord n (basisVector (i.1, y)) o.2 i.2 := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, leftCreator]

theorem leftCreator_right_entry (n : ℕ)
    (Q : CMatrix (TensorPower (α × α) (n + 1)))
    (o : α × TensorPower (α × α) (n + 1)) (i : α × TensorPower (α × α) n) :
    (Matrix.kronecker (1 : CMatrix α) Q * leftCreator (α := α) n) o i =
      (Q * creationWord n (basisVector (i.1, o.1))) o.2 i.2 := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, leftCreator]

/-- Exact `E^L` covariance on each fixed-length symmetric tensor sector.
The untouched right-record rotation can be tensored onto both sides. -/
theorem leftCreator_covariance (C D : Matrix.unitaryGroup α ℂ) (n : ℕ) :
    Matrix.kronecker (D : CMatrix α) (1 : CMatrix (TensorPower (α × α) (n + 1))) *
      leftCreator (α := α) n * Matrix.kronecker (C : CMatrix α)
        (unitaryTensorPowerMatrix (leftEdgeUnitary C D) n : CMatrix (TensorPower (α × α) n)) =
    Matrix.kronecker (1 : CMatrix α)
      (unitaryTensorPowerMatrix (leftEdgeUnitary C D) (n + 1) :
        CMatrix (TensorPower (α × α) (n + 1))) * leftCreator (α := α) n := by
  ext o i
  rw [leftCreator_right_entry, Matrix.mul_apply]
  simp only [Fintype.sum_prod_type]
  simp only [leftCreator_left_entry]
  simp only [
    Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.sum_mul]
  have h := congrFun (congrFun
    (creationWord_basis_covariance (leftEdgeUnitary C D) n (i.1, o.1)) o.2) i.2
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type, leftEdgeUnitary_apply] at h
  rw [h]
  simp only [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro w _
  ring

end
end ICO.MHCreationCovariance


