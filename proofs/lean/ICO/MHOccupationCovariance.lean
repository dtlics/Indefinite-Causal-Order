import ICO.MHCreationCoefficients
import ICO.MHRightCovariance

/-! Exact query/record covariance in the actual multiset occupation basis. -/

namespace ICO.MHOccupationCovariance

open QIT ICO.MHSymmetric ICO.MHCreationCovariance ICO.MHRightCovariance
open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section
set_option maxHeartbeats 1500000

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem creationOccupation_expansion (n : ℕ) (v : a → ℂ) :
    creationOccupation n v = ∑ z, v z • creationOccupation n (basisVector z) := by
  unfold creationOccupation
  rw [creationWord_expansion, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem creationOccupation_basis_covariance (U : Matrix.unitaryGroup a ℂ) (n : ℕ) (z : a) :
    occupationRotation U (n + 1) * creationOccupation n (basisVector z) =
      ∑ w, (U : CMatrix a) w z • (creationOccupation n (basisVector w) * occupationRotation U n) := by
  rw [creationOccupation_covariance, mulVec_basisVector, creationOccupation_expansion, Matrix.sum_mul]
  simp only [Matrix.smul_mul]

variable {α : Type*} [Fintype α] [DecidableEq α]
def occupationLeftCreator (n : ℕ) :
    Matrix (α × TensorPowerProfile (α × α) (n + 1)) (α × TensorPowerProfile (α × α) n) ℂ :=
  fun o i => creationOccupation n (basisVector (i.1, o.1)) o.2 i.2

theorem occupationLeftCreator_left_entry (n : ℕ) (D : CMatrix α)
    (o : α × TensorPowerProfile (α × α) (n + 1)) (i : α × TensorPowerProfile (α × α) n) :
    (Matrix.kronecker D (1 : CMatrix (TensorPowerProfile (α × α) (n + 1))) * occupationLeftCreator (α := α) n) o i =
      ∑ y : α, D o.1 y * creationOccupation n (basisVector (i.1, y)) o.2 i.2 := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, occupationLeftCreator]

theorem occupationLeftCreator_right_entry (n : ℕ)
    (Q : CMatrix (TensorPowerProfile (α × α) (n + 1)))
    (o : α × TensorPowerProfile (α × α) (n + 1)) (i : α × TensorPowerProfile (α × α) n) :
    (Matrix.kronecker (1 : CMatrix α) Q * occupationLeftCreator (α := α) n) o i =
      (Q * creationOccupation n (basisVector (i.1, o.1))) o.2 i.2 := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, occupationLeftCreator]

/-- Exact `E^L` covariance on each fixed-length symmetric tensor sector.
The untouched right-record rotation can be tensored onto both sides. -/
theorem occupationLeftCreator_covariance (C D : Matrix.unitaryGroup α ℂ) (n : ℕ) :
    Matrix.kronecker (D : CMatrix α) (1 : CMatrix (TensorPowerProfile (α × α) (n + 1))) *
      occupationLeftCreator (α := α) n * Matrix.kronecker (C : CMatrix α)
        (occupationRotation (leftEdgeUnitary C D) n : CMatrix (TensorPowerProfile (α × α) n)) =
    Matrix.kronecker (1 : CMatrix α)
      (occupationRotation (leftEdgeUnitary C D) (n + 1) :
        CMatrix (TensorPowerProfile (α × α) (n + 1))) * occupationLeftCreator (α := α) n := by
  ext o i
  rw [occupationLeftCreator_right_entry, Matrix.mul_apply]
  simp only [Fintype.sum_prod_type]
  simp only [occupationLeftCreator_left_entry]
  simp only [
    Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.sum_mul]
  have h := congrFun (congrFun
    (creationOccupation_basis_covariance (leftEdgeUnitary C D) n (i.1, o.1)) o.2) i.2
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

def occupationRightCreator (n : ℕ) :
    Matrix (α × TensorPowerProfile (α × α) (n + 1)) (α × TensorPowerProfile (α × α) n) ℂ :=
  fun o i => creationOccupation n (basisVector (o.1, i.1)) o.2 i.2

theorem occupationRightCreator_left_entry (n : ℕ) (D : CMatrix α)
    (o : α × TensorPowerProfile (α × α) (n + 1)) (i : α × TensorPowerProfile (α × α) n) :
    (Matrix.kronecker D (1 : CMatrix (TensorPowerProfile (α × α) (n + 1))) *
      occupationRightCreator (α := α) n) o i =
      ∑ x : α, D o.1 x * creationOccupation n (basisVector (x, i.1)) o.2 i.2 := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, occupationRightCreator]

theorem occupationRightCreator_right_entry (n : ℕ)
    (Q : CMatrix (TensorPowerProfile (α × α) (n + 1)))
    (o : α × TensorPowerProfile (α × α) (n + 1)) (i : α × TensorPowerProfile (α × α) n) :
    (Matrix.kronecker (1 : CMatrix α) Q * occupationRightCreator (α := α) n) o i =
      (Q * creationOccupation n (basisVector (o.1, i.1))) o.2 i.2 := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, occupationRightCreator]

theorem occupationRightCreator_covariance (C D : Matrix.unitaryGroup α ℂ) (n : ℕ) :
    Matrix.kronecker (D : CMatrix α) (1 : CMatrix (TensorPowerProfile (α × α) (n + 1))) *
      occupationRightCreator (α := α) n * Matrix.kronecker (C : CMatrix α)
        (occupationRotation (rightEdgeUnitary C D) n : CMatrix (TensorPowerProfile (α × α) n)) =
    Matrix.kronecker (1 : CMatrix α)
      (occupationRotation (rightEdgeUnitary C D) (n + 1) :
        CMatrix (TensorPowerProfile (α × α) (n + 1))) * occupationRightCreator (α := α) n := by
  ext o i
  rw [occupationRightCreator_right_entry, Matrix.mul_apply]
  simp only [Fintype.sum_prod_type]
  simp only [occupationRightCreator_left_entry]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.sum_mul]
  have h := congrFun (congrFun
    (creationOccupation_basis_covariance (rightEdgeUnitary C D) n (o.1, i.1)) o.2) i.2
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type, rightEdgeUnitary_apply] at h
  rw [h]
  simp only [Matrix.mul_apply, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro w _
  ring


end
end ICO.MHOccupationCovariance

