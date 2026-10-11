import ICO.MHCreationCovariance

/-! Exact covariance of the inverse-oracle creation term. -/

namespace ICO.MHRightCovariance

open QIT ICO.MHSymmetric ICO.MHCreationCovariance
open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section
set_option maxHeartbeats 1000000

variable {α : Type*} [Fintype α] [DecidableEq α]

def rightEdgeUnitary (C D : Matrix.unitaryGroup α ℂ) : Matrix.unitaryGroup (α × α) ℂ :=
  ⟨Matrix.kronecker (D : CMatrix α).transpose (C : CMatrix α),
    Matrix.kronecker_mem_unitary (Matrix.transpose_mem_unitaryGroup_iff.mpr D.property) C.property⟩

theorem rightEdgeUnitary_apply (C D : Matrix.unitaryGroup α ℂ) (x y u v : α) :
    (rightEdgeUnitary C D : CMatrix (α × α)) (x, y) (u, v) =
      (D : CMatrix α) u x * (C : CMatrix α) y v := rfl

def rightCreator (n : ℕ) :
    Matrix (α × TensorPower (α × α) (n + 1)) (α × TensorPower (α × α) n) ℂ :=
  fun o i => creationWord n (basisVector (o.1, i.1)) o.2 i.2

theorem rightCreator_left_entry (n : ℕ) (D : CMatrix α)
    (o : α × TensorPower (α × α) (n + 1)) (i : α × TensorPower (α × α) n) :
    (Matrix.kronecker D (1 : CMatrix (TensorPower (α × α) (n + 1))) *
      rightCreator (α := α) n) o i =
      ∑ x : α, D o.1 x * creationWord n (basisVector (x, i.1)) o.2 i.2 := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, rightCreator]

theorem rightCreator_right_entry (n : ℕ)
    (Q : CMatrix (TensorPower (α × α) (n + 1)))
    (o : α × TensorPower (α × α) (n + 1)) (i : α × TensorPower (α × α) n) :
    (Matrix.kronecker (1 : CMatrix α) Q * rightCreator (α := α) n) o i =
      (Q * creationWord n (basisVector (o.1, i.1))) o.2 i.2 := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, rightCreator]

theorem rightCreator_covariance (C D : Matrix.unitaryGroup α ℂ) (n : ℕ) :
    Matrix.kronecker (D : CMatrix α) (1 : CMatrix (TensorPower (α × α) (n + 1))) *
      rightCreator (α := α) n * Matrix.kronecker (C : CMatrix α)
        (unitaryTensorPowerMatrix (rightEdgeUnitary C D) n : CMatrix (TensorPower (α × α) n)) =
    Matrix.kronecker (1 : CMatrix α)
      (unitaryTensorPowerMatrix (rightEdgeUnitary C D) (n + 1) :
        CMatrix (TensorPower (α × α) (n + 1))) * rightCreator (α := α) n := by
  ext o i
  rw [rightCreator_right_entry, Matrix.mul_apply]
  simp only [Fintype.sum_prod_type]
  simp only [rightCreator_left_entry]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.sum_mul]
  have h := congrFun (congrFun
    (creationWord_basis_covariance (rightEdgeUnitary C D) n (o.1, i.1)) o.2) i.2
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

/-- Ma–Huang's inverse-record rotation is `conj(C) ⊗ D†`, exactly.
The creator covariance above applies with query matrices `C†` and `D†`. -/
theorem inverse_rightEdgeUnitary (C D : Matrix.unitaryGroup α ℂ) :
    (rightEdgeUnitary D⁻¹ C⁻¹ : CMatrix (α × α)) =
      Matrix.kronecker ((C : CMatrix α).map star) (D : CMatrix α).conjTranspose := by
  ext o i
  simp [rightEdgeUnitary, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.UnitaryGroup.inv_val, Matrix.conjTranspose_apply, Matrix.transpose_apply]

end
end ICO.MHRightCovariance
