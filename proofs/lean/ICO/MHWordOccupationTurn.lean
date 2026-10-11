import ICO.MHWordRotation

/-! Exact intertwining of finite-word and occupation-profile rotations. -/
namespace ICO.MHWordRotation
open Matrix QIT ICO.MHWordDistinct ICO.MHWordProfiles ICO.MHSymmetric
  ICO.MHCreationCovariance ICO.MHRightCovariance
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def rightSlots (l r : ℕ) : Finset (Fin l ⊕ Fin r) :=
  Finset.univ.map ⟨Sum.inr,Sum.inr_injective⟩

@[simp] theorem inl_not_rightSlots (l r : ℕ) (i : Fin l) : Sum.inl i ∉ rightSlots l r := by
  simp [rightSlots]

@[simp] theorem inr_mem_rightSlots (l r : ℕ) (i : Fin r) : Sum.inr i ∈ rightSlots l r := by
  simp [rightSlots]

def tensorWordTurn (C D : Matrix.unitaryGroup A ℂ) (l r : ℕ) :
    CMatrix (A × (TensorPower (A × A) l × TensorPower (A × A) r)) :=
  Matrix.kronecker (C : CMatrix A)
    (Matrix.kronecker
      (unitaryTensorPowerMatrix (leftEdgeUnitary C D) l : CMatrix (TensorPower (A × A) l))
      (unitaryTensorPowerMatrix (rightEdgeUnitary D⁻¹ C⁻¹) r : CMatrix (TensorPower (A × A) r)))

def profileTurn (C D : Matrix.unitaryGroup A ℂ) (l r : ℕ) :
    Matrix.unitaryGroup (ProfileBasis A l r) ℂ :=
  tensorUnitary C (tensorUnitary (symmetricRotation (leftEdgeUnitary C D) l)
    (symmetricRotation (rightEdgeUnitary D⁻¹ C⁻¹) r))

theorem turn_tensor (C D : Matrix.unitaryGroup A ℂ) (l r : ℕ) :
    (turn (rightSlots l r) C D : CMatrix (WordBasis A (Fin l ⊕ Fin r))) =
      (tensorWordTurn C D l r).submatrix (twoWordEquiv l r) (twoWordEquiv l r) := by
  ext o i
  change (C : CMatrix A) o.1 i.1 *
      (∏ j : Fin l ⊕ Fin r, (recordUnitary (rightSlots l r) C D j : CMatrix (A × A)) (o.2 j) (i.2 j)) =
    (C : CMatrix A) o.1 i.1 *
      ((unitaryTensorPowerMatrix (leftEdgeUnitary C D) l : CMatrix (TensorPower (A × A) l))
        (leftWord o.2) (leftWord i.2) *
       (unitaryTensorPowerMatrix (rightEdgeUnitary D⁻¹ C⁻¹) r : CMatrix (TensorPower (A × A) r))
        (rightWord o.2) (rightWord i.2))
  rw [Fintype.prod_sum_type]
  simp only [recordUnitary,inl_not_rightSlots,inr_mem_rightSlots,if_neg,if_pos,if_false,
    unitaryTensorPowerMatrix_apply_eq_fin_prod,leftWord,rightWord,Equiv.apply_symm_apply]

theorem turn_embedding (C D : Matrix.unitaryGroup A ℂ) (l r : ℕ) :
    (turn (rightSlots l r) C D : CMatrix (WordBasis A (Fin l ⊕ Fin r))) * wordEmbedding l r =
      wordEmbedding l r * (profileTurn C D l r : CMatrix (ProfileBasis A l r)) := by
  let E := Matrix.kronecker (1 : CMatrix A)
    (Matrix.kronecker (occupationEmbedding (a := A × A) l) (occupationEmbedding (a := A × A) r))
  have ht : tensorWordTurn C D l r * E = E * (profileTurn C D l r : CMatrix (ProfileBasis A l r)) := by
    simp only [tensorWordTurn,E,profileTurn,tensorUnitary,symmetricRotation,Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]
    simp only [Matrix.mul_one,Matrix.one_mul]
    rw [occupationRotation_intertwine,occupationRotation_intertwine]
  rw [turn_tensor,wordEmbedding_tensor,Matrix.submatrix_mul_equiv]
  change (tensorWordTurn C D l r * E).submatrix (twoWordEquiv l r) id =
    E.submatrix (twoWordEquiv l r) id * (profileTurn C D l r : CMatrix (ProfileBasis A l r))
  rw [ht]
  simpa only [Equiv.refl_apply,Matrix.submatrix_id_id] using
    (Matrix.submatrix_mul_equiv E (profileTurn C D l r : CMatrix (ProfileBasis A l r))
      (twoWordEquiv l r) (Equiv.refl (ProfileBasis A l r)) id).symm

#print axioms turn_tensor
#print axioms turn_embedding
end
end ICO.MHWordRotation

