import ICO.MHSymmetric

/-! Tail symmetry and absorption for the actual symmetric word projector. -/
namespace ICO.MHWordSymmetry
open Matrix QIT ICO.MHSymmetric
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
variable {a : Type*} [Fintype a] [DecidableEq a]

theorem unitVector_same_profile {n : ℕ} (p : TensorPowerProfile a n)
    (x y : TensorPower a n) (h : tensorPowerTypeProfile n x = tensorPowerTypeProfile n y) :
    tensorPowerProfileUnitVector p x = tensorPowerProfileUnitVector p y := by
  have he : x ∈ tensorPowerProfileClass p ↔ y ∈ tensorPowerProfileClass p := by
    rw [mem_tensorPowerProfileClass,mem_tensorPowerProfileClass,h]
  simp only [tensorPowerProfileUnitVector]
  simp only [he]

theorem symmetric_kernel_same_profile {n : ℕ} (x y z : TensorPower a n)
    (h : tensorPowerTypeProfile n y = tensorPowerTypeProfile n z) :
    symmetricProjectionMatrix n x y = symmetricProjectionMatrix n x z := by
  rw [symmetricProjectionMatrix_eq_sum_rankOne_profileUnitVector]
  simp only [Matrix.sum_apply,rankOneMatrix_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [unitVector_same_profile p y z h]

theorem symmetric_kernel_tail {n : ℕ} (x : TensorPower a (n+1)) (z : a)
    (y w : TensorPower a n) (h : tensorPowerTypeProfile n y = tensorPowerTypeProfile n w) :
    symmetricProjectionMatrix (n+1) x (z,y) = symmetricProjectionMatrix (n+1) x (z,w) := by
  apply symmetric_kernel_same_profile
  funext b
  simp only [tensorPowerTypeProfile_succ]
  rw [congrFun h b]

theorem symmetric_column_sum (n : ℕ) (y : TensorPower a n) :
    (∑ x : TensorPower a n, symmetricProjectionMatrix n x y) = 1 := by
  have hf : (fun _ : TensorPower a n => (1 : ℂ)) ∈ symmetricSubspace n := by
    intro σ
    rfl
  have hh := (mem_symmetric_iff_symmetricProjectionMatrix_mulVec_eq_self n _).mp hf
  have hy := congrFun hh y
  have hp := symmetricProjectionMatrix_conjTranspose (a := a) n
  have hstar (x : TensorPower a n) : star (symmetricProjectionMatrix n x y) =
      symmetricProjectionMatrix n y x := congrFun (congrFun hp y) x
  have hreal (x : TensorPower a n) : star (symmetricProjectionMatrix n x y) =
      symmetricProjectionMatrix n x y := by
    have hv (p : TensorPowerProfile a n) (w : TensorPower a n) :
        star (tensorPowerProfileUnitVector p w) = tensorPowerProfileUnitVector p w := by
      simp only [tensorPowerProfileUnitVector]
      split_ifs <;> simp
    rw [symmetricProjectionMatrix_eq_sum_rankOne_profileUnitVector]
    simp only [Matrix.sum_apply,rankOneMatrix_apply,star_sum,star_mul,star_star,hv]
    apply Finset.sum_congr rfl
    intro p _
    exact mul_comm _ _
  simpa only [Matrix.mulVec,dotProduct,mul_one,← hstar,hreal] using hy

def tailMatrix (n : ℕ) : CMatrix (TensorPower a (n+1)) :=
  Matrix.kronecker (1 : CMatrix a) (symmetricProjectionMatrix (a := a) n)

theorem symmetric_tail_absorption (n : ℕ) :
    symmetricProjectionMatrix (a := a) (n+1) * tailMatrix (a := a) n =
        symmetricProjectionMatrix (a := a) (n+1) := by
  ext x y
  rw [Matrix.mul_apply]
  rcases y with ⟨z,y⟩
  change (∑ v : a × TensorPower a n,
    symmetricProjectionMatrix (n+1) x v *
      ((if v.1 = z then 1 else 0) * symmetricProjectionMatrix n v.2 y)) =
      symmetricProjectionMatrix (n+1) x (z,y)
  simp only [tailMatrix,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply]
  rw [Finset.sum_comm]
  simp only [ite_mul,one_mul,zero_mul,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]
  calc
    (∑ w : TensorPower a n, symmetricProjectionMatrix (n+1) x (z,w) *
        symmetricProjectionMatrix n w y) =
      ∑ w : TensorPower a n, symmetricProjectionMatrix (n+1) x (z,y) *
        symmetricProjectionMatrix n w y := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : symmetricProjectionMatrix (a := a) n w y = 0
      · rw [hw,mul_zero,mul_zero]
      · have he := symmetricProjection_basisDelta_support_typeProfile w y hw
        rw [symmetric_kernel_tail x z w y he]
    _ = _ := by rw [← Finset.mul_sum,symmetric_column_sum,mul_one]

#print axioms symmetric_tail_absorption
end
end ICO.MHWordSymmetry
