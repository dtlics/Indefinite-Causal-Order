import ICO.MHWordRightImage

/-! The creator image is the sum of actual Bell images over symmetric slots. -/
namespace ICO.MHWordBellSum
open Matrix QIT ICO.MHWordRightImage ICO.MHRightCovariance
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def queryPermutation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    CMatrix (A × TensorPower (A × A) n) :=
  Matrix.kronecker 1 (permutationMatrix n σ)

theorem querySymmetry_permutation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    querySymmetry (A := A) n*queryPermutation n σ=querySymmetry (A := A) n := by
  simp only [querySymmetry,queryPermutation,Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul,Matrix.one_mul,symmetricProjectionMatrix_mul_permutationMatrix]

theorem permutation_querySymmetry (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    queryPermutation (A := A) n σ*querySymmetry n=querySymmetry (A := A) n := by
  simp only [querySymmetry,queryPermutation,Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul,Matrix.one_mul,permutationMatrix_mul_symmetricProjectionMatrix]

theorem queryPermutation_adjoint (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (queryPermutation (A := A) n σ).conjTranspose=queryPermutation (A := A) n σ⁻¹ := by
  simp only [queryPermutation,Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    permutationMatrix_conjTranspose]

def rotatedBell (n : ℕ) (j : Fin (n+1)) : CMatrix (Out (A := A) n) :=
  queryPermutation (n+1) (Equiv.swap 0 j) * firstBell (A := A) n *
    (queryPermutation (n+1) (Equiv.swap 0 j)).conjTranspose

def bellSum (n : ℕ) : CMatrix (Out (A := A) n) := ∑ j : Fin (n+1), rotatedBell n j

theorem symmetric_rotatedBell (n : ℕ) (j : Fin (n+1)) :
    querySymmetry (n+1)*rotatedBell (A := A) n j*querySymmetry (n+1)=
      querySymmetry (n+1)*firstBell (A := A) n*querySymmetry (n+1) := by
  unfold rotatedBell
  simp only [← Matrix.mul_assoc]
  rw [querySymmetry_permutation,Matrix.mul_assoc,
    queryPermutation_adjoint,permutation_querySymmetry]

theorem symmetric_bellSum (n : ℕ) :
    querySymmetry (n+1)*bellSum (A := A) n*querySymmetry (n+1)=
      ((n+1 : ℕ) : ℂ) • (querySymmetry (n+1)*firstBell (A := A) n*querySymmetry (n+1)) := by
  simp only [bellSum,Matrix.mul_sum,Matrix.sum_mul,symmetric_rotatedBell,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

theorem rightCreator_image_sum (n : ℕ) :
    rightCreator (α := A) n*(rightCreator n).conjTranspose =
      (Fintype.card A : ℂ) • (querySymmetry (n+1)*bellSum (A := A) n*querySymmetry (n+1)) := by
  rw [rightCreator_image,symmetric_bellSum,smul_smul]
  congr 1
  ring

#print axioms rightCreator_image_sum
end
end ICO.MHWordBellSum
