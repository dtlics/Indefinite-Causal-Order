import ICO.MHOccupationCovariance

/-! Exact transport of the query-coupled creation operators between word
and occupation coordinates. -/

namespace ICO.MHCreatorEmbedding

open QIT ICO.MHSymmetric ICO.MHCreationCovariance ICO.MHRightCovariance
  ICO.MHOccupationCovariance
open scoped BigOperators Matrix

noncomputable section
set_option maxHeartbeats 2200000

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem creationWord_domain (n : ℕ) (v : a → ℂ) :
    creationWord n v * symmetricProjectionMatrix n = creationWord n v := by
  simp only [creationWord, Matrix.smul_mul, Matrix.mul_assoc,
    symmetricProjectionMatrix_idempotent]

variable {α : Type*} [Fintype α] [DecidableEq α]

def queryOccupationEmbedding (n : ℕ) :
    Matrix (α × TensorPower (α × α) n) (α × TensorPowerProfile (α × α) n) ℂ :=
  Matrix.kronecker (1 : CMatrix α) (occupationEmbedding n)

theorem queryOccupation_gram (n : ℕ) :
    (queryOccupationEmbedding (α := α) n).conjTranspose * queryOccupationEmbedding (α := α) n =
      (1 : CMatrix (α × TensorPowerProfile (α × α) n)) := by
  unfold queryOccupationEmbedding
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul]
  simp only [Matrix.conjTranspose_one, Matrix.one_mul, occupationEmbedding_gram]
  exact Matrix.one_kronecker_one

theorem queryOccupation_image (n : ℕ) :
    queryOccupationEmbedding (α := α) n * (queryOccupationEmbedding n).conjTranspose =
      Matrix.kronecker (1 : CMatrix α) (symmetricProjectionMatrix (a := α × α) n) := by
  unfold queryOccupationEmbedding
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul]
  simp only [Matrix.conjTranspose_one, Matrix.mul_one, occupationEmbedding_projection]

theorem occupationRightCreator_compression (n : ℕ) :
    occupationRightCreator (α := α) n =
      (queryOccupationEmbedding (α := α) (n+1)).conjTranspose * rightCreator n * queryOccupationEmbedding n := by
  ext o i
  simp [queryOccupationEmbedding, Matrix.mul_apply, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, occupationRightCreator,
    creationOccupation, rightCreator]

theorem rightCreator_domain (n : ℕ) :
    rightCreator (α := α) n *
      Matrix.kronecker (1 : CMatrix α) (symmetricProjectionMatrix (a := α × α) n) = rightCreator n := by
  ext o i
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, rightCreator]
  simp only [ite_mul,one_mul,zero_mul,mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact congrFun (congrFun (creationWord_domain n (basisVector (o.1,i.1))) o.2) i.2

theorem occupationRightCreator_image (n : ℕ) :
    occupationRightCreator (α := α) n * (occupationRightCreator n).conjTranspose =
      (queryOccupationEmbedding (α := α) (n+1)).conjTranspose *
        (rightCreator n * (rightCreator n).conjTranspose) * queryOccupationEmbedding (n+1) := by
  rw [occupationRightCreator_compression]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (queryOccupationEmbedding (α := α) n)
    (queryOccupationEmbedding (α := α) n).conjTranspose, queryOccupation_image]
  rw [← Matrix.mul_assoc (rightCreator (α := α) n), rightCreator_domain]

end
end ICO.MHCreatorEmbedding
