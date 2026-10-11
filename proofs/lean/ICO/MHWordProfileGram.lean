import ICO.MHWordProfiles

/-! The normalized two-word embedding is an actual isometry. -/
namespace ICO.MHWordProfiles
open Matrix QIT ICO.MHSymmetric ICO.MHWordDistinct
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def twoWordEquiv (l r : ℕ) : WordBasis A (Fin l ⊕ Fin r) ≃
    A × (TensorPower (A × A) l × TensorPower (A × A) r) :=
  (Equiv.refl A).prodCongr ((Equiv.sumArrowEquivProdArrow (Fin l) (Fin r) (A × A)).trans
    ((tensorPowerEquiv l).symm.prodCongr (tensorPowerEquiv r).symm))

theorem wordEmbedding_tensor (l r : ℕ) : wordEmbedding (A := A) l r =
    (Matrix.kronecker (1 : CMatrix A)
      (Matrix.kronecker (occupationEmbedding (a := A × A) l) (occupationEmbedding (a := A × A) r))).submatrix
        (twoWordEquiv l r) id := by
  ext w p
  change ((if w.1=p.1 then 1 else 0) * occupationEmbedding l (leftWord w.2) p.2.1) *
    occupationEmbedding r (rightWord w.2) p.2.2 =
    (if w.1=p.1 then 1 else 0) * (occupationEmbedding l (leftWord w.2) p.2.1 *
      occupationEmbedding r (rightWord w.2) p.2.2)
  ring

theorem wordEmbedding_gram (l r : ℕ) :
    (wordEmbedding (A := A) l r).conjTranspose * wordEmbedding (A := A) l r =
      (1 : CMatrix (ProfileBasis A l r)) := by
  rw [wordEmbedding_tensor,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv]
  simp only [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]
  simp only [occupationEmbedding_gram,Matrix.one_mul,Matrix.one_kronecker_one,Matrix.submatrix_id_id]

theorem distinct_projection_compression (l r : ℕ) :
    (wordEmbedding (A := A) l r).conjTranspose * distinctProjection * wordEmbedding l r =
      profileProjection l r := by
  rw [Matrix.mul_assoc,distinct_projection_intertwining,← Matrix.mul_assoc,
    wordEmbedding_gram,Matrix.one_mul]

#print axioms wordEmbedding_gram
#print axioms distinct_projection_compression
end
end ICO.MHWordProfiles

