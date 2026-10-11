import ICO.RecordingOperatorSupport

/-! Known query-and-memory isometries remain isometries when lifted past the
private recording registers. This validates the intervening contraction used
in the purified recording recurrence. -/

namespace ICO.RecordingKnownOperation

open ICO.PathRecordingSupport ICO.RecordingOperatorSupport
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

variable {α μ ν : Type*} [Fintype α] [DecidableEq α]
  [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]

def queryMemoryFirst (μ : Type*) :
    Basis α × μ ≃ (α × μ) × (Relation α α × Relation α α) where
  toFun i := ((i.1.1, i.2), (i.1.2.1, i.1.2.2))
  invFun i := ((i.1.1, i.2.1, i.2.2), i.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem knownOperation_eq_tensor (K : Matrix (α × ν) (α × μ) ℂ) :
    knownOperation K =
      (Matrix.kronecker K (1 : Matrix (Relation α α × Relation α α)
        (Relation α α × Relation α α) ℂ)).submatrix (queryMemoryFirst ν) (queryMemoryFirst μ) := by
  ext o i
  simp only [knownOperation, Matrix.submatrix_apply, queryMemoryFirst,
    Equiv.coe_fn_mk, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
  by_cases h : o.1.2 = i.1.2
  · simp [h]
  · simp [h]

theorem knownOperation_isometry (K : Matrix (α × ν) (α × μ) ℂ)
    (hK : K.conjTranspose * K = 1) :
    (knownOperation K).conjTranspose * knownOperation K = 1 := by
  let R := Relation α α × Relation α α
  have hAdj : (Matrix.kronecker K (1 : Matrix R R ℂ)).conjTranspose =
      Matrix.kronecker K.conjTranspose (1 : Matrix R R ℂ) := by
    exact (Matrix.conjTranspose_kronecker K (1 : Matrix R R ℂ)).trans
      (by rw [Matrix.conjTranspose_one]; rfl)
  have hGram : (Matrix.kronecker K (1 : Matrix R R ℂ)).conjTranspose *
      Matrix.kronecker K (1 : Matrix R R ℂ) =
      Matrix.kronecker (K.conjTranspose * K) (1 : Matrix R R ℂ) := by
    rw [hAdj]
    symm
    simpa only [Matrix.one_mul] using
      Matrix.mul_kronecker_mul K.conjTranspose K (1 : Matrix R R ℂ) (1 : Matrix R R ℂ)
  have hOne : Matrix.kronecker (1 : Matrix (α × μ) (α × μ) ℂ) (1 : Matrix R R ℂ) = 1 :=
    Matrix.one_kronecker_one
  rw [knownOperation_eq_tensor, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, hGram, hK, hOne, Matrix.submatrix_one_equiv]

theorem knownOperation_norm_le (K : Matrix (α × ν) (α × μ) ℂ)
    (hK : K.conjTranspose * K = 1) : ‖knownOperation K‖ ≤ 1 := by
  have h := IsStarProjection.norm_le (1 : Matrix (Basis α × μ) (Basis α × μ) ℂ)
    (IsStarProjection.one _)
  rw [← knownOperation_isometry K hK, Matrix.l2_opNorm_conjTranspose_mul_self] at h
  nlinarith [norm_nonneg (knownOperation K)]

end
end ICO.RecordingKnownOperation
