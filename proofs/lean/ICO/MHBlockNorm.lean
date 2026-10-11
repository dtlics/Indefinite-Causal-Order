import ICO.MHUniqueNorm

/-! Uniform operator-norm bounds survive finite coherent direct sums. -/

namespace ICO.MHBlockNorm

open QIT ICO.MHUniqueNorm
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 1000000

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem square_sum_le_of_norm (A : Matrix b a ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hA : ‖A‖ ≤ Real.sqrt B) (v : a → ℂ) :
    (∑ i : b, ‖(A *ᵥ v) i‖ ^ 2) ≤ B * ∑ j : a, ‖v j‖ ^ 2 := by
  have h : ‖WithLp.toLp 2 (A *ᵥ v)‖ ≤ Real.sqrt B * ‖WithLp.toLp 2 v‖ :=
    (Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 v)).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr h
  rw [mul_pow, Real.sq_sqrt hB, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2] at hs
  exact hs

variable {k : Type*} [Fintype k] [DecidableEq k]
  {m n : k → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]

theorem blockDiagonal'_mulVec (A : ∀ i, Matrix (m i) (n i) ℂ)
    (v : (Σ i, n i) → ℂ) (i : k) (x : m i) :
    (Matrix.blockDiagonal' A *ᵥ v) ⟨i, x⟩ = (A i *ᵥ fun y => v ⟨i, y⟩) x := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Matrix.blockDiagonal'_apply', Ne.symm hj]
  · simp

theorem blockDiagonal'_square_sum_le (A : ∀ i, Matrix (m i) (n i) ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hA : ∀ i, ‖A i‖ ≤ Real.sqrt B)
    (v : (Σ i, n i) → ℂ) :
    (∑ x : (Σ i, m i), ‖(Matrix.blockDiagonal' A *ᵥ v) x‖ ^ 2) ≤
      B * ∑ y : (Σ i, n i), ‖v y‖ ^ 2 := by
  simp only [Fintype.sum_sigma, blockDiagonal'_mulVec]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact square_sum_le_of_norm (A i) B hB (hA i) _

theorem blockDiagonal'_norm_le (A : ∀ i, Matrix (m i) (n i) ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hA : ∀ i, ‖A i‖ ≤ Real.sqrt B) :
    ‖Matrix.blockDiagonal' A‖ ≤ Real.sqrt B :=
  matrix_norm_le_of_square_sum _ B hB (blockDiagonal'_square_sum_le A B hB hA)

theorem blockDiagonal_mulVec (A : k → Matrix b a ℂ)
    (v : a × k → ℂ) (i : b) (j : k) :
    (Matrix.blockDiagonal A *ᵥ v) (i, j) = (A j *ᵥ fun x => v (x, j)) i := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.blockDiagonal_apply']

theorem blockDiagonal_norm_le (A : k → Matrix b a ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hA : ∀ i, ‖A i‖ ≤ Real.sqrt B) :
    ‖Matrix.blockDiagonal A‖ ≤ Real.sqrt B := by
  apply matrix_norm_le_of_square_sum _ B hB
  intro v
  simp only [Fintype.sum_prod_type, blockDiagonal_mulVec]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖v (i, j)‖ ^ 2), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact square_sum_le_of_norm (A i) B hB (hA i) _

end
end ICO.MHBlockNorm
