import ICO.MHSparseNorm

/-! Norm bounds for matrices with at most one nonzero entry in each row. -/

namespace ICO.MHUniqueNorm

open QIT ICO.RecordingProcess
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 1000000

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem row_unique_norm_sq (A : Matrix b a ℂ)
    (hunique : ∀ i j k, A i j ≠ 0 → A i k ≠ 0 → j = k)
    (v : a → ℂ) (i : b) :
    ‖(A *ᵥ v) i‖ ^ 2 = ∑ j : a, ‖A i j‖ ^ 2 * ‖v j‖ ^ 2 := by
  by_cases hex : ∃ j, A i j ≠ 0
  · obtain ⟨j, hj⟩ := hex
    have hz (k : a) (hk : k ≠ j) : A i k = 0 := by
      by_contra h
      exact hk (hunique i k j h hj)
    have hs : (A *ᵥ v) i = A i j * v j := by
      apply Finset.sum_eq_single j
      · intro k _ hk; simp [hz k hk]
      · simp
    have hs' : (∑ k : a, ‖A i k‖ ^ 2 * ‖v k‖ ^ 2) = ‖A i j‖ ^ 2 * ‖v j‖ ^ 2 := by
      apply Finset.sum_eq_single j
      · intro k _ hk; rw [hz k hk]; simp
      · simp
    rw [hs, hs', norm_mul, mul_pow]
  · have hz : ∀ j, A i j = 0 := by simpa using hex
    simp [Matrix.mulVec, dotProduct, hz]

theorem row_unique_square_sum_le (A : Matrix b a ℂ)
    (hunique : ∀ i j k, A i j ≠ 0 → A i k ≠ 0 → j = k)
    (B : ℝ) (hcol : ∀ j, (∑ i : b, ‖A i j‖ ^ 2) ≤ B) (v : a → ℂ) :
    (∑ i : b, ‖(A *ᵥ v) i‖ ^ 2) ≤ B * ∑ j : a, ‖v j‖ ^ 2 := by
  simp_rw [row_unique_norm_sq A hunique]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)

theorem matrix_norm_le_of_square_sum (A : Matrix b a ℂ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ v : a → ℂ, (∑ i : b, ‖(A *ᵥ v) i‖ ^ 2) ≤ B * ∑ j : a, ‖v j‖ ^ 2) :
    ‖A‖ ≤ Real.sqrt B := by
  rw [← action_norm]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  have h' := h (WithLp.ofLp v)
  have hv : ‖v‖ ^ 2 = ∑ j : a, ‖(WithLp.ofLp v) j‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
  have hAv : ‖action A v‖ ^ 2 = ∑ i : b, ‖(A *ᵥ WithLp.ofLp v) i‖ ^ 2 := by
    rw [action_apply, PiLp.norm_sq_eq_of_L2]
  have hsqrt := Real.sq_sqrt hB
  have hnon : 0 ≤ Real.sqrt B * ‖v‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  rw [← hv, ← hAv] at h'
  nlinarith [norm_nonneg (action A v)]

theorem row_unique_norm_le (A : Matrix b a ℂ)
    (hunique : ∀ i j k, A i j ≠ 0 → A i k ≠ 0 → j = k)
    (B : ℝ) (hB : 0 ≤ B) (hcol : ∀ j, (∑ i : b, ‖A i j‖ ^ 2) ≤ B) :
    ‖A‖ ≤ Real.sqrt B :=
  matrix_norm_le_of_square_sum A B hB (row_unique_square_sum_le A hunique B hcol)

theorem sqrt_reciprocal_gap_sq (a d : ℝ) (ha : 0 < a) (had : a ≤ d) :
    a * ((Real.sqrt a)⁻¹ - (Real.sqrt d)⁻¹) ^ 2 ≤ (d - a) / d := by
  have hd : 0 < d := lt_of_lt_of_le ha had
  have hAs := ne_of_gt (Real.sqrt_pos.2 ha)
  have hDs := ne_of_gt (Real.sqrt_pos.2 hd)
  have hmono := Real.sqrt_le_sqrt had
  have hsA := Real.sq_sqrt ha.le
  have hsD := Real.sq_sqrt hd.le
  have hgap : (Real.sqrt d - Real.sqrt a) ^ 2 ≤ d - a := by
    nlinarith [mul_le_mul_of_nonneg_right hmono (Real.sqrt_nonneg a)]
  have heq : a * ((Real.sqrt a)⁻¹ - (Real.sqrt d)⁻¹) ^ 2 =
      (Real.sqrt d - Real.sqrt a) ^ 2 / d := by
    calc
      _ = (Real.sqrt a * ((Real.sqrt a)⁻¹ - (Real.sqrt d)⁻¹)) ^ 2 := by
        rw [mul_pow, hsA]
      _ = ((Real.sqrt d - Real.sqrt a) / Real.sqrt d) ^ 2 := by
        congr 1
        field_simp
      _ = _ := by rw [div_pow, hsD]
  rw [heq]
  exact div_le_div_of_nonneg_right hgap hd.le

end
end ICO.MHUniqueNorm
