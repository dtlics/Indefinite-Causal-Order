import ICO.MHFreshInsertion

/-! Quantitative comparison of the actual fresh-recording insertion and
symmetric creation on every unrestricted fixed-length multiset sector. -/

namespace ICO.MHERecordingApprox

open QIT ICO.MHSymmetric ICO.MHCreationCovariance ICO.MHCreationCoefficients
  ICO.MHOccupationCounts ICO.MHOccupationSupport ICO.MHBadInsertion
  ICO.MHFreshInsertion ICO.MHUniqueNorm ICO.MHSparseNorm
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 2000000

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The Ma–Huang fresh-output insertion on an arbitrary multiset sector. -/
def fullInsertion {n r : ℕ} (q : TensorPowerProfile (α × α) r) :
    Matrix (Input (α := α) (n + 1)) (Input (α := α) n) ℂ :=
  fun o i => if i ∈ freshSupport q o then
    (Real.sqrt ((Fintype.card α : ℝ) - (usedOutputs i.2 q).card) : ℂ)⁻¹ else 0

/-- Symmetric creation in actual normalized occupation coordinates. -/
def symmetricInsertion (n : ℕ) :
    Matrix (Input (α := α) (n + 1)) (Input (α := α) n) ℂ :=
  fun o i => (Real.sqrt (Fintype.card α) : ℂ)⁻¹ *
    creationOccupation n (basisVector (i.1, o.1)) o.2 i.2

theorem insertion_difference {n r : ℕ} (q : TensorPowerProfile (α × α) r) :
    fullInsertion q - symmetricInsertion n = freshError q - collisionInsertion q := by
  ext o i
  simp only [Matrix.sub_apply, fullInsertion, symmetricInsertion,
    creationOccupation_basis_entry, freshError, collisionInsertion]
  by_cases he : o.2 = incrementProfile (i.1, o.1) i.2
  · by_cases hy : o.1 ∈ usedOutputs i.2 q
    · have hf : i ∉ freshSupport q o := by simp [freshSupport, hy]
      have hc : i ∈ collisionSupport q o := by simp [collisionSupport, he, hy]
      simp only [if_neg hf, if_pos he, if_pos hc, zero_sub]
      simp only [div_eq_mul_inv, mul_comm]
    · have hf : i ∈ freshSupport q o := by simp [freshSupport, he, hy]
      have hc : i ∉ collisionSupport q o := by simp [collisionSupport, hy]
      have hz := fresh_count_zero i.2 q i.1 o.1 hy
      simp [hf, hc, he, hz, freshGap]
  · have hf : i ∉ freshSupport q o := by simp [freshSupport, he]
    have hc : i ∉ collisionSupport q o := by simp [collisionSupport, he]
    simp [hf, hc, he]

theorem insertion_support_disjoint {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (o : Input (α := α) (n + 1)) (i j : Input (α := α) n)
    (hi : i ∈ freshSupport q o) (hj : j ∈ collisionSupport q o) : False := by
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  have hgood := fresh_total_multiplicity i.2 q i.1 o.1 hi'.2
  have hbad := collision_total_multiplicity j.2 q j.1 o.1 hj'.2
  rw [← hi'.1] at hgood
  rw [← hj'.1] at hbad
  omega

theorem insertion_difference_row_sq {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (v : Input (α := α) n → ℂ) (o : Input (α := α) (n + 1)) :
    ‖((freshError q - collisionInsertion q) *ᵥ v) o‖ ^ 2 =
      ‖(freshError q *ᵥ v) o‖ ^ 2 + ‖(collisionInsertion q *ᵥ v) o‖ ^ 2 := by
  by_cases hex : ∃ i, i ∈ freshSupport q o
  · obtain ⟨i, hi⟩ := hex
    have hz (j : Input (α := α) n) : collisionInsertion q o j = 0 := by
      have hj : j ∉ collisionSupport q o := fun h => insertion_support_disjoint q o i j hi h
      simp [collisionInsertion, hj]
    have hmul : (collisionInsertion q *ᵥ v) o = 0 := by simp [Matrix.mulVec, dotProduct, hz]
    simp only [Matrix.sub_mulVec, Pi.sub_apply, hmul, sub_zero, norm_zero, zero_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, add_zero]
  · have hz (i : Input (α := α) n) : freshError q o i = 0 := by
      have hi : i ∉ freshSupport q o := fun h => hex ⟨i, h⟩
      simp [freshError, hi]
    have hmul : (freshError q *ᵥ v) o = 0 := by simp [Matrix.mulVec, dotProduct, hz]
    simp [Matrix.sub_mulVec, hmul]

theorem collision_square_sum_le {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (v : Input (α := α) n → ℂ) :
    (∑ o : Input (α := α) (n + 1), ‖(collisionInsertion q *ᵥ v) o‖ ^ 2) ≤
      (((n + 1 : ℝ) / Fintype.card α) * (n + r)) * ∑ i : Input (α := α) n, ‖v i‖ ^ 2 := by
  apply mulVec_square_sum_le (collisionInsertion q) (collisionSupport q)
    ((n + 1 : ℝ) / Fintype.card α) (n + r) (by positivity)
  · intro o i hi; simp [collisionInsertion, hi]
  · exact collision_row_weight q
  · intro i
    rw [collision_column_degree]
    exact_mod_cast usedOutputs_card_le i.2 q

/-- The full unrestricted-sector `V^L−E^L` estimate. No distinctness,
injectivity, or no-repeated-label promise is imposed on the source records. -/
theorem insertion_difference_norm_le {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (hsize : n + r < Fintype.card α) :
    ‖fullInsertion q - symmetricInsertion n‖ ≤
      Real.sqrt ((2 * (n + r : ℝ) * (n + r + 1)) / Fintype.card α) := by
  apply matrix_norm_le_of_square_sum _ _ (by positivity)
  intro v
  rw [insertion_difference]
  simp_rw [insertion_difference_row_sq]
  rw [Finset.sum_add_distrib]
  have hf := row_unique_square_sum_le (freshError q) (freshError_unique q)
    ((n + r : ℝ) / Fintype.card α) (freshError_column_le q hsize) v
  have hc := collision_square_sum_le q v
  have hsum : 0 ≤ ∑ i : Input (α := α) n, ‖v i‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcoef : ((n + r : ℝ) / Fintype.card α) +
      (((n + 1 : ℝ) / Fintype.card α) * (n + r)) ≤
      (2 * (n + r : ℝ) * (n + r + 1)) / Fintype.card α := by
    calc
      _ = ((n + 2 : ℝ) * (n + r)) / Fintype.card α := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n),
        (Nat.cast_nonneg r : (0 : ℝ) ≤ r)])
        (Nat.cast_nonneg _)
  have hlast := mul_le_mul_of_nonneg_right hcoef hsum
  nlinarith

end
end ICO.MHERecordingApprox
