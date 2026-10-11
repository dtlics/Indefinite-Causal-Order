import ICO.MHERecordingApprox

/-! Fresh insertion is an actual isometry on each unrestricted multiset
sector below the dimension cutoff. -/

namespace ICO.MHInsertionIsometry

open QIT ICO.MHOccupationSupport ICO.MHBadInsertion ICO.MHFreshInsertion
  ICO.MHERecordingApprox ICO.RecordingProcess
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 1500000

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem fullInsertion_unique {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (o : Input (α := α) (n + 1)) (i j : Input (α := α) n)
    (hi : fullInsertion q o i ≠ 0) (hj : fullInsertion q o j ≠ 0) : i = j := by
  apply freshSupport_unique q o i j
  · by_contra h; exact hi (by simp [fullInsertion, h])
  · by_contra h; exact hj (by simp [fullInsertion, h])

theorem fullInsertion_column_norm_sq {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (hsize : n + r < Fintype.card α) (i : Input (α := α) n) :
    (∑ o : Input (α := α) (n + 1), ‖fullInsertion q o i‖ ^ 2) = 1 := by
  have hk : ((usedOutputs i.2 q).card : ℝ) < Fintype.card α := by
    exact_mod_cast lt_of_le_of_lt (usedOutputs_card_le i.2 q) hsize
  have hp : 0 < (Fintype.card α : ℝ) - (usedOutputs i.2 q).card := by linarith
  have he (o : Input (α := α) (n + 1)) : ‖fullInsertion q o i‖ ^ 2 =
      if i ∈ freshSupport q o then
        (((Fintype.card α : ℝ) - (usedOutputs i.2 q).card))⁻¹ else 0 := by
    unfold fullInsertion
    split_ifs
    · rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        inv_pow, Real.sq_sqrt hp.le]
    · simp
  simp_rw [he]
  simp only [freshSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Fintype.sum_prod_type]
  simp_rw [ite_and]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [sum_fresh_const, mul_inv_cancel₀ (ne_of_gt hp)]

theorem fullInsertion_isometry {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (hsize : n + r < Fintype.card α) :
    (fullInsertion (n := n) q).conjTranspose * fullInsertion (n := n) q =
      (1 : CMatrix (Input (α := α) n)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst j
    rw [if_pos rfl]
    calc
      _ = ((∑ o : Input (α := α) (n + 1), ‖fullInsertion q o i‖ ^ 2 : ℝ) : ℂ) := by
        simp only [Complex.ofReal_sum, Complex.ofReal_pow, Complex.star_def, Complex.conj_mul']
      _ = 1 := by rw [fullInsertion_column_norm_sq q hsize]; norm_num
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro o _
    by_cases hi : fullInsertion q o i = 0
    · simp [hi]
    · have hj : fullInsertion q o j = 0 := by
        by_contra hj
        exact h (fullInsertion_unique q o i j hi hj)
      simp [hj]

theorem fullInsertion_norm_le {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (hsize : n + r < Fintype.card α) : ‖fullInsertion (n := n) q‖ ≤ 1 :=
  isometry_matrix_norm_le _ (fullInsertion_isometry q hsize)

end
end ICO.MHInsertionIsometry
