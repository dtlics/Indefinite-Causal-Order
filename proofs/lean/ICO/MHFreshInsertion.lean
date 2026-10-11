import ICO.MHBadInsertion
import ICO.MHUniqueNorm

/-! The fresh-output normalization error on unrestricted multiset sectors. -/

namespace ICO.MHFreshInsertion

open QIT ICO.MHOccupationCounts ICO.MHOccupationSupport ICO.MHBadInsertion ICO.MHUniqueNorm
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 1500000

variable {α : Type*} [Fintype α] [DecidableEq α]

def freshSupport {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (o : Input (α := α) (n + 1)) : Finset (Input (α := α) n) :=
  Finset.univ.filter fun i => o.2 = incrementProfile (i.1, o.1) i.2 ∧ o.1 ∉ usedOutputs i.2 q

def freshGap {n r : ℕ} (q : TensorPowerProfile (α × α) r) (i : Input (α := α) n) : ℝ :=
  (Real.sqrt ((Fintype.card α : ℝ) - (usedOutputs i.2 q).card))⁻¹ -
    (Real.sqrt (Fintype.card α))⁻¹

def freshError {n r : ℕ} (q : TensorPowerProfile (α × α) r) :
    Matrix (Input (α := α) (n + 1)) (Input (α := α) n) ℂ :=
  fun o i => if i ∈ freshSupport q o then (freshGap q i : ℂ) else 0

theorem freshSupport_unique {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (o : Input (α := α) (n + 1)) (i j : Input (α := α) n)
    (hi : i ∈ freshSupport q o) (hj : j ∈ freshSupport q o) : i = j := by
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  have h := fresh_predecessor_unique q i.2 j.2 i.1 j.1 o.1 hi'.2 hj'.2
    (hi'.1.symm.trans hj'.1)
  exact Prod.ext h.1 h.2

theorem freshError_unique {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (o : Input (α := α) (n + 1)) (i j : Input (α := α) n)
    (hi : freshError q o i ≠ 0) (hj : freshError q o j ≠ 0) : i = j := by
  apply freshSupport_unique q o i j
  · by_contra h; exact hi (by simp [freshError, h])
  · by_contra h; exact hj (by simp [freshError, h])

theorem sum_fresh_const (S : Finset α) (c : ℝ) :
    (∑ y : α, if y ∉ S then c else 0) = ((Fintype.card α : ℝ) - S.card) * c := by
  have hs : Finset.univ.filter (fun y : α => y ∉ S) = Sᶜ := by ext y; simp
  rw [← Finset.sum_filter, hs]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_compl]
  rw [Nat.cast_sub (Finset.card_le_univ _)]

theorem freshError_column_sum {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (i : Input (α := α) n) :
    (∑ o : Input (α := α) (n + 1), ‖freshError q o i‖ ^ 2) =
      ((Fintype.card α : ℝ) - (usedOutputs i.2 q).card) * (freshGap q i) ^ 2 := by
  have he (o : Input (α := α) (n + 1)) : ‖freshError q o i‖ ^ 2 =
      if i ∈ freshSupport q o then (freshGap q i) ^ 2 else 0 := by
    unfold freshError
    split_ifs <;> simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [he]
  simp only [freshSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Fintype.sum_prod_type]
  simp_rw [ite_and]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact sum_fresh_const _ _

theorem freshError_column_le {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (hsize : n + r < Fintype.card α) (i : Input (α := α) n) :
    (∑ o : Input (α := α) (n + 1), ‖freshError q o i‖ ^ 2) ≤
      (n + r : ℝ) / Fintype.card α := by
  have hk := usedOutputs_card_le i.2 q
  have hkr : ((usedOutputs i.2 q).card : ℝ) ≤ n + r := by exact_mod_cast hk
  have hkd : ((usedOutputs i.2 q).card : ℝ) < Fintype.card α := by exact_mod_cast lt_of_le_of_lt hk hsize
  rw [freshError_column_sum, freshGap]
  have h := sqrt_reciprocal_gap_sq
    ((Fintype.card α : ℝ) - (usedOutputs i.2 q).card) (Fintype.card α)
    (by linarith) (by exact sub_le_self _ (Nat.cast_nonneg _))
  calc
    _ ≤ ((usedOutputs i.2 q).card : ℝ) / Fintype.card α := by convert h using 1 <;> ring
    _ ≤ _ := div_le_div_of_nonneg_right hkr (Nat.cast_nonneg _)

theorem freshError_norm_le {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (hsize : n + r < Fintype.card α) :
    ‖freshError (n := n) q‖ ≤ Real.sqrt ((n + r : ℝ) / Fintype.card α) :=
  row_unique_norm_le (freshError q) (freshError_unique q) _ (by positivity)
    (freshError_column_le q hsize)

end
end ICO.MHFreshInsertion
