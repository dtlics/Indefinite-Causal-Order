import ICO.MHCreationCoefficients
import ICO.MHOccupationSupport
import ICO.MHSparseNorm

/-! Collision part of the unrestricted-multiset creation operator. -/

namespace ICO.MHBadInsertion

open QIT ICO.MHOccupationCounts ICO.MHOccupationSupport ICO.MHSparseNorm
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 1500000

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Input (n : ℕ) := α × TensorPowerProfile (α × α) n

def collisionSupport {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (o : Input (α := α) (n + 1)) : Finset (Input (α := α) n) :=
  Finset.univ.filter fun i => o.2 = incrementProfile (i.1, o.1) i.2 ∧ o.1 ∈ usedOutputs i.2 q

def collisionInsertion {n r : ℕ} (q : TensorPowerProfile (α × α) r) :
    Matrix (Input (α := α) (n + 1)) (Input (α := α) n) ℂ :=
  fun o i => if i ∈ collisionSupport q o then
    (Real.sqrt (i.2.val (i.1, o.1) + 1) : ℂ) / (Real.sqrt (Fintype.card α) : ℂ)
    else 0

theorem sqrt_amplitude_norm_sq (k d : ℕ) :
    ‖(Real.sqrt (k + 1) : ℂ) / (Real.sqrt d : ℂ)‖ ^ 2 = ((k + 1 : ℕ) : ℝ) / d := by
  rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _),
    div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  norm_cast

theorem collision_column_degree {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (i : Input (α := α) n) :
    (∑ o : Input (α := α) (n + 1), if i ∈ collisionSupport q o then (1 : ℝ) else 0) =
      ((usedOutputs i.2 q).card : ℝ) := by
  simp only [collisionSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Fintype.sum_prod_type]
  simp_rw [ite_and]
  simp

theorem collision_row_weight {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (o : Input (α := α) (n + 1)) :
    (∑ i ∈ collisionSupport q o, ‖collisionInsertion q o i‖ ^ 2) ≤
      (n + 1 : ℝ) / Fintype.card α := by
  have heq : (∑ i ∈ collisionSupport q o, ‖collisionInsertion q o i‖ ^ 2) =
      ∑ i : Input (α := α) n, if i ∈ collisionSupport q o then
        ((i.2.val (i.1, o.1) + 1 : ℕ) : ℝ) / Fintype.card α else 0 := by
    rw [← Finset.sum_filter]
    simp only [collisionSupport, Finset.filter_filter]
    apply Finset.sum_congr
    · ext i; simp
    · intro i hi
      have hm : i ∈ collisionSupport q o := by simpa [collisionSupport] using hi
      rw [collisionInsertion, if_pos hm, sqrt_amplitude_norm_sq]
  rw [heq]
  calc
    _ ≤ ∑ i : Input (α := α) n,
        if o.2 = incrementProfile (i.1, o.1) i.2 then
          ((i.2.val (i.1, o.1) + 1 : ℕ) : ℝ) / Fintype.card α else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h : i ∈ collisionSupport q o
      · have hm := (Finset.mem_filter.mp h).2.1
        rw [if_pos h, if_pos hm]
      · rw [if_neg h]
        split_ifs <;> positivity
    _ = ((∑ x : α, ∑ p : TensorPowerProfile (α × α) n,
          if o.2 = incrementProfile (x, o.1) p then p.val (x, o.1) + 1 else 0 : ℕ) : ℝ) /
        Fintype.card α := by
      simp only [Fintype.sum_prod_type, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero,
        Finset.sum_div, ite_div, zero_div]
    _ ≤ (n + 1 : ℝ) / Fintype.card α := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast predecessor_output_weight_sum_le o.2 o.1

/-- Collision creation has norm at most `sqrt((n+1)(n+r)/d)` on an
unrestricted fixed-length sector, with arbitrary repeated record pairs. -/
theorem collisionInsertion_norm_le {n r : ℕ} (q : TensorPowerProfile (α × α) r) :
    ‖collisionInsertion (n := n) q‖ ≤
      Real.sqrt (((n + 1 : ℝ) / Fintype.card α) * (n + r)) := by
  apply matrix_norm_le_sqrt (collisionInsertion q) (collisionSupport q)
    ((n + 1 : ℝ) / Fintype.card α) (n + r) (by positivity) (by positivity)
  · intro o i hi
    simp [collisionInsertion, hi]
  · exact collision_row_weight q
  · intro i
    rw [collision_column_degree]
    exact_mod_cast usedOutputs_card_le i.2 q

end
end ICO.MHBadInsertion
