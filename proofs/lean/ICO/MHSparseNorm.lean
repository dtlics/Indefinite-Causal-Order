import ICO.RecordingProcess
import Mathlib.Tactic

/-! Finite row-support Cauchy–Schwarz bounds used for unrestricted recording
operators. These are analytic lemmas, with all counting hypotheses explicit. -/

namespace ICO.MHSparseNorm

open QIT ICO.RecordingProcess
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 1000000

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem norm_sum_mul_sq_le (s : Finset a) (f g : a → ℂ) :
    ‖∑ j ∈ s, f j * g j‖ ^ 2 ≤ (∑ j ∈ s, ‖f j‖ ^ 2) * ∑ j ∈ s, ‖g j‖ ^ 2 := by
  calc
    _ ≤ (∑ j ∈ s, ‖f j‖ * ‖g j‖) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [norm_mul] using norm_sum_le s (fun j => f j * g j)
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq s (fun j => ‖f j‖) (fun j => ‖g j‖)

theorem support_sum_bound (S : b → Finset a) (v : a → ℂ) (C : ℝ)
    (hcol : ∀ j, (∑ i : b, if j ∈ S i then (1 : ℝ) else 0) ≤ C) :
    (∑ i : b, ∑ j ∈ S i, ‖v j‖ ^ 2) ≤ C * ∑ j : a, ‖v j‖ ^ 2 := by
  have hs (i : b) : (∑ j ∈ S i, ‖v j‖ ^ 2) =
      ∑ j : a, if j ∈ S i then ‖v j‖ ^ 2 else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  simp_rw [hs]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  calc
    _ = (∑ i : b, if j ∈ S i then (1 : ℝ) else 0) * ‖v j‖ ^ 2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)

theorem mulVec_square_sum_le (A : Matrix b a ℂ) (S : b → Finset a) (R C : ℝ)
    (hR : 0 ≤ R)
    (hsupport : ∀ i j, j ∉ S i → A i j = 0)
    (hrow : ∀ i, (∑ j ∈ S i, ‖A i j‖ ^ 2) ≤ R)
    (hcol : ∀ j, (∑ i : b, if j ∈ S i then (1 : ℝ) else 0) ≤ C)
    (v : a → ℂ) :
    (∑ i : b, ‖(A *ᵥ v) i‖ ^ 2) ≤ R * C * ∑ j : a, ‖v j‖ ^ 2 := by
  have hrowv (i : b) : ‖(A *ᵥ v) i‖ ^ 2 ≤ R * ∑ j ∈ S i, ‖v j‖ ^ 2 := by
    have heq : (A *ᵥ v) i = ∑ j ∈ S i, A i j * v j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      rw [hsupport i j hj, zero_mul]
    rw [heq]
    exact (norm_sum_mul_sq_le (S i) (A i) v).trans
      (mul_le_mul_of_nonneg_right (hrow i) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  calc
    _ ≤ ∑ i : b, R * ∑ j ∈ S i, ‖v j‖ ^ 2 := Finset.sum_le_sum (fun i _ => hrowv i)
    _ = R * (∑ i : b, ∑ j ∈ S i, ‖v j‖ ^ 2) := (Finset.mul_sum _ _ _).symm
    _ ≤ R * (C * ∑ j : a, ‖v j‖ ^ 2) := mul_le_mul_of_nonneg_left (support_sum_bound S v C hcol) hR
    _ = _ := by ring

theorem matrix_norm_le_sqrt (A : Matrix b a ℂ) (S : b → Finset a) (R C : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hsupport : ∀ i j, j ∉ S i → A i j = 0)
    (hrow : ∀ i, (∑ j ∈ S i, ‖A i j‖ ^ 2) ≤ R)
    (hcol : ∀ j, (∑ i : b, if j ∈ S i then (1 : ℝ) else 0) ≤ C) :
    ‖A‖ ≤ Real.sqrt (R * C) := by
  rw [← action_norm]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  have h := mulVec_square_sum_le A S R C hR hsupport hrow hcol (WithLp.ofLp v)
  have hv : ‖v‖ ^ 2 = ∑ j : a, ‖(WithLp.ofLp v) j‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
  have hAv : ‖action A v‖ ^ 2 = ∑ i : b, ‖(A *ᵥ WithLp.ofLp v) i‖ ^ 2 := by
    rw [action_apply, PiLp.norm_sq_eq_of_L2]
  have hsqrt := Real.sq_sqrt (mul_nonneg hR hC)
  have hnon : 0 ≤ Real.sqrt (R * C) * ‖v‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  rw [← hv, ← hAv] at h
  nlinarith [norm_nonneg (action A v)]

end
end ICO.MHSparseNorm
