import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Exact numerical constants used by the switch estimator and the
simulation-to-testing reduction. The concentration theorem and independence
of repeated experiments are separate operational obligations. -/

namespace ICO.ProbabilityConstants

theorem exp_neg_ten_ninths_lt_third : Real.exp (-(10 / 9 : ℝ)) < 1 / 3 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 10 / 9) 5
  norm_num [Finset.sum_range_succ] at h
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_lt_iff₀ (Real.exp_pos _)).2
  linarith

theorem exp_neg_seventy_one_sixty_fourths_lt_third :
    Real.exp (-(71 / 64 : ℝ)) < 1 / 3 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 71 / 64) 5
  norm_num [Finset.sum_range_succ] at h
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_lt_iff₀ (Real.exp_pos _)).2
  linarith

theorem eighty_switch_repetitions {m : ℝ} (hm : 80 ≤ m) :
    Real.exp (-2 * m * (1 / 12) ^ 2) < 1 / 3 := by
  calc
    Real.exp (-2 * m * (1 / 12) ^ 2) ≤ Real.exp (-(10 / 9 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ < 1 / 3 := exp_neg_ten_ninths_lt_third

theorem simulator_repetitions {m : ℝ} (hm : 142 ≤ m) :
    Real.exp (-2 * m * (1 / 16) ^ 2) < 1 / 3 := by
  calc
    Real.exp (-2 * m * (1 / 16) ^ 2) ≤ Real.exp (-(71 / 64 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ < 1 / 3 := exp_neg_seventy_one_sixty_fourths_lt_third

#print axioms eighty_switch_repetitions
#print axioms simulator_repetitions
end ICO.ProbabilityConstants
