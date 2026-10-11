import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar consequences of the proposed channel-testing distance bound

This module proves real inequalities and decision-theoretic reductions. It does
not define quantum strategies, Haar measure, channel access, or trace distance.
In particular, the transcript-distance premise in `testing_impossible` is an
explicit hypothesis, not a formalization of the physical indistinguishability
theorem. The radius parametrization is `d = r^16`, so `d^(1/8) = r^2` when
`r >= 0`; this module does not silently assume an identity for real powers.
-/

namespace ICO.TestingBounds

noncomputable section

/-- The scalar expression after writing the dimension as `d = r^16`. -/
def distanceBound (q d r : ℝ) : ℝ :=
  18 * (2 * q) * (2 * q + 1) / r ^ 2 +
    4 * q / Real.sqrt (d - 2 * q) + q ^ 2 / d

/-- The query threshold forces a large positive radius. -/
theorem radius_ge_hundred {q r : ℝ} (hq : 1 ≤ q)
    (hqr : q ≤ r / 100) : 100 ≤ r := by
  linarith

/-- A convenient elementary dimension estimate, avoiding fractional powers. -/
theorem pow_sixteen_ge_two_sq {r : ℝ} (hr : 2 ≤ r) :
    2 * r ^ 2 ≤ r ^ 16 := by
  have hr1 : 1 ≤ r := by linarith
  have hp : r ≤ r ^ 14 := by
    simpa using (pow_le_pow_right₀ hr1 (show (1 : ℕ) ≤ 14 by norm_num))
  have h14 : 2 ≤ r ^ 14 := le_trans hr hp
  calc
    2 * r ^ 2 ≤ r ^ 14 * r ^ 2 :=
      mul_le_mul_of_nonneg_right h14 (sq_nonneg r)
    _ = r ^ 16 := by ring

/-- All denominators in the testing bound are positive in the relevant range. -/
theorem threshold_denominators {q d r : ℝ} (hq : 1 ≤ q)
    (hqr : q ≤ r / 100) (hd : 2 * r ^ 2 ≤ d) :
    0 < r ∧ 0 < d ∧ 2 * q < d ∧ r ≤ Real.sqrt (d - 2 * q) := by
  have hr := radius_ge_hundred hq hqr
  have hr0 : 0 < r := by linarith
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr0
  have hsq : r ≤ r ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt hr0) (show 0 ≤ r - 1 by linarith)]
  have hdiff : r ^ 2 ≤ d - 2 * q := by nlinarith
  have hd0 : 0 < d := by linarith
  have hquery : 2 * q < d := by linarith
  exact ⟨hr0, hd0, hquery, Real.le_sqrt_of_sq_le hdiff⟩

/-- A slightly sharper scalar constant than the original `0.068` estimate. -/
theorem distanceBound_le {q d r : ℝ} (hq : 1 ≤ q)
    (hqr : q ≤ r / 100) (hd : 2 * r ^ 2 ≤ d) :
    distanceBound q d r ≤ 509 / 10000 := by
  obtain ⟨hr0, hd0, _, hsqrt⟩ := threshold_denominators hq hqr hd
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr0
  have hq0 : 0 ≤ q := by linarith
  have hq2 : q ^ 2 ≤ r ^ 2 / 10000 := by
    have h := mul_self_le_mul_self hq0 hqr
    nlinarith
  have hq2q : q ≤ q ^ 2 := by
    nlinarith [mul_nonneg hq0 (show 0 ≤ q - 1 by linarith)]
  have hfirst : 18 * (2 * q) * (2 * q + 1) / r ^ 2 ≤ 108 / 10000 := by
    apply (div_le_iff₀ hr2).2
    nlinarith
  have hsqrt0 : 0 < Real.sqrt (d - 2 * q) := lt_of_lt_of_le hr0 hsqrt
  have hsecond : 4 * q / Real.sqrt (d - 2 * q) ≤ 4 / 100 := by
    apply (div_le_iff₀ hsqrt0).2
    linarith
  have hthird : q ^ 2 / d ≤ 1 / 10000 := by
    apply (div_le_iff₀ hd0).2
    nlinarith [sq_nonneg r]
  unfold distanceBound
  linarith

theorem distanceBound_lt_one_third {q d r : ℝ} (hq : 1 ≤ q)
    (hqr : q ≤ r / 100) (hd : 2 * r ^ 2 ≤ d) :
    distanceBound q d r < 1 / 3 := by
  have h := distanceBound_le hq hqr hd
  linarith

/-- The same estimate specialized to the radius parametrization `d=r^16`. -/
theorem distanceBound_pow_sixteen_lt {q r : ℝ} (hq : 1 ≤ q)
    (hqr : q ≤ r / 100) : distanceBound q (r ^ 16) r < 1 / 3 := by
  apply distanceBound_lt_one_third hq hqr
  apply pow_sixteen_ge_two_sq
  have h := radius_ge_hundred hq hqr
  linarith

/-- The scalar price of conditioning the independent-basis low prior. -/
def hiddenOutcomeBound (q d r : ℝ) : ℝ :=
  3 * distanceBound q d r + 6 / (d + 1)

theorem hiddenOutcomeBound_lt_one_third {q d r : ℝ} (hq : 1 ≤ q)
    (hqr : q ≤ r / 100) (hd : 2 * r ^ 2 ≤ d) :
    hiddenOutcomeBound q d r < 1 / 3 := by
  have hr := radius_ge_hundred hq hqr
  have hr0 : 0 ≤ r := by linarith
  have hr2 : (100 : ℝ) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by norm_num) hr 2
  have hdlarge : 20000 ≤ d := by nlinarith
  have hdenom : 0 < d + 1 := by linarith
  have hcondition : 6 / (d + 1) ≤ 6 / 20000 := by
    apply (div_le_iff₀ hdenom).2
    linarith
  have h := distanceBound_le hq hqr hd
  unfold hiddenOutcomeBound
  linarith

theorem hiddenOutcomeBound_pow_sixteen_lt {q r : ℝ} (hq : 1 ≤ q)
    (hqr : q ≤ r / 100) : hiddenOutcomeBound q (r ^ 16) r < 1 / 3 := by
  apply hiddenOutcomeBound_lt_one_third hq hqr
  apply pow_sixteen_ge_two_sq
  have h := radius_ge_hundred hq hqr
  linarith

/-- Successful promised decision creates a probability gap of at least `1/3`. -/
theorem decision_gap {pHigh pLow : ℝ} (hHigh : 2 / 3 ≤ pHigh)
    (hLow : pLow ≤ 1 / 3) : 1 / 3 ≤ |pHigh - pLow| := by
  have habs : pHigh - pLow ≤ |pHigh - pLow| := le_abs_self _
  linarith

/-- An explicit scalar form of the measurement-to-distance reduction. -/
theorem distance_required_for_decision {pHigh pLow δ : ℝ}
    (hHigh : 2 / 3 ≤ pHigh) (hLow : pLow ≤ 1 / 3)
    (hMeasurement : |pHigh - pLow| ≤ δ) : 1 / 3 ≤ δ :=
  le_trans (decision_gap hHigh hLow) hMeasurement

/-- Equal-prior success is at most `(1+δ)/2` under a probability-gap bound. -/
theorem average_success_le {pHigh pLow δ : ℝ}
    (hMeasurement : |pHigh - pLow| ≤ δ) :
    (pHigh + (1 - pLow)) / 2 ≤ (1 + δ) / 2 := by
  have habs := le_abs_self (pHigh - pLow)
  linarith

/-- Conditional on the physical transcript-distance bridge, the small-query
    regime cannot solve the decision problem. No quantum premise is hidden. -/
theorem testing_impossible {q d r pHigh pLow δ : ℝ}
    (hq : 1 ≤ q) (hqr : q ≤ r / 100) (hd : 2 * r ^ 2 ≤ d)
    (hMeasurement : |pHigh - pLow| ≤ δ)
    (hPhysicalBridge : δ ≤ distanceBound q d r)
    (hHigh : 2 / 3 ≤ pHigh) (hLow : pLow ≤ 1 / 3) : False := by
  have hnecessary := distance_required_for_decision hHigh hLow hMeasurement
  have hsmall := distanceBound_lt_one_third hq hqr hd
  linarith

theorem hidden_outcome_testing_impossible {q d r pHigh pLow δ : ℝ}
    (hq : 1 ≤ q) (hqr : q ≤ r / 100) (hd : 2 * r ^ 2 ≤ d)
    (hMeasurement : |pHigh - pLow| ≤ δ)
    (hPhysicalBridge : δ ≤ hiddenOutcomeBound q d r)
    (hHigh : 2 / 3 ≤ pHigh) (hLow : pLow ≤ 1 / 3) : False := by
  have hnecessary := distance_required_for_decision hHigh hLow hMeasurement
  have hsmall := hiddenOutcomeBound_lt_one_third hq hqr hd
  linarith

/-- In dimension at least two, the depolarizing witness is on the low side. -/
theorem depolarizing_low_promise {d : ℝ} (hd : 2 ≤ d) :
    1 / d ^ 2 ≤ 1 / 3 := by
  have hd0 : 0 < d := by linarith
  apply (div_le_iff₀ (sq_pos_of_pos hd0)).2
  nlinarith [sq_nonneg (d - 2)]

/-- The control-measurement probability `(1+v)/2` has the promised gap. -/
theorem switch_high_probability {v : ℝ} (hv : 2 / 3 ≤ v) :
    5 / 6 ≤ (1 + v) / 2 := by linarith

theorem switch_low_probability {v : ℝ} (hv : v ≤ 1 / 3) :
    (1 + v) / 2 ≤ 2 / 3 := by linarith

theorem switch_threshold_margin :
    (5 / 6 : ℝ) - 3 / 4 = 1 / 12 ∧ 3 / 4 - 2 / 3 = 1 / 12 := by
  norm_num

theorem exp_neg_two_lt_one_third : Real.exp (-2 : ℝ) < 1 / 3 := by
  have hthree : (3 : ℝ) < Real.exp 2 := by
    have h := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)
    norm_num at h
    exact h
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_lt_iff₀ (Real.exp_pos 2)).2
  linarith

/-- The numerical Hoeffding tail at margin `1/12` is below `1/3` after
    144 repetitions. Independence and the concentration theorem are separate
    mathematical premises, not asserted by this scalar lemma. -/
theorem hoeffding_tail_lt_one_third {m : ℝ} (hm : 144 ≤ m) :
    Real.exp (-2 * m * (1 / 12) ^ 2) < 1 / 3 := by
  calc
    Real.exp (-2 * m * (1 / 12) ^ 2) ≤ Real.exp (-2 : ℝ) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ < 1 / 3 := exp_neg_two_lt_one_third

theorem switch_repetition_error_bound {m failure : ℝ} (hm : 144 ≤ m)
    (hConcentration : failure ≤ Real.exp (-2 * m * (1 / 12) ^ 2)) :
    failure < 1 / 3 :=
  lt_of_le_of_lt hConcentration (hoeffding_tail_lt_one_third hm)

/-- An algorithm making no observations has the same acceptance probability
    on both hypotheses, so the two success requirements are inconsistent. -/
theorem zero_query_impossible {p : ℝ}
    (hHigh : 2 / 3 ≤ p) (hLow : p ≤ 1 / 3) : False := by linarith

end

end ICO.TestingBounds

