import QIT.HypothesisTesting.Basic
import ICO.TestingBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ICO.QuantumDecision
open QIT
noncomputable section
variable {a : Type*} [Fintype a] [DecidableEq a]

/-- The probability gap of an actual Born-rule binary measurement is bounded
by trace distance; no scalar measurement-gap hypothesis is assumed. -/
theorem accept_gap_le_traceDistance (T : BinaryHypothesisTest a) (ρ σ : State a) :
    (T.acceptProb ρ : ℝ) - (T.acceptProb σ : ℝ) ≤ ρ.normalizedTraceDistance σ := by
  have hh := T.helstrom_equalPriorError_lower_bound ρ σ
  rw [T.equalPriorError_eq_half_one_sub_score] at hh
  have hp := T.acceptProb_eq_trace_re ρ
  have hq := T.acceptProb_eq_trace_re σ
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at hh
  rw [← hp, ← hq] at hh
  linarith

theorem successful_decision_requires_distance (T : BinaryHypothesisTest a) (ρ σ : State a)
    (hρ : 2 / 3 ≤ (T.acceptProb ρ : ℝ))
    (hσ : (T.acceptProb σ : ℝ) ≤ 1 / 3) :
    1 / 3 ≤ ρ.normalizedTraceDistance σ := by
  have hh := accept_gap_le_traceDistance T ρ σ
  linarith

theorem radius_power_sixteen (d : ℝ) (hd : 0 ≤ d) :
    (d ^ (1 / 16 : ℝ)) ^ (16 : ℕ) = d := by
  convert Real.rpow_inv_natCast_pow hd (show (16 : ℕ) ≠ 0 by norm_num) using 1 <;> norm_num

/-- The quantitative small-query contradiction uses actual states and an actual
POVM. Only the separate transcript-comparison theorem remains a premise. -/
theorem physical_testing_impossible (T : BinaryHypothesisTest a) (ρ σ : State a)
    (q d : ℝ) (hd : 0 ≤ d) (hq : 1 ≤ q) (hqd : q ≤ d ^ (1 / 16 : ℝ) / 100)
    (hPhysical : ρ.normalizedTraceDistance σ ≤
      ICO.TestingBounds.distanceBound q d (d ^ (1 / 16 : ℝ)))
    (hρ : 2 / 3 ≤ (T.acceptProb ρ : ℝ))
    (hσ : (T.acceptProb σ : ℝ) ≤ 1 / 3) : False := by
  have hs := ICO.TestingBounds.distanceBound_pow_sixteen_lt hq hqd
  rw [radius_power_sixteen d hd] at hs
  have hn := successful_decision_requires_distance T ρ σ hρ hσ
  linarith

#print axioms accept_gap_le_traceDistance
#print axioms successful_decision_requires_distance
#print axioms physical_testing_impossible
end
end ICO.QuantumDecision
