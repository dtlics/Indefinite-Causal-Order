import ICO.SwitchStatistics
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Pi

/-! A concrete distribution for independent repetitions of a binary switch
measurement. Independence, boundedness and the mean are proved for the product
distribution, rather than supplied as hypotheses to the testing theorem. -/

namespace ICO.SwitchSampling

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

def repetitions (m : ℕ) (p : NNReal) (hp : p ≤ 1) :
    Measure (Fin m → Bool) :=
  Measure.pi (fun _ => (PMF.bernoulli p hp).toMeasure)

instance repetitions_probability (m : ℕ) (p : NNReal) (hp : p ≤ 1) :
    IsProbabilityMeasure (repetitions m p hp) := by
  unfold repetitions
  infer_instance

def outcome {m : ℕ} (i : Fin m) (ω : Fin m → Bool) : ℝ :=
  cond (ω i) 1 0

theorem outcomes_independent (m : ℕ) (p : NNReal) (hp : p ≤ 1) :
    iIndepFun (outcome (m := m)) (repetitions m p hp) := by
  exact iIndepFun_pi (X := fun _ (b : Bool) => cond b (1 : ℝ) 0)
    (by intro i; exact Measurable.aemeasurable (by fun_prop))

theorem outcome_measurable {m : ℕ} (i : Fin m) : Measurable (outcome i) := by
  unfold outcome
  fun_prop

theorem outcome_bounded {m : ℕ} (i : Fin m) (ω : Fin m → Bool) :
    outcome i ω ∈ Set.Icc (0 : ℝ) 1 := by
  unfold outcome
  cases ω i <;> norm_num

theorem outcome_mean {m : ℕ} (p : NNReal) (hp : p ≤ 1) (i : Fin m) :
    (∫ ω, outcome i ω ∂repetitions m p hp) = (p : ℝ) := by
  unfold outcome repetitions
  have h := integral_comp_eval
    (μ := fun _ : Fin m => (PMF.bernoulli p hp).toMeasure)
    (i := i) (f := fun b : Bool => cond b (1 : ℝ) 0)
    (by fun_prop)
  exact h.trans (PMF.bernoulli_expectation hp)

theorem eighty_high_error (p : NNReal) (hp : p ≤ 1) (hgap : (5 / 6 : ℝ) ≤ p) :
    (repetitions 80 p hp).real {ω | (∑ i, outcome i ω) < 60} < 1 / 3 := by
  exact SwitchStatistics.eighty_high_error outcome
    (outcomes_independent 80 p hp)
    (fun i => (outcome_measurable i).aemeasurable)
    (fun i => Filter.Eventually.of_forall (outcome_bounded i))
    (p : ℝ) (outcome_mean p hp) hgap

theorem eighty_low_error (p : NNReal) (hp : p ≤ 1) (hgap : (p : ℝ) ≤ 2 / 3) :
    (repetitions 80 p hp).real {ω | 60 ≤ ∑ i, outcome i ω} < 1 / 3 := by
  exact SwitchStatistics.eighty_low_error outcome
    (outcomes_independent 80 p hp)
    (fun i => (outcome_measurable i).aemeasurable)
    (fun i => Filter.Eventually.of_forall (outcome_bounded i))
    (p : ℝ) (outcome_mean p hp) hgap

#print axioms eighty_high_error
#print axioms eighty_low_error

end
end ICO.SwitchSampling
