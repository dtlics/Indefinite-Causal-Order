import ICO.QuantumDecision
import ICO.LudersPromise
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Promised testing under the actual independent-basis prior. The bad
promise mass is bounded directly, without normalizing a conditional state. -/
namespace ICO.AveragedPromiseDecision
open MeasureTheory
noncomputable section
set_option maxHeartbeats 1200000
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem low_mean_le (f : Ω→ℝ) (hf : Integrable f μ) (bad : Set Ω)
    (hbad : MeasurableSet bad) (hgood : ∀ ω∉bad, f ω≤1/3)
    (hbound : ∀ ω, f ω≤1) :
    (∫ ω, f ω ∂μ)≤1/3+μ.real bad := by
  have hind : Integrable (bad.indicator (fun _ : Ω => (1:ℝ))) μ :=
    (integrable_const _).indicator hbad
  have hp (ω : Ω) : f ω≤1/3+bad.indicator (fun _ : Ω => (1:ℝ)) ω := by
    by_cases hw : ω∈bad
    · rw [Set.indicator_of_mem hw]
      linarith [hbound ω]
    · rw [Set.indicator_of_notMem hw,add_zero]
      exact hgood ω hw
  have hh := integral_mono hf ((integrable_const (1/3:ℝ)).add hind) hp
  change (∫ ω, f ω ∂μ)≤∫ ω, (1/3:ℝ)+bad.indicator (fun _ : Ω => (1:ℝ)) ω ∂μ at hh
  rw [integral_add (integrable_const _) hind,integral_const,integral_indicator_const _ hbad] at hh
  simpa only [probReal_univ,smul_eq_mul,one_mul,mul_one] using hh

theorem high_mean_ge (f : Ω→ℝ) (hf : Integrable f μ) (hhigh : ∀ ω, 2/3≤f ω) :
    (2/3:ℝ)≤∫ ω, f ω ∂μ := by
  have hh := integral_mono (integrable_const (2/3:ℝ)) hf hhigh
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

theorem averaged_test_impossible (high low : Ω→ℝ)
    (hh : Integrable high μ) (hl : Integrable low μ)
    (bad : Set Ω) (hbad : MeasurableSet bad)
    (hhigh : ∀ ω, 2/3≤high ω) (hgood : ∀ ω∉bad, low ω≤1/3)
    (hbound : ∀ ω, low ω≤1) (δ η : ℝ)
    (hgap : (∫ ω, high ω ∂μ)-(∫ ω, low ω ∂μ)≤δ)
    (hmass : μ.real bad≤η) (hsmall : δ+η<1/3) : False := by
  have hH := high_mean_ge high hh hhigh
  have hL := low_mean_le low hl bad hbad hgood hbound
  linarith

#print axioms low_mean_le
#print axioms averaged_test_impossible
end
end ICO.AveragedPromiseDecision
