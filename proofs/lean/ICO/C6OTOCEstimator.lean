import ICO.C6OTOC

/-! Actual independent switch outcomes estimate the phase-averaged OTOC.
The product distribution supplies independence, boundedness and expectation;
no concentration or quantum-observable premise is assumed. -/
namespace ICO.C6OTOCEstimator
open MeasureTheory ProbabilityTheory QIT ICO.SwitchSampling ICO.C6SwitchTest ICO.C6OTOC
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false

def estimate (m : ℕ) (ω : Fin m → Bool) : ℝ :=
  2*(∑i,outcome i ω)/(m:ℝ)-1

theorem bernoulli_error {m : ℕ} (hm : 0<m) (p : NNReal) (hp : p≤1)
    (ε : ℝ) (hε : 0≤ε) :
    (repetitions m p hp).real {ω | ε < |estimate m ω-(2*(p:ℝ)-1)|} ≤
      2*Real.exp (-(m:ℝ)*ε^2/2) := by
  have hu := ICO.SwitchStatistics.upper_tail hm outcome (outcomes_independent m p hp)
    (fun i => (outcome_measurable i).aemeasurable)
    (fun i => Filter.Eventually.of_forall (outcome_bounded i))
    (p:ℝ) (ε/2) (outcome_mean p hp) (by positivity)
  have hl := ICO.SwitchStatistics.lower_tail hm outcome (outcomes_independent m p hp)
    (fun i => (outcome_measurable i).aemeasurable)
    (fun i => Filter.Eventually.of_forall (outcome_bounded i))
    (p:ℝ) (ε/2) (outcome_mean p hp) (by positivity)
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hsub : {ω | ε < |estimate m ω-(2*(p:ℝ)-1)|} ⊆
      {ω | (∑i,outcome i ω)≤(m:ℝ)*((p:ℝ)-ε/2)} ∪
      {ω | (m:ℝ)*((p:ℝ)+ε/2)≤∑i,outcome i ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, estimate] at hω
    rcases lt_abs.mp hω with hω | hω
    · right
      have hx : (p:ℝ)+ε/2≤(∑i,outcome i ω)/(m:ℝ) := by
        rw [mul_div_assoc] at hω
        linarith
      simpa only [mul_comm] using (le_div_iff₀ hm').mp hx
    · left
      have hx : (∑i,outcome i ω)/(m:ℝ)≤(p:ℝ)-ε/2 := by
        rw [mul_div_assoc] at hω
        linarith
      simpa only [mul_comm] using (div_le_iff₀ hm').mp hx
  have hb := (measureReal_mono (μ := repetitions m p hp) hsub).trans
    (measureReal_union_le (μ := repetitions m p hp) _ _)
  have he : -2*(m:ℝ)*(ε/2)^2=-(m:ℝ)*ε^2/2 := by ring
  rw [he] at hu hl
  linarith

theorem two_exp_neg_two_lt_third : 2*Real.exp (-2:ℝ)<1/3 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤2) 4
  norm_num [Finset.sum_range_succ] at h
  rw [Real.exp_neg, inv_eq_one_div, ← div_eq_mul_one_div]
  apply (div_lt_iff₀ (Real.exp_pos 2)).mpr
  linarith

theorem sufficient_samples {m : ℕ} (hm : 0<m) (p : NNReal) (hp : p≤1)
    (ε : ℝ) (hε : 0<ε) (hs : 4/ε^2≤(m:ℝ)) :
    (repetitions m p hp).real {ω | ε < |estimate m ω-(2*(p:ℝ)-1)|}<1/3 := by
  have hpow : (0:ℝ)<ε^2 := sq_pos_of_pos hε
  have hs' := (div_le_iff₀ hpow).mp hs
  have he : -(m:ℝ)*ε^2/2≤-2 := by nlinarith
  exact (bernoulli_error hm p hp ε hε.le).trans_lt
    ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num)).trans_lt
      two_exp_neg_two_lt_third)

variable {d : ℕ} [NeZero d]

theorem switch_estimation (U V : Matrix.unitaryGroup (ZMod d) ℂ)
    (ε : ℝ) (hε : 0<ε) :
    let m := Nat.ceil (4/ε^2)
    (repetitions m (plusProbability U V) (plusProbability_le_one U V)).real
      {ω | ε < |estimate m ω-phaseOTOC (U:CMatrix (ZMod d)) (V:CMatrix (ZMod d))|}<1/3 := by
  dsimp only
  have hpos : 0<Nat.ceil (4/ε^2) := by
    exact Nat.one_le_ceil_iff.mpr (by positivity)
  have h := sufficient_samples hpos (plusProbability U V) (plusProbability_le_one U V)
    ε hε (Nat.le_ceil _)
  have hv := phaseOTOC_born U V
  have he : 2*(plusProbability U V:ℝ)-1 =
      phaseOTOC (U:CMatrix (ZMod d)) (V:CMatrix (ZMod d)) := by linarith
  simpa only [he] using h

theorem call_count (ε : ℝ) (hε : 0<ε) :
    (2*Nat.ceil (4/ε^2):ℝ)<8/ε^2+2 := by
  have hc := Nat.ceil_lt_add_one (show (0:ℝ)≤4/ε^2 by positivity)
  calc
    2*(Nat.ceil (4/ε^2):ℝ) < 2*(4/ε^2+1) := by linarith
    _ = 8/ε^2+2 := by ring

#print axioms switch_estimation
#print axioms call_count
end
end ICO.C6OTOCEstimator
