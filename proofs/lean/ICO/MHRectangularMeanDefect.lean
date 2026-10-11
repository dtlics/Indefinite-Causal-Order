import ICO.MHProjectedProtocol
namespace ICO.MHRectangularMeanDefect
open MeasureTheory ICO.MHProjectedProtocol
open scoped InnerProductSpace
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : Type*} [Fintype H]
theorem mean_step_defect {E : Type*} [Fintype E] (x y : Ω → EuclideanSpace ℂ H) (e : Ω → EuclideanSpace ℂ E)
    (hx : ∀ ω, ‖x ω‖≤1) (hy : ∀ ω, ‖y ω‖≤1)
    (he : ∀ ω, ‖e ω‖^2≤1-‖x ω‖^2)
    (hinner : Integrable (fun ω => (⟪x ω,y ω⟫_ℂ).re) μ)
    (heint : Integrable (fun ω => ‖e ω‖) μ)
    (hesq : Integrable (fun ω => ‖e ω‖^2) μ)
    (t : ℕ) (R : ℝ) (hR : 0<R)
    (hoverlap : 1-35*(t:ℝ)^2/R^2≤∫ ω, (⟪x ω,y ω⟫_ℂ).re ∂μ) :
    (∫ ω, ‖e ω‖ ∂μ)≤9*(t:ℝ)/R := by
  have hp (ω : Ω) : ‖e ω‖^2≤2-2*(⟪x ω,y ω⟫_ℂ).re := by
    have hh := (he ω).trans (mass_deficit_le_overlap (x ω) (y ω) (hx ω) (hy ω))
    linarith
  have hh := integral_mono hesq ((integrable_const (2:ℝ)).sub (hinner.const_mul 2)) hp
  change (∫ ω, ‖e ω‖^2 ∂μ)≤∫ ω, 2-2*(⟪x ω,y ω⟫_ℂ).re ∂μ at hh
  rw [integral_sub (integrable_const _) (hinner.const_mul 2),integral_const_mul] at hh
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hh
  have hm := ICO.MHAveragedHybrid.mean_square_ge (fun ω => ‖e ω‖) heint hesq
  change (∫ ω, ‖e ω‖ ∂μ)^2≤∫ ω, ‖e ω‖^2 ∂μ at hm
  have hn : 0≤∫ ω, ‖e ω‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  have hq : 0≤9*(t:ℝ)/R := by positivity
  have hcost : 0≤(t:ℝ)^2/R^2 := by positivity
  have hsq : (9*(t:ℝ)/R)^2=81*(t:ℝ)^2/R^2 := by ring
  have h70 : 2*(35*(t:ℝ)^2/R^2)≤81*(t:ℝ)^2/R^2 := by
    convert mul_le_mul_of_nonneg_right (show (70:ℝ)≤81 by norm_num) hcost using 1 <;> ring
  rw [← hsq] at h70
  have hdef : (∫ ω, ‖e ω‖^2 ∂μ)≤2*(35*(t:ℝ)^2/R^2) := by
    have heq : 2*(35*(t:ℝ)^2/R^2)=2*(1-(1-35*(t:ℝ)^2/R^2)) := by ring
    rw [heq]
    linarith
  have htotal := hm.trans (hdef.trans h70)
  nlinarith


#print axioms mean_step_defect
end
end ICO.MHRectangularMeanDefect
