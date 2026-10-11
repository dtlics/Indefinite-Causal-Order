import ICO.MHAveragedHybrid
import ICO.MHProjectedMeanLoss

/-! Converting averaged recording overlap into a physical isometric-run
hybrid. The deficit estimate does not square a potentially negative overlap. -/
namespace ICO.MHProjectedProtocol
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : Type*} [Fintype H]

theorem mass_deficit_le_overlap (x y : EuclideanSpace ℂ H)
    (hx : ‖x‖≤1) (hy : ‖y‖≤1) :
    1-‖x‖^2≤2*(1-(⟪x,y⟫_ℂ).re) := by
  have hh := (Complex.re_le_norm (⟪x,y⟫_ℂ)).trans (norm_inner_le_norm x y)
  have hm := mul_le_mul_of_nonneg_left hy (norm_nonneg x)
  nlinarith [sq_nonneg (‖x‖-1)]

theorem mean_step_defect (x y e : Ω → EuclideanSpace ℂ H)
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

theorem accumulated_defects (a : ℕ → ℝ) (q : ℕ) (R : ℝ)
    (hinit : a 0≤0)
    (hstep : ∀ t<q, a (t+1)≤a t+9*((t:ℝ)+1)/R) :
    a q≤9*(q:ℝ)*((q:ℝ)+1)/(2*R) := by
  have hg : ∀ k≤q, a k≤9*(k:ℝ)*((k:ℝ)+1)/(2*R) := by
    intro k
    induction k with
    | zero => intro _; simpa using hinit
    | succ k ih =>
      intro hk
      have hkq : k<q := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hk
      have hi := ih (Nat.le_of_lt hkq)
      have hh := hstep k hkq
      calc
        _ ≤ 9*(k:ℝ)*((k:ℝ)+1)/(2*R)+9*((k:ℝ)+1)/R := by linarith
        _ = _ := by push_cast; ring
  exact hg q le_rfl

theorem final_error_constant (q : ℕ) (R : ℝ) (hR : 0<R) (hq : 1≤q) :
    9*(q:ℝ)*((q:ℝ)+1)/(2*R)+9*(q:ℝ)/R≤9*(q:ℝ)*((q:ℝ)+1)/R := by
  have hqr : (1:ℝ)≤q := by exact_mod_cast hq
  have he : 9*(q:ℝ)*((q:ℝ)+1)/(2*R)+9*(q:ℝ)/R =
    (9*(q:ℝ)*((q:ℝ)+1)/2+9*(q:ℝ))/R := by ring
  rw [he]
  apply (div_le_div_iff_of_pos_right hR).2
  nlinarith

#print axioms mass_deficit_le_overlap
#print axioms mean_step_defect
#print axioms accumulated_defects
end
end ICO.MHProjectedProtocol
