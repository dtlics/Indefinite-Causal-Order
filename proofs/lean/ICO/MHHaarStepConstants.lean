import ICO.MHAveragedHybrid

/-! Explicit constants in the averaged overlap recurrence, with the radius
R parametrizing the dimension as d=R^8. -/
namespace ICO.MHHaarStepConstants
noncomputable section
set_option maxHeartbeats 2000000

theorem sqrt_quot_bound (t R : ℝ) (ht : 1≤t) (hR : 1≤R) :
    Real.sqrt (t/R^8)≤t/R^4 := by
  have hRp : 0<R := by linarith
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · have htt : t≤t^2 := by nlinarith
    have hr : 0<R^8 := pow_pos hRp _
    field_simp
    nlinarith

theorem loss_sqrt_bound (t R : ℝ) (ht : 1≤t) (hR : 1≤R) :
    Real.sqrt (6*t*Real.sqrt (t/R^8))≤3*t/R^2 := by
  have hRp : 0<R := by linarith
  have hh := sqrt_quot_bound t R ht hR
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · have hmul := mul_le_mul_of_nonneg_left hh (show 0≤6*t by linarith)
    have he : (3*t/R^2)^2=9*t^2/R^4 := by field_simp; ring
    rw [he]
    have hnon : 0≤t^2/R^4 := by positivity
    calc
      _ ≤ 6*t*(t/R^4) := hmul
      _ = 6*(t^2/R^4) := by ring
      _ ≤ 9*(t^2/R^4) := by nlinarith
      _ = _ := by ring

theorem covariance_sqrt_bound (t R : ℝ) (ht : 1≤t) (hR : 1≤R) :
    16*Real.sqrt (2*t*(t+1)/R^8)≤32*t/R^2 := by
  have hRp : 0<R := by linarith
  have hh : Real.sqrt (2*t*(t+1)/R^8)≤2*t/R^4 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have he : (2*t/R^4)^2=4*t^2/R^8 := by field_simp; ring
      rw [he]
      apply (div_le_div_iff_of_pos_right (pow_pos hRp 8)).2
      nlinarith
  have hpow : R^2≤R^4 := pow_le_pow_right₀ hR (by norm_num)
  have hdiv : 32*t/R^4≤32*t/R^2 :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hRp 2) hpow
  calc
    _ ≤ 16*(2*t/R^4) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = 32*t/R^4 := by ring
    _ ≤ _ := hdiv

theorem one_step_loss_bound (t : ℕ) (R : ℝ) (hR : 1≤R) :
    Real.sqrt (6*(t:ℝ)*Real.sqrt ((t:ℝ)/R^8))+
      16*Real.sqrt (2*(t:ℝ)*(t+1)/R^8)≤35*(t:ℝ)/R^2 := by
  by_cases h0 : t=0
  · simp [h0]
  · have ht : (1:ℝ)≤t := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
    have h1 := loss_sqrt_bound (t:ℝ) R ht hR
    have h2 := covariance_sqrt_bound (t:ℝ) R ht hR
    calc
      _ ≤ 3*(t:ℝ)/R^2+32*(t:ℝ)/R^2 := add_le_add h1 h2
      _ = _ := by ring

#print axioms one_step_loss_bound
end
end ICO.MHHaarStepConstants
