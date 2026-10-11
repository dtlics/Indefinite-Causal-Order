import ICO.PureHybrid
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! Averaged overlap and distance estimates for actual vector families.
The local operator identities and twirled-projector estimate are kept as
explicit premises until the concrete Ma--Huang operators discharge them. -/
namespace ICO.MHAveragedHybrid
open Matrix QIT MeasureTheory
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem mean_square_ge (f : Ω → ℝ) (hf : Integrable f μ)
    (hfsq : Integrable (fun ω => (f ω)^2) μ) :
    (∫ ω, f ω ∂μ)^2 ≤ ∫ ω, (f ω)^2 ∂μ := by
  let m := ∫ ω, f ω ∂μ
  have he : (fun ω => (f ω - m)^2) =
      (fun ω => (f ω)^2 - (2*m)*f ω + m^2) := by
    funext ω; ring
  have h0 : 0 ≤ ∫ ω, (f ω - m)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  rw [he] at h0
  have hi1 := integral_add (hfsq.sub (hf.const_mul (2*m))) (integrable_const (m^2))
  have hi2 := integral_sub hfsq (hf.const_mul (2*m))
  simp only [Pi.add_apply, Pi.sub_apply] at hi1 hi2
  rw [hi1, hi2, integral_const_mul] at h0
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h0
  dsimp only [m] at h0
  nlinarith

theorem mean_le_sqrt_mean_square (f : Ω → ℝ) (hf : Integrable f μ)
    (hfsq : Integrable (fun ω => (f ω)^2) μ) :
    (∫ ω, f ω ∂μ) ≤ Real.sqrt (∫ ω, (f ω)^2 ∂μ) :=
  Real.le_sqrt_of_sq_le (mean_square_ge f hf hfsq)

theorem averaged_loss_step (a b f : Ω → ℝ) (ε α : ℝ)
    (ha : Integrable a μ) (hb : Integrable b μ) (hf : Integrable f μ)
    (hfsq : Integrable (fun ω => (f ω)^2) μ)
    (hstep : ∀ ω, a ω - f ω - ε ≤ b ω)
    (hsq : (∫ ω, (f ω)^2 ∂μ) ≤ α) :
    (∫ ω, a ω ∂μ) - Real.sqrt α - ε ≤ ∫ ω, b ω ∂μ := by
  have hh := integral_mono ((ha.sub hf).sub (integrable_const _)) hb hstep
  have hi1 := integral_sub (ha.sub hf) (integrable_const ε)
  have hi2 := integral_sub ha hf
  simp only [Pi.sub_apply] at hh hi1 hi2
  rw [hi1, hi2] at hh
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
  have hhf := (mean_le_sqrt_mean_square f hf hfsq).trans (Real.sqrt_le_sqrt hsq)
  linarith

theorem overlap_recurrence (a : ℕ → ℝ) (q : ℕ) (R : ℝ) (hR : 0 < R)
    (hinit : 1 ≤ a 0)
    (hstep : ∀ t < q, a t - 35*(t : ℝ)/R^2 ≤ a (t+1)) :
    1 - 35*(q : ℝ)^2/R^2 ≤ a q := by
  have hg : ∀ k ≤ q, 1 - 35*(k : ℝ)^2/R^2 ≤ a k := by
    intro k
    induction k with
    | zero => intro _; simpa using hinit
    | succ k ih =>
      intro hk
      have hkq : k < q := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hk
      have hh := hstep k hkq
      have hi := ih (Nat.le_of_lt hkq)
      have hs : 0 < R^2 := sq_pos_of_pos hR
      simp only [Nat.cast_add, Nat.cast_one]
      have he : 35*((k : ℝ)+1)^2/R^2 =
          35*(k : ℝ)^2/R^2 + 70*(k : ℝ)/R^2 + 35/R^2 := by ring
      rw [he]
      have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
      have h1 : 0 ≤ 35*(k : ℝ)/R^2 := by positivity
      have h2 : 0 ≤ 35/R^2 := by positivity
      ring_nf at hh hi h1 h2 ⊢
      linarith
  exact hg q le_rfl

variable {H : Type*} [Fintype H]

theorem mean_vector_distance_sq (x y : Ω → EuclideanSpace ℂ H)
    (hx : ∀ ω, ‖x ω‖ ≤ 1) (hy : ∀ ω, ‖y ω‖ ≤ 1)
    (hinner : Integrable (fun ω => (⟪x ω, y ω⟫_ℂ).re) μ)
    (hdist : Integrable (fun ω => ‖x ω - y ω‖^2) μ) (c : ℝ)
    (hoverlap : 1-c ≤ ∫ ω, (⟪x ω, y ω⟫_ℂ).re ∂μ) :
    (∫ ω, ‖x ω-y ω‖^2 ∂μ) ≤ 2*c := by
  have hp (ω : Ω) : ‖x ω-y ω‖^2 ≤ 2 - 2*(⟪x ω,y ω⟫_ℂ).re := by
    rw [@norm_sub_sq ℂ _ _ _ _ (x ω) (y ω)]
    change ‖x ω‖^2 - 2*(⟪x ω,y ω⟫_ℂ).re + ‖y ω‖^2 ≤
      2 - 2*(⟪x ω,y ω⟫_ℂ).re
    nlinarith [hx ω, hy ω, norm_nonneg (x ω), norm_nonneg (y ω)]
  have hh := integral_mono hdist ((integrable_const (2 : ℝ)).sub
    (hinner.const_mul 2)) hp
  change (∫ ω, ‖x ω-y ω‖^2 ∂μ) ≤
    ∫ ω, 2-2*(⟪x ω,y ω⟫_ℂ).re ∂μ at hh
  rw [integral_sub (integrable_const _) (hinner.const_mul 2), integral_const_mul] at hh
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
  linarith

theorem mean_vector_distance_le (x y : Ω → EuclideanSpace ℂ H)
    (hx : ∀ ω, ‖x ω‖ ≤ 1) (hy : ∀ ω, ‖y ω‖ ≤ 1)
    (hinner : Integrable (fun ω => (⟪x ω,y ω⟫_ℂ).re) μ)
    (hdist : Integrable (fun ω => ‖x ω-y ω‖) μ)
    (hdistsq : Integrable (fun ω => ‖x ω-y ω‖^2) μ) (q : ℕ) (R : ℝ) (hR : 0 < R)
    (hoverlap : 1-35*(q : ℝ)^2/R^2 ≤ ∫ ω, (⟪x ω,y ω⟫_ℂ).re ∂μ) :
    (∫ ω, ‖x ω-y ω‖ ∂μ) ≤ 9*(q : ℝ)/R := by
  have hh := mean_vector_distance_sq x y hx hy hinner hdistsq
    (35*(q : ℝ)^2/R^2) hoverlap
  have hm := mean_square_ge (fun ω => ‖x ω-y ω‖) hdist hdistsq
  have hn : 0 ≤ ∫ ω, ‖x ω-y ω‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  have hp : 0 ≤ 9*(q : ℝ)/R := by positivity
  have he : (9*(q : ℝ)/R)^2 = 81*(q : ℝ)^2/R^2 := by ring
  have h70 : 2*(35*(q : ℝ)^2/R^2) ≤ 81*(q : ℝ)^2/R^2 := by
    have hz : 0 ≤ (q : ℝ)^2/R^2 := by positivity
    convert mul_le_mul_of_nonneg_right (show (70 : ℝ) ≤ 81 by norm_num) hz using 1 <;> ring
  rw [← he] at h70
  nlinarith

#print axioms mean_le_sqrt_mean_square
#print axioms overlap_recurrence
#print axioms mean_vector_distance_le
end
end ICO.MHAveragedHybrid
