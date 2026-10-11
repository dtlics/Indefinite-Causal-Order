import ICO.MHProjectedProtocol

/-! Hybrid calculus for actual rectangular isometries and varying Hilbert
spaces, including growing purification and private-copy registers. -/
namespace ICO.MHIsometricHybrid
open MeasureTheory Matrix QIT ICO.MHProtocolOverlap ICO.MHProjectedMeanLoss
open scoped InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
variable {E : ℕ → Type*}
  [∀ t, NormedAddCommGroup (E t)] [∀ t, InnerProductSpace ℂ (E t)]

theorem local_step (t : ℕ) (U : E t →ₗᵢ[ℂ] E (t+1))
    (S : E t →L[ℂ] E (t+1)) (z w : E t) :
    ‖U z-S w‖≤‖z-w‖+‖S w-U w‖ := by
  calc
    _ = ‖U (z-w)+(U w-S w)‖ := by rw [map_sub]; congr 1; abel
    _ ≤ ‖U (z-w)‖+‖U w-S w‖ := norm_add_le _ _
    _ = _ := by rw [U.norm_map,norm_sub_rev (U w) (S w)]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem mean_local_step (t : ℕ)
    (U : Ω → E t →ₗᵢ[ℂ] E (t+1)) (S : Ω → E t →L[ℂ] E (t+1))
    (z w : Ω → E t)
    (hnext : Integrable (fun ω => ‖U ω (z ω)-S ω (w ω)‖) μ)
    (hprev : Integrable (fun ω => ‖z ω-w ω‖) μ)
    (herr : Integrable (fun ω => ‖S ω (w ω)-U ω (w ω)‖) μ)
    (δ : ℝ) (hδ : (∫ ω, ‖S ω (w ω)-U ω (w ω)‖ ∂μ)≤δ) :
    (∫ ω, ‖U ω (z ω)-S ω (w ω)‖ ∂μ)≤
      (∫ ω, ‖z ω-w ω‖ ∂μ)+δ := by
  have hh := integral_mono hnext (hprev.add herr)
    (fun ω => local_step t (U ω) (S ω) (z ω) (w ω))
  change (∫ ω, ‖U ω (z ω)-S ω (w ω)‖ ∂μ)≤
    ∫ ω, ‖z ω-w ω‖+‖S ω (w ω)-U ω (w ω)‖ ∂μ at hh
  rw [integral_add hprev herr] at hh
  linarith

theorem varying_run_hybrid
    (z w : (t : ℕ) → Ω → E t)
    (U : (t : ℕ) → Ω → E t →ₗᵢ[ℂ] E (t+1))
    (S : (t : ℕ) → Ω → E t →L[ℂ] E (t+1))
    (q : ℕ) (R : ℝ) (hinit : z 0=w 0)
    (hz : ∀ t<q, z (t+1)=fun ω => U t ω (z t ω))
    (hw : ∀ t<q, w (t+1)=fun ω => S t ω (w t ω))
    (hdist : ∀ t≤q, Integrable (fun ω => ‖z t ω-w t ω‖) μ)
    (herr : ∀ t<q, Integrable (fun ω => ‖S t ω (w t ω)-U t ω (w t ω)‖) μ)
    (hcost : ∀ t<q, (∫ ω, ‖S t ω (w t ω)-U t ω (w t ω)‖ ∂μ)≤9*((t:ℝ)+1)/R) :
    (∫ ω, ‖z q ω-w q ω‖ ∂μ)≤9*(q:ℝ)*((q:ℝ)+1)/(2*R) := by
  apply ICO.MHProjectedProtocol.accumulated_defects (fun t => ∫ ω, ‖z t ω-w t ω‖ ∂μ) q R
  · simp [hinit]
  · intro t ht
    have hn := hdist (t+1) (by omega)
    rw [hz t ht,hw t ht] at hn ⊢
    exact mean_local_step t (U t) (S t) (z t) (w t) hn
      (hdist t (by omega)) (herr t ht) _ (hcost t ht)

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K]

theorem projection_deficit (P : CMatrix H) (hP : IsStarProjection P)
    (w : EuclideanSpace ℂ H) (U : EuclideanSpace ℂ H →ₗᵢ[ℂ] EuclideanSpace ℂ K)
    (hw : ‖w‖≤1) :
    ‖U (act P w)-U w‖^2≤1-‖U (act P w)‖^2 := by
  have hsq := projection_norm_square P hP w
  have hself : P.conjTranspose=P := hP.isSelfAdjoint.star_eq
  have hinner : (⟪act P w,w⟫_ℂ).re=(⟪w,act P w⟫_ℂ).re := by
    rw [← inner_conj_symm (w) (act P w),Complex.conj_re]
  rw [← map_sub,U.norm_map,U.norm_map]
  rw [@norm_sub_sq ℂ _ _ _ _ (act P w) w]
  change ‖act P w‖^2-2*(⟪act P w,w⟫_ℂ).re+‖w‖^2≤1-‖act P w‖^2
  rw [hinner,← hsq]
  nlinarith [norm_nonneg w]

#print axioms varying_run_hybrid
#print axioms projection_deficit
end
end ICO.MHIsometricHybrid
