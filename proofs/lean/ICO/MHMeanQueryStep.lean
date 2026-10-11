import ICO.MHProjectedMeanLoss
import ICO.MHHaarStepConstants

/-! Averaging the actual bilinear query estimate. The hypotheses name the
operator identities supplied by the concrete recording construction. -/
namespace ICO.MHMeanQueryStep
open Matrix QIT MeasureTheory ICO.MHProtocolOverlap ICO.MHOverlapStep
  ICO.MHProjectedMeanLoss ICO.MHAveragedHybrid ICO.MHHaarStepConstants
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
variable {H Ω : Type*} [Fintype H] [DecidableEq H] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem mean_query_step (x : Ω→EuclideanSpace ℂ H) (y : EuclideanSpace ℂ H)
    (W V P B : CMatrix H) (C D Q : Ω→Matrix.unitaryGroup H ℂ) (ε α : ℝ)
    (hx : ∀ ω, ‖x ω‖≤1) (hy : ‖y‖≤1) (hW : ‖W‖≤1)
    (hWV : W.conjTranspose*V=P) (hB : B.conjTranspose=B)
    (hBx : ∀ ω, act B (act (C ω : CMatrix H) (x ω))=act (C ω : CMatrix H) (x ω))
    (hcov : ∀ ω, ‖(Q ω : CMatrix H)*V-
      (D ω : CMatrix H)*V*(C ω : CMatrix H)*(Q ω : CMatrix H)‖≤ε)
    (hmiss : IsStarProjection (B-P))
    (hM : Integrable (fun ω =>
      ((C ω : CMatrix H)*(Q ω : CMatrix H)).conjTranspose*(B-P)*
        ((C ω : CMatrix H)*(Q ω : CMatrix H))) μ)
    (hmean : ‖∫ ω,
      ((C ω : CMatrix H)*(Q ω : CMatrix H)).conjTranspose*(B-P)*
        ((C ω : CMatrix H)*(Q ω : CMatrix H)) ∂μ‖≤α)
    (ha : Integrable (fun ω => (⟪x ω,act (Q ω : CMatrix H) y⟫_ℂ).re) μ)
    (hb : Integrable (fun ω =>
      (⟪act ((D ω : CMatrix H)*W*(C ω : CMatrix H)) (x ω),
        act (Q ω : CMatrix H) (act V y)⟫_ℂ).re) μ)
    (hf : Integrable (fun ω =>
      ‖act (B-P) (act (C ω : CMatrix H) (act (Q ω : CMatrix H) y))‖) μ)
    (hfsq : Integrable (fun ω =>
      ‖act (B-P) (act (C ω : CMatrix H) (act (Q ω : CMatrix H) y))‖^2) μ) :
    (∫ ω, (⟪x ω,act (Q ω : CMatrix H) y⟫_ℂ).re ∂μ)-Real.sqrt α-ε ≤
      ∫ ω, (⟪act ((D ω : CMatrix H)*W*(C ω : CMatrix H)) (x ω),
        act (Q ω : CMatrix H) (act V y)⟫_ℂ).re ∂μ := by
  apply averaged_loss_step _ _ _ ε α ha hb hf hfsq
  · intro ω
    exact query_overlap_step (x ω) y W V P B (C ω) (D ω) (Q ω) ε
      (hx ω) hy hW hWV hB (hBx ω) (hcov ω)
  · have hh := mean_loss_square (B-P) hmiss (fun ω => C ω*Q ω) y hM hy α hmean
    simpa only [Matrix.UnitaryGroup.mul_val,act_mul] using hh

theorem query_constant (t : ℕ) (R : ℝ) (hR : 1≤R) :
    Real.sqrt (6*(t:ℝ)*Real.sqrt ((t:ℝ)/R^8))+
      16*Real.sqrt ((2*(t:ℝ)*(t+1))/R^8)≤35*(t:ℝ)/R^2 :=
  one_step_loss_bound t R hR

theorem mean_overlap_recurrence
    (E : ℕ→Type*) [∀ t,Fintype (E t)]
    (x : (t:ℕ)→Ω→EuclideanSpace ℂ (E t))
    (y : (t:ℕ)→Ω→EuclideanSpace ℂ (E t))
    (q : ℕ) (R : ℝ) (hR : 0<R)
    (hinit : 1≤∫ ω, (⟪x 0 ω,y 0 ω⟫_ℂ).re ∂μ)
    (hstep : ∀ t<q,
      (∫ ω, (⟪x t ω,y t ω⟫_ℂ).re ∂μ)-35*(t:ℝ)/R^2 ≤
        ∫ ω, (⟪x (t+1) ω,y (t+1) ω⟫_ℂ).re ∂μ) :
    1-35*(q:ℝ)^2/R^2≤∫ ω, (⟪x q ω,y q ω⟫_ℂ).re ∂μ :=
  overlap_recurrence (fun t => ∫ ω, (⟪x t ω,y t ω⟫_ℂ).re ∂μ) q R hR hinit hstep

#print axioms mean_query_step
#print axioms mean_overlap_recurrence
end
end ICO.MHMeanQueryStep
