import ICO.MHMeanQueryStep
import ICO.MHCompressedMeanLoss

namespace ICO.MHCompressedQueryStep
open Matrix QIT MeasureTheory ICO.MHProtocolOverlap ICO.MHOverlapStep
  ICO.MHCompressedMeanLoss ICO.MHRectangularAction ICO.MHAveragedHybrid
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 512
variable {H K Ω : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem mean_query_step_compressed (x : Ω→EuclideanSpace ℂ K) (y : EuclideanSpace ℂ K)
    (W V P B : CMatrix K) (C D Q : Ω→Matrix.unitaryGroup K ℂ)
    (J : Matrix K H ℂ) (hJ : J.conjTranspose*J=1)
    (hsupport : rectAct J (rectAct J.conjTranspose y)=y) (ε α : ℝ)
    (hx : ∀ ω, ‖x ω‖≤1) (hy : ‖y‖≤1) (hW : ‖W‖≤1)
    (hWV : W.conjTranspose*V=P) (hB : B.conjTranspose=B)
    (hBx : ∀ ω, act B (act (C ω : CMatrix K) (x ω))=act (C ω : CMatrix K) (x ω))
    (hcov : ∀ ω, ‖(Q ω : CMatrix K)*V-
      (D ω : CMatrix K)*V*(C ω : CMatrix K)*(Q ω : CMatrix K)‖≤ε)
    (hmiss : IsStarProjection (B-P))
    (hM : Integrable (fun ω => J.conjTranspose*
      ((C ω : CMatrix K)*(Q ω : CMatrix K)).conjTranspose*(B-P)*
        ((C ω : CMatrix K)*(Q ω : CMatrix K))*J) μ)
    (hmean : ‖∫ ω, J.conjTranspose*
      ((C ω : CMatrix K)*(Q ω : CMatrix K)).conjTranspose*(B-P)*
        ((C ω : CMatrix K)*(Q ω : CMatrix K))*J ∂μ‖≤α)
    (ha : Integrable (fun ω => (⟪x ω,act (Q ω : CMatrix K) y⟫_ℂ).re) μ)
    (hb : Integrable (fun ω =>
      (⟪act ((D ω : CMatrix K)*W*(C ω : CMatrix K)) (x ω),
        act (Q ω : CMatrix K) (act V y)⟫_ℂ).re) μ)
    (hf : Integrable (fun ω =>
      ‖act (B-P) (act (C ω : CMatrix K) (act (Q ω : CMatrix K) y))‖) μ)
    (hfsq : Integrable (fun ω =>
      ‖act (B-P) (act (C ω : CMatrix K) (act (Q ω : CMatrix K) y))‖^2) μ) :
    (∫ ω, (⟪x ω,act (Q ω : CMatrix K) y⟫_ℂ).re ∂μ)-Real.sqrt α-ε ≤
      ∫ ω, (⟪act ((D ω : CMatrix K)*W*(C ω : CMatrix K)) (x ω),
        act (Q ω : CMatrix K) (act V y)⟫_ℂ).re ∂μ := by
  apply averaged_loss_step _ _ _ ε α ha hb hf hfsq
  · intro ω
    exact query_overlap_step (x ω) y W V P B (C ω) (D ω) (Q ω) ε
      (hx ω) hy hW hWV hB (hBx ω) (hcov ω)
  · have hh := mean_loss_square_supported (B-P) hmiss (fun ω => C ω*Q ω) J hJ
      y hy hsupport hM α hmean
    simpa only [Matrix.UnitaryGroup.mul_val,act_mul] using hh

#print axioms mean_query_step_compressed
end
end ICO.MHCompressedQueryStep
