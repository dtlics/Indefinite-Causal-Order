import ICO.MHRectangularAction

/-! Averaged projection loss on a reachable rectangular subspace. The mean
operator is compressed before bounding its norm. -/
namespace ICO.MHCompressedMeanLoss
open Matrix QIT MeasureTheory ICO.MHProtocolOverlap ICO.MHOverlapStep
  ICO.MHProjectedMeanLoss ICO.MHRectangularAction ICO.CausalReverse
  ICO.RecordingCopyIdentity ICO.RecordingProcess
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
set_option maxHeartbeats 1800000
variable {H K Ω : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [MeasurableSpace Ω] {μ : Measure Ω}

theorem mean_loss_square_compressed (P : CMatrix K) (hP : IsStarProjection P)
    (T : Ω→Matrix.unitaryGroup K ℂ) (J : Matrix K H ℂ) (z : EuclideanSpace ℂ H)
    (hM : Integrable (fun ω => J.conjTranspose*(T ω : CMatrix K).conjTranspose*
      P*(T ω : CMatrix K)*J) μ) (hz : ‖z‖≤1) (α : ℝ)
    (hα : ‖∫ ω, J.conjTranspose*(T ω : CMatrix K).conjTranspose*
      P*(T ω : CMatrix K)*J ∂μ‖≤α) :
    (∫ ω, ‖act P (act (T ω : CMatrix K) (rectAct J z))‖^2 ∂μ)≤α := by
  have he (ω : Ω) : ‖act P (act (T ω : CMatrix K) (rectAct J z))‖^2=
      tracePair (ICO.PureHybrid.outer z z)
        (J.conjTranspose*(T ω : CMatrix K).conjTranspose*P*(T ω : CMatrix K)*J) := by
    rw [projection_norm_square P hP]
    have hh := compressed_quadratic J
      ((T ω : CMatrix K).conjTranspose*P*(T ω : CMatrix K)) z
    rw [quadratic_trace] at hh
    simp only [act_mul] at hh
    rw [←act_adjoint_inner] at hh
    simpa only [Matrix.mul_assoc] using hh
  simp_rw [he]
  change (∫ ω, (tracePairCLM (ICO.PureHybrid.outer z z))
    (J.conjTranspose*(T ω : CMatrix K).conjTranspose*P*(T ω : CMatrix K)*J) ∂μ)≤α
  have hi := (tracePairCLM (ICO.PureHybrid.outer z z)).integral_comp_comm hM
  change (∫ ω, (tracePairCLM (ICO.PureHybrid.outer z z))
      (J.conjTranspose*(T ω : CMatrix K).conjTranspose*P*(T ω : CMatrix K)*J) ∂μ)=
    tracePair (ICO.PureHybrid.outer z z)
      (∫ ω, J.conjTranspose*(T ω : CMatrix K).conjTranspose*P*(T ω : CMatrix K)*J ∂μ) at hi
  calc
    _ = _ := hi
    _ ≤ α := by rw [quadratic_trace]; exact (quadratic_norm_le _ z hz).trans hα

theorem mean_loss_square_supported (P : CMatrix K) (hP : IsStarProjection P)
    (T : Ω→Matrix.unitaryGroup K ℂ) (J : Matrix K H ℂ) (hJ : J.conjTranspose*J=1)
    (y : EuclideanSpace ℂ K) (hy : ‖y‖≤1)
    (hsupport : rectAct J (rectAct J.conjTranspose y)=y)
    (hM : Integrable (fun ω => J.conjTranspose*(T ω : CMatrix K).conjTranspose*
      P*(T ω : CMatrix K)*J) μ) (α : ℝ)
    (hα : ‖∫ ω, J.conjTranspose*(T ω : CMatrix K).conjTranspose*
      P*(T ω : CMatrix K)*J ∂μ‖≤α) :
    (∫ ω, ‖act P (act (T ω : CMatrix K) y)‖^2 ∂μ)≤α := by
  have hJn : ‖J.conjTranspose‖≤1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact isometry_matrix_norm_le J hJ
  have hz : ‖rectAct J.conjTranspose y‖≤1 :=
    (rectAct_norm_le J.conjTranspose y).trans
      (by nlinarith [norm_nonneg J.conjTranspose,norm_nonneg y])
  have hh := mean_loss_square_compressed P hP T J (rectAct J.conjTranspose y) hM hz α hα
  simpa only [hsupport] using hh

#print axioms mean_loss_square_compressed
#print axioms mean_loss_square_supported
end
end ICO.MHCompressedMeanLoss
