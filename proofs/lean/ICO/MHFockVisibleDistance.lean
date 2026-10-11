import ICO.MHFockRotationErasure
import ICO.MHFockRunContinuity
import ICO.MHOutputMixture
import ICO.MHDomainMeanProduct

/-! Turn the actual rotated vector comparison into an accessible-output
trace-distance comparison, erasing the record rotation exactly. -/
namespace ICO.MHFockVisibleDistance
open Matrix QIT MeasureTheory ICO.MHFockRotationErasure ICO.MHDecompressionErasure
  ICO.MHFockRunContinuity ICO.MHFockRotation ICO.MHFockKnownOperation
  ICO.MHBoundedRecording ICO.MHProtocolOverlap ICO.MHOutputMixture
  ICO.MHSectorCovariance ICO.MHDomainMeanProduct ICO.PureHybrid ICO.RecordingDistance
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 512
variable {α μ : Type} [Fintype α] [DecidableEq α] [Nontrivial α]
  [Fintype μ] [DecidableEq μ]
local instance cmContinuousENorm {ι : Type} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) := SeminormedAddGroup.toContinuousENorm

theorem visible_outer (T : ℕ) (z : EuclideanSpace ℂ (InputCutoff (α := α) T×μ)) :
    (visibleChannel T).map (outer z z)=fockVisible T (WithLp.ofLp z) := by
  rw [visibleChannel_apply]
  rfl

theorem visible_pure_distance (T : ℕ)
    (x y : EuclideanSpace ℂ (InputCutoff (α := α) T×μ)) (hx : ‖x‖≤1) (hy : ‖y‖≤1) :
    normalizedTraceDistance (fockVisible T (WithLp.ofLp x)) (fockVisible T (WithLp.ofLp y))≤‖x-y‖ := by
  have hh := pure_output_distance_le (visibleChannel T).map (visibleChannel_TNI T) x y hx hy
  simpa only [visible_outer] using hh

theorem mean_visible_rotation_distance (T : ℕ)
    (x : Matrix.unitaryGroup α ℂ × Matrix.unitaryGroup α ℂ→EuclideanSpace ℂ (InputCutoff (α := α) T×μ))
    (y : EuclideanSpace ℂ (InputCutoff (α := α) T×μ)) (hx : Continuous x)
    (hnx : ∀p,‖x p‖≤1) (hny : ‖y‖≤1) :
    normalizedTraceDistance (∫p, fockVisible T (WithLp.ofLp (x p)) ∂rotationMeasure α)
      (fockVisible T (WithLp.ofLp y))≤
    ∫p, ‖x p-act (Matrix.kronecker (fockQ p.1 p.2 T : CMatrix (InputCutoff (α := α) T))
      (1 : CMatrix μ)) y‖ ∂rotationMeasure α := by
  let yQ := fun p : Matrix.unitaryGroup α ℂ × Matrix.unitaryGroup α ℂ =>
    act (Matrix.kronecker (fockQ p.1 p.2 T : CMatrix (InputCutoff (α := α) T)) (1 : CMatrix μ)) y
  have hc : Continuous yQ := (recordAction_continuous T μ).clm_apply continuous_const
  have hn (p : Matrix.unitaryGroup α ℂ × Matrix.unitaryGroup α ℂ) : ‖yQ p‖≤1 := by
    have hQ : ‖Matrix.kronecker (fockQ p.1 p.2 T : CMatrix (InputCutoff (α := α) T)) (1 : CMatrix μ)‖≤1 :=
      (tensor_identity_norm_le _).trans (unitary_norm_le _)
    exact (act_norm_le _ y).trans ((mul_le_mul hQ hny (norm_nonneg _) (by norm_num)).trans_eq (by ring))
  have hh := mean_output_distance_le (μ := rotationMeasure α)
    (visibleChannel T).map (visibleChannel_TNI T) x yQ hx hc hnx hn
  have he (p : Matrix.unitaryGroup α ℂ × Matrix.unitaryGroup α ℂ) :
      (visibleChannel T).map (outer (yQ p) (yQ p))=fockVisible T (WithLp.ofLp y) := by
    rw [visible_outer]
    exact rotation_visible p.1 p.2 T (WithLp.ofLp y)
  simpa only [visible_outer,he,integral_const,probReal_univ,one_smul] using hh

#print axioms mean_visible_rotation_distance
end
end ICO.MHFockVisibleDistance
