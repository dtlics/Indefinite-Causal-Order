import ICO.MHOverlapStep
import ICO.CausalReverse
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The average squared recording loss equals a quadratic form of the
twirled missing-domain projection. -/
namespace ICO.MHProjectedMeanLoss
open Matrix QIT MeasureTheory ICO.MHProtocolOverlap ICO.MHOverlapStep ICO.CausalReverse
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
variable {H : Type*} [Fintype H] [DecidableEq H]

def tracePairCLM (C : CMatrix H) : CMatrix H →L[ℝ] ℝ :=
  ({ toFun := tracePair C
     map_add' := by intro X Y; simp [tracePair,Matrix.mul_add,Matrix.trace_add]
     map_smul' := by
       intro r X
       simp [tracePair,Matrix.mul_smul,Matrix.trace_smul,Complex.real_smul] } :
    CMatrix H →ₗ[ℝ] ℝ).toContinuousLinearMap

theorem projection_norm_square (P : CMatrix H) (hP : IsStarProjection P)
    (z : EuclideanSpace ℂ H) :
    ‖act P z‖^2=(⟪z,act P z⟫_ℂ).re := by
  have hh := act_adjoint_inner P z (act P z)
  have hPs : P.conjTranspose=P := hP.isSelfAdjoint.star_eq
  rw [hPs,← act_mul,hP.isIdempotentElem.eq] at hh
  have hs : (⟪act P z,act P z⟫_ℂ).re=‖act P z‖^2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (act P z)
  exact hs.symm.trans (congrArg Complex.re hh)

theorem quadratic_trace (M : CMatrix H) (z : EuclideanSpace ℂ H) :
    tracePair (ICO.PureHybrid.outer z z) M=(⟪z,act M z⟫_ℂ).re := by
  exact congrArg Complex.re (ICO.PureHybrid.outer_trace_unitary z z M)

theorem quadratic_norm_le (M : CMatrix H) (z : EuclideanSpace ℂ H)
    (hz : ‖z‖≤1) : (⟪z,act M z⟫_ℂ).re≤‖M‖ := by
  have hh := (Complex.re_le_norm (⟪z,act M z⟫_ℂ)).trans (norm_inner_le_norm z (act M z))
  have ha := act_norm_le M z
  have hb := mul_le_mul_of_nonneg_left hz (norm_nonneg M)
  have hc := mul_le_mul_of_nonneg_left (ha.trans hb) (norm_nonneg z)
  have hd := mul_le_mul_of_nonneg_right hz (norm_nonneg M)
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem mean_loss_square (P : CMatrix H) (hP : IsStarProjection P)
    (T : Ω → Matrix.unitaryGroup H ℂ) (z : EuclideanSpace ℂ H)
    (hM : Integrable (fun ω => (T ω : CMatrix H).conjTranspose*P*(T ω : CMatrix H)) μ)
    (hz : ‖z‖≤1) (α : ℝ)
    (hα : ‖∫ ω, (T ω : CMatrix H).conjTranspose*P*(T ω : CMatrix H) ∂μ‖≤α) :
    (∫ ω, ‖act P (act (T ω : CMatrix H) z)‖^2 ∂μ)≤α := by
  have he (ω : Ω) : ‖act P (act (T ω : CMatrix H) z)‖^2=
      tracePair (ICO.PureHybrid.outer z z) ((T ω : CMatrix H).conjTranspose*P*(T ω : CMatrix H)) := by
    rw [projection_norm_square P hP,quadratic_trace]
    simp only [act_mul]
    rw [← act_adjoint_inner]
  simp_rw [he]
  change (∫ ω, (tracePairCLM (ICO.PureHybrid.outer z z))
    ((T ω : CMatrix H).conjTranspose*P*(T ω : CMatrix H)) ∂μ)≤α
  have hi := (tracePairCLM (ICO.PureHybrid.outer z z)).integral_comp_comm hM
  change (∫ ω, (tracePairCLM (ICO.PureHybrid.outer z z))
    ((T ω : CMatrix H).conjTranspose*P*(T ω : CMatrix H)) ∂μ)=
      tracePair (ICO.PureHybrid.outer z z)
        (∫ ω, (T ω : CMatrix H).conjTranspose*P*(T ω : CMatrix H) ∂μ) at hi
  calc
    _ = _ := hi
    _ ≤ α := by
      rw [quadratic_trace]
      exact (quadratic_norm_le _ z hz).trans hα

#print axioms mean_loss_square
end
end ICO.MHProjectedMeanLoss
