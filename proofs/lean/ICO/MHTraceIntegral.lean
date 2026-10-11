import ICO.PureHybrid
import ICO.RecordingDistance
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Convexity of trace distance under continuous mixtures of actual matrices. -/
namespace ICO.MHTraceIntegral
open Matrix QIT MeasureTheory ICO.RecordingDistance
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
variable {H : Type*} [Fintype H] [DecidableEq H]

def traceMulCLM (U : CMatrix H) : CMatrix H →L[ℂ] ℂ :=
  ({ toFun := fun M => (M*U).trace
     map_add' := by intro M N; simp [Matrix.add_mul,Matrix.trace_add]
     map_smul' := by intro c M; simp [Matrix.smul_mul,Matrix.trace_smul] } :
    CMatrix H →ₗ[ℂ] ℂ).toContinuousLinearMap

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem traceNorm_integral_le (M : Ω → CMatrix H) (hM : Integrable M μ)
    (hTN : Integrable (fun ω => traceNorm (M ω)) μ) :
    traceNorm (∫ ω, M ω ∂μ)≤∫ ω, traceNorm (M ω) ∂μ := by
  obtain ⟨U,hU⟩ := traceNorm_variational_exists_unitary_abs_trace (∫ ω, M ω ∂μ)
  have hi := (traceMulCLM (U : CMatrix H)).integral_comp_comm hM
  change (∫ ω, (M ω*(U : CMatrix H)).trace ∂μ)=
    ((∫ ω, M ω ∂μ)*(U : CMatrix H)).trace at hi
  rw [← hU,← hi]
  have htrace := (traceMulCLM (U : CMatrix H)).integrable_comp hM
  change Integrable (fun ω => (M ω*(U : CMatrix H)).trace) μ at htrace
  calc
    _ ≤ ∫ ω, ‖(M ω*(U : CMatrix H)).trace‖ ∂μ := by
      simpa only [Complex.abs] using norm_integral_le_integral_norm (fun ω => (M ω*(U : CMatrix H)).trace)
    _ ≤ _ := integral_mono htrace.norm hTN (fun ω => by
      simpa only [Complex.abs] using traceNorm_variational_unitary_abs_trace_le (M ω) U)

theorem distance_integral_le (M N : Ω → CMatrix H) (hM : Integrable M μ)
    (hN : Integrable N μ)
    (hTN : Integrable (fun ω => traceNorm (M ω-N ω)) μ) :
    normalizedTraceDistance (∫ ω, M ω ∂μ) (∫ ω, N ω ∂μ)≤
      ∫ ω, normalizedTraceDistance (M ω) (N ω) ∂μ := by
  unfold normalizedTraceDistance traceNormDistance
  rw [← integral_sub hM hN,integral_const_mul]
  exact mul_le_mul_of_nonneg_left (traceNorm_integral_le _ (hM.sub hN) hTN) (by norm_num)

#print axioms traceNorm_integral_le
#print axioms distance_integral_le
end
end ICO.MHTraceIntegral
