import QIT.States.TraceNorm.Variational

/-! A common positive substate gives a quantitative trace-distance coupling. -/

namespace ICO.CommonPartDistance
open Matrix QIT
open scoped ComplexOrder MatrixOrder
noncomputable section
variable {H : Type} [Fintype H] [DecidableEq H]

theorem distance_le_missing_trace (ρ σ : State H) (C : CMatrix H)
    (hρ : (ρ.matrix - C).PosSemidef) (hσ : (σ.matrix - C).PosSemidef) :
    ρ.normalizedTraceDistance σ ≤ 1 - C.trace.re := by
  have heq : ρ.matrix - σ.matrix = (ρ.matrix - C) + -(σ.matrix - C) := by abel
  have h := traceNorm_add_le (ρ.matrix - C) (-(σ.matrix - C))
  rw [← heq, traceNorm_neg, traceNorm_posSemidef_eq_trace_re _ hρ,
    traceNorm_posSemidef_eq_trace_re _ hσ] at h
  simp only [Matrix.trace_sub, Complex.sub_re, ρ.trace_eq_one, σ.trace_eq_one, Complex.one_re] at h
  change (1 / 2 : ℝ) * traceNorm (ρ.matrix - σ.matrix) ≤ _
  linarith

end
end ICO.CommonPartDistance
