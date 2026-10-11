import ICO.RecordingWrapperDistance
import ICO.SwitchExperiment

namespace ICO.RecordingDepolarizing
open QIT ICO.RecordingWrapperDistance ICO.RecordingDistance
open scoped BigOperators ComplexOrder MatrixOrder
noncomputable section
variable {α μ : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [Fintype μ] [DecidableEq μ]

/-- The actual completely depolarizing channel, constructed as state preparation. -/
def depolarizing : Channel α α :=
  Channel.prepare (fun _ : α => ICO.SwitchExperiment.mixedState (n := α))

theorem depolarizing_entry (X : CMatrix α) (i j : α) :
    (depolarizing.map X) i j =
      if i = j then (Fintype.card α : ℂ)⁻¹ * X.trace else 0 := by
  simp [depolarizing, Channel.prepare_map, ICO.SwitchExperiment.mixedState,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.trace,
    Finset.mul_sum, mul_comm]

/-- Side memory is preserved, including its entanglement with the query register. -/
def withMemory : Channel (α × μ) (α × μ) :=
  (depolarizing (α := α)).prod (Channel.idChannel μ)

theorem withMemory_apply (ρ : CMatrix (α × μ)) :
    withMemory.map ρ = uniformOutput (QIT.partialTraceA ρ) := by
  ext u v
  rcases u with ⟨x, i⟩
  rcases v with ⟨y, j⟩
  change (MatrixMap.kron depolarizing.map (Channel.idChannel μ).map ρ) (x, i) (y, j) = _
  rw [MatrixMap.kron_idChannel_apply_slice, depolarizing_entry]
  change (if x = y then _ else 0) =
    (QIT.Classical.block (QIT.Classical.blockDiagonal
      (fun _ : α => ((1 / (Fintype.card α : ℝ) : ℝ) : ℂ) • QIT.partialTraceA ρ)) x y) i j
  by_cases hxy : x = y
  · subst y
    rw [if_pos rfl, QIT.Classical.blockDiagonal_block_self]
    simp [QIT.partialTraceA, Matrix.smul_apply, Matrix.trace, Matrix.diag_apply,
      Complex.ofReal_natCast, div_eq_mul_inv]
  · rw [if_neg hxy, QIT.Classical.blockDiagonal_block_ne _ hxy]
    rfl

theorem withMemory_TNI : MatrixMap.TraceNonincreasingCP (withMemory (α := α) (μ := μ)).map :=
  MatrixMap.traceNonincreasingCP_of_tracePreserving withMemory.completelyPositive
    withMemory.tracePreserving

theorem withMemory_pos (ρ : CMatrix (α × μ)) (hρ : ρ.PosSemidef) :
    (uniformOutput (α := α) (QIT.partialTraceA ρ)).PosSemidef := by
  rw [← withMemory_apply (α := α) (μ := μ) ρ]
  exact (withMemory (α := α) (μ := μ)).mapsPositive ρ hρ

theorem withMemory_trace (ρ : CMatrix (α × μ)) :
    (uniformOutput (α := α) (QIT.partialTraceA ρ)).trace = ρ.trace := by
  rw [← withMemory_apply (α := α) (μ := μ) ρ]
  exact (withMemory (α := α) (μ := μ)).tracePreserving ρ

theorem withMemory_distance_contract (ρ σ : CMatrix (α × μ))
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    normalizedTraceDistance (uniformOutput (α := α) (QIT.partialTraceA ρ))
      (uniformOutput (α := α) (QIT.partialTraceA σ)) ≤ normalizedTraceDistance ρ σ := by
  rw [← withMemory_apply (α := α) (μ := μ) ρ, ← withMemory_apply (α := α) (μ := μ) σ]
  exact distance_contract (withMemory (α := α) (μ := μ)).map withMemory_TNI ρ σ hρ hσ

/-- A known computation after the replacement remains an actual CPTP channel. -/
def followedBy (K : Channel (α × μ) (α × μ)) : Channel (α × μ) (α × μ) :=
  K.comp withMemory

theorem followedBy_apply (K : Channel (α × μ) (α × μ)) (ρ : CMatrix (α × μ)) :
    (followedBy K).map ρ = K.map (uniformOutput (QIT.partialTraceA ρ)) := by
  change K.map (withMemory.map ρ) = _
  rw [withMemory_apply]

#print axioms withMemory_apply
#print axioms withMemory_TNI
#print axioms withMemory_distance_contract
end
end ICO.RecordingDepolarizing
