import ICO.RecordingRetainedProcess

/-! Arbitrary public CPTP operations lift past the inaccessible record
registers. Their visible action commutes exactly with record erasure. -/

namespace ICO.RecordingKnownChannel

open QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport
  ICO.RecordingKnownOperation ICO.RecordingRetainedProcess
  ICO.RecordingDistance
open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section

variable {α μ ν : Type*} [Fintype α] [DecidableEq α]
  [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]

def liftKnown (Φ : MatrixMap (α × μ) (α × ν))
    (ρ : CMatrix (Basis α × μ)) : CMatrix (Basis α × ν) :=
  (MatrixMap.kron Φ (Channel.idChannel (Relation α α × Relation α α)).map
    (ρ.submatrix (queryMemoryFirst μ).symm (queryMemoryFirst μ).symm)).submatrix
      (queryMemoryFirst ν) (queryMemoryFirst ν)

theorem liftKnown_apply (Φ : MatrixMap (α × μ) (α × ν))
    (ρ : CMatrix (Basis α × μ)) (y z : α) (l r : Relation α α × Relation α α)
    (i j : ν) :
    liftKnown Φ ρ ((y, l), i) ((z, r), j) =
      Φ (fun u v => ρ ((u.1, l), u.2) ((v.1, r), v.2)) (y, i) (z, j) := by
  simp only [liftKnown, Matrix.submatrix_apply, queryMemoryFirst,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, MatrixMap.kron_idChannel_apply_slice]

theorem liftKnown_visible (Φ : MatrixMap (α × μ) (α × ν))
    (ρ : CMatrix (Basis α × μ)) :
    visibleMap (liftKnown Φ ρ) = Φ (visibleMap ρ) := by
  ext u v
  rcases u with ⟨y, i⟩
  rcases v with ⟨z, j⟩
  simp only [visibleMap_apply, liftKnown_apply]
  have hSum : (∑ lr : Relation α α × Relation α α,
      (fun u v : α × μ => ρ ((u.1, lr), u.2) ((v.1, lr), v.2))) = visibleMap ρ := by
    ext u v
    simpa only [Finset.sum_apply] using (visibleMap_apply ρ u.1 v.1 u.2 v.2).symm
  rw [← hSum]
  have h := congrFun (congrFun (map_sum Φ
    (fun lr : Relation α α × Relation α α =>
      (fun u v : α × μ => ρ ((u.1, lr), u.2) ((v.1, lr), v.2))) Finset.univ) (y, i)) (z, j)
  simpa only [Matrix.sum_apply] using h.symm

theorem liftKnown_posSemidef (Φ : MatrixMap (α × μ) (α × ν))
    (hΦ : MatrixMap.IsCompletelyPositive Φ) (ρ : CMatrix (Basis α × μ))
    (hρ : ρ.PosSemidef) : (liftKnown Φ ρ).PosSemidef := by
  apply Matrix.PosSemidef.submatrix
  apply MatrixMap.isCompletelyPositive_mapsPositive _
    (MatrixMap.isCompletelyPositive_kron _ _ hΦ
      (Channel.idChannel (Relation α α × Relation α α)).completelyPositive)
  exact hρ.submatrix _

theorem liftKnown_trace (Φ : MatrixMap (α × μ) (α × ν))
    (hΦ : MatrixMap.IsTracePreserving Φ) (ρ : CMatrix (Basis α × μ)) :
    (liftKnown Φ ρ).trace = ρ.trace := by
  rw [← visibleMap_trace, liftKnown_visible, hΦ, visibleMap_trace]

theorem liftKnown_local_distance (Φ : Channel (α × μ) (α × ν))
    (m : ℕ) (hm : m < Fintype.card α) (ρ : CMatrix (Basis α × μ))
    (hρ : ρ.PosSemidef) (hmass : ρ.trace.re ≤ 1) :
    normalizedTraceDistance
      (visibleMap (liftKnown Φ.map (retainedGrowingWrapper m ρ)))
      (Φ.map (ICO.RecordingWrapperDistance.uniformOutput
        (QIT.partialTraceA (visibleMap ρ)))) ≤
      (m : ℝ) / (Fintype.card α : ℝ) +
        (ρ.trace.re - (liftKnown Φ.map (retainedGrowingWrapper m ρ)).trace.re) / 2 := by
  rw [liftKnown_visible, liftKnown_trace _ Φ.tracePreserving]
  have hΦ : MatrixMap.TraceNonincreasingCP Φ.map :=
    ⟨Φ.completelyPositive, fun X _ => le_of_eq (congrArg Complex.re (Φ.tracePreserving X))⟩
  exact (distance_contract Φ.map hΦ _ _
    (visibleMap_TNI.mapsPositive _ (retainedGrowingWrapper_posSemidef m ρ hρ))
    (ICO.RecordingWrapperDistance.uniformOutput_posSemidef _
      (QIT.partialTraceA_posSemidef (visibleMap_TNI.mapsPositive ρ hρ)))).trans
      (retainedGrowingWrapper_local_distance m hm ρ hρ hmass)

end
end ICO.RecordingKnownChannel

