import ICO.RecordingActiveWrapper

/-!
# Retaining private records and erasing only the copied label

This realizes the modified recording process as a CP map on its actual
private record registers.  Its visible marginal is exactly the map already
bounded in `RecordingActiveWrapper`.
-/

namespace ICO.RecordingRetainedProcess

open QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport
  ICO.RecordingFreshOutput ICO.RecordingWrapperDistance
  ICO.RecordingActiveWrapper ICO.RecordingDistance
open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section

variable {a b r e : Type*} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype r] [DecidableEq r]
  [Fintype e]

theorem partialTraceB_ofKraus (K : e → Matrix (b × r) a ℂ) (X : CMatrix a) :
    QIT.partialTraceB (MatrixMap.ofKraus K X) =
      MatrixMap.ofKraus (fun er : e × r => fun y s => K er.1 (y, er.2) s) X := by
  ext y z
  simp only [QIT.partialTraceB, ofKraus_entry, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

variable {α μ : Type*} [Fintype α] [DecidableEq α]
  [Fintype μ] [DecidableEq μ]

def visibleMap : MatrixMap (Basis α × μ) (α × μ) :=
  MatrixMap.kron (MatrixMap.partialTraceB α (Relation α α × Relation α α))
    (Channel.idChannel μ).map

theorem visibleMap_TNI : MatrixMap.TraceNonincreasingCP
    (visibleMap (α := α) (μ := μ)) :=
  MatrixMap.traceNonincreasingCP_kron_id MatrixMap.partialTraceB_traceNonincreasingCP

theorem visibleMap_apply (ρ : CMatrix (Basis α × μ)) (y z : α) (i j : μ) :
    visibleMap ρ (y, i) (z, j) = ∑ lr, ρ ((y, lr), i) ((z, lr), j) := by
  rw [visibleMap, MatrixMap.kron_idChannel_apply_slice]
  rfl

theorem visibleMap_trace (ρ : CMatrix (Basis α × μ)) :
    (visibleMap ρ).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, visibleMap_apply]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  exact Finset.sum_comm

theorem visibleMap_memory (ρ : CMatrix (Basis α × μ)) :
    QIT.partialTraceA (visibleMap ρ) = QIT.partialTraceA ρ := by
  ext i j
  simp only [QIT.partialTraceA, visibleMap_apply, Fintype.sum_prod_type]

def retainedLeftKraus (m : ℕ) (x : α) (o : Basis α) (s : ActiveSource α m) : ℂ :=
  if x = s.val.val.1 then leftInsertion o s.val.val else 0

def retainedGrowingWrapper (m : ℕ) (ρ : CMatrix (Basis α × μ)) :
    CMatrix (Basis α × μ) :=
  MatrixMap.kron (MatrixMap.ofKraus (retainedLeftKraus m)) (Channel.idChannel μ).map
    (activeInverseWithMemory m ρ)

theorem retainedGrowingWrapper_posSemidef (m : ℕ) (ρ : CMatrix (Basis α × μ))
    (hρ : ρ.PosSemidef) : (retainedGrowingWrapper m ρ).PosSemidef := by
  apply MatrixMap.isCompletelyPositive_mapsPositive _
    (MatrixMap.isCompletelyPositive_kron _ _ (MatrixMap.ofKraus_completelyPositive _)
      (Channel.idChannel μ).completelyPositive)
  exact (activeInverseWithMemory_TNI m).mapsPositive ρ hρ

theorem retained_erasure (m : ℕ) (X : CMatrix (ActiveSource α m)) :
    QIT.partialTraceB (MatrixMap.ofKraus (retainedLeftKraus m) X) =
      MatrixMap.ofKraus (copiedLeftKraus m) X := by
  rw [partialTraceB_ofKraus]
  ext y z
  simp only [ofKraus_entry, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  simpa only [retainedLeftKraus, copiedLeftKraus] using
    (Finset.sum_comm (f := fun l r =>
      (if x = s.val.val.1 then leftInsertion (y, l, r) s.val.val else 0) *
        star (if x = t.val.val.1 then leftInsertion (z, l, r) t.val.val else 0)))

theorem retainedGrowingWrapper_visible (m : ℕ) (ρ : CMatrix (Basis α × μ)) :
    visibleMap (retainedGrowingWrapper m ρ) = visibleGrowingWrapper m ρ := by
  ext u v
  rcases u with ⟨y, i⟩
  rcases v with ⟨z, j⟩
  simp only [visibleMap_apply, retainedGrowingWrapper, visibleGrowingWrapper,
    MatrixMap.kron_idChannel_apply_slice]
  exact congrFun (congrFun (retained_erasure m
    (fun s t => activeInverseWithMemory m ρ (s, i) (t, j))) y) z

theorem retainedGrowingWrapper_trace_le (m : ℕ) (hm : m < Fintype.card α)
    (ρ : CMatrix (Basis α × μ)) (hρ : ρ.PosSemidef) :
    (retainedGrowingWrapper m ρ).trace.re ≤ ρ.trace.re := by
  rw [← visibleMap_trace (retainedGrowingWrapper m ρ), retainedGrowingWrapper_visible,
    visibleGrowingWrapper_trace m hm]
  exact (activeInverseWithMemory_TNI m).traceNonincreasing ρ hρ

theorem retainedGrowingWrapper_local_distance (m : ℕ) (hm : m < Fintype.card α)
    (ρ : CMatrix (Basis α × μ)) (hρ : ρ.PosSemidef) (hmass : ρ.trace.re ≤ 1) :
    normalizedTraceDistance (visibleMap (retainedGrowingWrapper m ρ))
      (uniformOutput (QIT.partialTraceA (visibleMap ρ))) ≤
      (m : ℝ) / (Fintype.card α : ℝ) +
        (ρ.trace.re - (retainedGrowingWrapper m ρ).trace.re) / 2 := by
  rw [retainedGrowingWrapper_visible, visibleMap_memory,
    ← visibleMap_trace (retainedGrowingWrapper m ρ), retainedGrowingWrapper_visible]
  exact visibleGrowingWrapper_distance_by_output_mass m hm ρ hρ hmass

end
end ICO.RecordingRetainedProcess


