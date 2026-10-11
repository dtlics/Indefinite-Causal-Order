import ICO.RecordingPureCorrespondence
import ICO.RecordingKnownChannel

/-! Erasing accumulated private copied labels commutes with the physical
recording maps and with arbitrary public computation. -/

namespace ICO.RecordingHistory

open QIT ICO.RecordingPureCorrespondence ICO.RecordingRetainedProcess
  ICO.RecordingActiveWrapper ICO.RecordingKnownChannel
  ICO.PathRecordingSupport ICO.RecordingOperatorSupport
open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section

variable {a b h μ : Type*} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype h] [DecidableEq h]
  [Fintype μ] [DecidableEq μ]

def eraseHistory : Channel (a × (h × μ)) (a × μ) :=
  (Channel.idChannel a).prod (Channel.traceOutLeft h μ)

theorem eraseHistory_apply (ρ : CMatrix (a × (h × μ))) (x y : a) (i j : μ) :
    eraseHistory.map ρ (x, i) (y, j) = ∑ e : h, ρ (x, (e, i)) (y, (e, j)) := by
  change MatrixMap.kron (Channel.idChannel a).map (Channel.traceOutLeft h μ).map
    ρ (x, i) (y, j) = _
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  rfl

theorem eraseHistory_rankOne (v : a × (h × μ) → ℂ) :
    eraseHistory.map (rankOneMatrix v) =
      ∑ e : h, rankOneMatrix (fun u : a × μ => v (u.1, (e, u.2))) := by
  ext u w
  rcases u with ⟨u, i⟩
  rcases w with ⟨w, j⟩
  simp only [eraseHistory_apply, Matrix.sum_apply, rankOneMatrix_apply]

theorem eraseHistory_tensor (Φ : MatrixMap a b) (ρ : CMatrix (a × (h × μ))) :
    eraseHistory.map (MatrixMap.kron Φ (Channel.idChannel (h × μ)).map ρ) =
      MatrixMap.kron Φ (Channel.idChannel μ).map (eraseHistory.map ρ) := by
  ext u v
  rcases u with ⟨x, i⟩
  rcases v with ⟨y, j⟩
  simp only [eraseHistory_apply, MatrixMap.kron_idChannel_apply_slice]
  have hSum : (∑ e : h, (fun s t : a => ρ (s, (e, i)) (t, (e, j)))) =
      (fun s t : a => ∑ e : h, ρ (s, (e, i)) (t, (e, j))) := by
    ext s t
    simp only [Finset.sum_apply]
  rw [← hSum]
  have hMap := congrFun (congrFun (map_sum Φ
    (fun e : h => (fun s t : a => ρ (s, (e, i)) (t, (e, j)))) Finset.univ) x) y
  simpa only [Matrix.sum_apply] using hMap.symm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem eraseHistory_retainedGrowingWrapper (m : ℕ)
    (ρ : CMatrix (Basis α × (h × μ))) :
    eraseHistory.map (retainedGrowingWrapper m ρ) =
      retainedGrowingWrapper m (eraseHistory.map ρ) := by
  unfold retainedGrowingWrapper activeInverseWithMemory
  rw [eraseHistory_tensor, eraseHistory_tensor]

/-- Old private copies may remain entangled throughout. Erasing all of them
    after the next copied label gives precisely the same retained process. -/
theorem retainedGrowingWrapper_purified_history (m : ℕ)
    (v : Basis α × (h × μ) → ℂ)
    (hv : ∀ i, v i ≠ 0 → Good i.1.2.1 i.1.2.2 ∧
      i.1.2.1.card + i.1.2.2.card ≤ m) :
    retainedGrowingWrapper (m + 1) (eraseHistory.map (rankOneMatrix v)) =
      eraseHistory.map (eraseCopied (rankOneMatrix (modifiedWrapper v))) := by
  rw [← eraseHistory_retainedGrowingWrapper, retainedGrowingWrapper_rankOne m v hv]

end
end ICO.RecordingHistory
