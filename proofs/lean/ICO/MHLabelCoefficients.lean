import ICO.MHFockLabels
import ICO.MHSectorCovariance

/-! Exact equality of the fresh multiset insertion and the labelled oracle
coefficients, with no no-repetition assumption. -/

namespace ICO.MHLabelCoefficients

open QIT ICO.MHFockLabels ICO.MHOccupationCounts ICO.MHOccupationSupport
  ICO.RecordingMultisetBridge ICO.MHERecordingApprox ICO.MHFreshInsertion
  ICO.MHBadInsertion ICO.MHSectorCovariance
open scoped BigOperators Matrix

noncomputable section
set_option maxHeartbeats 1800000

variable {α : Type*} [Fintype α] [DecidableEq α]

def fixedLabel {n r : ℕ} (q : TensorPowerProfile (α × α) r) (i : Input (α := α) n) : MultisetBasis α :=
  (i.1, occupationMultiset n i.2, occupationMultiset r q)

theorem increment_multiset_iff {n : ℕ} (z : α × α)
    (p : TensorPowerProfile (α × α) n) (o : TensorPowerProfile (α × α) (n + 1)) :
    (occupationMultiset (n+1) o : Multiset (α × α)) = z ::ₘ (occupationMultiset n p : Multiset (α × α)) ↔
      o = incrementProfile z p := by
  rw [← incrementProfile_multiset]
  exact Sym.coe_injective.eq_iff.trans (occupationMultiset (n+1)).injective.eq_iff

theorem fixed_left_step {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (o : Input (α := α) (n+1)) (i : Input (α := α) n) :
    MultisetLeftStep (fixedLabel q i) (fixedLabel q o) ↔ i ∈ freshSupport q o := by
  simp only [MultisetLeftStep, fixedLabel, true_and, ← usedOutputs_multisets, increment_multiset_iff]
  simp only [freshSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

theorem fullInsertion_label_coefficient {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (o : Input (α := α) (n+1)) (i : Input (α := α) n) (hsize : n+r < Fintype.card α) :
    fullInsertion q o i = multisetLeftInsertion (fixedLabel q o) (fixedLabel q i) := by
  unfold fullInsertion multisetLeftInsertion
  rw [fixed_left_step]
  simp only [fixedLabel, profile_multiset_card, hsize, true_and, ← usedOutputs_multisets]
  split_ifs <;> simp

def sectorLabel {n r : ℕ} (i : Sector (α := α) n r) : MultisetBasis α := fixedLabel i.2 i.1

theorem sectorV_label_coefficient (n r : ℕ) (o : Sector (α := α) (n+1) r)
    (i : Sector (α := α) n r) (hsize : n+r < Fintype.card α) :
    sectorV (α := α) n r o i = multisetLeftInsertion (sectorLabel o) (sectorLabel i) := by
  rcases o with ⟨o,q⟩
  rcases i with ⟨i,p⟩
  by_cases hp : p = q
  · subst p
    simpa only [sectorV, Matrix.blockDiagonal_apply_eq, sectorLabel] using
      fullInsertion_label_coefficient q o i hsize
  · have hR : (occupationMultiset r q : Multiset (α × α)) ≠ occupationMultiset r p := by
      intro he
      exact hp ((occupationMultiset r).injective (Sym.coe_injective he)).symm
    simp [sectorV, Matrix.blockDiagonal_apply', Ne.symm hp,
      multisetLeftInsertion, sectorLabel, fixedLabel, MultisetLeftStep, hR]

end
end ICO.MHLabelCoefficients
