import ICO.MHFockEntries
import ICO.MHFockOracle

/-! The swapped left insertion is exactly the inverse-recording insertion
on arbitrary multiset labels. -/

namespace ICO.MHFockRightEntries

open QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockLabels
  ICO.MHFockEntries ICO.MHFockProjection ICO.MHFockSwap ICO.MHFockOracle
  ICO.MHProfileTranspose ICO.MHOccupationCounts ICO.MHOccupationSupport
  ICO.RecordingMultisetBridge ICO.RecordingCopyIdentity
open scoped BigOperators Matrix

noncomputable section
set_option maxHeartbeats 2000000
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {α : Type*} [Fintype α] [DecidableEq α]

def swapLabel (i : MultisetBasis α) : MultisetBasis α :=
  (i.1, i.2.2.map Prod.swap, i.2.1.map Prod.swap)

theorem fockLabel_recordSwap {T : ℕ} (i : InputCutoff (α := α) T) :
    fockLabel (recordSwap i) = swapLabel (fockLabel i) := by
  dsimp only [fockLabel, recordSwap, swapLabel]
  rw [profileTranspose_multiset, profileTranspose_multiset]
  rfl

theorem swap_imageLabels (i : MultisetBasis α) :
    imageLabels (swapLabel i).2.1 (swapLabel i).2.2 = domainLabels i.2.1 i.2.2 := by
  simp [swapLabel, imageLabels, domainLabels, Multiset.toFinset_map,
    ← Finset.image_union, Finset.image_image, Finset.union_comm]
  rfl

theorem swap_map_cons_iff (L M : Multiset (α × α)) (x y : α) :
    L.map Prod.swap = (x,y) ::ₘ M.map Prod.swap ↔ L = (y,x) ::ₘ M := by
  change L.map Prod.swap = (Prod.swap (y,x)) ::ₘ M.map Prod.swap ↔ _
  rw [← Multiset.map_cons]
  exact (Multiset.map_injective (Equiv.prodComm α α).injective).eq_iff

theorem swapped_left_step (i o : MultisetBasis α) :
    MultisetLeftStep (swapLabel i) (swapLabel o) ↔ MultisetRightStep i o := by
  simp only [MultisetLeftStep, swapLabel, MultisetRightStep]
  change o.2.1.map Prod.swap = i.2.1.map Prod.swap ∧
    o.1 ∉ imageLabels (swapLabel i).2.1 (swapLabel i).2.2 ∧
    o.2.2.map Prod.swap = (i.1,o.1) ::ₘ i.2.2.map Prod.swap ↔ _
  have hs : Function.Injective (Prod.swap : α × α → α × α) := (Equiv.prodComm α α).injective
  rw [swap_imageLabels, swap_map_cons_iff, (Multiset.map_injective hs).eq_iff]

theorem rightOnFock_entry {t T : ℕ} (h : t+1 ≤ T) (o i : InputCutoff (α := α) T) :
    rightOnFock h o i = leftOnFock h (recordSwap o) (recordSwap i) := by
  have he : rightOnFock (α := α) h = (leftOnFock (α := α) h).submatrix
      (recordSwapEquiv (α := α) T) (recordSwapEquiv (α := α) T) := by
    calc
      _ = (basisEmbedding (recordSwapEquiv (α := α) T)).conjTranspose * leftOnFock h *
          basisEmbedding (recordSwapEquiv (α := α) T) := by
        change swapMatrix T * leftOnFock h * (swapMatrix T).conjTranspose =
          (swapMatrix T).conjTranspose * leftOnFock h * swapMatrix T
        rw [swapMatrix_selfAdjoint]
      _ = _ := basisEmbedding_compression (recordSwapEquiv (α := α) T) (leftOnFock h)
  exact congrArg (fun M => M o i) he

theorem rightOnFock_coefficient {t T : ℕ} (h : t+1 ≤ T) (o i : InputCutoff (α := α) T) :
    rightOnFock h o i = if grade i ≤ t ∧ MultisetRightStep (fockLabel i) (fockLabel o) then
      (Real.sqrt ((Fintype.card α : ℝ) - (domainLabels (fockLabel i).2.1 (fockLabel i).2.2).card) : ℂ)⁻¹ else 0 := by
  rw [rightOnFock_entry, leftOnFock_coefficient, fockLabel_recordSwap, fockLabel_recordSwap,
    swapped_left_step]
  have hg : grade (recordSwap i) = grade i := Nat.add_comm _ _
  rw [hg, usedOutputs_multisets]
  change (if grade i ≤ t ∧ MultisetRightStep (fockLabel i) (fockLabel o) then
    (Real.sqrt ((Fintype.card α : ℝ) - (imageLabels (fockLabel (recordSwap i)).2.1
      (fockLabel (recordSwap i)).2.2).card) : ℂ)⁻¹ else 0) = _
  rw [fockLabel_recordSwap, swap_imageLabels]

theorem rightOnFock_support {t T : ℕ} (h : t+1 ≤ T) (o i : InputCutoff (α := α) T)
    (hB : rightOnFock h o i ≠ 0) : grade i ≤ t ∧ MultisetRightStep (fockLabel i) (fockLabel o) := by
  rw [rightOnFock_coefficient] at hB
  by_contra hn
  simp [hn] at hB

end
end ICO.MHFockRightEntries
