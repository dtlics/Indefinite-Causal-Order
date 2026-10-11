import ICO.MHWEmbedding
import ICO.MHFiniteWCanonical
import ICO.MHWOccupation

/-! Exact coefficients of the finite-set partial recording branch after its
canonical embedding into the unrestricted occupation register. -/
namespace ICO.MHWRecordEntries
open QIT ICO.MHFockLabels ICO.MHFockNodup ICO.MHFockSpace ICO.MHFockEntries
  ICO.MHFockProjection ICO.MHWEmbedding ICO.MHWPartial ICO.MHFiniteWCanonical
  ICO.MHBijectionProfiles ICO.RecordingCopyIdentity ICO.RecordingOperatorSupport
  ICO.RecordingMultisetBridge ICO.MHBoundedRecording
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2000000
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem embedding_sandwich_zero_row {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (f : a → b) (M : CMatrix a) (o i : b)
    (ho : ¬∃ x, f x=o) :
    (basisEmbedding f*M*(basisEmbedding f).conjTranspose) o i=0 := by
  simp only [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro y _
  have hz : ∀ x, basisEmbedding f o x=0 := by
    intro x
    simp [basisEmbedding,Matrix.submatrix_apply,Matrix.one_apply,
      show o≠f x from fun h => ho ⟨x,h.symm⟩]
  simp [hz]

theorem embedding_sandwich_zero_col {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (f : a → b) (M : CMatrix a) (o i : b)
    (hi : ¬∃ x, f x=i) :
    (basisEmbedding f*M*(basisEmbedding f).conjTranspose) o i=0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro y _
  have hz : basisEmbedding f i y=0 := by
    simp [basisEmbedding,Matrix.submatrix_apply,Matrix.one_apply,
      show i≠f y from fun h => hi ⟨y,h.symm⟩]
  simp [Matrix.conjTranspose_apply,hz]

variable {α : Type*} [Fintype α] [DecidableEq α]

def recordRightW {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) : CMatrix (InputCutoff (α := α) T) :=
  basisEmbedding (setEmbedding hT)*rightW*(basisEmbedding (setEmbedding hT)).conjTranspose

theorem recordRightW_coefficient {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (o i : InputCutoff (α := α) T) :
    recordRightW hT o i = if grade i<Fintype.card α ∧
      MultisetRightStep (fockLabel i) (fockLabel o) ∧
      BijMultiset (fockLabel o).2.1 (fockLabel o).2.2 then
        (((Real.sqrt ((Fintype.card α : ℝ)-(fockLabel i).2.1.card-(fockLabel i).2.2.card))⁻¹ : ℝ) : ℂ)
      else 0 := by
  by_cases ho : ∃ x, setEmbedding hT x=o
  · obtain ⟨o,rfl⟩ := ho
    by_cases hi : ∃ x, setEmbedding hT x=i
    · obtain ⟨i,rfl⟩ := hi
      rw [recordRightW,embedding_sandwich_entry _ _ (setEmbedding_injective hT)
        (setEmbedding_injective hT),rightW_coefficient,setEmbedding_grade,
        setEmbedding_label,setEmbedding_label,embedded_right_step]
      simp only [embed,bijMultiset_sets]
      rfl
    · rw [recordRightW,embedding_sandwich_zero_col _ _ _ _ hi]
      have hn : ¬(grade i<Fintype.card α ∧
          MultisetRightStep (fockLabel i) (fockLabel (setEmbedding hT o)) ∧
          BijMultiset (fockLabel (setEmbedding hT o)).2.1 (fockLabel (setEmbedding hT o)).2.2) := by
        rintro ⟨_,hs,hb⟩
        exact hi ((setEmbedding_range hT i).mpr
          (multiset_right_reverse_preserves_nodup (bijMultiset_nodup hb) hs))
      simp [hn]
  · rw [recordRightW,embedding_sandwich_zero_row _ _ _ _ ho]
    have hn : ¬(grade i<Fintype.card α ∧ MultisetRightStep (fockLabel i) (fockLabel o) ∧
        BijMultiset (fockLabel o).2.1 (fockLabel o).2.2) := by
      rintro ⟨_,_,hb⟩
      exact ho ((setEmbedding_range hT o).mpr (bijMultiset_nodup hb))
    simp [hn]

end
end ICO.MHWRecordEntries
