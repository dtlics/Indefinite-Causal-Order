import ICO.MHWRecordSwap
import ICO.MHFockReachability

/-! The actual partial recording query stays on bijection records and raises
total length by at most one in either direction. -/
namespace ICO.MHWReachability
open QIT ICO.MHWRecordSwap ICO.MHWPartial ICO.MHFiniteWCanonical ICO.MHWEmbedding
  ICO.MHWRecordEntries ICO.MHFockEntries ICO.MHFockLabels ICO.MHFockNodup
  ICO.MHFockProjection ICO.MHFockRightEntries ICO.MHFockSwap ICO.MHFockReachability
  ICO.MHBijectionProfiles ICO.MHBoundedRecording ICO.RecordingCopyIdentity
  ICO.RecordingOperatorSupport ICO.RecordingMultisetBridge ICO.MHOracleCutoff
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2200000
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem oracleW_input_bij (o i : Basis α) (h : oracleW o i≠0) : BijRecord i.2.1 i.2.2 := by
  by_cases hL : leftW o i=0
  · have hR : rightW i o≠0 := by
      intro hz
      exact h (by simp [oracleW,Matrix.add_apply,Matrix.conjTranspose_apply,hL,hz])
    rw [rightW_coefficient] at hR
    split_ifs at hR with hc
    · exact hc.2.2
    · exact False.elim (hR rfl)
  · exact (leftW_support hL).1.1

theorem recordW_support_sets {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (o i : InputCutoff (α := α) T) (h : recordW hT o i≠0) :
    ∃ o' i' : Basis α, o=setEmbedding hT o' ∧ i=setEmbedding hT i' ∧ oracleW o' i'≠0 := by
  by_cases ho : ∃ x,setEmbedding hT x=o
  · obtain ⟨o',rfl⟩ := ho
    by_cases hi : ∃ x,setEmbedding hT x=i
    · obtain ⟨i',rfl⟩ := hi
      refine ⟨o',i',rfl,rfl,?_⟩
      simpa only [recordW,embedding_sandwich_entry _ _ (setEmbedding_injective hT)
        (setEmbedding_injective hT)] using h
    · exact False.elim (h (embedding_sandwich_zero_col _ _ _ _ hi))
  · exact False.elim (h (embedding_sandwich_zero_row _ _ _ _ ho))

theorem recordW_input_bij {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (o i : InputCutoff (α := α) T) (h : recordW hT o i≠0) :
    BijMultiset (fockLabel i).2.1 (fockLabel i).2.2 := by
  obtain ⟨o',i',_,hi,hh⟩ := recordW_support_sets hT o i h
  rw [hi,setEmbedding_label]
  exact (bijMultiset_sets _ _).mpr (oracleW_input_bij o' i' hh)

theorem recordW_output_bij {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (o i : InputCutoff (α := α) T) (h : recordW hT o i≠0) :
    BijMultiset (fockLabel o).2.1 (fockLabel o).2.2 := by
  have hs : recordW hT (recordSwap i) (recordSwap o)≠0 := by
    rw [recordW_entry_swap,Matrix.conjTranspose_apply]
    exact star_ne_zero.mpr h
  have hb := recordW_input_bij hT (recordSwap i) (recordSwap o) hs
  simpa only [fockLabel_recordSwap,swapLabel,bijMultiset_swap] using hb

theorem oracleW_grade_bound (o i : Basis α) (h : oracleW o i≠0) :
    setGrade o≤setGrade i+1 ∧ setGrade i≤setGrade o+1 := by
  by_cases hL : leftW o i=0
  · have hR : rightW i o≠0 := by intro hz; exact h (by simp [oracleW,Matrix.add_apply,Matrix.conjTranspose_apply,hL,hz])
    have hB : rightInsertion i o≠0 := by
      intro hz
      exact hR (by simp [rightW,rightProjection,predicateProjection,Matrix.mul_diagonal,hz])
    have hh := rightInsertion_grade i o hB
    omega
  · have hA : leftInsertion o i≠0 := by
      intro hz
      exact hL (by simp [leftW,leftProjection,predicateProjection,Matrix.mul_diagonal,hz])
    have hh := leftInsertion_grade o i hA
    omega

theorem recordW_grade_step {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (o i : InputCutoff (α := α) T) (h : recordW hT o i≠0) :
    grade o≤grade i+1 ∧ grade i≤grade o+1 := by
  obtain ⟨o',i',ho,hi,hh⟩ := recordW_support_sets hT o i h
  rw [ho,hi,setEmbedding_grade,setEmbedding_grade]
  exact oracleW_grade_bound o' i' hh

theorem recordW_inverse_output_bij {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (o i : InputCutoff (α := α) T) (h : (recordW hT).conjTranspose o i≠0) :
    BijMultiset (fockLabel o).2.1 (fockLabel o).2.2 := by
  apply recordW_input_bij hT i o
  intro hz
  exact h (by simp [Matrix.conjTranspose_apply,hz])

theorem recordW_inverse_grade_step {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (o i : InputCutoff (α := α) T) (h : (recordW hT).conjTranspose o i≠0) :
    grade o≤grade i+1 ∧ grade i≤grade o+1 := by
  have hh : recordW hT i o≠0 := by intro hz; exact h (by simp [Matrix.conjTranspose_apply,hz])
  exact (recordW_grade_step hT i o hh).symm

end
end ICO.MHWReachability
