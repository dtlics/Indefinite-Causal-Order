import ICO.MHWLeftProjection

/-! The actual partial-oracle domain preserves each record length, including
the empty-right-record boundary. -/
namespace ICO.MHWLengths
open QIT ICO.MHFockLabels ICO.MHFockNodup ICO.MHFockSpace ICO.MHFockEntries
  ICO.MHFockProjection ICO.MHWRecordEntries ICO.MHWEmbedding ICO.MHWPartial
  ICO.MHWLeftProjection ICO.MHOccupationCounts ICO.RecordingCopyIdentity
  ICO.RecordingMultisetBridge ICO.MHBoundedRecording
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2300000
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem recordRightW_support {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (o i : InputCutoff (α := α) T) (h : recordRightW hT o i≠0) :
    MultisetRightStep (fockLabel i) (fockLabel o) := by
  rw [recordRightW_coefficient] at h
  split_ifs at h with hc
  · exact hc.2.1
  · exact False.elim (h rfl)

theorem recordRightW_lengths {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (o i : InputCutoff (α := α) T) (h : recordRightW hT o i≠0) :
    o.1.1.val.1.val=i.1.1.val.1.val ∧ o.1.1.val.2.val=i.1.1.val.2.val+1 := by
  have hs := recordRightW_support hT o i h
  have hL := congrArg Multiset.card hs.1
  have hR := congrArg Multiset.card hs.2.2
  simpa only [fockLabel,profile_multiset_card,Multiset.card_cons] using And.intro hL hR

theorem rightImage_lengths {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (o i : InputCutoff (α := α) T) (h : (recordRightW hT*(recordRightW hT).conjTranspose) o i≠0) :
    o.1.1=i.1.1 := by
  obtain ⟨k,hok,hki⟩ := mul_entry_nonzero _ _ o i h
  have hik : recordRightW hT i k≠0 := by
    intro hz
    exact hki (by simp [Matrix.conjTranspose_apply,hz])
  have ho := recordRightW_lengths hT o k hok
  have hi := recordRightW_lengths hT i k hik
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · exact ho.1.trans hi.1.symm
  · exact ho.2.trans hi.2.symm

theorem recordRightW_empty_row {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (o i : InputCutoff (α := α) T) (ho : o.1.1.val.2.val=0) : recordRightW hT o i=0 := by
  by_contra hz
  have hR := (recordRightW_lengths hT o i hz).2
  omega

theorem rightImage_empty_row {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (o i : InputCutoff (α := α) T) (ho : o.1.1.val.2.val=0) :
    (recordRightW hT*(recordRightW hT).conjTranspose) o i=0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [recordRightW_empty_row hT o k ho,zero_mul]

theorem recordRightW_image {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) :
    recordRightW hT*(recordRightW hT).conjTranspose=
      basisEmbedding (setEmbedding hT)*(rightW*rightW.conjTranspose)*
        (basisEmbedding (setEmbedding hT)).conjTranspose := by
  simp only [recordRightW,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (basisEmbedding (setEmbedding hT)).conjTranspose (basisEmbedding (setEmbedding hT)),
    basisEmbedding_gram _ (setEmbedding_injective hT),Matrix.one_mul]

theorem recordGram_decomposition {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) :
    (recordW hT).conjTranspose*recordW hT=fockLeftProjection T+
      recordRightW hT*(recordRightW hT).conjTranspose := by
  rw [recordW_gram,oracle_gram,Matrix.mul_add,Matrix.add_mul,recordLeftProjection,
    recordRightW_image]

theorem recordGram_lengths {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (o i : InputCutoff (α := α) T) (h : ((recordW hT).conjTranspose*recordW hT) o i≠0) :
    o.1.1=i.1.1 := by
  by_contra hn
  have hoi : o≠i := fun he => hn (congrArg (fun v : InputCutoff (α := α) T => v.1.1) he)
  have hright : (recordRightW hT*(recordRightW hT).conjTranspose) o i=0 := by
    by_contra hz
    exact hn (rightImage_lengths hT o i hz)
  apply h
  rw [recordGram_decomposition,Matrix.add_apply,hright,add_zero]
  simp [fockLeftProjection,Matrix.diagonal_apply,hoi]

theorem recordGram_cutoff_commute {t T : ℕ} (ht : t≤T) (hT : 2*Fintype.card (α×α)≤T) :
    Commute (ICO.MHFockAlgebra.sourceProjection (α := α) ht)
      ((recordW hT).conjTranspose*recordW hT) := by
  rw [sourceProjection_diagonal]
  apply cutoff_commute_of_grade
  intro o i hi
  have he := recordGram_lengths hT o i hi
  exact congrArg (fun s : Lengths T => s.val.1.val+s.val.2.val) he

end
end ICO.MHWLengths
