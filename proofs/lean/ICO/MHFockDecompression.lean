import ICO.MHConcreteCompression
import ICO.MHWDomainProjection

/-! Literal ternary/permutation decompression of the unrestricted Fock
recording space, with its exact physical-oracle domain identities. -/
namespace ICO.MHFockDecompression
open Matrix QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockLabels
  ICO.MHFockNodup ICO.MHWEmbedding ICO.MHWRecordEntries ICO.MHWDomainProjection
  ICO.MHBijectionProfiles ICO.RecordingCopyIdentity ICO.RecordingOperatorSupport
  ICO.RecordingMultisetBridge ICO.MHTernaryCompression ICO.MHPurifiedOracle
  ICO.MHConcreteCompression ICO.MHWPartial ICO.RecordingProcess ICO.MHFockEntries
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
variable {A : Type*} [Fintype A] [DecidableEq A]
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def fockD {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) :
    Matrix (A×Environment A) (InputCutoff (α := A) T) ℂ :=
  ICO.MHRecordDecompression.D*(basisEmbedding (setEmbedding hT)).conjTranspose

theorem oldBij_fock {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) :
    basisEmbedding (setEmbedding hT)*oldBijProjection*(basisEmbedding (setEmbedding hT)).conjTranspose=
      bijProjection (α := A) T := by
  ext o i
  by_cases ho : ∃ x, setEmbedding hT x=o
  · obtain ⟨o,rfl⟩ := ho
    by_cases hi : ∃ x, setEmbedding hT x=i
    · obtain ⟨i,rfl⟩ := hi
      rw [embedding_sandwich_entry _ _ (setEmbedding_injective hT) (setEmbedding_injective hT)]
      simp only [oldBijProjection,predicateProjection,bijProjection,Matrix.diagonal_apply,
        setEmbedding_label,embed,bijMultiset_sets,(setEmbedding_injective hT).eq_iff]
    · rw [embedding_sandwich_zero_col _ _ _ _ hi]
      have he : setEmbedding hT o≠i := fun he => hi ⟨o,he⟩
      simp [bijProjection,he]
  · rw [embedding_sandwich_zero_row _ _ _ _ ho]
    have hb : ¬BijMultiset (fockLabel o).2.1 (fockLabel o).2.2 :=
      fun hb => ho ((setEmbedding_range hT o).mpr (bijMultiset_nodup hb))
    by_cases he : o=i
    · subst i; simp [bijProjection,hb]
    · simp [bijProjection,he]

theorem fockD_gram {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) :
    (fockD hT).conjTranspose*fockD hT=bijProjection T := by
  rw [fockD,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ICO.MHRecordDecompression.D.conjTranspose ICO.MHRecordDecompression.D,
    ICO.MHRecordDecompression.decompression_gram]
  simpa only [oldBijProjection,ICO.MHRecordDecompression.bijProjection,Matrix.mul_assoc] using oldBij_fock hT

theorem fockD_forward_domain {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) :
    queryMatrix*fockD hT*((recordW hT).conjTranspose*recordW hT)=fockD hT*recordW hT := by
  rw [recordW_gram,fockD,recordW]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (basisEmbedding (setEmbedding hT)).conjTranspose (basisEmbedding (setEmbedding hT)),
    basisEmbedding_gram _ (setEmbedding_injective hT),Matrix.one_mul]
  simp only [← Matrix.mul_assoc (basisEmbedding (setEmbedding hT)).conjTranspose (basisEmbedding (setEmbedding hT)),
    basisEmbedding_gram _ (setEmbedding_injective hT),Matrix.one_mul]
  have he := congrArg (fun M => M*(basisEmbedding (setEmbedding hT)).conjTranspose)
    (forward_domain_intertwine (A := A))
  simpa only [Matrix.mul_assoc] using he

theorem recordW_final_gram {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) :
    recordW hT*(recordW hT).conjTranspose=
      basisEmbedding (setEmbedding hT)*(oracleW*oracleW.conjTranspose)*(basisEmbedding (setEmbedding hT)).conjTranspose := by
  simp only [recordW,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (basisEmbedding (setEmbedding hT)).conjTranspose (basisEmbedding (setEmbedding hT)),
    basisEmbedding_gram _ (setEmbedding_injective hT),Matrix.one_mul]

theorem fockD_inverse_domain {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) :
    queryMatrix.conjTranspose*fockD hT*(recordW hT*(recordW hT).conjTranspose)=fockD hT*(recordW hT).conjTranspose := by
  rw [recordW_final_gram,fockD,recordW]
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (basisEmbedding (setEmbedding hT)).conjTranspose (basisEmbedding (setEmbedding hT)),
    basisEmbedding_gram _ (setEmbedding_injective hT),Matrix.one_mul]
  simp only [← Matrix.mul_assoc (basisEmbedding (setEmbedding hT)).conjTranspose (basisEmbedding (setEmbedding hT)),
    basisEmbedding_gram _ (setEmbedding_injective hT),Matrix.one_mul]
  have he := congrArg (fun M => M*(basisEmbedding (setEmbedding hT)).conjTranspose)
    (inverse_domain_intertwine (A := A))
  simpa only [Matrix.mul_assoc] using he

#print axioms fockD_gram
#print axioms fockD_forward_domain
#print axioms fockD_inverse_domain
end
end ICO.MHFockDecompression