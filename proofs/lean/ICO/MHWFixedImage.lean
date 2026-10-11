import ICO.MHWFixedSector
import ICO.MHEmbeddingProjector

/-! A fixed-length image block of the actual partial oracle, with the full
sum over possible predecessor records explicitly accounted for. -/
namespace ICO.MHWFixedImage
open QIT ICO.MHFockLabels ICO.MHFockNodup ICO.MHFockSpace ICO.MHFockEntries
  ICO.MHFockProjection ICO.MHWRecordEntries ICO.MHWOccupation ICO.MHOccupationCounts
  ICO.MHBijectionProfiles ICO.RecordingCopyIdentity ICO.RecordingMultisetBridge
  ICO.MHBoundedRecording ICO.MHLabelCoefficients ICO.MHWFixedSector ICO.MHEmbeddingProjector
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2200000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem fixedRight_source {n r T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (hi : n+r≤T) (ho : n+(r+1)≤T) (p : TensorPowerProfile (α×α) n)
    (o : α × TensorPowerProfile (α×α) (r+1)) (i : InputCutoff (α := α) T)
    (hz : recordRightW hT (fixedRightEmbed ho p o) i≠0) :
    ∃ j, fixedRightEmbed hi p j=i := by
  rw [recordRightW_coefficient] at hz
  have hc : grade i<Fintype.card α ∧
      MultisetRightStep (fockLabel i) (fockLabel (fixedRightEmbed ho p o)) ∧
      BijMultiset (fockLabel (fixedRightEmbed ho p o)).2.1
        (fockLabel (fixedRightEmbed ho p o)).2.2 := by
    by_contra hn
    simp [hn] at hz
  apply (fixedRight_range hi p i).mpr
  have hs := hc.2.1
  rw [fixedRight_label] at hs
  refine ⟨hs.1.symm,?_⟩
  have hcard := congrArg Multiset.card hs.2.2
  simp only [profile_multiset_card,Multiset.card_cons] at hcard
  omega

theorem embedding_adjoint_mul {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (f : a→b) (M : CMatrix b) :
    (basisEmbedding f).conjTranspose*M=M.submatrix f id := by
  simp only [basisEmbedding,Matrix.conjTranspose_submatrix,Matrix.conjTranspose_one]
  change (1:CMatrix b).submatrix f (Equiv.refl b)*M=_
  rw [Matrix.one_submatrix_mul f (Equiv.refl b)]
  rfl

theorem fixedRight_source_projection {n r T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (hi : n+r≤T) (ho : n+(r+1)≤T) (p : TensorPowerProfile (α×α) n) :
    ((basisEmbedding (fixedRightEmbed ho p)).conjTranspose*recordRightW hT)*
        (basisEmbedding (fixedRightEmbed hi p)*(basisEmbedding (fixedRightEmbed hi p)).conjTranspose)=
      (basisEmbedding (fixedRightEmbed ho p)).conjTranspose*recordRightW hT := by
  rw [basisEmbedding_image _ (fixedRight_injective hi p),embedding_adjoint_mul]
  ext o i
  rw [Matrix.mul_diagonal]
  change recordRightW hT (fixedRightEmbed ho p o) i*
    (if ∃ x, fixedRightEmbed hi p x=i then 1 else 0)=_
  by_cases hz : recordRightW hT (fixedRightEmbed ho p o) i=0
  · simp [hz]
  · rw [if_pos (fixedRight_source hT hi ho p o i hz),mul_one]
    rfl

theorem compressed_image_of_source {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (J : Matrix c a ℂ) (K : Matrix c b ℂ) (B : CMatrix c) (C : Matrix a b ℂ)
    (hc : J.conjTranspose*B*K=C)
    (hs : (J.conjTranspose*B)*(K*K.conjTranspose)=J.conjTranspose*B) :
    J.conjTranspose*(B*B.conjTranspose)*J=C*C.conjTranspose := by
  rw [← hc]
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  calc
    _ = (J.conjTranspose*B)*(B.conjTranspose*J) := by simp only [Matrix.mul_assoc]
    _ = ((J.conjTranspose*B)*(K*K.conjTranspose))*(B.conjTranspose*J) := by rw [hs]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem fixedRight_image {n r T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (hi : n+r≤T) (ho : n+(r+1)≤T) (p : TensorPowerProfile (α×α) n)
    (hsize : n+r<Fintype.card α) :
    (basisEmbedding (fixedRightEmbed ho p)).conjTranspose*
        (recordRightW hT*(recordRightW hT).conjTranspose)*basisEmbedding (fixedRightEmbed ho p)=
      rightWOccupation p*(rightWOccupation p).conjTranspose :=
  compressed_image_of_source _ _ _ _ (fixedRight_compression hT hi ho p hsize)
    (fixedRight_source_projection hT hi ho p)

end
end ICO.MHWFixedImage
