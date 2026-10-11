import ICO.MHWFixedImage

/-! Coherent full-length sectors of the actual partial right oracle. The left
occupation profile is a quantum register, retained by a block-diagonal map. -/
namespace ICO.MHWRightSector
open QIT ICO.MHFockLabels ICO.MHFockNodup ICO.MHFockSpace ICO.MHFockEntries
  ICO.MHFockProjection ICO.MHWRecordEntries ICO.MHWOccupation ICO.MHOccupationCounts
  ICO.MHBijectionProfiles ICO.RecordingCopyIdentity ICO.RecordingMultisetBridge
  ICO.MHBoundedRecording ICO.MHLabelCoefficients ICO.MHWFixedSector ICO.MHWFixedImage
  ICO.MHEmbeddingProjector
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2500000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev RightSector (n r : ℕ) := (α×TensorPowerProfile (α×α) r)×TensorPowerProfile (α×α) n

def rightSectorEmbed {n r T : ℕ} (h : n+r≤T) (i : RightSector (α := α) n r) :
    InputCutoff (α := α) T := fixedRightEmbed h i.2 i.1

theorem rightSector_injective {n r T : ℕ} (h : n+r≤T) :
    Function.Injective (rightSectorEmbed (α := α) h) := by
  intro i j he
  apply Prod.ext
  · apply Prod.ext
    · exact congrArg (fun v : InputCutoff (α := α) T => v.2.1) he
    · apply Subtype.ext
      exact congrArg (fun v : InputCutoff (α := α) T => v.1.2.val) he
  · apply Subtype.ext
    exact congrArg (fun v : InputCutoff (α := α) T => v.2.2.val) he

def rightSectorW (n r : ℕ) : Matrix (RightSector (α := α) n (r+1)) (RightSector (α := α) n r) ℂ :=
  Matrix.blockDiagonal (fun p : TensorPowerProfile (α×α) n => rightWOccupation (r := r) p)

theorem rightSector_coefficient {n r T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (hi : n+r≤T) (ho : n+(r+1)≤T) (hsize : n+r<Fintype.card α)
    (o : RightSector (α := α) n (r+1)) (i : RightSector (α := α) n r) :
    recordRightW hT (rightSectorEmbed ho o) (rightSectorEmbed hi i)=rightSectorW n r o i := by
  rcases o with ⟨o,p⟩
  rcases i with ⟨i,q⟩
  by_cases he : p=q
  · subst q
    simpa only [rightSectorEmbed,rightSectorW,Matrix.blockDiagonal_apply_eq] using
      fixedRight_coefficient hT hi ho p hsize o i
  · have hL : (occupationMultiset n p : Multiset (α×α))≠occupationMultiset n q := by
      intro hh
      exact he ((occupationMultiset n).injective (Sym.coe_injective hh))
    simp only [rightSectorEmbed,recordRightW_coefficient,fixedRight_label,
      MultisetRightStep,hL,false_and,and_false,if_false,rightSectorW,
      Matrix.blockDiagonal_apply_ne _ _ _ he]

theorem rightSector_compression {n r T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (hi : n+r≤T) (ho : n+(r+1)≤T) (hsize : n+r<Fintype.card α) :
    (basisEmbedding (rightSectorEmbed (α := α) ho)).conjTranspose*recordRightW hT*
      basisEmbedding (rightSectorEmbed hi)=rightSectorW n r := by
  rw [embedding_compression_rect]
  ext o i
  exact rightSector_coefficient hT hi ho hsize o i

theorem rightSector_source_projection {n r T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (hi : n+r≤T) (ho : n+(r+1)≤T) :
    ((basisEmbedding (rightSectorEmbed (α := α) ho)).conjTranspose*recordRightW hT)*
        (basisEmbedding (rightSectorEmbed hi)*(basisEmbedding (rightSectorEmbed hi)).conjTranspose)=
      (basisEmbedding (rightSectorEmbed ho)).conjTranspose*recordRightW hT := by
  rw [basisEmbedding_image _ (rightSector_injective hi),embedding_adjoint_mul]
  ext o i
  rw [Matrix.mul_diagonal]
  change recordRightW hT (rightSectorEmbed ho o) i*
    (if ∃ x, rightSectorEmbed hi x=i then 1 else 0)=_
  by_cases hz : recordRightW hT (rightSectorEmbed ho o) i=0
  · simp [hz]
  · obtain ⟨j,hj⟩ := fixedRight_source hT hi ho o.2 o.1 i hz
    rw [if_pos ⟨(j,o.2),hj⟩,mul_one]
    rfl

theorem rightSector_image {n r T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (hi : n+r≤T) (ho : n+(r+1)≤T) (hsize : n+r<Fintype.card α) :
    (basisEmbedding (rightSectorEmbed (α := α) ho)).conjTranspose*
        (recordRightW hT*(recordRightW hT).conjTranspose)*basisEmbedding (rightSectorEmbed ho)=
      Matrix.blockDiagonal (fun p : TensorPowerProfile (α×α) n =>
        rightWOccupation (r := r) p*(rightWOccupation (r := r) p).conjTranspose) := by
  rw [compressed_image_of_source _ _ _ _ (rightSector_compression hT hi ho hsize)
    (rightSector_source_projection hT hi ho)]
  simp only [rightSectorW,Matrix.blockDiagonal_conjTranspose,← Matrix.blockDiagonal_mul]

end
end ICO.MHWRightSector
