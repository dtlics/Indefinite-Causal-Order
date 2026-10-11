import ICO.MHWRecordEntries
import ICO.MHLabelCoefficients

/-! The actual partial right branch restricted to a fixed left occupation
profile and consecutive right-record lengths. -/
namespace ICO.MHWFixedSector
open QIT ICO.MHFockLabels ICO.MHFockNodup ICO.MHFockSpace ICO.MHFockEntries
  ICO.MHFockProjection ICO.MHWRecordEntries ICO.MHWOccupation ICO.MHOccupationCounts
  ICO.MHBijectionProfiles ICO.RecordingCopyIdentity ICO.RecordingMultisetBridge
  ICO.MHBoundedRecording ICO.MHLabelCoefficients
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2200000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {α : Type*} [Fintype α] [DecidableEq α]

def fixedRightEmbed {n r T : ℕ} (h : n+r≤T) (p : TensorPowerProfile (α×α) n)
    (i : α × TensorPowerProfile (α×α) r) : InputCutoff (α := α) T :=
  ⟨⟨⟨(⟨n,by omega⟩,⟨r,by omega⟩),h⟩,i.2⟩,(i.1,p)⟩

theorem fixedRight_label {n r T : ℕ} (h : n+r≤T) (p : TensorPowerProfile (α×α) n)
    (i : α × TensorPowerProfile (α×α) r) :
    fockLabel (fixedRightEmbed h p i)=(i.1,(occupationMultiset n p : Multiset (α×α)),
      (occupationMultiset r i.2 : Multiset (α×α))) := rfl

theorem fixedRight_grade {n r T : ℕ} (h : n+r≤T) (p : TensorPowerProfile (α×α) n)
    (i : α × TensorPowerProfile (α×α) r) : grade (fixedRightEmbed h p i)=n+r := rfl

theorem fixedRight_injective {n r T : ℕ} (h : n+r≤T) (p : TensorPowerProfile (α×α) n) :
    Function.Injective (fixedRightEmbed h p) := by
  intro i j he
  apply Prod.ext
  · exact congrArg (fun v : InputCutoff (α := α) T => v.2.1) he
  · apply Subtype.ext
    exact congrArg (fun v : InputCutoff (α := α) T => v.1.2.val) he

theorem fixedRight_range {n r T : ℕ} (h : n+r≤T) (p : TensorPowerProfile (α×α) n)
    (i : InputCutoff (α := α) T) :
    (∃ j, fixedRightEmbed h p j=i) ↔
      (fockLabel i).2.1=occupationMultiset n p ∧ (fockLabel i).2.2.card=r := by
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨rfl,profile_multiset_card j.2⟩
  · rintro ⟨hL,hR⟩
    let q : TensorPowerProfile (α×α) r := (occupationMultiset r).symm (Sym.mk (fockLabel i).2.2 hR)
    refine ⟨((fockLabel i).1,q),fockLabel_injective T ?_⟩
    rw [fixedRight_label]
    apply Prod.ext
    · rfl
    apply Prod.ext
    · exact hL.symm
    dsimp only [q]
    rw [Equiv.apply_symm_apply]
    rfl

theorem fixedRight_step_bij {n r : ℕ} (p : TensorPowerProfile (α×α) n)
    (o : α × TensorPowerProfile (α×α) (r+1)) (i : α × TensorPowerProfile (α×α) r) :
    (MultisetRightStep (i.1,occupationMultiset n p,occupationMultiset r i.2)
       (o.1,occupationMultiset n p,occupationMultiset (r+1) o.2) ∧ BijProfile p o.2) ↔
      o.2=incrementProfile (o.1,i.1) i.2 ∧ BijProfile p o.2 := by
  simp only [MultisetRightStep,true_and,increment_multiset_iff]
  constructor
  · rintro ⟨⟨_,he⟩,hb⟩
    exact ⟨he,hb⟩
  · rintro ⟨he,hb⟩
    have hinc : BijProfile p (incrementProfile (o.1,i.1) i.2) := he ▸ hb
    exact ⟨⟨((bijProfile_increment_right p i.2 o.1 i.1).mp hinc).2.1,he⟩,hb⟩

theorem fixedRight_coefficient {n r T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (hi : n+r≤T) (ho : n+(r+1)≤T) (p : TensorPowerProfile (α×α) n)
    (hsize : n+r<Fintype.card α) (o : α × TensorPowerProfile (α×α) (r+1))
    (i : α × TensorPowerProfile (α×α) r) :
    recordRightW hT (fixedRightEmbed ho p o) (fixedRightEmbed hi p i)=rightWOccupation p o i := by
  rw [recordRightW_coefficient,fixedRight_grade,fixedRight_label,fixedRight_label]
  simp only [hsize,true_and,profile_multiset_card]
  change (if MultisetRightStep _ _ ∧ BijProfile p o.2 then _ else _) = _
  simp only [fixedRight_step_bij,rightWOccupation]

theorem embedding_compression_rect {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c] (f : a→c) (g : b→c) (M : CMatrix c) :
    (basisEmbedding f).conjTranspose*M*basisEmbedding g=M.submatrix f g := by
  simp only [basisEmbedding,Matrix.conjTranspose_submatrix,Matrix.conjTranspose_one]
  change (1:CMatrix c).submatrix f (Equiv.refl c)*M*
    (1:CMatrix c).submatrix (Equiv.refl c) g=_
  rw [Matrix.one_submatrix_mul f (Equiv.refl c),Matrix.mul_submatrix_one (Equiv.refl c) g]
  rfl

theorem fixedRight_compression {n r T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (hi : n+r≤T) (ho : n+(r+1)≤T) (p : TensorPowerProfile (α×α) n)
    (hsize : n+r<Fintype.card α) :
    (basisEmbedding (fixedRightEmbed ho p)).conjTranspose*recordRightW hT*
      basisEmbedding (fixedRightEmbed hi p)=rightWOccupation p := by
  rw [embedding_compression_rect]
  ext o i
  exact fixedRight_coefficient hT hi ho p hsize o i

end
end ICO.MHWFixedSector
