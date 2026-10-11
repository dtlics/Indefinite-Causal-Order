import ICO.MHWordFreshProfile
import ICO.MHWRightSector

/-! Exact full-sector compression of the fresh left part of W's domain. -/
namespace ICO.MHWProfileLeft
open Matrix QIT ICO.MHWordProfiles ICO.MHWordFreshProfile ICO.MHWLeftProjection
  ICO.MHWFixedSector ICO.MHWRightSector ICO.MHBijectionProfiles
  ICO.MHOccupationCounts ICO.RecordingCopyIdentity ICO.RecordingMultisetBridge
  ICO.MHFockLabels ICO.MHFockProjection ICO.MHBoundedRecording
  ICO.MHWordDistinct ICO.MHWPartial
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1800000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def profileEmbed {l r T : ℕ} (h : l+r≤T) (p : ProfileBasis A l r) : InputCutoff (α := A) T :=
  rightSectorEmbed h ((p.1,p.2.2),p.2.1)

theorem profileEmbed_injective {l r T : ℕ} (h : l+r≤T) :
    Function.Injective (profileEmbed (A := A) h) := by
  intro i j he
  have hh := rightSector_injective h he
  apply Prod.ext
  · exact congrArg (fun p : RightSector (α := A) l r => p.1.1) hh
  apply Prod.ext
  · exact congrArg Prod.snd hh
  · exact congrArg (fun p : RightSector (α := A) l r => p.1.2) hh

theorem profileEmbed_label {l r T : ℕ} (h : l+r≤T) (p : ProfileBasis A l r) :
    fockLabel (profileEmbed h p)=(p.1,(occupationMultiset l p.2.1 : Multiset (A×A)),
      (occupationMultiset r p.2.2 : Multiset (A×A))) := rfl

theorem profileEmbed_grade {l r T : ℕ} (h : l+r≤T) (p : ProfileBasis A l r) :
    grade (profileEmbed h p)=l+r := rfl

theorem diagonal_submatrix_injective {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (g : X→Y) (hg : Function.Injective g) (a : Y→ℂ) :
    (Matrix.diagonal a).submatrix g g=Matrix.diagonal (a ∘ g) := by
  ext i j
  simp only [Matrix.submatrix_apply,Matrix.diagonal_apply,Function.comp_apply]
  by_cases he : i=j
  · subst j; simp
  · have hne : g i≠g j := fun hh => he (hg hh)
    simp [he,hne]

theorem left_profile_factor (l r : ℕ) :
    Matrix.diagonal (fun p : ProfileBasis A l r => if BijProfile p.2.1 p.2.2 ∧
      p.1∉domainLabels (occupationMultiset l p.2.1) (occupationMultiset r p.2.2) then 1 else 0) =
      profileProjection l r*profileFresh l r*profileProjection l r := by
  simp only [profileProjection,profileFresh,Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  split_ifs <;> simp_all

theorem record_left_compression {l r T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (h : l+r≤T) (hsize : l+r<Fintype.card A) :
    (basisEmbedding (profileEmbed (A := A) h)).conjTranspose*
      (basisEmbedding (ICO.MHFockNodup.setEmbedding hT)*leftProjection*
        (basisEmbedding (ICO.MHFockNodup.setEmbedding hT)).conjTranspose)*
          basisEmbedding (profileEmbed h)=
      (wordEmbedding (A := A) l r).conjTranspose*
        (distinctProjection*freshProjection*distinctProjection)*wordEmbedding l r := by
  rw [recordLeftProjection,embedding_compression_rect,
    fockLeftProjection,diagonal_submatrix_injective _ (profileEmbed_injective h),
    distinct_fresh_compression,← left_profile_factor]
  congr 1
  funext p
  simp only [Function.comp_apply,fockLeftPredicate,profileEmbed_label,profileEmbed_grade,
    hsize,and_true]
  rfl

#print axioms record_left_compression
end
end ICO.MHWProfileLeft
