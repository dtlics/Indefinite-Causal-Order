import ICO.MHWLeftProjection

/-! Fresh-query equality is preserved by the normalized two-word occupation
embedding, including coherent superpositions of both occupation profiles. -/
namespace ICO.MHWordFreshProfile
open Matrix QIT ICO.MHWordDistinct ICO.MHWordProfiles ICO.MHBijectionProfiles
  ICO.MHOccupationCounts ICO.RecordingMultisetBridge ICO.MHSymmetric
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1800000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem wordEmbedding_support {l r : ℕ} (w : WordBasis A (Fin l ⊕ Fin r))
    (p : ProfileBasis A l r) (h : wordEmbedding l r w p≠0) :
    w.1=p.1 ∧ wordProfile (leftWord w.2)=p.2.1 ∧ wordProfile (rightWord w.2)=p.2.2 := by
  have hx : w.1=p.1 := by
    by_contra hn
    exact h (by simp [wordEmbedding,hn])
  have hl : leftWord w.2∈tensorPowerProfileClass p.2.1 := by
    by_contra hn
    exact h (by simp [wordEmbedding,occupationEmbedding,tensorPowerProfileUnitVector,hn])
  have hr : rightWord w.2∈tensorPowerProfileClass p.2.2 := by
    by_contra hn
    exact h (by simp [wordEmbedding,occupationEmbedding,tensorPowerProfileUnitVector,hn])
  exact ⟨hx,wordProfile_of_mem _ _ hl,wordProfile_of_mem _ _ hr⟩

theorem word_fresh_iff {l r : ℕ} (w : Fin l ⊕ Fin r → A×A) (x : A) :
    (∀ j, x≠(w j).1) ↔
      x ∉ domainLabels (occupationMultiset l (wordProfile (leftWord w)))
        (occupationMultiset r (wordProfile (rightWord w))) := by
  rw [domainLabels_mem,wordProfile_multiset,wordProfile_multiset,← enumeration_sum]
  simp [enumeration,Multiset.map_map,Function.comp_def,eq_comm]

def profileFresh (l r : ℕ) : CMatrix (ProfileBasis A l r) :=
  Matrix.diagonal (fun p => if p.1∉domainLabels (occupationMultiset l p.2.1)
    (occupationMultiset r p.2.2) then 1 else 0)

theorem fresh_projection_intertwining (l r : ℕ) :
    freshProjection (A := A) (J := Fin l ⊕ Fin r)*wordEmbedding l r=
      wordEmbedding l r*profileFresh l r := by
  ext w p
  simp only [freshProjection,profileFresh,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases hz : wordEmbedding l r w p=0
  · simp [hz]
  · obtain ⟨hx,hl,hr⟩ := wordEmbedding_support w p hz
    have he : (∀ j, w.1≠(w.2 j).1) ↔
      p.1∉domainLabels (occupationMultiset l p.2.1) (occupationMultiset r p.2.2) := by
      rw [word_fresh_iff,hx,hl,hr]
    simp only [he]
    split_ifs <;> simp

theorem fresh_projection_compression (l r : ℕ) :
    (wordEmbedding (A := A) l r).conjTranspose*freshProjection*wordEmbedding l r=
      profileFresh l r := by
  rw [Matrix.mul_assoc,fresh_projection_intertwining,← Matrix.mul_assoc,
    wordEmbedding_gram,Matrix.one_mul]

theorem distinct_fresh_compression (l r : ℕ) :
    (wordEmbedding (A := A) l r).conjTranspose*
      (distinctProjection*freshProjection*distinctProjection)*wordEmbedding l r=
        profileProjection l r*profileFresh l r*profileProjection l r := by
  have hp : (distinctProjection (A := A) (J := Fin l ⊕ Fin r)).conjTranspose=distinctProjection :=
    distinct_projection.isSelfAdjoint.star_eq
  have hj := congrArg Matrix.conjTranspose (distinct_projection_intertwining (A := A) l r)
  have hprof : (profileProjection (A := A) l r).conjTranspose=profileProjection l r := by
    ext i j
    by_cases he : i=j
    · subst j; simp [profileProjection]
    · simp [profileProjection,Matrix.conjTranspose_apply,he,Ne.symm he]
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hp,hprof] at hj
  simp only [Matrix.mul_assoc]
  rw [distinct_projection_intertwining]
  simp only [← Matrix.mul_assoc]
  rw [hj]
  have he := congrArg (fun M => profileProjection (A := A) l r*M*profileProjection l r)
    (fresh_projection_compression (A := A) l r)
  simpa only [Matrix.mul_assoc] using he

#print axioms fresh_projection_intertwining
#print axioms distinct_fresh_compression
end
end ICO.MHWordFreshProfile
