import ICO.MHWProfileRight
import ICO.MHWLengths
import ICO.MHWordOccupationTurn
import ICO.MHWordDomain

/-! Exact identification of every low-length block of the physical W-domain
with the distinct-record fresh/Bell model used in the Haar bound. -/
namespace ICO.MHWDomainModel
open QIT ICO.MHWordProfiles ICO.MHWordDistinct ICO.MHWordDomain ICO.MHWordRotation
  ICO.MHWProfileLeft ICO.MHWProfileRight ICO.MHWLengths ICO.MHWLeftProjection
  ICO.MHWEmbedding ICO.MHWRecordEntries ICO.MHWDomainProjection ICO.MHFockNodup
  ICO.MHFockLabels ICO.MHOccupationCounts ICO.MHBijectionProfiles ICO.RecordingCopyIdentity
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2500000
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

def domainScale (l r : ℕ) : ℝ :=
  if r=0 then 1 else (Fintype.card α : ℝ)/((Fintype.card α : ℝ)-l-((r-1 : ℕ) : ℝ))

theorem sum_rightSlots (l r : ℕ) (f : (Fin l⊕Fin r)→CMatrix (WordBasis α (Fin l⊕Fin r))) :
    (∑ j∈rightSlots l r,f j)=∑ j : Fin r,f (Sum.inr j) := by
  simp only [rightSlots,Finset.sum_map,Function.Embedding.coeFn_mk]

theorem profile_bij_compression {l r T : ℕ} (h : l+r≤T) :
    (basisEmbedding (profileEmbed (A := α) h)).conjTranspose*bijProjection T*
      basisEmbedding (profileEmbed h)=profileProjection l r := by
  rw [basisEmbedding_compression,bijProjection,
    diagonal_submatrix_injective _ (profileEmbed_injective h)]
  rfl

theorem profile_right_empty {l T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (h : l+0≤T) :
    (basisEmbedding (profileEmbed (A := α) (l := l) (r := 0) h)).conjTranspose*
      (recordRightW hT*(recordRightW hT).conjTranspose)*basisEmbedding (profileEmbed (A := α) (l := l) (r := 0) h)=0 := by
  rw [basisEmbedding_compression]
  ext o i
  exact rightImage_empty_row hT (profileEmbed h o) (profileEmbed h i) rfl

theorem record_domain_compression {l r T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (h : l+r≤T) (hsize : l+r<Fintype.card α) :
    (basisEmbedding (profileEmbed (A := α) h)).conjTranspose*
      ((recordW hT).conjTranspose*recordW hT)*basisEmbedding (profileEmbed h)=
      (wordEmbedding (A := α) l r).conjTranspose*
        domainModel (rightSlots l r) (domainScale (α := α) l r)*wordEmbedding l r := by
  rw [recordGram_decomposition,Matrix.mul_add,Matrix.add_mul]
  have hleft := record_left_compression hT h hsize
  rw [recordLeftProjection] at hleft
  rw [hleft]
  cases r with
  | zero =>
    rw [profile_right_empty hT h,add_zero]
    simp [domainModel,rightSlots]
  | succ r =>
    have hi : l+r≤T := by omega
    have hs : l+r<Fintype.card α := by omega
    rw [record_right_compression hT hi h hs]
    simp only [domainModel,domainScale,Nat.add_eq_zero_iff,Nat.succ_ne_zero,if_false,
      Nat.add_sub_cancel,sum_rightSlots,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul]

theorem missing_domain_compression {l r T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (h : l+r≤T) (hsize : l+r<Fintype.card α) :
    (basisEmbedding (profileEmbed (A := α) h)).conjTranspose*
      (bijProjection T-(recordW hT).conjTranspose*recordW hT)*basisEmbedding (profileEmbed h)=
      (wordEmbedding (A := α) l r).conjTranspose*
        (distinctProjection-domainModel (rightSlots l r) (domainScale (α := α) l r))*wordEmbedding l r := by
  rw [Matrix.mul_sub,Matrix.sub_mul,profile_bij_compression,record_domain_compression hT h hsize]
  rw [Matrix.mul_sub,Matrix.sub_mul,distinct_projection_compression]

end
end ICO.MHWDomainModel
