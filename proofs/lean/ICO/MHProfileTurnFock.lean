import ICO.MHProfileBlocks
import ICO.MHActualDomainTwirl
import ICO.MHFockBothCovariance

/-! The physical rotation and missing-domain projector are exact coherent
direct sums of the checked occupation-profile blocks. -/
namespace ICO.MHProfileTurnFock
open QIT ICO.MHWordProfiles ICO.MHWProfileLeft ICO.MHBoundedRecording ICO.MHProfileBlocks
  ICO.MHFockSpace ICO.MHFockProjection ICO.MHFockRotation ICO.MHFockTransport
  ICO.MHFockBothCovariance ICO.RecordingCopyIdentity ICO.MHWEmbedding ICO.MHWLengths
  ICO.MHWDomainProjection ICO.MHActualDomainTwirl ICO.MHWordRotation
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2500000
variable {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α]

def profileBlocks (T : ℕ) (F : ∀ s : Lengths T, CMatrix (ProfileBasis α s.val.1.val s.val.2.val)) :
    CMatrix (InputCutoff (α := α) T) :=
  (Matrix.blockDiagonal' F).submatrix (profileFockEquiv T) (profileFockEquiv T)

theorem profileBlocks_mul (T : ℕ) (F G : ∀ s : Lengths T, CMatrix (ProfileBasis α s.val.1.val s.val.2.val)) :
    profileBlocks T F*profileBlocks T G=profileBlocks T (fun s => F s*G s) := by
  simp only [profileBlocks,Matrix.submatrix_mul_equiv,← Matrix.blockDiagonal'_mul]

theorem profileBlocks_adjoint (T : ℕ) (F : ∀ s : Lengths T, CMatrix (ProfileBasis α s.val.1.val s.val.2.val)) :
    (profileBlocks T F).conjTranspose=profileBlocks T (fun s => (F s).conjTranspose) := by
  simp only [profileBlocks,Matrix.conjTranspose_submatrix,Matrix.blockDiagonal'_conjTranspose]

def actualTurn (C D : Matrix.unitaryGroup α ℂ) (T : ℕ) : CMatrix (InputCutoff (α := α) T) :=
  (fockQuery C T : CMatrix (InputCutoff (α := α) T))*(fockQ C D T : CMatrix (InputCutoff (α := α) T))

theorem actual_turn_profileBlocks (C D : Matrix.unitaryGroup α ℂ) (T : ℕ) :
    actualTurn C D T=profileBlocks T (fun s : Lengths T =>
      (profileTurn C D s.val.1.val s.val.2.val : CMatrix (ProfileBasis α s.val.1.val s.val.2.val))) := by
  rw [actualTurn,fockQuery_fockQ]
  ext ⟨⟨s,q⟩,x,p⟩ ⟨⟨s',q'⟩,y,p'⟩
  by_cases he : s=s'
  · subst s'
    rw [inputFamily_same]
    simp only [profileBlocks,Matrix.submatrix_apply,profileFockEquiv,Equiv.coe_fn_mk,
      Matrix.blockDiagonal'_apply_eq]
    simp only [ICO.MHSectorCovariance.inputTurn,ICO.MHSectorCovariance.tensorUnitary,
      profileTurn,ICO.MHWordRotation.tensorUnitary,Matrix.kronecker,Matrix.kroneckerMap_apply]
    ring
  · rw [inputFamily_other _ _ _ _ he]
    simp [profileBlocks,profileFockEquiv,Matrix.submatrix_apply,Matrix.blockDiagonal'_apply,he]

theorem actualTurn_cutoff (C D : Matrix.unitaryGroup α ℂ) {t T : ℕ} (ht : t≤T) :
    actualTurn C D T*basisEmbedding (inputEmbed (α := α) ht)=
      basisEmbedding (inputEmbed ht)*actualTurn C D t := by
  simp only [actualTurn,fockQuery_fockQ]
  exact inputFamily_intertwine _ ht

def missingMatrix {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) : CMatrix (InputCutoff (α := α) T) :=
  bijProjection T-(recordW hT).conjTranspose*recordW hT

theorem missingMatrix_lengths {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (o i : InputCutoff (α := α) T) (h : missingMatrix hT o i≠0) : o.1.1=i.1.1 := by
  by_contra hn
  have hoi : o≠i := fun he => hn (congrArg (fun v : InputCutoff (α := α) T => v.1.1) he)
  have hg : ((recordW hT).conjTranspose*recordW hT) o i=0 := by
    by_contra hz
    exact hn (recordGram_lengths hT o i hz)
  exact h (by simp [missingMatrix,bijProjection,Matrix.sub_apply,hoi,hg])

def boundedMissing {t T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (ht : t≤T) :
    CMatrix (InputCutoff (α := α) t) :=
  (basisEmbedding (inputEmbed ht)).conjTranspose*missingMatrix hT*basisEmbedding (inputEmbed ht)

theorem boundedMissing_lengths {t T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (ht : t≤T)
    (o i : InputCutoff (α := α) t) (h : boundedMissing hT ht o i≠0) : o.1.1=i.1.1 := by
  rw [boundedMissing,basisEmbedding_compression] at h
  exact lengthEmbed_injective ht (missingMatrix_lengths hT (inputEmbed ht o) (inputEmbed ht i) h)

theorem boundedMissing_sector {t T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (ht : t≤T)
    (s : Lengths t) :
    (boundedMissing hT ht).submatrix (profileEmbed (A := α) s.property) (profileEmbed s.property)=
      sectorMissing hT (s.property.trans ht) := by
  rw [boundedMissing,basisEmbedding_compression,sectorMissing,basisEmbedding_compression]
  rfl

theorem boundedMissing_profileBlocks {t T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (ht : t≤T) :
    boundedMissing hT ht=profileBlocks t (fun s : Lengths t => sectorMissing hT (s.property.trans ht)) := by
  rw [matrix_profile_blocks t (boundedMissing hT ht) (boundedMissing_lengths hT ht)]
  simp only [boundedMissing_sector,profileBlocks]

theorem compressed_missing_conjugation (C D : Matrix.unitaryGroup α ℂ) {t T : ℕ}
    (hT : 2*Fintype.card (α×α)≤T) (ht : t≤T) :
    (basisEmbedding (inputEmbed (α := α) ht)).conjTranspose*
      ((actualTurn C D T).conjTranspose*missingMatrix hT*actualTurn C D T)*
        basisEmbedding (inputEmbed ht)=
      profileBlocks t (fun s : Lengths t =>
        (profileTurn C D s.val.1.val s.val.2.val : CMatrix (ProfileBasis α s.val.1.val s.val.2.val)).conjTranspose*
          sectorMissing hT (s.property.trans ht)*
            (profileTurn C D s.val.1.val s.val.2.val : CMatrix (ProfileBasis α s.val.1.val s.val.2.val))) := by
  have hturn := actualTurn_cutoff C D ht
  have ha := congrArg Matrix.conjTranspose hturn
  simp only [Matrix.conjTranspose_mul] at ha
  calc
    _ = (actualTurn C D t).conjTranspose*boundedMissing hT ht*actualTurn C D t := by
      simp only [boundedMissing,Matrix.mul_assoc]
      rw [hturn]
      simp only [← Matrix.mul_assoc]
      rw [ha]
    _ = _ := by
      rw [actual_turn_profileBlocks,boundedMissing_profileBlocks,profileBlocks_adjoint,
        profileBlocks_mul,profileBlocks_mul]

end
end ICO.MHProfileTurnFock
