import ICO.MHWDomainProjection
import ICO.MHWFixedSector
import ICO.MHWordProfileGram

/-! Literal fresh-domain projector of the finite partial oracle, after its
embedding in unrestricted occupation coordinates. -/
namespace ICO.MHWLeftProjection
open Matrix QIT ICO.MHWPartial ICO.MHWDomainProjection ICO.MHFockNodup
  ICO.MHFockLabels ICO.MHFockSpace ICO.MHBijectionProfiles ICO.MHEmbeddingProjector
  ICO.MHBoundedRecording ICO.RecordingMultisetBridge ICO.RecordingCopyIdentity
  ICO.MHWFixedSector ICO.MHWordProfiles
open ICO.MHFockProjection ICO.RecordingOperatorSupport
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2000000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {α : Type*} [Fintype α] [DecidableEq α]

def fockLeftPredicate {T : ℕ} (i : InputCutoff (α := α) T) : Prop :=
  BijMultiset (fockLabel i).2.1 (fockLabel i).2.2 ∧
    (fockLabel i).1 ∉ domainLabels (fockLabel i).2.1 (fockLabel i).2.2 ∧
      grade i<Fintype.card α

def fockLeftProjection (T : ℕ) : CMatrix (InputCutoff (α := α) T) :=
  Matrix.diagonal (fun i => if fockLeftPredicate i then 1 else 0)

theorem embedded_predicate {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (i : Basis α) :
    fockLeftPredicate (setEmbedding hT i) ↔ leftPredicate i := by
  simp only [fockLeftPredicate,setEmbedding_label,setEmbedding_grade,embed,
    bijMultiset_sets,domainLabels,Finset.val_toFinset,leftPredicate,
    freshLeft_iff_not_mem_domain]

theorem projection_intertwine {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) :
    fockLeftProjection T*basisEmbedding (setEmbedding hT)=
      basisEmbedding (setEmbedding hT)*leftProjection := by
  ext o i
  simp only [fockLeftProjection,leftProjection,predicateProjection,
    Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases he : o=setEmbedding hT i
  · subst o
    simp only [embedded_predicate]
    exact mul_comm _ _
  · simp [basisEmbedding,Matrix.submatrix_apply,Matrix.one_apply,he]

theorem projection_nodup {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) :
    fockLeftProjection T*(basisEmbedding (setEmbedding hT)*
      (basisEmbedding (setEmbedding hT)).conjTranspose)=fockLeftProjection T := by
  rw [basisEmbedding_image _ (setEmbedding_injective hT)]
  simp only [fockLeftProjection,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hp : fockLeftPredicate i
  · have hr : ∃ j, setEmbedding hT j=i :=
      (setEmbedding_range hT i).mpr (bijMultiset_nodup hp.1)
    simp [hp,hr]
  · simp [hp]

theorem recordLeftProjection {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) :
    basisEmbedding (setEmbedding hT)*leftProjection*
      (basisEmbedding (setEmbedding hT)).conjTranspose=fockLeftProjection T := by
  rw [← projection_intertwine,Matrix.mul_assoc,projection_nodup]

#print axioms recordLeftProjection
end
end ICO.MHWLeftProjection
