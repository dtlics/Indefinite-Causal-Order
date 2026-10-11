import ICO.MHFockFiniteTrajectory
import ICO.MHFockRotationErasure
import ICO.RecordingRetainedProcess

/-! Canonical finite-set-to-occupation embedding preserves the entire
accessible density matrix after the private records are erased. -/
namespace ICO.MHFockFiniteErasure
open QIT ICO.MHFockFiniteKnown ICO.MHFockKnownOperation ICO.MHFockNodup
  ICO.MHFockLabels ICO.MHBoundedRecording ICO.RecordingOperatorSupport
  ICO.RecordingCopyIdentity ICO.MHDecompressionErasure ICO.RecordingRetainedProcess ICO.PathRecordingSupport
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 512
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

def finiteFirst (μ : Type*) : (Basis α×μ)≃(α×μ)×(Relation α α×Relation α α) where
  toFun i := ((i.1.1,i.2),i.1.2)
  invFun i := ((i.1.1,i.2),i.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def recordSetEmbedding {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (lr : Relation α α×Relation α α) : Records (α := α) T :=
  records (setEmbedding hT (Classical.arbitrary α,lr))

theorem recordSetEmbedding_injective {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) :
    Function.Injective (recordSetEmbedding hT) := by
  intro lr lr' he
  exact (set_records_eq hT _ _).mp he

theorem setMemory_tensor_coordinates {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    {μ : Type*} (i : Basis α×μ) :
    queryMemoryFirst T μ (setMemory hT i)=
      ((finiteFirst μ i).1,recordSetEmbedding hT (finiteFirst μ i).2) := by
  apply Prod.ext
  · rfl
  · exact (set_records_eq hT _ _).mpr rfl

theorem setMemory_private_tensor {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    {μ : Type*} [Fintype μ] [DecidableEq μ] :
    basisEmbedding (setMemory hT (μ := μ))=
      (Matrix.kronecker (1 : CMatrix (α×μ)) (basisEmbedding (recordSetEmbedding hT))).submatrix
        (queryMemoryFirst T μ) (finiteFirst μ) := by
  ext o i
  have he : o=setMemory hT i ↔
      (queryMemoryFirst T μ o).1=(finiteFirst μ i).1 ∧
      (queryMemoryFirst T μ o).2=recordSetEmbedding hT (finiteFirst μ i).2 := by
    rw [←(queryMemoryFirst T μ).injective.eq_iff,setMemory_tensor_coordinates,Prod.ext_iff]
  simp only [basisEmbedding,Matrix.submatrix_apply,id_eq,Matrix.one_apply,
    Matrix.kronecker,Matrix.kroneckerMap_apply]
  simp only [he]
  split_ifs <;> simp_all

theorem finite_visible_reindex {μ : Type*} [Fintype μ] [DecidableEq μ] (v : Basis α×μ→ℂ) :
    partialTraceB (rankOneMatrix (v ∘ (finiteFirst μ).symm))=visibleMap (rankOneMatrix v) := by
  ext i j
  rcases i with ⟨x,m⟩
  rcases j with ⟨y,n⟩
  rw [visibleMap_apply]
  rfl

theorem setMemory_visible {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    {μ : Type*} [Fintype μ] [DecidableEq μ] (v : Basis α×μ→ℂ) :
    fockVisible T (basisEmbedding (setMemory hT)*ᵥv)=visibleMap (rankOneMatrix v) := by
  rw [fockVisible,setMemory_private_tensor,Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id]
  rw [private_erasure (basisEmbedding (recordSetEmbedding hT)) _ (by
    simp only [basisEmbedding_gram _ (recordSetEmbedding_injective hT),Matrix.kronecker,
      Matrix.one_kronecker_one,Matrix.one_mulVec])]
  exact finite_visible_reindex v

#print axioms setMemory_visible
end
end ICO.MHFockFiniteErasure
