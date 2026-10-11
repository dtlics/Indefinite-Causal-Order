import ICO.RecordingRetainedProcess
import QIT.Core.Pure

/-! Exact correspondence between a supported purified modified wrapper and
the retained-record CP wrapper after discarding its copied query label. -/

namespace ICO.RecordingPureCorrespondence

open QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport
  ICO.RecordingFreshOutput ICO.RecordingRetainedProcess
  ICO.RecordingActiveWrapper ICO.RecordingSupportCompression
  ICO.RecordingCopyIdentity ICO.RecordingProcess
open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section

variable {a b c μ e : Type*} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype μ] [DecidableEq μ] [Fintype e]

theorem tensor_mulVec_apply (A : Matrix b a ℂ) (v : a × μ → ℂ) (x : b) (i : μ) :
    (Matrix.kronecker A (1 : CMatrix μ) *ᵥ v) (x, i) =
      ∑ s, A x s * v (s, i) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem ofKraus_tensor_rankOne (K : e → Matrix b a ℂ) (v : a × μ → ℂ) :
    MatrixMap.kron (MatrixMap.ofKraus K) (Channel.idChannel μ).map (rankOneMatrix v) =
      ∑ k, rankOneMatrix (Matrix.kronecker (K k) (1 : CMatrix μ) *ᵥ v) := by
  ext x y
  rcases x with ⟨x, i⟩
  rcases y with ⟨y, j⟩
  rw [MatrixMap.kron_idChannel_apply_slice]
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply, rankOneMatrix_apply, tensor_mulVec_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem rectSingle_tensor_rankOne (A : Matrix b a ℂ) (v : a × μ → ℂ) :
    MatrixMap.kron (rectSingleOperatorMap A) (Channel.idChannel μ).map (rankOneMatrix v) =
      rankOneMatrix (Matrix.kronecker A (1 : CMatrix μ) *ᵥ v) := by
  simpa only [rectSingleOperatorMap, Finset.univ_unique, Finset.sum_singleton] using
    (ofKraus_tensor_rankOne (fun _ : Unit => A) v)

theorem tensor_comp_identity (Φ : MatrixMap a b) (Ψ : MatrixMap b c)
    (ρ : CMatrix (a × μ)) :
    MatrixMap.kron (Ψ.comp Φ) (Channel.idChannel μ).map ρ =
      MatrixMap.kron Ψ (Channel.idChannel μ).map
        (MatrixMap.kron Φ (Channel.idChannel μ).map ρ) := by
  ext u v
  simp only [MatrixMap.kron_idChannel_apply_slice, LinearMap.comp_apply]

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem active_compression_mulVec (m : ℕ) (v : Basis α × μ → ℂ) :
    Matrix.kronecker (basisEmbedding (activeSourceEmbed m)).conjTranspose
      (1 : CMatrix μ) *ᵥ v = v ∘ activeMemoryEmbed m := by
  funext s
  rcases s with ⟨s, i⟩
  rw [tensor_mulVec_apply]
  simp [basisEmbedding, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
    Matrix.one_apply, activeSourceEmbed, activeMemoryEmbed]

theorem activeInverse_rankOne (m : ℕ) (v : Basis α × μ → ℂ) :
    activeInverseWithMemory m (rankOneMatrix v) =
      rankOneMatrix ((Matrix.kronecker inverseRecording (1 : CMatrix μ) *ᵥ v) ∘
        activeMemoryEmbed m) := by
  rw [activeInverseWithMemory, activeInverse, tensor_comp_identity]
  change MatrixMap.kron (rectSingleOperatorMap (basisEmbedding (activeSourceEmbed m)).conjTranspose)
    (Channel.idChannel μ).map
    (MatrixMap.kron (rectSingleOperatorMap inverseRecording) (Channel.idChannel μ).map
      (rankOneMatrix v)) = _
  rw [rectSingle_tensor_rankOne, rectSingle_tensor_rankOne, active_compression_mulVec]

theorem mul_basisEmbedding (M : Matrix b a ℂ) (f : c → a) :
    M * basisEmbedding f = M.submatrix id f := by
  change M * (1 : CMatrix a).submatrix (Equiv.refl a) f = _
  rw [Matrix.mul_submatrix_one (Equiv.refl a) f]
  rfl

def restrictedCopiedInsertion (m : ℕ) :
    Matrix (Basis α × (α × μ)) (ActiveSource α m × μ) ℂ :=
  Matrix.kronecker leftInsertion (1 : CMatrix (α × μ)) *
    copyQuery * basisEmbedding (activeMemoryEmbed m)

theorem restrictedCopiedInsertion_entry (m : ℕ) (o : Basis α) (x : α) (i : μ)
    (s : ActiveSource α m) (j : μ) :
    restrictedCopiedInsertion m (o, (x, i)) (s, j) =
      Matrix.kronecker (retainedLeftKraus m x) (1 : CMatrix μ) (o, i) (s, j) := by
  rw [restrictedCopiedInsertion, copyQuery_eq_embedding, mul_basisEmbedding,
    mul_basisEmbedding]
  simp only [Matrix.submatrix_apply, id_eq, copiedLabel, activeMemoryEmbed,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq,
    retainedLeftKraus]
  by_cases hx : x = s.val.val.1 <;> by_cases hi : i = j <;> simp [hx, hi]

theorem restrictedCopiedInsertion_branch (m : ℕ) (θ : ActiveSource α m × μ → ℂ)
    (o : Basis α) (x : α) (i : μ) :
    (restrictedCopiedInsertion m *ᵥ θ) (o, (x, i)) =
      (Matrix.kronecker (retainedLeftKraus m x) (1 : CMatrix μ) *ᵥ θ) (o, i) := by
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro s _
  rw [restrictedCopiedInsertion_entry]

theorem modifiedWrapper_restricted (m : ℕ) (v : Basis α × μ → ℂ)
    (hv : ∀ i, v i ≠ 0 → Good i.1.2.1 i.1.2.2 ∧
      i.1.2.1.card + i.1.2.2.card ≤ m) :
    modifiedWrapper v = restrictedCopiedInsertion (m + 1) *ᵥ
      ((Matrix.kronecker inverseRecording (1 : CMatrix μ) *ᵥ v) ∘
        activeMemoryEmbed (m + 1)) := by
  simp only [restrictedCopiedInsertion, ← Matrix.mulVec_mulVec]
  rw [inverse_active_compression_recovers m v hv]
  rfl

def eraseCopied (X : CMatrix (Basis α × (α × μ))) : CMatrix (Basis α × μ) :=
  fun u v => ∑ x, X (u.1, (x, u.2)) (v.1, (x, v.2))

theorem eraseCopied_rankOne (v : Basis α × (α × μ) → ℂ) :
    eraseCopied (rankOneMatrix v) =
      ∑ x, rankOneMatrix (fun u : Basis α × μ => v (u.1, (x, u.2))) := by
  ext u w
  simp only [eraseCopied, Matrix.sum_apply, rankOneMatrix_apply]

/-- The active-basis compression is invisible on the actual supported pure
    wrapper. Discarding precisely its newly copied private label gives the
    retained-record CP process, with the same subnormalized mass. -/
theorem retainedGrowingWrapper_rankOne (m : ℕ) (v : Basis α × μ → ℂ)
    (hv : ∀ i, v i ≠ 0 → Good i.1.2.1 i.1.2.2 ∧
      i.1.2.1.card + i.1.2.2.card ≤ m) :
    retainedGrowingWrapper (m + 1) (rankOneMatrix v) =
      eraseCopied (rankOneMatrix (modifiedWrapper v)) := by
  rw [retainedGrowingWrapper, activeInverse_rankOne, ofKraus_tensor_rankOne,
    eraseCopied_rankOne, modifiedWrapper_restricted m v hv]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  funext u
  exact (restrictedCopiedInsertion_branch (m + 1) _ u.1 x u.2).symm

end
end ICO.RecordingPureCorrespondence
