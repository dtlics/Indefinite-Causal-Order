import ICO.C6SectorChannel
import ICO.MHFockRotation

/-! Exact covariance of private sector embeddings and state compression. -/
namespace ICO.C6SectorCovariance
open QIT Matrix ICO.C6SectorChannel ICO.C6MatrixCovariance ICO.RecordingCopyIdentity
  ICO.MHFockRotation
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1600000
universe u v
variable {I : Type v} [Fintype I] [DecidableEq I]
  {H : I → Type u} [∀i,Fintype (H i)] [∀i,DecidableEq (H i)]

theorem inclusion_covariance (U : ∀i,Matrix.unitaryGroup (H i) ℂ) (i : I) :
    (blockUnitary U : CMatrix (Σi,H i))*inclusion i =
      inclusion i*(U i : CMatrix (H i)) := by
  have he : (blockUnitary U : CMatrix (Σi,H i))*inclusion i =
      (blockUnitary U : CMatrix (Σi,H i)).submatrix id (Sigma.mk i) := by
    simp only [inclusion, basisEmbedding]
    change (blockUnitary U : CMatrix (Σi,H i))*(1 : CMatrix (Σi,H i)).submatrix
      (Equiv.refl _) (Sigma.mk i)=_
    rw [Matrix.mul_submatrix_one (Equiv.refl _) (Sigma.mk i)]
    rfl
  rw [he]
  ext ⟨j,x⟩ a
  by_cases h : j=i
  · subst j
    simp [blockUnitary, Matrix.submatrix_apply, Matrix.mul_apply, inclusion,
      basisEmbedding, Matrix.one_apply, Sigma.mk.inj_iff]
  · simp [blockUnitary, Matrix.submatrix_apply, Matrix.mul_apply, inclusion,
      basisEmbedding, Matrix.one_apply, Sigma.mk.inj_iff, h]
    exact Matrix.blockDiagonal'_apply_ne (fun j => (U j : CMatrix (H j))) x a h

theorem encode_sector_invariant (U : ∀i,Matrix.unitaryGroup (H i) ℂ) (i : I)
    (X : CMatrix (H i)) (h : (U i : CMatrix (H i))*X=X*(U i : CMatrix (H i))) :
    (blockUnitary U : CMatrix (Σi,H i))*(inclusion i*X*(inclusion i).conjTranspose)=
      inclusion i*X*(inclusion i).conjTranspose*(blockUnitary U : CMatrix (Σi,H i)) :=
  encode_invariant _ (U i) (blockUnitary U) (inclusion_covariance U i) X h

theorem decode_sector_invariant (U : ∀i,Matrix.unitaryGroup (H i) ℂ) (i : I)
    (X : CMatrix (Σi,H i))
    (h : (blockUnitary U : CMatrix (Σi,H i))*X=X*(blockUnitary U : CMatrix (Σi,H i))) :
    (U i : CMatrix (H i))*((inclusion i).conjTranspose*X*inclusion i)=
      (inclusion i).conjTranspose*X*inclusion i*(U i : CMatrix (H i)) :=
  decode_invariant _ (U i) (blockUnitary U) (inclusion_covariance U i) X h

theorem block_mass (X : CMatrix (Σi,H i)) :
    (∑i : I,((inclusion i).conjTranspose*X*inclusion i).trace)=X.trace := by
  have ht (i : I) : ((inclusion i).conjTranspose*X*inclusion i).trace=
      (inclusion i*(inclusion i).conjTranspose*X).trace := by
    simpa only [ICO.C6CacheMap.conjugate_apply,Matrix.conjTranspose_conjTranspose]
      using ICO.C6CacheMap.conjugate_trace (inclusion (H := H) i).conjTranspose X
  simp_rw [ht]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, inclusion_complete, Matrix.one_mul]

#print axioms inclusion_covariance
#print axioms block_mass
end
end ICO.C6SectorCovariance
