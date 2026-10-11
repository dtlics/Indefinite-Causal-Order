import ICO.C6MatrixCovariance

/-! Reindexing finite systems as genuine trace-preserving quantum channels. -/
namespace ICO.C6ReindexChannel
open QIT Matrix ICO.C6MatrixCovariance ICO.RecordingCopyIdentity
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def channel (e : b ≃ a) : Channel a b :=
  isometryChannel (basisEmbedding e.symm) (basisEmbedding_gram _ e.symm.injective)

theorem apply (e : b ≃ a) (X : CMatrix a) :
    (channel e).map X = X.submatrix e e := by
  change ICO.C6CacheMap.conjugate (basisEmbedding e.symm) X = _
  rw [ICO.C6CacheMap.conjugate_apply]
  ext i j
  simp [basisEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Function.id_def, apply_ite, ← e.apply_eq_iff_eq_symm_apply]
  have he (x : a) : e.symm x = j ↔ x = e j := by
    constructor
    · intro h
      simpa only [Equiv.apply_symm_apply] using congrArg e h
    · intro h
      simp [h]
  simp [he]

#print axioms apply
end
end ICO.C6ReindexChannel
