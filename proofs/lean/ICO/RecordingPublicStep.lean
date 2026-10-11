import ICO.RecordingPublicHistory

/-! A public isometry, lifted over all private copied labels, is an actual
isometry in the purified recording recurrence. -/

namespace ICO.RecordingPublicStep

open QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport
  ICO.RecordingPublicHistory ICO.RecordingPureCorrespondence
  ICO.RecordingProcess ICO.RecordingRemovalNorm
open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section

variable {α μ ν h : Type*} [Fintype α] [DecidableEq α]
  [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]
  [Fintype h] [DecidableEq h]

def publicFirst (α h μ : Type*) : (α × (h × μ)) ≃ ((α × μ) × h) where
  toFun u := ((u.1, u.2.2), u.2.1)
  invFun u := (u.1.1, (u.2, u.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem historyKnown_eq_tensor (K : Matrix (α × ν) (α × μ) ℂ) :
    historyKnown (h := h) K = (Matrix.kronecker K (1 : CMatrix h)).submatrix
      (publicFirst α h ν) (publicFirst α h μ) := by
  ext o i
  simp only [historyKnown, Matrix.submatrix_apply, publicFirst, Equiv.coe_fn_mk,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
  by_cases he : o.2.1 = i.2.1 <;> simp [he]

theorem historyKnown_isometry (K : Matrix (α × ν) (α × μ) ℂ)
    (hK : K.conjTranspose * K = 1) :
    (historyKnown (h := h) K).conjTranspose * historyKnown (h := h) K = 1 := by
  have hAdj : (Matrix.kronecker K (1 : CMatrix h)).conjTranspose =
      Matrix.kronecker K.conjTranspose (1 : CMatrix h) :=
    (Matrix.conjTranspose_kronecker K (1 : CMatrix h)).trans
      (by rw [Matrix.conjTranspose_one]; rfl)
  have hGram : Matrix.kronecker K.conjTranspose (1 : CMatrix h) *
      Matrix.kronecker K (1 : CMatrix h) =
      Matrix.kronecker (K.conjTranspose * K) (1 : CMatrix h) := by
    symm
    simpa only [Matrix.one_mul] using
      Matrix.mul_kronecker_mul K.conjTranspose K (1 : CMatrix h) (1 : CMatrix h)
  rw [historyKnown_eq_tensor, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, hAdj, hGram, hK]
  have hOne : Matrix.kronecker (1 : CMatrix (α × μ)) (1 : CMatrix h) = 1 :=
    Matrix.one_kronecker_one
  rw [hOne, Matrix.submatrix_one_equiv]

def regroupInput (α h μ : Type*) : (α × (α × (h × μ))) ≃ (α × ((α × h) × μ)) where
  toFun u := (u.1, ((u.2.1, u.2.2.1), u.2.2.2))
  invFun u := (u.1, (u.2.1.1, (u.2.1.2, u.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

def publicStep (K : Matrix (α × ν) (α × μ) ℂ) :
    Matrix (α × ((α × h) × ν)) (α × (α × (h × μ))) ℂ :=
  (historyKnown K).submatrix id (regroupInput α h μ)

theorem publicStep_isometry (K : Matrix (α × ν) (α × μ) ℂ)
    (hK : K.conjTranspose * K = 1) :
    (publicStep (h := h) K).conjTranspose * publicStep (h := h) K = 1 := by
  rw [publicStep, Matrix.conjTranspose_submatrix]
  change (historyKnown K).conjTranspose.submatrix (regroupInput α h μ)
      (Equiv.refl (α × ((α × h) × ν))) *
    (historyKnown K).submatrix (Equiv.refl (α × ((α × h) × ν)))
      (regroupInput α h μ) = _
  rw [Matrix.submatrix_mul_equiv, historyKnown_isometry K hK, Matrix.submatrix_one_equiv]

def regroupBasis (α h μ : Type*) [DecidableEq α] :
    (Basis α × (α × (h × μ))) ≃ (Basis α × ((α × h) × μ)) where
  toFun u := (u.1, ((u.2.1, u.2.2.1), u.2.2.2))
  invFun u := (u.1, (u.2.1.1, (u.2.1.2, u.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

theorem knownOperation_publicStep (K : Matrix (α × ν) (α × μ) ℂ) :
    knownOperation (publicStep (h := h) K) =
      (knownOperation (historyKnown K)).submatrix id (regroupBasis α h μ) := by
  rfl

theorem publicStep_mulVec (K : Matrix (α × ν) (α × μ) ℂ)
    (v : Basis α × (α × (h × μ)) → ℂ) :
    knownOperation (publicStep K) *ᵥ v =
      knownOperation (historyKnown K) *ᵥ regroupCopy v := by
  rw [knownOperation_publicStep, Matrix.submatrix_mulVec_equiv]
  rfl

end
end ICO.RecordingPublicStep

