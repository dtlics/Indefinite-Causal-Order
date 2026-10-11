import ICO.MHFockRotation
import ICO.MHFockProjection

/-! Transport of length-preserving operators through the actual finite
Fock inclusions. -/

namespace ICO.MHFockTransport

open QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockRotation
  ICO.MHFockProjection ICO.MHFockAlgebra ICO.RecordingCopyIdentity
  ICO.MHSectorCovariance
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 2000000

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem intertwine_of_compression (J : Matrix b a ℂ) (U : CMatrix b)
    (V : CMatrix a) (hJ : J.conjTranspose * J = 1)
    (hC : J.conjTranspose * U * J = V)
    (hcomm : Commute U (J * J.conjTranspose)) : U * J = J * V := by
  rw [← hC]
  calc
    U * J = U * (J * J.conjTranspose) * J := by simp [Matrix.mul_assoc, hJ]
    _ = (J * J.conjTranspose) * U * J := by rw [hcomm.eq]
    _ = _ := by simp only [Matrix.mul_assoc]

variable {α : Type*} [Fintype α] [DecidableEq α]

def outputSectorEquiv (t : ℕ) : OutputCutoff (α := α) t ≃
    Σ s : Lengths t, Sector (α := α) (s.val.1.val + 1) s.val.2.val where
  toFun v := ⟨v.1.1, (v.2, v.1.2)⟩
  invFun v := ⟨⟨v.1, v.2.2⟩, v.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

def inputFamily (F : ∀ n r, CMatrix (Sector (α := α) n r)) (t : ℕ) :
    CMatrix (InputCutoff (α := α) t) :=
  (Matrix.blockDiagonal' (fun s : Lengths t => F s.val.1.val s.val.2.val)).submatrix
    (sectorEquiv t) (sectorEquiv t)

def outputFamily (F : ∀ n r, CMatrix (Sector (α := α) n r)) (t : ℕ) :
    CMatrix (OutputCutoff (α := α) t) :=
  (Matrix.blockDiagonal' (fun s : Lengths t => F (s.val.1.val + 1) s.val.2.val)).submatrix
    (outputSectorEquiv t) (outputSectorEquiv t)

theorem inputFamily_same (F : ∀ n r, CMatrix (Sector (α := α) n r)) (t : ℕ)
    (s : Lengths t) (q q' : TensorPowerProfile (α × α) s.val.2.val)
    (p p' : ICO.MHBadInsertion.Input (α := α) s.val.1.val) :
    inputFamily F t ⟨⟨s, q⟩, p⟩ ⟨⟨s, q'⟩, p'⟩ = F _ _ (p,q) (p',q') := by
  simp [inputFamily, sectorEquiv]

theorem inputFamily_other (F : ∀ n r, CMatrix (Sector (α := α) n r)) (t : ℕ)
    (v w : InputCutoff (α := α) t) (h : v.1.1 ≠ w.1.1) : inputFamily F t v w = 0 := by
  simp [inputFamily, sectorEquiv, Matrix.blockDiagonal'_apply, h]

theorem lengthEmbed_injective {t T : ℕ} (h : t ≤ T) : Function.Injective (lengthEmbed h) := by
  intro s s' he
  apply Subtype.ext
  exact Prod.ext (Fin.ext (congrArg (fun z : Lengths T => z.val.1.val) he))
    (Fin.ext (congrArg (fun z : Lengths T => z.val.2.val) he))

theorem lengthGrow_injective {t T : ℕ} (h : t + 1 ≤ T) : Function.Injective (lengthGrow h) := by
  intro s s' he
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact Nat.add_right_cancel (congrArg (fun z : Lengths T => z.val.1.val) he)
  · exact Fin.ext (congrArg (fun z : Lengths T => z.val.2.val) he)

theorem inputFamily_compression (F : ∀ n r, CMatrix (Sector (α := α) n r))
    {t T : ℕ} (h : t ≤ T) :
    (basisEmbedding (inputEmbed (α := α) h)).conjTranspose * inputFamily F T *
      basisEmbedding (inputEmbed (α := α) h) = inputFamily F t := by
  rw [basisEmbedding_compression]
  ext ⟨⟨s,q⟩,p⟩ ⟨⟨s',q'⟩,p'⟩
  change inputFamily F T (inputEmbed h _) (inputEmbed h _) = _
  by_cases hs : s = s'
  · subst s'
    exact (inputFamily_same F T (lengthEmbed h s) q q' p p').trans
      (inputFamily_same F t s q q' p p').symm
  · rw [inputFamily_other F t _ _ hs]
    exact inputFamily_other F T _ _ (fun he => hs (lengthEmbed_injective h he))

theorem inputFamily_grade (F : ∀ n r, CMatrix (Sector (α := α) n r))
    (T : ℕ) (i j : InputCutoff (α := α) T) (h : inputFamily F T i j ≠ 0) : grade i = grade j := by
  have he : i.1.1 = j.1.1 := by
    by_contra hne
    exact h (inputFamily_other F T i j hne)
  exact congrArg (fun s : Lengths T => s.val.1.val + s.val.2.val) he

theorem inputFamily_intertwine (F : ∀ n r, CMatrix (Sector (α := α) n r))
    {t T : ℕ} (h : t ≤ T) : inputFamily F T * basisEmbedding (inputEmbed (α := α) h) =
      basisEmbedding (inputEmbed (α := α) h) * inputFamily F t := by
  apply intertwine_of_compression _ _ _ (inputEmbed_gram h) (inputFamily_compression F h)
  change Commute (inputFamily F T) (sourceProjection h)
  rw [sourceProjection_diagonal]
  exact (cutoff_commute_of_grade grade t _ (inputFamily_grade F T)).symm

theorem outputFamily_same (F : ∀ n r, CMatrix (Sector (α := α) n r)) (t : ℕ)
    (s : Lengths t) (q q' : TensorPowerProfile (α × α) s.val.2.val)
    (p p' : ICO.MHBadInsertion.Input (α := α) (s.val.1.val + 1)) :
    outputFamily F t ⟨⟨s, q⟩, p⟩ ⟨⟨s, q'⟩, p'⟩ = F _ _ (p,q) (p',q') := by
  simp [outputFamily, outputSectorEquiv]

theorem outputFamily_other (F : ∀ n r, CMatrix (Sector (α := α) n r)) (t : ℕ)
    (v w : OutputCutoff (α := α) t) (h : v.1.1 ≠ w.1.1) : outputFamily F t v w = 0 := by
  simp [outputFamily, outputSectorEquiv, Matrix.blockDiagonal'_apply, h]

theorem outputFamily_compression (F : ∀ n r, CMatrix (Sector (α := α) n r))
    {t T : ℕ} (h : t + 1 ≤ T) :
    (basisEmbedding (outputEmbed (α := α) h)).conjTranspose * inputFamily F T *
      basisEmbedding (outputEmbed (α := α) h) = outputFamily F t := by
  rw [basisEmbedding_compression]
  ext ⟨⟨s,q⟩,p⟩ ⟨⟨s',q'⟩,p'⟩
  change inputFamily F T (outputEmbed h _) (outputEmbed h _) = _
  by_cases hs : s = s'
  · subst s'
    exact (inputFamily_same F T (lengthGrow h s) q q' p p').trans
      (outputFamily_same F t s q q' p p').symm
  · rw [outputFamily_other F t _ _ hs]
    exact inputFamily_other F T _ _ (fun he => hs (lengthGrow_injective h he))

theorem outputEmbed_range_of_length {t T : ℕ} (h : t + 1 ≤ T)
    (v : OutputCutoff (α := α) t) (i : InputCutoff (α := α) T)
    (he : i.1.1 = (outputEmbed h v).1.1) : ∃ w, outputEmbed h w = i := by
  rcases v with ⟨⟨s,q⟩,p⟩
  rcases i with ⟨⟨s',q'⟩,p'⟩
  change s' = lengthGrow h s at he
  subst s'
  exact ⟨⟨⟨s,q'⟩,p'⟩, rfl⟩

theorem outputFamily_intertwine (F : ∀ n r, CMatrix (Sector (α := α) n r))
    {t T : ℕ} (h : t + 1 ≤ T) : inputFamily F T * basisEmbedding (outputEmbed (α := α) h) =
      basisEmbedding (outputEmbed (α := α) h) * outputFamily F t := by
  apply intertwine_of_compression _ _ _ (outputEmbed_gram h) (outputFamily_compression F h)
  rw [ICO.MHEmbeddingProjector.basisEmbedding_image _ (outputEmbed_injective h)]
  change inputFamily F T * Matrix.diagonal _ = Matrix.diagonal _ * inputFamily F T
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : inputFamily F T i j = 0
  · simp [hz]
  have he : i.1.1 = j.1.1 := by
    by_contra hn
    exact hz (inputFamily_other F T i j hn)
  have hr : (∃ w, outputEmbed h w = i) ↔ ∃ w, outputEmbed h w = j := by
    constructor
    · rintro ⟨v,rfl⟩
      exact outputEmbed_range_of_length h v j he.symm
    · rintro ⟨v,rfl⟩
      exact outputEmbed_range_of_length h v i he
  simp only [hr]
  exact mul_comm _ _

end
end ICO.MHFockTransport
