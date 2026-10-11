import ICO.MHFockSpace

/-! Elementary coordinate-inclusion and permutation matrix identities. -/

namespace ICO.MHEmbeddingProjector

open QIT ICO.RecordingCopyIdentity
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 1000000

variable {a b c : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype c] [DecidableEq c]

theorem basisEmbedding_mul (f : b → c) (g : a → b) :
    basisEmbedding f * basisEmbedding g = basisEmbedding (f ∘ g) := by
  ext i j
  simp [Matrix.mul_apply, basisEmbedding, Matrix.submatrix_apply, Matrix.one_apply]

theorem basisEmbedding_image (f : a → b) (hf : Function.Injective f) :
    basisEmbedding f * (basisEmbedding f).conjTranspose =
      Matrix.diagonal (fun i : b => if ∃ x, f x = i then (1 : ℂ) else 0) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, basisEmbedding,
    Matrix.submatrix_apply, id_eq, Matrix.one_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    by_cases hex : ∃ x, f x = i
    · obtain ⟨x, hx⟩ := hex
      rw [if_pos ⟨x, hx⟩, Finset.sum_eq_single x]
      · simp [hx]
      · intro y _ hy
        have hi : i ≠ f y := by intro he; exact hy (hf (he.symm.trans hx.symm))
        simp [hi]
      · simp
    · rw [if_neg hex]
      apply Finset.sum_eq_zero
      intro x _
      have hi : i ≠ f x := fun h => hex ⟨x, h.symm⟩
      simp [hi]
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hi : i = f x
    · have hj : j ≠ f x := fun h => hij (hi.trans h.symm)
      simp [hj]
    · simp [hi]

theorem basisEmbedding_adjoint_involutive (f : a → a) (hf : Function.Involutive f) :
    (basisEmbedding f).conjTranspose = basisEmbedding f := by
  ext i j
  simp only [Matrix.conjTranspose_apply, basisEmbedding, Matrix.submatrix_apply,
    id_eq, Matrix.one_apply]
  by_cases h : i = f j
  · have h' : j = f i := by rw [h, hf]
    simp only [if_pos h, if_pos h', star_one]
  · have h' : j ≠ f i := by intro he; apply h; rw [he, hf]
    simp only [if_neg h, if_neg h', star_zero]

end
end ICO.MHEmbeddingProjector
