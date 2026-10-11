import ICO.RecordingDephasedOracle

/-!
# Copying a private query label equals dephasing an observable

The copied register is retained privately. Its exact isometry identities show
why its effect on expectations is query dephasing, even with side memory.
-/

namespace ICO.RecordingCopyIdentity

open QIT ICO.RecordingOperatorSupport ICO.RecordingDephasedOracle
  ICO.PathRecordingSupport
open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def basisEmbedding (f : a → b) : Matrix b a ℂ :=
  (1 : CMatrix b).submatrix id f

omit [Fintype a] [DecidableEq a] in
theorem basisEmbedding_compression (f : a → b) (K : CMatrix b) :
    (basisEmbedding f).conjTranspose * K * basisEmbedding f = K.submatrix f f := by
  simp only [basisEmbedding, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  change (1 : CMatrix b).submatrix f (Equiv.refl b) * K *
    (1 : CMatrix b).submatrix (Equiv.refl b) f = _
  rw [Matrix.one_submatrix_mul f (Equiv.refl b),
    Matrix.mul_submatrix_one (Equiv.refl b) f]
  rfl

theorem basisEmbedding_gram (f : a → b) (hf : Function.Injective f) :
    (basisEmbedding f).conjTranspose * basisEmbedding f = 1 := by
  have h := basisEmbedding_compression f (1 : CMatrix b)
  rw [Matrix.mul_one, Matrix.submatrix_one f hf] at h
  exact h

variable {α μ : Type*} [Fintype α] [DecidableEq α] [Fintype μ] [DecidableEq μ]

def copiedLabel (i : Basis α × μ) : Basis α × (α × μ) :=
  (i.1, (i.1.1, i.2))

omit [Fintype α] [DecidableEq α] [Fintype μ] [DecidableEq μ] in
theorem copiedLabel_injective : Function.Injective (copiedLabel (α := α) (μ := μ)) := by
  intro i j h
  have hb := congrArg (fun k : Basis α × (α × μ) => k.1) h
  have hm := congrArg (fun k : Basis α × (α × μ) => k.2.2) h
  exact Prod.ext hb hm

omit [Fintype α] [Fintype μ] in
theorem copyQuery_eq_embedding :
    copyQuery (α := α) (μ := μ) = basisEmbedding copiedLabel := by
  ext o i
  simp only [copyQuery, basisEmbedding, Matrix.submatrix_apply, id_eq, copiedLabel,
    Matrix.one_apply]
  congr 1
  apply propext
  constructor
  · rintro ⟨hb, hm, hc⟩
    exact Prod.ext hb (Prod.ext hc hm)
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg (fun k => k.2.2) h,
      congrArg (fun k => k.2.1) h⟩

/-- Copying the query into a private register preserves norm exactly. -/
theorem copyQuery_isometry :
    ((copyQuery (α := α) (μ := μ)).conjTranspose * copyQuery : CMatrix (Basis α × μ)) = 1 := by
  rw [copyQuery_eq_embedding]
  exact basisEmbedding_gram _ copiedLabel_injective

/-- Compressing any query-record observable through the copy is exactly
    computational dephasing of its query coordinate. The memory is untouched. -/
theorem copyQuery_observable (K : CMatrix (Basis α)) :
    (copyQuery (α := α) (μ := μ)).conjTranspose *
      Matrix.kronecker K (1 : CMatrix (α × μ)) * copyQuery =
      Matrix.kronecker (dephaseQuery K) (1 : CMatrix μ) := by
  rw [copyQuery_eq_embedding, basisEmbedding_compression]
  ext i j
  simp only [Matrix.submatrix_apply, copiedLabel, Matrix.kronecker,
    Matrix.kroneckerMap_apply, dephaseQuery, Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

def boundedMemoryEmbed (m : ℕ)
    (u : (α × BoundedPair (α := α) (β := α) m) × μ) : Basis α × μ :=
  (boundedEmbed m u.1, u.2)

/-- Embed bounded records and then copy the query into a fresh private
    register. This is the precise restricted prefix used in the local hybrid. -/
def boundedCopiedEmbedding (m : ℕ) :
    Matrix (Basis α × (α × μ)) ((α × BoundedPair (α := α) (β := α) m) × μ) ℂ :=
  copyQuery * basisEmbedding (boundedMemoryEmbed m)

theorem boundedCopied_gram (m : ℕ) (hm : m < Fintype.card α) :
    (boundedCopiedEmbedding (α := α) (μ := μ) m).conjTranspose *
      Matrix.kronecker (rightInsertion * rightInsertion.conjTranspose)
        (1 : CMatrix (α × μ)) * boundedCopiedEmbedding m =
      Matrix.kronecker (fullCompressedDephasedGram (α := α) (β := α) m)
        (1 : CMatrix μ) := by
  unfold boundedCopiedEmbedding
  rw [Matrix.conjTranspose_mul]
  have hAssoc :
      (basisEmbedding (boundedMemoryEmbed (α := α) (μ := μ) m)).conjTranspose *
        copyQuery.conjTranspose *
        Matrix.kronecker (rightInsertion * rightInsertion.conjTranspose)
          (1 : CMatrix (α × μ)) * (copyQuery * basisEmbedding (boundedMemoryEmbed m)) =
      (basisEmbedding (boundedMemoryEmbed m)).conjTranspose *
        (copyQuery.conjTranspose *
          Matrix.kronecker (rightInsertion * rightInsertion.conjTranspose)
            (1 : CMatrix (α × μ)) * copyQuery) * basisEmbedding (boundedMemoryEmbed m) := by
    simp only [Matrix.mul_assoc]
  rw [hAssoc, copyQuery_observable, basisEmbedding_compression]
  change Matrix.kronecker
    ((dephaseQuery (rightInsertion * rightInsertion.conjTranspose)).submatrix
      (boundedEmbed m) (boundedEmbed m)) (1 : CMatrix μ) = _
  rw [dephased_right_image_compression m hm]

omit [DecidableEq a] [DecidableEq b] in
theorem trace_sandwich_compression (J : Matrix b a ℂ) (K : CMatrix b) (ρ : CMatrix a) :
    (K * (J * ρ * J.conjTranspose)).trace =
      ((J.conjTranspose * K * J) * ρ).trace := by
  calc
    (K * (J * ρ * J.conjTranspose)).trace =
        ((K * J * ρ) * J.conjTranspose).trace := by simp only [Matrix.mul_assoc]
    _ = (J.conjTranspose * (K * J * ρ)).trace := Matrix.trace_mul_comm _ _
    _ = ((J.conjTranspose * K * J) * ρ).trace := by simp only [Matrix.mul_assoc]

/-- Actual B B† expectation after the private copy, for any entangled
    positive input on the bounded recording sector. -/
theorem boundedCopied_rightImage_expectation_le (m : ℕ) (hm : m < Fintype.card α)
    (ρ : CMatrix ((α × BoundedPair (α := α) (β := α) m) × μ))
    (hρ : ρ.PosSemidef) :
    ((Matrix.kronecker (rightInsertion * rightInsertion.conjTranspose)
      (1 : CMatrix (α × μ)) *
      (boundedCopiedEmbedding m * ρ * (boundedCopiedEmbedding m).conjTranspose)).trace).re ≤
      (1 / ((Fintype.card α : ℝ) - (m : ℝ))) * ρ.trace.re := by
  rw [trace_sandwich_compression, boundedCopied_gram m hm]
  exact ICO.RecordingMultisetBridge.compressed_gram_expectation_le m hm ρ hρ

end
end ICO.RecordingCopyIdentity
