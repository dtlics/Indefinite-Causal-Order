import ICO.RecordingCopyIdentity
import ICO.RecordingOracleAlgebra

/-!
# Norm suppression of the removal branch

The operator bound is uniform over all finite side-memory spaces. It combines
the exact copied Gram with the partial-isometry algebra of the real recording
matrices, rather than postulating a local replacement error.
-/

namespace ICO.RecordingRemovalNorm

open QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport
  ICO.RecordingPartialIsometry ICO.RecordingOracleAlgebra ICO.RecordingCopyIdentity
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

variable {a μ : Type*} [Fintype a] [DecidableEq a] [Fintype μ] [DecidableEq μ]

omit [DecidableEq a] in
theorem tensor_mul (A B : CMatrix a) :
    Matrix.kronecker (A * B) (1 : CMatrix μ) =
      Matrix.kronecker A (1 : CMatrix μ) * Matrix.kronecker B 1 := by
  simpa only [Matrix.one_mul] using
    Matrix.mul_kronecker_mul A B (1 : CMatrix μ) (1 : CMatrix μ)

theorem tensor_conjTranspose (A : CMatrix a) :
    (Matrix.kronecker A (1 : CMatrix μ)).conjTranspose =
      Matrix.kronecker A.conjTranspose (1 : CMatrix μ) := by
  exact (Matrix.conjTranspose_kronecker A (1 : CMatrix μ)).trans
    (by rw [Matrix.conjTranspose_one]; rfl)

omit [Fintype a] [Fintype μ] in
theorem diagonal_tensor (f : a → ℂ) :
    Matrix.kronecker (Matrix.diagonal f) (1 : CMatrix μ) =
      Matrix.diagonal (fun i : a × μ => f i.1) := by
  simpa only [mul_one, Matrix.diagonal_one] using
    Matrix.diagonal_kronecker_diagonal f (fun _ : μ => (1 : ℂ))

theorem projection_tensor_identity (P : CMatrix a) (hP : IsStarProjection P) :
    IsStarProjection (Matrix.kronecker P (1 : CMatrix μ)) := by
  refine ⟨?_, ?_⟩
  · change Matrix.kronecker P (1 : CMatrix μ) * Matrix.kronecker P 1 = _
    rw [← tensor_mul, hP.isIdempotentElem.eq]
  · change (Matrix.kronecker P (1 : CMatrix μ)).conjTranspose = _
    rw [tensor_conjTranspose]
    have h : P.conjTranspose = P := hP.isSelfAdjoint.star_eq
    rw [h]

theorem partial_isometry_tensor_norm_le (A : CMatrix a)
    (hA : IsStarProjection (A.conjTranspose * A)) :
    ‖Matrix.kronecker A (1 : CMatrix μ)‖ ≤ 1 := by
  have h := IsStarProjection.norm_le _ (projection_tensor_identity (μ := μ) _ hA)
  have hGram :
      (Matrix.kronecker A (1 : CMatrix μ)).conjTranspose * Matrix.kronecker A 1 =
      Matrix.kronecker (A.conjTranspose * A) (1 : CMatrix μ) := by
    rw [tensor_conjTranspose, ← tensor_mul]
  rw [← hGram, Matrix.l2_opNorm_conjTranspose_mul_self] at h
  nlinarith [norm_nonneg (Matrix.kronecker A (1 : CMatrix μ))]

theorem diagonal_tensor_norm_le (f : a → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hf : ‖Matrix.diagonal f‖ ≤ c) :
    ‖Matrix.kronecker (Matrix.diagonal f) (1 : CMatrix μ)‖ ≤ c := by
  rw [diagonal_tensor, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hc).mpr
  intro i
  have h := (pi_norm_le_iff_of_nonneg hc).mp
    (by simpa only [Matrix.l2_opNorm_diagonal] using hf) i.1
  simpa only [mul_one] using h

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem fullGram_tensor_norm_le (m : ℕ) (hm : m < Fintype.card α) :
    ‖Matrix.kronecker (fullCompressedDephasedGram (α := α) (β := α) m)
      (1 : CMatrix μ)‖ ≤ 1 / ((Fintype.card α : ℝ) - (m : ℝ)) := by
  have hc : 0 ≤ 1 / ((Fintype.card α : ℝ) - (m : ℝ)) := by
    have h : (m : ℝ) < Fintype.card α := by exact_mod_cast hm
    positivity
  have h := fullCompressedDephasedGram_operator_norm_le (α := α) (β := α) m hm
  rw [fullCompressedDephasedGram_eq_diagonal] at h ⊢
  exact diagonal_tensor_norm_le _ _ hc h

def removalOnCopied (m : ℕ) :
    Matrix (Basis α × (α × μ)) ((α × BoundedPair (α := α) (β := α) m) × μ) ℂ :=
  Matrix.kronecker rightInsertion.conjTranspose (1 : CMatrix (α × μ)) *
    boundedCopiedEmbedding m

theorem removalOnCopied_gram (m : ℕ) (hm : m < Fintype.card α) :
    (removalOnCopied (α := α) (μ := μ) m).conjTranspose * removalOnCopied m =
      Matrix.kronecker (fullCompressedDephasedGram (α := α) (β := α) m)
        (1 : CMatrix μ) := by
  simp only [removalOnCopied, Matrix.conjTranspose_mul, tensor_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc
    (Matrix.kronecker rightInsertion (1 : CMatrix (α × μ))),
    ← tensor_mul, ← Matrix.mul_assoc]
  exact boundedCopied_gram m hm

theorem removalOnCopied_norm_le (m : ℕ) (hm : m < Fintype.card α) :
    ‖removalOnCopied (α := α) (μ := μ) m‖ ≤
      Real.sqrt (1 / ((Fintype.card α : ℝ) - (m : ℝ))) := by
  have hc : 0 ≤ 1 / ((Fintype.card α : ℝ) - (m : ℝ)) := by
    have h : (m : ℝ) < Fintype.card α := by exact_mod_cast hm
    positivity
  have h := fullGram_tensor_norm_le (μ := μ) m hm
  rw [← removalOnCopied_gram m hm, Matrix.l2_opNorm_conjTranspose_mul_self] at h
  nlinarith [norm_nonneg (removalOnCopied (α := α) (μ := μ) m),
    Real.sqrt_nonneg (1 / ((Fintype.card α : ℝ) - (m : ℝ))), Real.mul_self_sqrt hc]

def differenceFactor : CMatrix (Basis α) :=
  (1 - leftInsertion * leftInsertion.conjTranspose) - leftInsertion * rightInsertion

theorem differenceFactor_identity :
    forwardRecording (α := α) - leftInsertion = differenceFactor * rightInsertion.conjTranspose := by
  unfold forwardRecording differenceFactor
  noncomm_ring

theorem differenceFactor_tensor_norm_le :
    ‖Matrix.kronecker (differenceFactor (α := α)) (1 : CMatrix μ)‖ ≤ 2 := by
  have hA : IsStarProjection (leftInsertion.conjTranspose * leftInsertion : CMatrix (Basis α)) := by
    rw [left_gram_eq_projection]
    exact domainProjection_isStarProjection
  have hB : IsStarProjection (rightInsertion.conjTranspose * rightInsertion : CMatrix (Basis α)) := by
    rw [right_gram_eq_projection]
    exact domainProjection_isStarProjection
  have hQ := (image_projection (leftInsertion (α := α)) domainProjection
    left_gram_eq_projection left_domain_identity).one_sub
  have hQn := IsStarProjection.norm_le _ (projection_tensor_identity (μ := μ) _ hQ)
  change ‖Matrix.kronecker (1 - (leftInsertion (α := α)) * leftInsertion.conjTranspose)
    (1 : CMatrix μ)‖ ≤ 1 at hQn
  have hAn := partial_isometry_tensor_norm_le (μ := μ) _ hA
  have hBn := partial_isometry_tensor_norm_le (μ := μ) _ hB
  have he : Matrix.kronecker (differenceFactor (α := α)) (1 : CMatrix μ) =
      Matrix.kronecker (1 - leftInsertion * leftInsertion.conjTranspose) (1 : CMatrix μ) -
        Matrix.kronecker leftInsertion (1 : CMatrix μ) * Matrix.kronecker rightInsertion 1 := by
    rw [← tensor_mul]
    ext i j
    simp only [differenceFactor, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.sub_apply, sub_mul]
  rw [he]
  have hsub := norm_sub_le
    (Matrix.kronecker (1 - (leftInsertion (α := α)) * leftInsertion.conjTranspose) (1 : CMatrix μ))
    (Matrix.kronecker (leftInsertion (α := α)) (1 : CMatrix μ) *
      Matrix.kronecker (rightInsertion (α := α)) 1)
  have hmul := Matrix.l2_opNorm_mul (Matrix.kronecker (leftInsertion (α := α)) (1 : CMatrix μ))
    (Matrix.kronecker (rightInsertion (α := α)) (1 : CMatrix μ))
  have hprod : ‖Matrix.kronecker (leftInsertion (α := α)) (1 : CMatrix μ)‖ *
      ‖Matrix.kronecker (rightInsertion (α := α)) (1 : CMatrix μ)‖ ≤ 1 := by
    calc
      _ ≤ (1 : ℝ) * 1 := mul_le_mul hAn hBn (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  linarith

/-- The actual local V-to-A replacement, after the private copy and bounded
    support embedding, has norm at most 2/sqrt(d-m), independently of memory. -/
theorem replacementOnCopied_norm_le (m : ℕ) (hm : m < Fintype.card α) :
    ‖Matrix.kronecker (forwardRecording (α := α) - leftInsertion)
      (1 : CMatrix (α × μ)) * boundedCopiedEmbedding m‖ ≤
      2 * Real.sqrt (1 / ((Fintype.card α : ℝ) - (m : ℝ))) := by
  have he :
      Matrix.kronecker (forwardRecording (α := α) - leftInsertion)
        (1 : CMatrix (α × μ)) * boundedCopiedEmbedding m =
      Matrix.kronecker differenceFactor (1 : CMatrix (α × μ)) * removalOnCopied m := by
    rw [differenceFactor_identity, removalOnCopied, ← Matrix.mul_assoc, ← tensor_mul]
  rw [he]
  calc
    _ ≤ ‖Matrix.kronecker differenceFactor (1 : CMatrix (α × μ))‖ *
        ‖removalOnCopied (α := α) (μ := μ) m‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ 2 * Real.sqrt (1 / ((Fintype.card α : ℝ) - (m : ℝ))) :=
      mul_le_mul differenceFactor_tensor_norm_le (removalOnCopied_norm_le m hm)
        (norm_nonneg _) (by norm_num)

end
end ICO.RecordingRemovalNorm
