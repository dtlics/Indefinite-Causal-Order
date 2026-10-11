import ICO.MHFockSpace

/-! Initial projection and contraction of the full multiset Fock insertion. -/

namespace ICO.MHFockAlgebra

open QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHERecordingApprox
  ICO.MHInsertionIsometry ICO.RecordingCopyIdentity ICO.RecordingActiveWrapper
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 2000000

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem boundedInsertion_gram (t : ℕ) (ht : t < Fintype.card α) :
    (boundedInsertion (α := α) t).conjTranspose * boundedInsertion (α := α) t =
      (1 : CMatrix (InputCutoff (α := α) t)) := by
  unfold boundedInsertion
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  have hb (k : Block (α := α) t) :
      (fullInsertion (n := k.1.val.1.val) k.2).conjTranspose *
        fullInsertion (n := k.1.val.1.val) k.2 = 1 :=
    fullInsertion_isometry k.2 (lt_of_le_of_lt k.1.property ht)
  simp only [hb]
  exact Matrix.blockDiagonal'_one

def sourceProjection {t T : ℕ} (h : t ≤ T) : CMatrix (InputCutoff (α := α) T) :=
  basisEmbedding (inputEmbed h) * (basisEmbedding (inputEmbed h)).conjTranspose

theorem sourceProjection_projection {t T : ℕ} (h : t ≤ T) :
    IsStarProjection (sourceProjection (α := α) h) :=
  rectangular_image_projection _ (inputEmbed_gram h)

theorem leftOnFock_gram {t T : ℕ} (h : t + 1 ≤ T) (ht : t < Fintype.card α) :
    (leftOnFock (α := α) h).conjTranspose * leftOnFock h =
      sourceProjection (Nat.le_trans (Nat.le_succ t) h) := by
  unfold leftOnFock sourceProjection
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (basisEmbedding (outputEmbed (α := α) h)).conjTranspose
      (basisEmbedding (outputEmbed (α := α) h)), outputEmbed_gram, Matrix.one_mul,
    ← Matrix.mul_assoc (boundedInsertion (α := α) t).conjTranspose (boundedInsertion (α := α) t),
    boundedInsertion_gram t ht, Matrix.one_mul]

theorem leftOnFock_domain {t T : ℕ} (h : t + 1 ≤ T) :
    leftOnFock (α := α) h * sourceProjection (Nat.le_trans (Nat.le_succ t) h) = leftOnFock h := by
  unfold leftOnFock sourceProjection
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc
      (basisEmbedding (inputEmbed (α := α) (Nat.le_trans (Nat.le_succ t) h))).conjTranspose
      (basisEmbedding (inputEmbed (α := α) (Nat.le_trans (Nat.le_succ t) h))),
    inputEmbed_gram, Matrix.one_mul]

theorem leftOnFock_norm_le {t T : ℕ} (h : t + 1 ≤ T) (ht : t < Fintype.card α) :
    ‖leftOnFock (α := α) h‖ ≤ 1 := by
  have hn := IsStarProjection.norm_le _
    (sourceProjection_projection (α := α) (Nat.le_trans (Nat.le_succ t) h))
  rw [← leftOnFock_gram h ht, Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  nlinarith [norm_nonneg (leftOnFock (α := α) h)]

end
end ICO.MHFockAlgebra
