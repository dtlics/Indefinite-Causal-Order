import ICO.MHFockProjection
import ICO.MHFockSwap
import ICO.RecordingOracleAlgebra

/-! The full bidirectional Ma–Huang oracle on a common finite multiset Fock
space is an actual partial isometry. -/

namespace ICO.MHFockOracle

open QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockAlgebra
  ICO.MHFockProjection ICO.MHFockSwap ICO.MHEmbeddingProjector
  ICO.RecordingCopyIdentity ICO.RecordingOracleAlgebra
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 2000000

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem swapMatrix_selfAdjoint (T : ℕ) : (swapMatrix (α := α) T).conjTranspose = swapMatrix T :=
  basisEmbedding_adjoint_involutive _ recordSwap_involutive

theorem swapMatrix_sq (T : ℕ) : swapMatrix (α := α) T * swapMatrix (α := α) T = 1 := by
  have h := swapMatrix_gram (α := α) T
  rwa [swapMatrix_selfAdjoint] at h

theorem swapMatrix_grade (T : ℕ) (i j : InputCutoff (α := α) T)
    (h : swapMatrix T i j ≠ 0) : grade i = grade j := by
  have he := basisEmbedding_support (recordSwapEquiv T) i j h
  rw [he]
  exact Nat.add_comm _ _

theorem source_commute_swap {t T : ℕ} (h : t ≤ T) :
    Commute (sourceProjection (α := α) h) (swapMatrix T) := by
  rw [sourceProjection_diagonal]
  exact cutoff_commute_of_grade grade t _ (swapMatrix_grade T)

theorem rightOnFock_gram {t T : ℕ} (h : t + 1 ≤ T) (ht : t < Fintype.card α) :
    (rightOnFock (α := α) h).conjTranspose * rightOnFock h =
      sourceProjection (Nat.le_trans (Nat.le_succ t) h) := by
  unfold rightOnFock
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    swapMatrix_selfAdjoint, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (swapMatrix (α := α) T) (swapMatrix (α := α) T), swapMatrix_sq,
    Matrix.one_mul, ← Matrix.mul_assoc (leftOnFock (α := α) h).conjTranspose (leftOnFock (α := α) h),
    leftOnFock_gram h ht, ← Matrix.mul_assoc,
    ← (source_commute_swap (α := α) (Nat.le_trans (Nat.le_succ t) h)).eq,
    Matrix.mul_assoc, swapMatrix_sq, Matrix.mul_one]

theorem rightOnFock_domain {t T : ℕ} (h : t + 1 ≤ T) :
    rightOnFock (α := α) h * sourceProjection (Nat.le_trans (Nat.le_succ t) h) = rightOnFock h := by
  unfold rightOnFock
  rw [swapMatrix_selfAdjoint]
  simp only [Matrix.mul_assoc]
  rw [← (source_commute_swap (α := α) (Nat.le_trans (Nat.le_succ t) h)).eq,
    ← Matrix.mul_assoc (leftOnFock (α := α) h), leftOnFock_domain]

theorem rightOnFock_grade {t T : ℕ} (h : t + 1 ≤ T)
    (o i : InputCutoff (α := α) T) (hA : rightOnFock h o i ≠ 0) : grade o = grade i + 1 := by
  obtain ⟨j, hj, hji⟩ := mul_entry_nonzero _ _ o i hA
  obtain ⟨k, hok, hkj⟩ := mul_entry_nonzero _ _ o j hj
  have ho := swapMatrix_grade T o k hok
  have hi := swapMatrix_grade T j i (by simpa only [swapMatrix_selfAdjoint] using hji)
  have ha := leftOnFock_grade h k j hkj
  omega

theorem source_commute_right_image {t T : ℕ} (h : t + 1 ≤ T) :
    Commute (sourceProjection (α := α) (Nat.le_trans (Nat.le_succ t) h))
      (rightOnFock h * (rightOnFock h).conjTranspose) := by
  rw [sourceProjection_diagonal]
  apply cutoff_commute_of_grade
  exact grade_image_preserved grade (rightOnFock h) (rightOnFock_grade h)

def fullOracle {t T : ℕ} (h : t + 1 ≤ T) : CMatrix (InputCutoff (α := α) T) :=
  leftOnFock h * (1 - rightOnFock h * (rightOnFock h).conjTranspose) +
    (1 - leftOnFock h * (leftOnFock h).conjTranspose) * (rightOnFock h).conjTranspose

theorem fullOracle_initial_projection {t T : ℕ} (h : t + 1 ≤ T) (ht : t < Fintype.card α) :
    IsStarProjection ((fullOracle (α := α) h).conjTranspose * fullOracle h) :=
  oracle_initial_projection (leftOnFock h) (rightOnFock h)
    (sourceProjection (Nat.le_trans (Nat.le_succ t) h))
    (sourceProjection_projection _) (leftOnFock_gram h ht) (rightOnFock_gram h ht)
    (leftOnFock_domain h) (rightOnFock_domain h)
    (source_commute_left_image h) (source_commute_right_image h)

theorem fullOracle_norm_le {t T : ℕ} (h : t + 1 ≤ T) (ht : t < Fintype.card α) :
    ‖fullOracle (α := α) h‖ ≤ 1 := by
  have hn := IsStarProjection.norm_le _ (fullOracle_initial_projection (α := α) h ht)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  nlinarith [norm_nonneg (fullOracle (α := α) h)]

theorem fullOracle_adjoint_norm_le {t T : ℕ} (h : t + 1 ≤ T) (ht : t < Fintype.card α) :
    ‖(fullOracle (α := α) h).conjTranspose‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_conjTranspose]
  exact fullOracle_norm_le h ht

end
end ICO.MHFockOracle
