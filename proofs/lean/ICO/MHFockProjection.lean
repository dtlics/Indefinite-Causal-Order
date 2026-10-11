import ICO.MHFockAlgebra
import ICO.MHEmbeddingProjector

/-! The initial Fock projection is exactly the total-length cutoff. -/

namespace ICO.MHFockProjection

open QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockAlgebra
  ICO.MHEmbeddingProjector ICO.RecordingCopyIdentity
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 1500000

variable {α : Type*} [Fintype α] [DecidableEq α]

def grade {t : ℕ} (v : InputCutoff (α := α) t) : ℕ :=
  v.1.1.val.1.val + v.1.1.val.2.val

def restrictInput {t T : ℕ} (v : InputCutoff (α := α) T) (hv : grade v ≤ t) : InputCutoff (α := α) t :=
  ⟨⟨⟨(⟨v.1.1.val.1.val, by unfold grade at hv; omega⟩,
      ⟨v.1.1.val.2.val, by unfold grade at hv; omega⟩), hv⟩, v.1.2⟩, v.2⟩

theorem inputEmbed_range {t T : ℕ} (h : t ≤ T) (v : InputCutoff (α := α) T) :
    (∃ w, inputEmbed h w = v) ↔ grade v ≤ t := by
  constructor
  · rintro ⟨w, rfl⟩
    exact w.1.1.property
  · intro hv
    refine ⟨restrictInput v hv, ?_⟩
    apply input_ext <;> rfl

theorem sourceProjection_diagonal {t T : ℕ} (h : t ≤ T) :
    sourceProjection (α := α) h = Matrix.diagonal (fun v : InputCutoff (α := α) T =>
      if grade v ≤ t then (1 : ℂ) else 0) := by
  rw [sourceProjection, basisEmbedding_image _ (inputEmbed_injective h)]
  congr 1
  funext v
  simp only [inputEmbed_range]

theorem basisEmbedding_support {a b : Type*} [Fintype b] [DecidableEq b]
    (f : a → b) (o : b) (i : a) (h : basisEmbedding f o i ≠ 0) : o = f i := by
  by_contra hn
  exact h (by simp [basisEmbedding, Matrix.submatrix_apply, Matrix.one_apply, hn])

theorem mul_entry_nonzero {a b c : Type*} [Fintype b]
    (M : Matrix c b ℂ) (N : Matrix b a ℂ) (o : c) (i : a) (h : (M * N) o i ≠ 0) :
    ∃ j, M o j ≠ 0 ∧ N j i ≠ 0 := by
  obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨j, (mul_ne_zero_iff.mp hj).1, (mul_ne_zero_iff.mp hj).2⟩

theorem leftOnFock_grade {t T : ℕ} (h : t + 1 ≤ T)
    (o i : InputCutoff (α := α) T) (hA : leftOnFock h o i ≠ 0) : grade o = grade i + 1 := by
  obtain ⟨j, hj, hji⟩ := mul_entry_nonzero _ _ o i hA
  obtain ⟨k, hok, hkj⟩ := mul_entry_nonzero _ _ o j hj
  have ho := basisEmbedding_support (outputEmbed h) o k hok
  have hi : i = inputEmbed (Nat.le_trans (Nat.le_succ t) h) j := by
    apply basisEmbedding_support
    intro hz
    apply hji
    simp only [Matrix.conjTranspose_apply, hz, star_zero]
  have hblock : k.1 = j.1 := by
    by_contra hn
    exact hkj (by simp [boundedInsertion, Matrix.blockDiagonal'_apply, hn])
  have hg := congrArg (fun b : Block (α := α) t => b.1.val.1.val + b.1.val.2.val) hblock
  dsimp only at hg
  rw [ho, hi]
  change k.1.1.val.1.val + 1 + k.1.1.val.2.val = j.1.1.val.1.val + j.1.1.val.2.val + 1
  omega

theorem grade_image_preserved {a : Type*} [Fintype a] [DecidableEq a]
    (g : a → ℕ) (A : CMatrix a) (hA : ∀ i j, A i j ≠ 0 → g i = g j + 1)
    (i j : a) (h : (A * A.conjTranspose) i j ≠ 0) : g i = g j := by
  obtain ⟨k, hik, hjk⟩ := mul_entry_nonzero _ _ i j h
  have hjk' : A j k ≠ 0 := by intro hz; apply hjk; simp [Matrix.conjTranspose_apply, hz]
  rw [hA i k hik, hA j k hjk']

theorem cutoff_commute_of_grade {a : Type*} [Fintype a] [DecidableEq a]
    (g : a → ℕ) (t : ℕ) (M : CMatrix a) (hM : ∀ i j, M i j ≠ 0 → g i = g j) :
    Commute (Matrix.diagonal (fun i => if g i ≤ t then (1 : ℂ) else 0)) M := by
  change Matrix.diagonal _ * M = M * Matrix.diagonal _
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hm : M i j = 0
  · simp [hm]
  · rw [hM i j hm]
    exact mul_comm _ _

theorem source_commute_left_image {t T : ℕ} (h : t + 1 ≤ T) :
    Commute (sourceProjection (α := α) (Nat.le_trans (Nat.le_succ t) h))
      (leftOnFock h * (leftOnFock h).conjTranspose) := by
  rw [sourceProjection_diagonal]
  apply cutoff_commute_of_grade
  exact grade_image_preserved grade (leftOnFock h) (leftOnFock_grade h)

end
end ICO.MHFockProjection
