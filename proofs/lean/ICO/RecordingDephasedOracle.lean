import ICO.RecordingOracleChannel
import ICO.RecordingMultisetBridge

/-!
# The dephased image projection of the actual recording matrix

This file identifies the earlier bounded Gram matrix with the compression of
the full finite B B† operator, including its cutoff and both record registers.
-/

namespace ICO.RecordingDephasedOracle

open QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem rightInsertion_eq_block (o i : Basis α) :
    rightInsertion o i = if o.2.1 = i.2.1 then
      cutoffRightInsertionMatrix o.2.1 (o.1, o.2.2) (i.1, i.2.2) else 0 := by
  classical
  by_cases hL : o.2.1 = i.2.1
  · simp only [rightInsertion, RightStep, hL, true_and,
      cutoffRightInsertionMatrix, rightInsertionMatrix]
    split_ifs <;> first | rfl | tauto
  · simp [rightInsertion, RightStep, hL]

theorem rightImage_eq_block (o i : Basis α) :
    (rightInsertion * rightInsertion.conjTranspose : CMatrix (Basis α)) o i =
      if o.2.1 = i.2.1 then
        (cutoffRightInsertionMatrix o.2.1 *
          (cutoffRightInsertionMatrix o.2.1).conjTranspose)
          (o.1, o.2.2) (i.1, i.2.2) else 0 := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  by_cases hL : o.2.1 = i.2.1
  · rw [if_pos hL]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_eq_single o.2.1]
    · apply Finset.sum_congr rfl
      intro r _
      simp only [rightInsertion_eq_block, ← hL, ite_true]
    · intro l _ hl
      apply Finset.sum_eq_zero
      intro r _
      simp only [rightInsertion_eq_block, if_neg (Ne.symm hl), zero_mul]
    · simp
  · rw [if_neg hL]
    apply Finset.sum_eq_zero
    intro x _
    apply Finset.sum_eq_zero
    intro l _
    apply Finset.sum_eq_zero
    intro r _
    by_cases hoL : o.2.1 = l
    · have hiL : i.2.1 ≠ l := by intro hiL; exact hL (hoL.trans hiL.symm)
      simp [rightInsertion_eq_block, hiL]
    · simp [rightInsertion_eq_block, hoL]

def dephaseQuery (K : CMatrix (Basis α)) : CMatrix (Basis α) :=
  fun o i => if o.1 = i.1 then K o i else 0

def boundedEmbed (m : ℕ) (u : α × BoundedPair (α := α) (β := α) m) : Basis α :=
  (u.1, u.2.val.1, u.2.val.2)

theorem dephased_right_image_compression (m : ℕ) (hm : m < Fintype.card α) :
    (dephaseQuery (rightInsertion * rightInsertion.conjTranspose)).submatrix
      (boundedEmbed m) (boundedEmbed m) =
      fullCompressedDephasedGram (α := α) (β := α) m := by
  classical
  ext u v
  simp only [Matrix.submatrix_apply, dephaseQuery, boundedEmbed, rightImage_eq_block,
    fullCompressedDephasedGram]
  by_cases hq : u.1 = v.1
  · rw [if_pos hq]
    by_cases hL : u.2.val.1 = v.2.val.1
    · rw [if_pos hL, if_pos ⟨hq, hL⟩]
      apply cutoffRightInsertionMatrix_gram_eq
      · exact lt_of_le_of_lt u.2.property hm
      · rw [hL]
        exact lt_of_le_of_lt v.2.property hm
    · rw [if_neg hL, if_neg (fun h => hL h.2)]
  · rw [if_neg hq, if_neg (fun h => hq h.1)]

theorem dephased_right_image_norm_le (m : ℕ) (hm : m < Fintype.card α) :
    ‖(dephaseQuery (α := α) (rightInsertion * rightInsertion.conjTranspose)).submatrix
      (boundedEmbed m) (boundedEmbed m)‖ ≤
      1 / ((Fintype.card α : ℝ) - (m : ℝ)) := by
  rw [dephased_right_image_compression m hm]
  exact fullCompressedDephasedGram_operator_norm_le m hm

end
end ICO.RecordingDephasedOracle
