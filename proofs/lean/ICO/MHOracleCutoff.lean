import ICO.MHFockNodup
import ICO.MHOracleCovariance

/-! An explicit source cutoff does not change the recording oracle on
states already below that cutoff. -/

namespace ICO.MHOracleCutoff

open QIT ICO.MHFockNodup ICO.MHFockProjection ICO.RecordingOperatorSupport
  ICO.MHOracleCovariance
open scoped BigOperators Matrix

noncomputable section
set_option maxHeartbeats 2500000

variable {a : Type*} [Fintype a] [DecidableEq a]

def cutoff (g : a → ℕ) (t : ℕ) : CMatrix a :=
  Matrix.diagonal (fun i => if g i ≤ t then 1 else 0)

theorem fullOracle_adjoint (A B : CMatrix a) :
    (fullOracle A B).conjTranspose=fullOracle B A := by
  simp only [fullOracle,Matrix.conjTranspose_add,Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul,Matrix.conjTranspose_one,Matrix.conjTranspose_conjTranspose]
  exact add_comm _ _

theorem cutoff_idempotent (g : a → ℕ) (t : ℕ) : cutoff g t * cutoff g t = cutoff g t := by
  simp only [cutoff, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem cutoff_adjoint (g : a → ℕ) (t : ℕ) : (cutoff g t).conjTranspose = cutoff g t := by
  ext i j
  by_cases he : i=j
  · subst j; simp [cutoff]
  · simp [cutoff, Matrix.conjTranspose_apply, he, Ne.symm he]

theorem adjoint_cutoff (g : a → ℕ) (t : ℕ) (A : CMatrix a)
    (hA : ∀ o i, A o i ≠ 0 → g o = g i + 1) :
    cutoff g t * A.conjTranspose * cutoff g t = A.conjTranspose * cutoff g t := by
  ext o i
  simp only [cutoff, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  by_cases hi : g i ≤ t
  · by_cases hz : A i o = 0
    · simp [hz]
    · have ho : g o ≤ t := by have hg := hA i o hz; omega
      simp [hi,ho]
  · simp [hi]

theorem fullOracle_cutoff (A B P : CMatrix a) (hPP : P*P=P) (hPs : P.conjTranspose=P)
    (hAd : P*A.conjTranspose*P=A.conjTranspose*P)
    (hBd : P*B.conjTranspose*P=B.conjTranspose*P)
    (hPB : Commute P (B*B.conjTranspose)) :
    fullOracle (A*P) (B*P) * P = fullOracle A B * P := by
  have hIm (M : CMatrix a) : (M*P)*(M*P).conjTranspose=M*P*M.conjTranspose := by
    rw [Matrix.conjTranspose_mul,hPs]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P,hPP]
  have hOne : (A*P)*P=A*P := by rw [Matrix.mul_assoc,hPP]
  have hTwo : (A*P)*(B*P*B.conjTranspose)*P=A*B*B.conjTranspose*P := by
    calc
      _ = A*(P*B*(P*B.conjTranspose*P)) := by simp only [Matrix.mul_assoc]
      _ = A*(P*(B*B.conjTranspose)*P) := by rw [hBd]; simp only [Matrix.mul_assoc]
      _ = A*((B*B.conjTranspose)*P*P) := by rw [hPB.eq]
      _ = _ := by rw [Matrix.mul_assoc (B*B.conjTranspose),hPP]; simp only [Matrix.mul_assoc]
  have hFour : (A*P*A.conjTranspose)*(P*B.conjTranspose)*P=A*A.conjTranspose*B.conjTranspose*P := by
    calc
      _ = A*(P*A.conjTranspose*P)*B.conjTranspose*P := by simp only [Matrix.mul_assoc]
      _ = A*A.conjTranspose*(P*B.conjTranspose*P) := by rw [hAd]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBd]; simp only [Matrix.mul_assoc]
  unfold fullOracle
  rw [hIm A,hIm B,Matrix.conjTranspose_mul,hPs]
  simp only [Matrix.add_mul,Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one]
  rw [hOne,hTwo,hBd,hFour]
  simp only [Matrix.mul_assoc]

theorem graded_fullOracle_cutoff (g : a → ℕ) (t : ℕ) (A B : CMatrix a)
    (hA : ∀ o i, A o i ≠ 0 → g o = g i + 1)
    (hB : ∀ o i, B o i ≠ 0 → g o = g i + 1) :
    fullOracle (A*cutoff g t) (B*cutoff g t) * cutoff g t = fullOracle A B * cutoff g t :=
  fullOracle_cutoff A B _ (cutoff_idempotent g t) (cutoff_adjoint g t)
    (adjoint_cutoff g t A hA) (adjoint_cutoff g t B hB)
    (cutoff_commute_of_grade g t _ (grade_image_preserved g B hB))

variable {α : Type*} [Fintype α] [DecidableEq α]

def setGrade (i : Basis α) : ℕ := i.2.1.card + i.2.2.card

theorem leftInsertion_grade (o i : Basis α) (h : leftInsertion o i ≠ 0) : setGrade o=setGrade i+1 := by
  obtain ⟨hR,hf,hL⟩ := leftInsertion_support h
  have hn : (i.1,o.1) ∉ i.2.1 := fun hm => hf i.1 (Finset.mem_union_left _ hm)
  unfold setGrade
  rw [hR,hL,Finset.card_insert_of_notMem hn]
  omega

theorem rightInsertion_grade (o i : Basis α) (h : rightInsertion o i ≠ 0) : setGrade o=setGrade i+1 := by
  obtain ⟨hL,hf,hR⟩ := rightInsertion_support h
  have hn : (o.1,i.1) ∉ i.2.2 := fun hm => hf i.1 (Finset.mem_union_right _ hm)
  unfold setGrade
  rw [hL,hR,Finset.card_insert_of_notMem hn]
  omega

theorem finite_oracle_cutoff (t : ℕ) :
    fullOracle (leftInsertion * oldSourceCutoff (α := α) t) (rightInsertion * oldSourceCutoff (α := α) t) *
      oldSourceCutoff (α := α) t =
      fullOracle (leftInsertion (α := α)) rightInsertion * oldSourceCutoff (α := α) t :=
  graded_fullOracle_cutoff setGrade t leftInsertion rightInsertion leftInsertion_grade rightInsertion_grade

theorem finite_inverse_cutoff (t : ℕ) :
    (fullOracle (leftInsertion * oldSourceCutoff (α := α) t) (rightInsertion * oldSourceCutoff (α := α) t)).conjTranspose *
      oldSourceCutoff (α := α) t =
      (fullOracle (leftInsertion (α := α)) rightInsertion).conjTranspose * oldSourceCutoff (α := α) t := by
  rw [fullOracle_adjoint,fullOracle_adjoint]
  exact graded_fullOracle_cutoff setGrade t rightInsertion leftInsertion rightInsertion_grade leftInsertion_grade

end
end ICO.MHOracleCutoff
