import ICO.C6FockCompressionSharp
import ICO.C6PolarLengths

/-! Exact right-length support identities used in the inverse replacement. -/
namespace ICO.C6BosonicLengthMasks
open QIT ICO.C6PolarFock ICO.C6PolarLengths ICO.C6FockQueryMatrix
  ICO.MHBoundedRecording
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem mask_projection (m T : ℕ) : IsStarProjection (rightLengthMask (α:=A) m T) := by
  rw [rightLengthMask_diagonal]
  constructor
  · change (Matrix.diagonal _ : CMatrix (InputCutoff (α:=A) T))*Matrix.diagonal _=Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    split_ifs <;> simp
  · change (Matrix.diagonal _ : CMatrix (InputCutoff (α:=A) T)).conjTranspose=Matrix.diagonal _
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    ext i
    simp only [Pi.star_apply]
    split_ifs <;> simp

theorem left_mask (m : ℕ) {t T : ℕ} (h : t+1≤T) :
    rightLengthMask m T*polarLeftOnFock (α:=A) h=
      polarLeftOnFock h*rightLengthMask m T := by
  rw [rightLengthMask_diagonal]
  ext o i
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases he : polarLeftOnFock h o i=0
  · simp [he]
  · rw [(left_lengths h o i he).2]
    split_ifs <;> simp

theorem left_adjoint_mask (m : ℕ) {t T : ℕ} (h : t+1≤T) :
    rightLengthMask m T*(polarLeftOnFock (α:=A) h).conjTranspose=
      (polarLeftOnFock h).conjTranspose*rightLengthMask m T := by
  have hm : (rightLengthMask (α:=A) m T).conjTranspose=rightLengthMask m T :=
    (mask_projection m T).isSelfAdjoint.star_eq
  have hh := congrArg Matrix.conjTranspose (left_mask (A:=A) m h)
  simpa only [Matrix.conjTranspose_mul,hm] using hh.symm

theorem right_adjoint_predecessor (m : ℕ) {t T : ℕ} (h : t+1≤T) :
    (polarRightOnFock (α:=A) h).conjTranspose*rightLengthMask (m+1) T=
      rightLengthMask m T*(polarRightOnFock h).conjTranspose*rightLengthMask (m+1) T := by
  rw [rightLengthMask_diagonal,rightLengthMask_diagonal]
  ext o i
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.conjTranspose_apply]
  by_cases he : polarRightOnFock h i o=0
  · simp [he]
  · have hl := (right_lengths h i o he).2
    by_cases hi : i.1.1.val.2.val≤m+1
    · have ho : o.1.1.val.2.val≤m := by omega
      simp [hi,ho]
    · simp [hi]

theorem right_adjoint_vacuum {t T : ℕ} (h : t+1≤T) :
    (polarRightOnFock (α:=A) h).conjTranspose*rightLengthMask 0 T=0 := by
  rw [rightLengthMask_diagonal]
  ext o i
  simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply,Matrix.zero_apply]
  by_cases he : polarRightOnFock h i o=0
  · simp [he]
  · have hl := (right_lengths h i o he).2
    have hn : ¬i.1.1.val.2.val≤0 := by omega
    simp [hn]

#print axioms left_adjoint_mask
#print axioms right_adjoint_predecessor
#print axioms right_adjoint_vacuum
end
end ICO.C6BosonicLengthMasks
