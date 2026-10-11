import ICO.MHFockSpace
import ICO.MHProfileTranspose

/-! Swapping the two record registers and transposing each recorded pair
realizes the symmetry between forward and inverse insertion. -/

namespace ICO.MHFockSwap

open QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHProfileTranspose
  ICO.RecordingCopyIdentity ICO.RecordingProcess
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 1500000

variable {α : Type*} [Fintype α] [DecidableEq α]

def lengthSwap {t : ℕ} (s : Lengths t) : Lengths t :=
  ⟨(s.val.2, s.val.1), by have h := s.property; simpa [Nat.add_comm] using h⟩

def recordSwap {t : ℕ} (v : InputCutoff (α := α) t) : InputCutoff (α := α) t :=
  ⟨⟨lengthSwap v.1.1, profileTranspose _ v.2.2⟩,
    (v.2.1, profileTranspose _ v.1.2)⟩

theorem recordSwap_involutive {t : ℕ} (v : InputCutoff (α := α) t) :
    recordSwap (recordSwap v) = v := by
  apply input_ext
  · rfl
  · rfl
  · rfl
  · exact congrArg Subtype.val (profileTranspose_involutive v.2.2)
  · exact congrArg Subtype.val (profileTranspose_involutive v.1.2)

def recordSwapEquiv (t : ℕ) : InputCutoff (α := α) t ≃ InputCutoff (α := α) t :=
  ⟨recordSwap, recordSwap, recordSwap_involutive, recordSwap_involutive⟩

theorem recordSwap_inputEmbed {t T : ℕ} (h : t ≤ T) (v : InputCutoff (α := α) t) :
    recordSwap (inputEmbed h v) = inputEmbed h (recordSwap v) := by
  apply input_ext <;> rfl

def swapMatrix (t : ℕ) : CMatrix (InputCutoff (α := α) t) :=
  basisEmbedding (recordSwapEquiv t)

theorem swapMatrix_gram (t : ℕ) :
    (swapMatrix (α := α) t).conjTranspose * swapMatrix (α := α) t = 1 :=
  basisEmbedding_gram _ (recordSwapEquiv t).injective

theorem swapMatrix_norm_le (t : ℕ) : ‖swapMatrix (α := α) t‖ ≤ 1 :=
  isometry_matrix_norm_le _ (swapMatrix_gram t)

def rightOnFock {t T : ℕ} (h : t + 1 ≤ T) : CMatrix (InputCutoff (α := α) T) :=
  swapMatrix T * leftOnFock h * (swapMatrix T).conjTranspose

def symmetricRightOnFock {t T : ℕ} (h : t + 1 ≤ T) : CMatrix (InputCutoff (α := α) T) :=
  swapMatrix T * symmetricOnFock h * (swapMatrix T).conjTranspose

theorem rightOnFock_difference_norm_le {t T : ℕ} (h : t + 1 ≤ T) (ht : t < Fintype.card α) :
    ‖rightOnFock (α := α) h - symmetricRightOnFock h‖ ≤
      Real.sqrt ((2 * (t : ℝ) * (t + 1)) / Fintype.card α) := by
  have hS := swapMatrix_norm_le (α := α) T
  have hAdj : ‖(swapMatrix (α := α) T).conjTranspose‖ ≤ 1 := by
    rwa [Matrix.l2_opNorm_conjTranspose]
  rw [rightOnFock, symmetricRightOnFock, ← Matrix.sub_mul, ← Matrix.mul_sub]
  calc
    _ ≤ (‖swapMatrix (α := α) T‖ * ‖leftOnFock (α := α) h - symmetricOnFock h‖) *
        ‖(swapMatrix (α := α) T).conjTranspose‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ ((1 : ℝ) * Real.sqrt ((2 * (t : ℝ) * (t + 1)) / Fintype.card α)) * 1 :=
      mul_le_mul (mul_le_mul hS (leftOnFock_difference_norm_le h ht)
        (norm_nonneg _) (by norm_num)) hAdj (norm_nonneg _) (by positivity)
    _ = _ := by ring

end
end ICO.MHFockSwap
