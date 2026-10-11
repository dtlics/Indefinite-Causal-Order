import ICO.MHFockRotationSwap

/-! Quantitative covariance of both actual recording insertions under the
same global record rotation. -/

namespace ICO.MHFockBothCovariance

open QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockRotation
  ICO.MHFockTransport ICO.MHFockCovariance ICO.MHFockSwap ICO.MHFockOracle
  ICO.MHFockRotationSwap ICO.MHSectorCovariance
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 2500000

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem inputFamily_mul (F G : ∀ n r, CMatrix (Sector (α := α) n r)) (T : ℕ) :
    inputFamily F T * inputFamily G T = inputFamily (fun n r => F n r * G n r) T := by
  unfold inputFamily
  rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]

theorem query_output_turn (C D : Matrix.unitaryGroup α ℂ) (n r : ℕ) :
    (queryTurn C n r : CMatrix (Sector (α := α) n r)) *
      (outputTurn C D n r : CMatrix (Sector (α := α) n r)) =
    (inputTurn C D n r : CMatrix (Sector (α := α) n r)) := by
  change Matrix.kronecker (Matrix.kronecker (C : CMatrix α) 1) 1 *
    Matrix.kronecker (Matrix.kronecker 1 _) _ = _
  simp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.mul_one, Matrix.one_mul]
  rfl

theorem fockQuery_fockQ (C D : Matrix.unitaryGroup α ℂ) (T : ℕ) :
    (fockQuery C T : CMatrix (InputCutoff (α := α) T)) * (fockQ C D T : CMatrix (InputCutoff (α := α) T)) =
      inputFamily (fun n r => (inputTurn C D n r : CMatrix (Sector (α := α) n r))) T := by
  change inputFamily (fun n r => (queryTurn C n r : CMatrix (Sector (α := α) n r))) T *
      inputFamily (fun n r => (outputTurn C D n r : CMatrix (Sector (α := α) n r))) T = _
  rw [inputFamily_mul]
  simp only [query_output_turn]

theorem queryTurn_adjoint (U : Matrix.unitaryGroup α ℂ) (n r : ℕ) :
    (queryTurn U n r : CMatrix (Sector (α := α) n r)).conjTranspose =
      (queryTurn U⁻¹ n r : CMatrix (Sector (α := α) n r)) := by
  simp [queryTurn, tensorUnitary, Matrix.conjTranspose_kronecker, Matrix.UnitaryGroup.inv_val]
  rfl

theorem fockQuery_inverse (U : Matrix.unitaryGroup α ℂ) (T : ℕ) :
    (fockQuery U⁻¹ T : CMatrix (InputCutoff (α := α) T)) =
      (fockQuery U T : CMatrix (InputCutoff (α := α) T)).conjTranspose := by
  change inputFamily (fun n r => (queryTurn U⁻¹ n r : CMatrix (Sector (α := α) n r))) T =
    (inputFamily (fun n r => (queryTurn U n r : CMatrix (Sector (α := α) n r))) T).conjTranspose
  rw [inputFamily_adjoint]
  simp only [queryTurn_adjoint]

theorem left_covariance (C D : Matrix.unitaryGroup α ℂ)
    {t T : ℕ} (h : t+1 ≤ T) (ht : t < Fintype.card α) :
    ‖(fockQuery D T : CMatrix (InputCutoff (α := α) T)) * leftOnFock h *
        ((fockQuery C T : CMatrix (InputCutoff (α := α) T)) * (fockQ C D T : CMatrix (InputCutoff (α := α) T))) -
      (fockQ C D T : CMatrix (InputCutoff (α := α) T)) * leftOnFock h‖ ≤
      2 * Real.sqrt ((2 * (t : ℝ) * (t+1)) / Fintype.card α) := by
  rw [fockQuery_fockQ]
  exact leftOnFock_covariance_norm C D h ht

theorem swap_mul (T : ℕ) (M N : CMatrix (InputCutoff (α := α) T)) :
    swapMatrix T * (M*N) * swapMatrix T =
      (swapMatrix T * M * swapMatrix T) * (swapMatrix T * N * swapMatrix T) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (swapMatrix (α := α) T) (swapMatrix (α := α) T), swapMatrix_sq, Matrix.one_mul]

theorem swap_sub (T : ℕ) (M N : CMatrix (InputCutoff (α := α) T)) :
    swapMatrix T * (M-N) * swapMatrix T =
      swapMatrix T * M * swapMatrix T - swapMatrix T * N * swapMatrix T := by
  simp only [Matrix.mul_sub, Matrix.sub_mul]

theorem swap_norm_le (T : ℕ) (M : CMatrix (InputCutoff (α := α) T)) :
    ‖swapMatrix T * M * swapMatrix T‖ ≤ ‖M‖ := by
  have hS := swapMatrix_norm_le (α := α) T
  calc
    _ ≤ (‖swapMatrix (α := α) T‖ * ‖M‖) * ‖swapMatrix (α := α) T‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖M‖) * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hS (norm_nonneg M)) hS (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem right_covariance (C D : Matrix.unitaryGroup α ℂ)
    {t T : ℕ} (h : t+1 ≤ T) (ht : t < Fintype.card α) :
    ‖(fockQuery C⁻¹ T : CMatrix (InputCutoff (α := α) T)) * rightOnFock h *
        ((fockQuery D⁻¹ T : CMatrix (InputCutoff (α := α) T)) * (fockQ C D T : CMatrix (InputCutoff (α := α) T))) -
      (fockQ C D T : CMatrix (InputCutoff (α := α) T)) * rightOnFock h‖ ≤
      2 * Real.sqrt ((2 * (t : ℝ) * (t+1)) / Fintype.card α) := by
  have he : swapMatrix T *
      ((fockQuery C⁻¹ T : CMatrix (InputCutoff (α := α) T)) * leftOnFock h *
        ((fockQuery D⁻¹ T : CMatrix (InputCutoff (α := α) T)) * (fockQ D⁻¹ C⁻¹ T : CMatrix (InputCutoff (α := α) T))) -
      (fockQ D⁻¹ C⁻¹ T : CMatrix (InputCutoff (α := α) T)) * leftOnFock h) * swapMatrix T =
      (fockQuery C⁻¹ T : CMatrix (InputCutoff (α := α) T)) * rightOnFock h *
        ((fockQuery D⁻¹ T : CMatrix (InputCutoff (α := α) T)) * (fockQ C D T : CMatrix (InputCutoff (α := α) T))) -
      (fockQ C D T : CMatrix (InputCutoff (α := α) T)) * rightOnFock h := by
    simp only [swap_sub, swap_mul, swap_fockQuery, swap_fockQ, inv_inv,
      rightOnFock, swapMatrix_selfAdjoint]
  rw [← he]
  exact (swap_norm_le T _).trans (left_covariance D⁻¹ C⁻¹ h ht)

end
end ICO.MHFockBothCovariance
