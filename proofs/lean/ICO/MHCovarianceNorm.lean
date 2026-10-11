import ICO.MHBlockNorm

/-! Quantitative covariance from exact covariance and an operator-norm
approximation; all maps may be rectangular between adjacent record sectors. -/

namespace ICO.MHCovarianceNorm

open QIT
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 1000000

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem approximate_intertwine (V E : Matrix b a ℂ) (D Q : CMatrix b) (R : CMatrix a)
    (ε : ℝ) (hε : ‖V - E‖ ≤ ε)
    (hD : ‖D‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hcov : D * E * R = Q * E) :
    ‖D * V * R - Q * V‖ ≤ 2 * ε := by
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hε
  have heq : D * V * R - Q * V = D * (V - E) * R + Q * (E - V) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, ← hcov]
    abel
  have hfirst : ‖D * (V - E) * R‖ ≤ ε := by
    calc
      _ ≤ (‖D‖ * ‖V - E‖) * ‖R‖ :=
        (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ ((1 : ℝ) * ε) * 1 :=
        mul_le_mul (mul_le_mul hD hε (norm_nonneg _) (by norm_num)) hR
          (norm_nonneg _) (by positivity)
      _ = ε := by ring
  have hsecond : ‖Q * (E - V)‖ ≤ ε := by
    calc
      _ ≤ ‖Q‖ * ‖E - V‖ := Matrix.l2_opNorm_mul _ _
      _ = ‖Q‖ * ‖V - E‖ := by rw [norm_sub_rev E V]
      _ ≤ 1 * ε := mul_le_mul hQ hε (norm_nonneg _) (by norm_num)
      _ = ε := one_mul _
  rw [heq]
  exact (norm_add_le _ _).trans (by linarith)

end
end ICO.MHCovarianceNorm
