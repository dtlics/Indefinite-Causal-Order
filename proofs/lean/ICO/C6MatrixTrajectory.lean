import ICO.MHRectangularAction

/-! A literal varying-memory matrix trajectory and its uniform hybrid estimate. -/
namespace ICO.C6MatrixTrajectory
open QIT ICO.MHRectangularAction
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
set_option Elab.async false
variable {H:ℕ→Type*} [∀i,Fintype (H i)] [∀i,DecidableEq (H i)]

def run (S:∀i,Matrix (H (i+1)) (H i) ℂ) (z:EuclideanSpace ℂ (H 0)) :
    (i:ℕ)→EuclideanSpace ℂ (H i)
  | 0 => z
  | i+1 => rectAct (S i) (run S z i)

theorem run_norm (S:∀i,Matrix (H (i+1)) (H i) ℂ) (hS:∀i,‖S i‖≤1)
    (z:EuclideanSpace ℂ (H 0)) (hz:‖z‖≤1) (n:ℕ) : ‖run S z n‖≤1 := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    exact (rectAct_norm_le _ _).trans
      (by simpa using mul_le_mul (hS n) ih (norm_nonneg _) (by norm_num))

theorem rectAct_sub {A B:Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (M N:Matrix B A ℂ) (x:EuclideanSpace ℂ A) :
    rectAct (M-N) x=rectAct M x-rectAct N x := by
  change WithLp.toLp 2 ((M-N)*ᵥWithLp.ofLp x)=_
  rw [Matrix.sub_mulVec]
  rfl

theorem run_distance (S T:∀i,Matrix (H (i+1)) (H i) ℂ)
    (hS:∀i,‖S i‖≤1) (hT:∀i,‖T i‖≤1)
    (ε:ℝ) (hε:∀i,‖S i-T i‖≤ε)
    (z:EuclideanSpace ℂ (H 0)) (hz:‖z‖≤1) (n:ℕ) :
    ‖run S z n-run T z n‖≤(n:ℝ)*ε := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hx := run_norm S hS z hz n
    have he : run S z (n+1)-run T z (n+1)=
        rectAct (S n-T n) (run S z n)+rectAct (T n) (run S z n-run T z n) := by
      rw [rectAct_sub,map_sub]
      simp only [run]
      abel
    have hfirst : ‖rectAct (S n-T n) (run S z n)‖≤ε := by
      calc
        _ ≤ ‖S n-T n‖*‖run S z n‖ := rectAct_norm_le _ _
        _ ≤ ‖S n-T n‖*1 := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
        _ ≤ ε := by simpa using hε n
    have hsecond : ‖rectAct (T n) (run S z n-run T z n)‖≤‖run S z n-run T z n‖ := by
      exact (rectAct_norm_le _ _).trans (by
        simpa using mul_le_mul_of_nonneg_right (hT n) (norm_nonneg (run S z n-run T z n)))
    rw [he,Nat.cast_add,Nat.cast_one]
    exact (norm_add_le _ _).trans (by linarith)

#print axioms run_distance
end
end ICO.C6MatrixTrajectory
