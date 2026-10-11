import ICO.C6MatrixTrajectory

/-! State-dependent prefix hybrid for actual varying-memory matrix runs. -/
namespace ICO.C6MatrixLocalHybrid
open QIT ICO.C6MatrixTrajectory ICO.MHRectangularAction
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000
variable {H:ℕ→Type*} [∀i,Fintype (H i)] [∀i,DecidableEq (H i)]

theorem run_distance_upto (S T:∀i,Matrix (H (i+1)) (H i) ℂ)
    (z:EuclideanSpace ℂ (H 0)) (ε:ℕ→ℝ) (n:ℕ)
    (hT:∀i<n,‖T i‖≤1)
    (hloc:∀i<n,‖rectAct (S i-T i) (run S z i)‖≤ε i) :
    ‖run S z n-run T z n‖≤∑i∈Finset.range n,ε i := by
  have hb : ∀k≤n,‖run S z k-run T z k‖≤∑i∈Finset.range k,ε i := by
    intro k
    induction k with
    | zero => intro hk; simp [run]
    | succ k ih =>
      intro hk
      have hkn : k<n := by omega
      have hprev := ih (by omega)
      have he : run S z (k+1)-run T z (k+1)=
          rectAct (S k-T k) (run S z k)+rectAct (T k) (run S z k-run T z k) := by
        rw [rectAct_sub,map_sub]
        simp only [run]
        abel
      have hsecond : ‖rectAct (T k) (run S z k-run T z k)‖≤‖run S z k-run T z k‖ := by
        exact (rectAct_norm_le _ _).trans (by
          simpa using mul_le_mul_of_nonneg_right (hT k hkn) (norm_nonneg (run S z k-run T z k)))
      rw [he,Finset.sum_range_succ]
      exact (norm_add_le _ _).trans (by linarith [hloc k hkn])
  exact hb n le_rfl

#print axioms run_distance_upto
end
end ICO.C6MatrixLocalHybrid
