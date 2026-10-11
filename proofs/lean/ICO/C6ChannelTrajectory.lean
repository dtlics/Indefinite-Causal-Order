import ICO.C6SectorChannel
import ICO.RecordingDistance

/-! Literal mixed-state channel trajectories with changing finite memory,
and the telescoping bound on actual reference prefixes. -/
namespace ICO.C6ChannelTrajectory
open QIT Matrix ICO.RecordingDistance
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1600000
variable {H : ℕ → Type*} [∀i,Fintype (H i)] [∀i,DecidableEq (H i)]

def run (S : ∀i,Channel (H i) (H (i+1))) (X : CMatrix (H 0)) :
    (i : ℕ) → CMatrix (H i)
  | 0 => X
  | i+1 => (S i).map (run S X i)

theorem run_pos (S : ∀i,Channel (H i) (H (i+1))) (X : CMatrix (H 0))
    (hX : X.PosSemidef) (n : ℕ) : (run S X n).PosSemidef := by
  induction n with
  | zero => exact hX
  | succ n ih => exact (S n).mapsPositive _ ih

theorem run_trace (S : ∀i,Channel (H i) (H (i+1))) (X : CMatrix (H 0))
    (n : ℕ) : (run S X n).trace=X.trace := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run,(S n).tracePreserving,ih]

theorem run_property (S : ∀i,Channel (H i) (H (i+1)))
    (P : ∀i,CMatrix (H i) → Prop) (hS : ∀i X,P i X → P (i+1) ((S i).map X))
    (X : CMatrix (H 0)) (hX : P 0 X) (n : ℕ) : P n (run S X n) := by
  induction n with
  | zero => exact hX
  | succ n ih => exact hS n _ ih

theorem run_distance (S T : ∀i,Channel (H i) (H (i+1)))
    (X : CMatrix (H 0)) (hX : X.PosSemidef) (ε : ℝ)
    (hε : ∀i,traceNorm ((S i).map (run T X i)-(T i).map (run T X i))≤ε)
    (n : ℕ) : traceNorm (run S X n-run T X n)≤(n:ℝ)*ε := by
  induction n with
  | zero => simp [run,traceNorm_zero]
  | succ n ih =>
    have he : run S X (n+1)-run T X (n+1)=
        (S n).map (run S X n-run T X n)+
          ((S n).map (run T X n)-(T n).map (run T X n)) := by
      rw [map_sub]
      simp only [run]
      abel
    have hc := traceNorm_contract_hermitian (S n).map
      (MatrixMap.traceNonincreasingCP_of_tracePreserving (S n).completelyPositive
        (S n).tracePreserving) (run S X n-run T X n)
      ((run_pos S X hX n).isHermitian.sub (run_pos T X hX n).isHermitian)
    rw [he, Nat.cast_add, Nat.cast_one]
    exact (traceNorm_add_le _ _).trans (by linarith [hε n])

#print axioms run_distance
end
end ICO.C6ChannelTrajectory
