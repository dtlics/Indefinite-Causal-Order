import ICO.ProtocolLudersTrajectory
import Mathlib.Topology.Instances.Matrix

namespace ICO.ProtocolLudersTrajectory
open Matrix QIT ICO.SequentialIsometry
noncomputable section
universe u
set_option maxHeartbeats 1800000
variable {A M N H O B : Type u} [Fintype A] [DecidableEq A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
  [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O]
  [Fintype B] [DecidableEq B]

theorem luders_continuous (K : Matrix (A×N) (A×M) ℂ) :
    Continuous (fun U : CMatrix A => ICO.PrivateQueryStep.luders (H:=H) U K) := by
  apply continuous_matrix
  intro o i
  simp only [ICO.PrivateQueryStep.luders_eq_step,ICO.PrivateQueryStep.step]
  split_ifs
  · simp only [Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,
      ICO.SwitchObservable.basisProjection,Matrix.conjTranspose_apply]
    fun_prop
  · exact continuous_const

theorem run_continuous {q : ℕ} (tail : Protocol A (A×M) O q) (v : A×M → ℂ) (t : ℕ) :
    Continuous (fun U : CMatrix A => run tail U v t) := by
  induction t with
  | zero => exact continuous_const
  | succ t ih =>
    exact (luders_continuous (tail.tailKnown t)).matrix_mulVec ih

#print axioms run_continuous
end
end ICO.ProtocolLudersTrajectory
