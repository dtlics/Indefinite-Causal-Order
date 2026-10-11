import ICO.C6ResidualSelection
import ICO.C6BosonicStageBlocks

namespace ICO.C6FlagZero
open Matrix QIT ICO.C6ResidualSelection ICO.C6ResidualModes ICO.C6CacheSpanProjection
  ICO.C6BosonicQueryAlgebra ICO.C6BosonicReencoding ICO.C6BosonicFockRotated
  ICO.C6BosonicStageBlocks ICO.C6BosonicHistorySupport ICO.C6FockQueryMatrix
  ICO.C6PolarFock ICO.MHBoundedRecording
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 700000
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem inactive_fresh_measurement {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (i:Fin q)
    (hi:residual v i=0) (U:Matrix.unitaryGroup A ℂ) (B:Finset A)
    (hB:historyProjection (prior v i)=spanProjection U B) (T:ℕ) :
    queryMatrix (rankOne (v i)) T*rotatedFresh U B T=0 := by
  rw [rotatedFresh_complement,←ICO.C6BosonicQueryAlgebra.query_one,←query_sub,
    ←query_mul,←hB,inactive_selection v i hi,query_zero]

theorem inactive_birth {q t T:ℕ} (v:Fin q→EuclideanSpace ℂ A) (i:Fin q)
    (hi:residual v i=0) (U:Matrix.unitaryGroup A ℂ) (B:Finset A)
    (hB:historyProjection (prior v i)=spanProjection U B) (h:t+1≤T) :
    polarLeftOnFock h*queryMatrix (rankOne (v i)) T*rotatedFresh U B T*
        polarRightOnFock h*(1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)*historySupport (prior v i) T=0 := by
  rw [Matrix.mul_assoc (polarLeftOnFock h),inactive_fresh_measurement v i hi U B hB T]
  simp

#print axioms inactive_birth
end
end ICO.C6FlagZero
