import ICO.C6FlagSlices
import ICO.C6FlagCore
import ICO.C6NumberStageTransfer
import ICO.C6FlagVacuum

namespace ICO.C6FlagPrefixRun
open Matrix QIT ICO.C6FlagSlices ICO.C6FlagCore ICO.C6NumberStageTransfer
  ICO.C6BirthFlags ICO.C6RetainedHistory ICO.C6HistoryCoordinates ICO.C6HistoryPrefixSteps
  ICO.C6FixedHistoryBasis ICO.C6ResidualModes ICO.C6ResidualCoordinates
  ICO.C6CacheSpanProjection ICO.C6NumberRotationAlgebra ICO.C6CacheHistorySpan
  ICO.C6ChoiceMeasurement ICO.C6BosonicReencoding ICO.C6FockQueryMatrix ICO.C6PolarFock
  ICO.MHBoundedRecording ICO.MHFockKnownOperation ICO.MHRectangularAction
  ICO.RecordingPurifiedProtocol ICO.C6PairedTrajectory
noncomputable section
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def prefixRun {q t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0))
    (η:History (A×Bool) q) (n:ℕ) (hn:n≤q) (κ:History Bool n) :
    EuclideanSpace ℂ (InputCutoff (α:=A) T×(Bool×μ n)) :=
  slice (prefixHistory η n hn) (flagRun h H K z n κ)

theorem prefixRun_step {q t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0))
    (η:History (A×Bool) q) (n:ℕ) (hn:n+1≤q) (κ:History Bool n) (f:Bool) :
    prefixRun h H K z η (n+1) hn (f,κ)=
      rectAct (branchStage h H K n (prefixHistory η n (by omega))
        (historyEquiv (A×Bool) q η ⟨n,by omega⟩).1
        (historyEquiv (A×Bool) q η ⟨n,by omega⟩).2 f)
          (prefixRun h H K z η n (by omega) κ) := by
  unfold prefixRun
  rw [prefixHistory_succ]
  exact flagRun_slice_succ h H K z n _ κ _ _ f

theorem branchStage_core {q t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (η:History (A×Bool) q) (i:Fin q) (U:Matrix.unitaryGroup A ℂ) (B:Finset A)
    (hB:historyProjection (prior (vectors H q η) i)=spanProjection U B) (f:Bool) :
    branchStage h H K i (prefixHistory η i i.isLt.le)
      (historyEquiv (A×Bool) q η i).1 (historyEquiv (A×Bool) q η i).2 f=
      known T (smallKnown (K i))*Matrix.kronecker
        (measuredCore h (vectors H q η) i U B f)
        (choiceProject (historyEquiv (A×Bool) q η i).2 (μ i)) := by
  rw [branchStage,branchMiddle_tensor,←vectors_coords,actual_core h H η i U B hB]

theorem prefixRun_core_step {q t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0))
    (η:History (A×Bool) q) (n:ℕ) (hn:n+1≤q) (κ:History Bool n) (f:Bool)
    (U:Matrix.unitaryGroup A ℂ) (B:Finset A)
    (hB:historyProjection (prior (vectors H q η) ⟨n,by omega⟩)=spanProjection U B) :
    prefixRun h H K z η (n+1) hn (f,κ)=
      rectAct (known T (smallKnown (K n))*Matrix.kronecker
        (measuredCore h (vectors H q η) ⟨n,by omega⟩ U B f)
        (choiceProject (historyEquiv (A×Bool) q η ⟨n,by omega⟩).2 (μ n)))
          (prefixRun h H K z η n (by omega) κ) := by
  rw [prefixRun_step,branchStage_core h H K η ⟨n,by omega⟩ U B hB]

#print axioms prefixRun_core_step
end
end ICO.C6FlagPrefixRun
