import ICO.C6SharedEndpoint

/-! Actual shared-U SAME/MUB channel strategies inherit the signed-query
Haar-recording estimate on the original d-dimensional query register. -/
namespace ICO.C6SharedHaarBound
open Matrix QIT MeasureTheory ICO.SequentialIsometry ICO.C6SharedBasis ICO.C6SharedStages
  ICO.C6SharedSchedule ICO.C6SharedQuerySchedule ICO.C6SharedEndpoint
  ICO.MHProtocolHaarRecording ICO.MHActualRecordingOverlap ICO.MHDecompressionErasure
  ICO.MHFockFiniteErasure ICO.MHFockTrajectory
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1600000
set_option Elab.async false
variable {A M O : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

def recordingDensity {q T:ℕ} (tail : Protocol (A×Bool) ((A×Bool)×M) O q)
    (H : Matrix.unitaryGroup A ℂ) (v:(A×Bool)×M→ℂ) (n:ℕ) (hq:2*n+1≤T) :
    CMatrix ((A×Bool)×tail.tailMemory n) :=
  (stageErasure tail n).map (fockVisible T
    (ICO.MHFockTrajectory.run T (known H tail.tailKnown 0)
      (fun t=>Vchoice hq (ICO.DoubleQuerySchedule.direction t))
      (initial tail v ∘ (regroup (Memory (A:=A) tail.tailMemory 0 0)).symm) (2*n)))

theorem shared_haar_recording {q T:ℕ} (tail : Protocol (A×Bool) ((A×Bool)×M) O q)
    (H : Matrix.unitaryGroup A ℂ) (v:(A×Bool)×M→ℂ) (hv:‖WithLp.toLp 2 v‖=1)
    (n:ℕ) (hT:2*Fintype.card (A×A)≤T) (hq:2*n+1≤T)
    (hsmall:4*n≤Fintype.card A) (R:ℝ) (hR:1≤R) (hd:(Fintype.card A:ℝ)=R^8) :
    normalizedTraceDistance (haarDensity tail H v n) (recordingDensity tail H v n hq)≤
      9*(2*(n:ℝ))*(2*(n:ℝ)+1)/R := by
  have hn : 2*n<Fintype.card A := by have hpos:=Fintype.card_pos (α:=A); omega
  have hs : 2*(2*n)≤Fintype.card A := by omega
  have hz : ‖WithLp.toLp 2
      (initial tail v ∘ (regroup (Memory (A:=A) tail.tailMemory 0 0)).symm)‖=1 :=
    (initial_norm tail v).trans hv
  have hh := channel_frequency_distance hT hq hn hs (known H tail.tailKnown 0)
    (fun t=>known_isometry H tail.tailKnown tail.tailKnown_isometry 0 t)
    ICO.DoubleQuerySchedule.direction
    (initial tail v ∘ (regroup (Memory (A:=A) tail.tailMemory 0 0)).symm)
    hz R hR hd (stageErasure tail n)
  change normalizedTraceDistance
    ((stageErasure tail n).map (∫p,physicalVisible
      (ICO.C6SharedFrequency.frequency H tail.tailKnown p.1 p.2 0 (initial tail v) (2*n))
      ∂ICO.MHDomainMeanProduct.rotationMeasure A))
    (recordingDensity tail H v n hq)≤_ at hh
  rw [ICO.C6SharedEndpoint.physical_mean_endpoint] at hh
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh

#print axioms shared_haar_recording
end
end ICO.C6SharedHaarBound
