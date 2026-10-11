import ICO.C6NativePolar
import ICO.C6SharedHaarBound

/-! The original shared-basis Haar-averaged physical output is close to the
literal polar recording process, with every adaptive protocol map retained. -/
namespace ICO.C6SharedPolarBound
open Matrix QIT ICO.SequentialIsometry ICO.C6SharedEndpoint ICO.C6SharedHaarBound
  ICO.C6NativePolar ICO.C6PairedHybrid ICO.C6PairedTrajectory ICO.C6SharedStages
  ICO.C6SharedSchedule ICO.C6SharedQuerySchedule ICO.MHDecompressionErasure
  ICO.RecordingDistance
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A M O:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

def polarDensity {q T:ℕ} (tail:Protocol (A×Bool) ((A×Bool)×M) O q)
    (H:Matrix.unitaryGroup A ℂ) (v:(A×Bool)×M→ℂ) (n:ℕ) (h:2*n+1≤T) :
    CMatrix ((A×Bool)×tail.tailMemory n) :=
  (stageErasure tail n).map (fockVisible T (polarNative h H tail.tailKnown
    (initial tail v ∘ (regroup (Memory (A:=A) tail.tailMemory 0 0)).symm) n))

theorem recording_polar_distance {q T:ℕ} (tail:Protocol (A×Bool) ((A×Bool)×M) O q)
    (H:Matrix.unitaryGroup A ℂ) (v:(A×Bool)×M→ℂ) (hv:‖WithLp.toLp 2 v‖≤1)
    (n:ℕ) (h:2*n+1≤T) (hd:2*n<Fintype.card A) :
    normalizedTraceDistance (recordingDensity tail H v n h) (polarDensity tail H v n h)≤
      (∑i∈Finset.range n,deletionCost (Fintype.card A) i)+
        7*(n:ℝ)*ICO.C6PolarFockBounds.delta (2*n) (Fintype.card A) := by
  have hz := (initial_norm tail v).le.trans hv
  have hh := native_polar_visible h hd H tail.tailKnown tail.tailKnown_isometry
    (initial tail v ∘ (regroup (Memory (A:=A) tail.tailMemory 0 0)).symm) hz n le_rfl
  exact (distance_contract (stageErasure tail n).map
    (stageErasure tail n).traceNonincreasingCP_map _ _
    (partialTraceB_posSemidef (Matrix.posSemidef_vecMulVec_self_star _))
    (partialTraceB_posSemidef (Matrix.posSemidef_vecMulVec_self_star _))).trans hh

theorem shared_haar_polar {q T:ℕ} (tail:Protocol (A×Bool) ((A×Bool)×M) O q)
    (H:Matrix.unitaryGroup A ℂ) (v:(A×Bool)×M→ℂ) (hv:‖WithLp.toLp 2 v‖=1)
    (n:ℕ) (hT:2*Fintype.card (A×A)≤T) (h:2*n+1≤T)
    (hsmall:4*n≤Fintype.card A) (R:ℝ) (hR:1≤R) (hd:(Fintype.card A:ℝ)=R^8) :
    normalizedTraceDistance (haarDensity tail H v n) (polarDensity tail H v n h)≤
      9*(2*(n:ℝ))*(2*(n:ℝ)+1)/R+
      (∑i∈Finset.range n,deletionCost (Fintype.card A) i)+
        7*(n:ℝ)*ICO.C6PolarFockBounds.delta (2*n) (Fintype.card A) := by
  have hnd : 2*n<Fintype.card A := by have hp:=Fintype.card_pos (α:=A); omega
  have hh := shared_haar_recording tail H v hv n hT h hsmall R hR hd
  have hp := recording_polar_distance tail H v hv.le n h hnd
  exact (normalizedTraceDistance_triangle _ (recordingDensity tail H v n h) _).trans
    (by linarith)

#print axioms shared_haar_polar
end
end ICO.C6SharedPolarBound
