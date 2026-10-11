import ICO.C6NativeFresh
import ICO.C6BosonicFreshPrefix

/-! The shared-U physical output versus the actual fresh recording process.
Every support premise is derived from the literal empty-record trajectory. -/
namespace ICO.C6PhysicalFresh
open Matrix QIT ICO.C6NativeFresh ICO.C6BosonicFreshPrefix ICO.C6HistoryControlled
  ICO.C6SharedPolarBound ICO.C6SharedHaarBound ICO.C6SharedEndpoint
  ICO.C6SharedStages ICO.C6SharedSchedule ICO.C6SharedQuerySchedule
  ICO.C6PairedHybrid ICO.SequentialIsometry ICO.MHDecompressionErasure
  ICO.RecordingDistance
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A M O:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

def freshDensity {q T:ℕ} (tail:Protocol (A×Bool) ((A×Bool)×M) O q)
    (H:Matrix.unitaryGroup A ℂ) (v:(A×Bool)×M→ℂ) (n:ℕ) (h:2*n+1≤T) :
    CMatrix ((A×Bool)×tail.tailMemory n) :=
  (stageErasure tail n).map (fockVisible T (freshNative h H tail.tailKnown
    (initial tail v ∘ (regroup (Memory (A:=A) tail.tailMemory 0 0)).symm) n))

theorem polar_fresh_distance {q T:ℕ} (tail:Protocol (A×Bool) ((A×Bool)×M) O q)
    (H:Matrix.unitaryGroup A ℂ) (v:(A×Bool)×M→ℂ) (hv:‖WithLp.toLp 2 v‖≤1)
    (n:ℕ) (h:2*n+1≤T) (hd:2*n<Fintype.card A) :
    normalizedTraceDistance (polarDensity tail H v n h) (freshDensity tail H v n h)≤
      ∑i∈Finset.range n,freshCost (Fintype.card A) i := by
  have hz := (initial_norm tail v).le.trans hv
  have hh := polar_fresh_visible_of_prefix h hd H tail.tailKnown tail.tailKnown_isometry
    (initial tail v ∘ (regroup (Memory (A:=A) tail.tailMemory 0 0)).symm) hz n (by omega)
    (fun i _=>freshRun_prefix h hd H tail.tailKnown _ i)
  exact (distance_contract (stageErasure tail n).map
    (stageErasure tail n).traceNonincreasingCP_map _ _
    (partialTraceB_posSemidef (Matrix.posSemidef_vecMulVec_self_star _))
    (partialTraceB_posSemidef (Matrix.posSemidef_vecMulVec_self_star _))).trans hh

theorem shared_haar_fresh {q T:ℕ} (tail:Protocol (A×Bool) ((A×Bool)×M) O q)
    (H:Matrix.unitaryGroup A ℂ) (v:(A×Bool)×M→ℂ) (hv:‖WithLp.toLp 2 v‖=1)
    (n:ℕ) (hT:2*Fintype.card (A×A)≤T) (h:2*n+1≤T)
    (hsmall:4*n≤Fintype.card A) (R:ℝ) (hR:1≤R) (hd:(Fintype.card A:ℝ)=R^8) :
    normalizedTraceDistance (haarDensity tail H v n) (freshDensity tail H v n h)≤
      9*(2*(n:ℝ))*(2*(n:ℝ)+1)/R+
      (∑i∈Finset.range n,deletionCost (Fintype.card A) i)+
        7*(n:ℝ)*ICO.C6PolarFockBounds.delta (2*n) (Fintype.card A)+
          ∑i∈Finset.range n,freshCost (Fintype.card A) i := by
  have hnd:2*n<Fintype.card A := by have hp:=Fintype.card_pos (α:=A); omega
  have h1:=shared_haar_polar tail H v hv n hT h hsmall R hR hd
  have h2:=polar_fresh_distance tail H v hv.le n h hnd
  exact (normalizedTraceDistance_triangle _ (polarDensity tail H v n h) _).trans
    (add_le_add h1 h2)

#print axioms shared_haar_fresh
end
end ICO.C6PhysicalFresh
