import ICO.C6RawHybrid
import ICO.C6FlagVisible
import ICO.C6FreshVisibleEndpoint

/-! The concrete globally contractive raw process differs from the physical
fresh process by the proved sum of the per-step inverse errors. -/
namespace ICO.C6FreshRawEndpoint
open QIT Matrix ICO.C6RawHybrid ICO.C6RawFlags ICO.C6FlagVisible
  ICO.C6HistoryVisible ICO.C6FreshVisibleEndpoint ICO.C6PhysicalFresh
  ICO.C6RetainedHistory ICO.C6PairedTrajectory ICO.SequentialIsometry
  ICO.C6SharedEndpoint ICO.C6SharedStages ICO.C6SharedQuerySchedule
  ICO.C6SharedSchedule ICO.MHBoundedRecording ICO.RecordingHistory
  ICO.RecordingPurifiedProtocol ICO.C6NativeFresh
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 2048
set_option Elab.async false
variable {A M O : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

def rawDensity {q T : ℕ} (tail : Protocol (A×Bool) ((A×Bool)×M) O q)
    (H : Matrix.unitaryGroup A ℂ) (v : (A×Bool)×M→ℂ) (n : ℕ) (h : 2*n+1≤T) :
    CMatrix ((A×Bool)×tail.tailMemory n) :=
  ∑κ:History Bool n,ICO.C6HistoryVisible.visible (WithLp.ofLp
    (rawFlagRun h H tail.tailKnown (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T
      (initial tail v ∘ (regroup (Memory (A:=A) tail.tailMemory 0 0)).symm))) n κ))

theorem fresh_raw_distance {q T : ℕ} (tail : Protocol (A×Bool) ((A×Bool)×M) O q)
    (H : Matrix.unitaryGroup A ℂ) (v : (A×Bool)×M→ℂ) (hv : ‖WithLp.toLp 2 v‖≤1)
    (n : ℕ) (h : 2*n+1≤T) (hd : 2*n<Fintype.card A) :
    normalizedTraceDistance (freshDensity tail H v n h) (rawDensity tail H v n h)≤
      ∑i∈Finset.range n,(i:ℝ)/Fintype.card A := by
  let z := initial tail v ∘ (regroup (Memory (A:=A) tail.tailMemory 0 0)).symm
  have hz : ‖WithLp.toLp 2 z‖≤1 := (initial_norm tail v).le.trans hv
  have hn : n≤Fintype.card A := by omega
  rw [freshDensity_visible]
  change normalizedTraceDistance (ICO.C6HistoryVisible.visible
    (WithLp.ofLp (freshVector h H tail.tailKnown z n))) (rawDensity tail H v n h)≤_
  rw [visible_fresh_flags (q:=n) h hd H tail.tailKnown z]
  exact (visible_mixture_distance T n _ _
    (flag_packed_norm h hd H tail.tailKnown tail.tailKnown_isometry z hz n)
    (raw_packed_norm h hd H tail.tailKnown tail.tailKnown_isometry z hz n)).trans
      (flag_raw_distance h hd H tail.tailKnown tail.tailKnown_isometry z hz n hn)

#print axioms fresh_raw_distance
end
end ICO.C6FreshRawEndpoint
