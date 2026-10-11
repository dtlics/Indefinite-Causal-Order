import ICO.C6HistoryVisible
import ICO.C6PhysicalFresh

namespace ICO.C6FreshVisibleEndpoint
open Matrix QIT ICO.C6HistoryVisible ICO.C6PhysicalFresh ICO.C6NativeFresh
  ICO.C6SharedFockSchedule ICO.C6SharedEndpoint ICO.C6SharedQuerySchedule
  ICO.C6SharedSchedule ICO.C6SharedStages ICO.C6PairedTrajectory
  ICO.SequentialIsometry ICO.MHDecompressionErasure ICO.MHFockKnownOperation
  ICO.MHBoundedRecording ICO.RecordingHistory ICO.RecordingPurifiedProtocol
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem cast_visible {M N:Type} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
    (h:M=N) (T:ℕ) (v:InputCutoff (α:=A) T×(Bool×N)→ℂ) :
    (fockVisible T (v ∘ Equiv.cast (congrArg (fun X=>InputCutoff (α:=A) T×(Bool×X)) h))).submatrix
      ((Equiv.cast (congrArg (fun X=>(A×Bool)×X) h)).symm.trans (regroup M))
      ((Equiv.cast (congrArg (fun X=>(A×Bool)×X) h)).symm.trans (regroup M))=
        (fockVisible T v).submatrix (Equiv.prodAssoc A Bool N) (Equiv.prodAssoc A Bool N) := by
  cases h
  rfl

variable {M O:Type} [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

theorem native_visible {q T:ℕ} (tail:Protocol (A×Bool) ((A×Bool)×M) O q) (n:ℕ)
    (v:InputCutoff (α:=A) T×Public (A:=A) tail.tailMemory n→ℂ) :
    (stageErasure tail n).map (fockVisible T
      (v ∘ ICO.C6SharedFockSchedule.endpointEquiv (μ:=tail.tailMemory) T n))=
        ICO.C6HistoryVisible.visible v := by
  rw [stageErasure_apply]
  change eraseHistory.map ((fockVisible T (v ∘ _)).submatrix _ _)=_
  rw [show (fockVisible T (v ∘ ICO.C6SharedFockSchedule.endpointEquiv (μ:=tail.tailMemory) T n)).submatrix
      (ICO.C6SharedEndpoint.endpointEquiv tail n).symm
      (ICO.C6SharedEndpoint.endpointEquiv tail n).symm=
      (fockVisible T v).submatrix
        (Equiv.prodAssoc A Bool (History (A×Bool) n×tail.tailMemory n))
        (Equiv.prodAssoc A Bool (History (A×Bool) n×tail.tailMemory n)) from
    cast_visible (by simpa only [Nat.zero_add] using
      ICO.DoubleQuerySchedule.memory_even_eq (A:=A×Bool) (μ:=tail.tailMemory) 0 n) T v]
  simp only [ICO.C6HistoryVisible.visible,erasePrivate,Channel.comp,
    LinearMap.comp_apply,ICO.C6ReindexChannel.apply]

theorem freshDensity_visible {q T:ℕ} (tail:Protocol (A×Bool) ((A×Bool)×M) O q)
    (H:Matrix.unitaryGroup A ℂ) (v:(A×Bool)×M→ℂ) (n:ℕ) (h:2*n+1≤T) :
    freshDensity tail H v n h=ICO.C6HistoryVisible.visible
      (WithLp.ofLp (freshVector h H tail.tailKnown
        (initial tail v ∘ (regroup (Memory (A:=A) tail.tailMemory 0 0)).symm) n)) := by
  exact native_visible tail n _

#print axioms freshDensity_visible
end
end ICO.C6FreshVisibleEndpoint
