import ICO.C6RawDecoded
import ICO.C6FreshRawEndpoint
import ICO.C6WeightedHistoryOutput
import ICO.C6RawDecodedVisible
import ICO.C6DecodedWeighted

namespace ICO.C6RawWeightedEndpoint
open QIT Matrix ICO.C6RawDecoded ICO.C6ModeFockVacuum ICO.C6RawFlagSlices
  ICO.C6FreshRawEndpoint ICO.C6WeightedHistoryOutput ICO.C6CacheVisibleOutput
  ICO.C6SharedEndpoint ICO.C6SharedStages ICO.C6SharedSchedule
  ICO.C6PairedTrajectory ICO.C6CacheDecode ICO.SequentialIsometry
  ICO.RecordingCopyIdentity ICO.RecordingPureCorrespondence
open scoped Matrix BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 2048
set_option Elab.async false
variable {A M O:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

def physicalInput {q:ℕ} (tail:Protocol (A×Bool) ((A×Bool)×M) O q)
    (v:(A×Bool)×M→ℂ) : A×Public (A:=A) tail.tailMemory 0→ℂ :=
  ICO.C6SharedEndpoint.initial tail v ∘ (regroup (Memory (A:=A) tail.tailMemory 0 0)).symm

def cacheInput {q:ℕ} (tail:Protocol (A×Bool) ((A×Bool)×M) O q)
    (v:(A×Bool)×M→ℂ) : CMatrix (Cache (A:=A) (M:=Bool×tail.tailMemory 0) 0) :=
  rankOneMatrix (basisEmbedding vacuumCache*ᵥsmallInput (physicalInput tail v))

def cacheDensity {q:ℕ} (tail:Protocol (A×Bool) ((A×Bool)×M) O q)
    (H:Matrix.unitaryGroup A ℂ) (v:(A×Bool)×M→ℂ) (n:ℕ)
    (hpos:0<n) (hQ:n<Fintype.card A) : CMatrix ((A×Bool)×tail.tailMemory n) :=
  ICO.C6WeightedHistoryOutput.density n hpos hQ H
    (fun i=>smallKnown (tail.tailKnown i)) (cacheInput tail v) n (output n).map

theorem rawDensity_weighted {q T:ℕ} (tail:Protocol (A×Bool) ((A×Bool)×M) O q)
    (H:Matrix.unitaryGroup A ℂ) (v:(A×Bool)×M→ℂ) (n:ℕ)
    (hpos:0<n) (hQ:n<Fintype.card A) (h:2*n+1≤T) (ht:2*n<Fintype.card A) :
    rawDensity tail H v n h=cacheDensity tail H v n hpos hQ := by
  have he:partialTraceB (rankOneMatrix (decodedInitial (physicalInput tail v)))=cacheInput tail v :=
    vacuumInput_erasure _
  have hw:=ICO.C6DecodedWeighted.visible_erasure n hpos hQ H tail.tailKnown
    (decodedInitial (physicalInput tail v)) n le_rfl
  rw [he] at hw
  have hr:=ICO.C6RawDecodedVisible.raw_visible_sum h ht H tail.tailKnown
    (physicalInput tail v) n le_rfl
  exact hr.trans hw.symm

#print axioms rawDensity_weighted

end
end ICO.C6RawWeightedEndpoint
