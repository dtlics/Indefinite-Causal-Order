import ICO.C6CacheInputFacts
import ICO.C6PhysicalPairCost

namespace ICO.C6SharedPairBound
open QIT Matrix ICO.C6RawWeightedEndpoint ICO.C6RawDecoded
  ICO.C6ModeFockVacuum ICO.C6RawFlagSlices ICO.C6SharedEndpoint
  ICO.C6PairedTrajectory ICO.C6CacheDecode ICO.SequentialIsometry
  ICO.C6WeightedHistoryOutput ICO.C6CacheVisibleOutput ICO.C6UniformBounds
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 2048
set_option Elab.async false
variable {A M O : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

theorem raw_pair {q T : ℕ}
    (tail : Protocol (A×Bool) ((A×Bool)×M) O q)
    (H₀ H₁ : Matrix.unitaryGroup A ℂ) (v : (A×Bool)×M→ℂ) (n : ℕ)
    (hv : ‖WithLp.toLp 2 v‖=1) (hn : 0<n)
    (h : 2*n+1≤T) (ht : 2*n<Fintype.card A) :
    normalizedTraceDistance (ICO.C6FreshRawEndpoint.rawDensity tail H₀ v n h)
      (ICO.C6FreshRawEndpoint.rawDensity tail H₁ v n h)≤
      uniformCacheError n (Fintype.card A)+
        (n:ℝ)*((n-1:ℕ):ℝ)/(2*(Fintype.card A:ℝ)) := by
  have hQ : n<Fintype.card A := by omega
  rw [rawDensity_weighted tail H₀ v n hn hQ h ht,
    rawDensity_weighted tail H₁ v n hn hQ h ht]
  exact unit_mass_pair_distance n hn hQ H₀ H₁
    (fun i=>smallKnown (tail.tailKnown i))
    (fun i=>smallKnown_isometry i _ (tail.tailKnown_isometry i))
    (cacheInput tail v) (cacheInput_pos tail v) (cacheInput_trace tail v hv)
    (output n).map (output n).traceNonincreasingCP_map

theorem shared_haar_pair {q : ℕ}
    (tail : Protocol (A×Bool) ((A×Bool)×M) O q)
    (H₀ H₁ : Matrix.unitaryGroup A ℂ) (v : (A×Bool)×M→ℂ) (n : ℕ)
    (hv : ‖WithLp.toLp 2 v‖=1) (hn : 0<n) (hfour : 4*n≤Fintype.card A)
    (R : ℝ) (hR : 1≤R) (hdim : (Fintype.card A:ℝ)=R^8) :
    normalizedTraceDistance (haarDensity tail H₀ v n) (haarDensity tail H₁ v n)≤
      uniformError n (Fintype.card A) (Real.sqrt R) := by
  let T := 2*Fintype.card (A×A)+2*n+1
  have hT : 2*Fintype.card (A×A)≤T := by dsimp [T];omega
  have h : 2*n+1≤T := by dsimp [T];omega
  have ht : 2*n<Fintype.card A := by omega
  exact ICO.C6PhysicalPairCost.haar_pair_of_raw_bound tail H₀ H₁ v hv n
    hT h hfour R hR hdim (raw_pair tail H₀ H₁ v n hv hn h ht)

#print axioms cacheInput_trace
#print axioms raw_pair
#print axioms shared_haar_pair
end
end ICO.C6SharedPairBound
