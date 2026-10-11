import ICO.C6FreshRawEndpoint
import ICO.C6PhysicalCosts
import ICO.C6WeightedHistoryOutput

/-! The exact physical triangle and safe paper constants. The raw pair
comparison is an explicitly exposed intermediate premise in this module;
the final theorem substitutes the literal cache identification for it. -/
namespace ICO.C6PhysicalPairCost
open QIT Matrix ICO.C6FreshRawEndpoint ICO.C6PhysicalFresh ICO.C6PhysicalCosts
  ICO.C6SharedEndpoint ICO.C6Bounds ICO.C6UniformBounds
  ICO.C6WeightedHistoryOutput ICO.SequentialIsometry
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A M O : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

theorem haar_pair_of_raw_bound {q T : ℕ}
    (tail : Protocol (A×Bool) ((A×Bool)×M) O q)
    (H₀ H₁ : Matrix.unitaryGroup A ℂ) (v : (A×Bool)×M→ℂ)
    (hv : ‖WithLp.toLp 2 v‖=1) (n : ℕ)
    (hT : 2*Fintype.card (A×A)≤T) (h : 2*n+1≤T)
    (hsmall : 4*n≤Fintype.card A) (R : ℝ) (hR : 1≤R)
    (hd : (Fintype.card A:ℝ)=R^8)
    (hraw : normalizedTraceDistance (rawDensity tail H₀ v n h) (rawDensity tail H₁ v n h)≤
      uniformCacheError n (Fintype.card A)+(n:ℝ)*((n-1:ℕ):ℝ)/(2*(Fintype.card A:ℝ))) :
    normalizedTraceDistance (haarDensity tail H₀ v n) (haarDensity tail H₁ v n)≤
      uniformError n (Fintype.card A) (Real.sqrt R) := by
  have hnd : 2*n<Fintype.card A := by have hp:=Fintype.card_pos (α:=A); omega
  have h₀:=shared_haar_fresh tail H₀ v hv n hT h hsmall R hR hd
  have h₁:=shared_haar_fresh tail H₁ v hv n hT h hsmall R hR hd
  have hr₀:=fresh_raw_distance tail H₀ v hv.le n h hnd
  have hr₁:=fresh_raw_distance tail H₁ v hv.le n h hnd
  rw [deletionCost_sum,freshCost_sum,delta_creatorError] at h₀ h₁
  simp only [Nat.cast_mul,Nat.cast_ofNat] at h₀ h₁
  rw [sum_deficit_cost] at hr₀ hr₁
  have ht₀:=normalizedTraceDistance_triangle (haarDensity tail H₀ v n)
    (freshDensity tail H₀ v n h) (rawDensity tail H₀ v n h)
  have ht₁:=normalizedTraceDistance_triangle (haarDensity tail H₁ v n)
    (freshDensity tail H₁ v n h) (rawDensity tail H₁ v n h)
  have ht₂:=normalizedTraceDistance_triangle (haarDensity tail H₀ v n)
    (rawDensity tail H₀ v n h) (haarDensity tail H₁ v n)
  have ht₃:=normalizedTraceDistance_triangle (rawDensity tail H₀ v n h)
    (rawDensity tail H₁ v n h) (haarDensity tail H₁ v n)
  rw [normalizedTraceDistance_comm (rawDensity tail H₁ v n h)] at ht₃
  rw [uniformError_formula,Real.sq_sqrt (by linarith : (0:ℝ)≤R)]
  have hn : 0≤(n:ℝ)*((n-1:ℕ):ℝ)/(2*(Fintype.card A:ℝ)) := by positivity
  have he : 2*(n:ℝ)*((n-1:ℕ):ℝ)/(Fintype.card A:ℝ)=
      4*((n:ℝ)*((n-1:ℕ):ℝ)/(2*(Fintype.card A:ℝ))) := by ring
  rw [he]
  ring_nf at h₀ h₁ hr₀ hr₁ hraw hn ⊢
  linarith

#print axioms haar_pair_of_raw_bound
end
end ICO.C6PhysicalPairCost
