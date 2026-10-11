import ICO.C6PhysicalFresh
import ICO.C6Bounds

/-! Exact identification of physical trajectory costs with the paper's
finite sums; there is no asymptotic estimate in these identities. -/
namespace ICO.C6PhysicalCosts
open ICO.C6HistoryControlled ICO.C6PairedHybrid ICO.C6Bounds ICO.C6BosonicLocalInverse
  ICO.C6FockCompressionSharp
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 900000
set_option Elab.async false

theorem deletionCost_sum (q d:ℕ) :
    (∑i∈Finset.range q,deletionCost d i)=forwardError q d := by
  simpa only [forwardError,deletionCost] using
    (Fin.sum_univ_eq_sum_range (fun i:ℕ=>deletionCost d i) q).symm

theorem freshCost_formula (d i:ℕ) : freshCost d i=
    if i=0 then 0 else Real.sqrt ((2*(i:ℝ)-1)/((d:ℝ)-i+1))+
      Real.sqrt (2*(i:ℝ)/((d:ℝ)-i)) := by
  cases i with
  | zero=>simp [freshCost]
  | succ i=>
    simp only [freshCost,compressionBound,Nat.cast_add,Nat.cast_one,Nat.succ_ne_zero,if_false]
    congr 2 <;> ring

theorem freshCost_sum (q d:ℕ) :
    (∑i∈Finset.range q,freshCost d i)=birthError q d := by
  rw [←Fin.sum_univ_eq_sum_range (fun i:ℕ=>freshCost d i) q]
  unfold birthError
  apply Finset.sum_congr rfl
  intro i hi
  exact freshCost_formula d i

theorem delta_creatorError (t d:ℕ) :
    ICO.C6PolarFockBounds.delta t d=creatorError t d := rfl

#print axioms freshCost_sum
end
end ICO.C6PhysicalCosts
