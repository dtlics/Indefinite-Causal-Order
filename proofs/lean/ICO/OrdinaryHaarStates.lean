import ICO.OrdinaryHaarIndistinguishability
import ICO.BudgetPreparation
import ICO.QuantumDecision

/-! The paper's adaptive fixed-basis transcript theorem, including arbitrary
mixed input states and the literal fractional-power dimension bound. -/
namespace ICO.OrdinaryHaarStates
open Matrix QIT MeasureTheory ICO.BudgetQueryTree ICO.BudgetHaarBound
open scoped Matrix.Norms.L2Operator
noncomputable section
variable {A M B O : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Nonempty M]
  [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O] [Nonempty O]

theorem mixed_circuit_haar_bound {q : ℕ}
    (tree : Tree (A×M) O (q+1) B) (ρ : State B)
    (hqd : 2*(q+1)<Fintype.card A) (r : ℝ) (hr : 1≤r)
    (hd : (Fintype.card A:ℝ)=r^16) :
    normalizedTraceDistance
      (∫U,(ludersCircuit tree U).map ρ.matrix ∂unitaryHaarMeasure (a:=A))
      ((depolarizingCircuit tree).map ρ.matrix)≤
        ICO.TestingBounds.distanceBound (q+1:ℕ) (Fintype.card A) r := by
  have hh := ICO.OrdinaryHaarIndistinguishability.circuit_haar_bound
    (Classical.arbitrary A) (Classical.arbitrary M) (Classical.arbitrary O)
    (ICO.BudgetPreparation.prepare tree ρ) (fun _ : PUnit => (1:ℂ))
    ICO.BudgetPreparation.initial_norm ICO.BudgetPreparation.initial_mass hqd r hr hd
  simpa only [ludersCircuit,depolarizingCircuit,ICO.BudgetPreparation.prepare_output] using hh

theorem adaptive_haar_distance {q : ℕ}
    (tree : Tree (A×M) O q B) (ρ : State B)
    (hq : 1≤q) (hqd : 2*q<Fintype.card A) :
    normalizedTraceDistance
      (∫U,(ludersCircuit tree U).map ρ.matrix ∂unitaryHaarMeasure (a:=A))
      ((depolarizingCircuit tree).map ρ.matrix)≤
      18*(2*(q:ℝ))*(2*(q:ℝ)+1)/(Fintype.card A:ℝ)^(1/8:ℝ)+
        4*(q:ℝ)/Real.sqrt ((Fintype.card A:ℝ)-2*(q:ℝ))+
        (q:ℝ)^2/(Fintype.card A:ℝ) := by
  let r := (Fintype.card A:ℝ)^(1/16:ℝ)
  have hd0 : 0≤(Fintype.card A:ℝ) := Nat.cast_nonneg _
  have hr : 1≤r := Real.one_le_rpow (by exact_mod_cast Fintype.card_pos (α:=A))
    (by norm_num : (0:ℝ)≤1/16)
  have hd : (Fintype.card A:ℝ)=r^16 :=
    (ICO.QuantumDecision.radius_power_sixteen _ hd0).symm
  have hr2 : r^2=(Fintype.card A:ℝ)^(1/8:ℝ) := by
    dsimp only [r]
    rw [←Real.rpow_two,←Real.rpow_mul hd0]
    norm_num
  cases q with
  | zero => omega
  | succ q =>
    have hh := mixed_circuit_haar_bound tree ρ hqd r hr hd
    simpa only [ICO.TestingBounds.distanceBound,hr2] using hh

#print axioms mixed_circuit_haar_bound
#print axioms adaptive_haar_distance
end
end ICO.OrdinaryHaarStates
