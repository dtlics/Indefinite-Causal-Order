import ICO.C4Scaling
import ICO.SwitchChoiWitness

/-! The C4 theorem stated entirely for physical finite-Kraus switch channels. -/

namespace ICO.C4PhysicalEnsemble
open Matrix QIT ICO.ChoiWitnessState ICO.SwitchChoiWitness
noncomputable section
variable {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Nonempty M]

def switchTarget {r : ℕ} (UV : Sample A r) : State ((A × A) × Bool) :=
  normalizedChoiState (mixtureSwitchChannel (Nat.zero_lt_succ r) (Nat.zero_lt_succ r) UV.1 UV.2)

theorem switchTarget_eq_ideal {r : ℕ} (UV : Sample A r) : switchTarget UV = ideal UV :=
  normalizedChoi_eq_ideal UV.1 UV.2

/-- Every finite adaptive ordinary circuit of total call budget `q` has a
mixed-unitary instance on which its physical Choi-state error has this bound. -/
theorem exists_switch_error_bound {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) :
    ∃ UV : Sample A r,
      1/2 - 13 * (((r+1)*(r+1) : ℕ) : ℝ) / (3*Fintype.card A) -
          (q : ℝ)*(q-1)/(2*(r+1)) ≤ (switchTarget UV).normalizedTraceDistance (ordinary tree UV) := by
  simpa only [switchTarget_eq_ideal] using exists_distance_bound (r := r) tree

/-- A universal simulator with physical normalized Choi error at most `1/48`
requires `q > d^(1/4)/8` whenever `d ≥ 64`. -/
theorem switch_query_fourth_power_lower_bound {q : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A)
    (hdim : 64 ≤ Fintype.card A)
    (haccurate : ∀ r (UV : Sample A r),
      (switchTarget UV).normalizedTraceDistance (ordinary tree UV) ≤ 1/48) :
    (Fintype.card A : ℝ) < 4096 * (q : ℝ)^4 := by
  apply query_fourth_power_lower_bound tree hdim
  simpa only [switchTarget_eq_ideal] using haccurate

#print axioms exists_switch_error_bound
#print axioms switch_query_fourth_power_lower_bound
end
end ICO.C4PhysicalEnsemble
