import ICO.C4GeneralAccuracy
import ICO.ChoiDiamond

/-! Actual half-diamond lower bounds for universal plus-control switch simulation. -/
namespace ICO.C4PhysicalEnsemble
open Matrix QIT ICO.ChoiWitnessState ICO.SwitchChoiWitness
noncomputable section
variable {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Nonempty M]

def switchChannel {r : ℕ} (UV : Sample A r) : Channel A (A × Bool) :=
  mixtureSwitchChannel (Nat.zero_lt_succ r) (Nat.zero_lt_succ r) UV.1 UV.2

def circuitChannel {q r : ℕ} (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A)
    (UV : Sample A r) : Channel A (A × Bool) :=
  ICO.SamplingOrdinary.ordinaryChannel tree (ICO.AtMostFamilyCoherence.familyChannels UV.1 UV.2)

theorem choi_error_le_diamond {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) (UV : Sample A r) :
    (switchTarget UV).normalizedTraceDistance (ordinary tree UV) ≤
      (switchChannel UV).diamondTraceDistance (circuitChannel tree UV) :=
  normalizedChoi_distance_le_diamond _ _

theorem exists_switch_diamond_error_bound {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) :
    ∃ UV : Sample A r,
      1/2 - 13 * (((r+1)*(r+1) : ℕ) : ℝ) / (3*Fintype.card A) -
          (q : ℝ)*(q-1)/(2*(r+1)) ≤
        (switchChannel UV).diamondTraceDistance (circuitChannel tree UV) := by
  obtain ⟨UV,hUV⟩ := exists_switch_error_bound (r := r) tree
  exact ⟨UV, hUV.trans (choi_error_le_diamond tree UV)⟩

theorem diamond_fixed_accuracy_constant (ε : ℝ) (hε : ε < 1/2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
        [Fintype M] [DecidableEq M] [Nonempty M] {q : ℕ}
        (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A),
        C ≤ Fintype.card A →
        (∀ r (UV : Sample A r),
          (switchChannel UV).diamondTraceDistance (circuitChannel tree UV) ≤ ε) →
        (Fintype.card A : ℝ) < C*(q : ℝ)^4 := by
  obtain ⟨C,hC,h⟩ := exists_fixed_accuracy_constant ε hε
  refine ⟨C,hC,?_⟩
  intro A M _ _ _ _ _ _ q tree hdim hacc
  apply h tree hdim
  intro r UV
  exact (choi_error_le_diamond tree UV).trans (hacc r UV)

#print axioms exists_switch_diamond_error_bound
#print axioms diamond_fixed_accuracy_constant
end
end ICO.C4PhysicalEnsemble
