import ICO.FullSwitchChannel
import ICO.BudgetPreparation
import ICO.DiamondPreprocessing

/-! Full-control switch simulation: physical total-query half-diamond bound. -/
namespace ICO.C4PhysicalEnsemble
open Matrix QIT ICO.FullSwitchChannel ICO.BudgetQueryTree
noncomputable section
variable {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Nonempty M]

def fullSwitch {r : ℕ} (UV : Sample A r) : Channel (A × Bool) (A × Bool) :=
  fullChannel (Nat.zero_lt_succ r) (Nat.zero_lt_succ r) UV.1 UV.2

def fullCircuit {q r : ℕ} (tree : Tree (A × M) (A × Bool) q (A × Bool))
    (UV : Sample A r) : Channel (A × Bool) (A × Bool) :=
  ICO.SamplingOrdinary.ordinaryChannel tree (ICO.AtMostFamilyCoherence.familyChannels UV.1 UV.2)

def prepared {q : ℕ} (tree : Tree (A × M) (A × Bool) q (A × Bool)) :
    Tree (A × M) (A × Bool) q A := tree.prepare plusMatrix plus_isometry

theorem fullSwitch_prepared {r : ℕ} (UV : Sample A r) :
    (fullSwitch UV).comp plusChannel = switchChannel UV :=
  channel_eq_of_map_eq (full_plus_map _ _ UV.1 UV.2)

theorem fullCircuit_prepared {q r : ℕ} (tree : Tree (A × M) (A × Bool) q (A × Bool))
    (UV : Sample A r) :
    (fullCircuit tree UV).comp plusChannel = circuitChannel (prepared tree) UV := by
  symm
  exact tree.prepare_channel plusMatrix plus_isometry _ _

theorem prepared_diamond_le {q r : ℕ} (tree : Tree (A × M) (A × Bool) q (A × Bool))
    (UV : Sample A r) :
    (switchChannel UV).diamondTraceDistance (circuitChannel (prepared tree) UV) ≤
      (fullSwitch UV).diamondTraceDistance (fullCircuit tree UV) := by
  rw [← fullSwitch_prepared UV, ← fullCircuit_prepared tree UV]
  exact ICO.DiamondPreprocessing.diamond_precompose_of_embedding _ _ _
    ⟨fun a => (a,false), fun _ _ h => congrArg Prod.fst h⟩

/-- The tradeoff for the standard switch on arbitrary input control states.
The circuit has one total budget for both oracle types and may stop early. -/
theorem exists_full_switch_error_bound {q r : ℕ}
    (tree : Tree (A × M) (A × Bool) q (A × Bool)) :
    ∃ UV : Sample A r,
      1/2 - 13 * (((r+1)*(r+1) : ℕ) : ℝ) / (3*Fintype.card A) -
          (q : ℝ)*(q-1)/(2*(r+1)) ≤
        (fullSwitch UV).diamondTraceDistance (fullCircuit tree UV) := by
  obtain ⟨UV,hUV⟩ := exists_switch_diamond_error_bound (r := r) (prepared tree)
  exact ⟨UV,hUV.trans (prepared_diamond_le tree UV)⟩

/-- Every fixed error below one half requires order `d^(1/4)` total queries,
with a constant depending only on the fixed error. -/
theorem full_switch_fixed_accuracy_constant (ε : ℝ) (hε : ε < 1/2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
        [Fintype M] [DecidableEq M] [Nonempty M] {q : ℕ}
        (tree : Tree (A × M) (A × Bool) q (A × Bool)),
        C ≤ Fintype.card A →
        (∀ r (UV : Sample A r),
          (fullSwitch UV).diamondTraceDistance (fullCircuit tree UV) ≤ ε) →
        (Fintype.card A : ℝ) < C*(q : ℝ)^4 := by
  obtain ⟨C,hC,h⟩ := diamond_fixed_accuracy_constant ε hε
  refine ⟨C,hC,?_⟩
  intro A M _ _ _ _ _ _ q tree hdim hacc
  apply h (prepared tree) hdim
  intro r UV
  exact (prepared_diamond_le tree UV).trans (hacc r UV)

/-- The explicit constant specialization used in the paper. -/
theorem full_switch_one_over_48 {q : ℕ}
    (tree : Tree (A × M) (A × Bool) q (A × Bool))
    (hdim : 64 ≤ Fintype.card A)
    (haccurate : ∀ r (UV : Sample A r),
      (fullSwitch UV).diamondTraceDistance (fullCircuit tree UV) ≤ 1/48) :
    (Fintype.card A : ℝ) < 4096*(q : ℝ)^4 := by
  apply switch_query_fourth_power_lower_bound (prepared tree) hdim
  intro r UV
  exact (choi_error_le_diamond (prepared tree) UV).trans
    ((prepared_diamond_le tree UV).trans (haccurate r UV))

#print axioms exists_full_switch_error_bound
#print axioms full_switch_fixed_accuracy_constant
#print axioms full_switch_one_over_48
end
end ICO.C4PhysicalEnsemble
