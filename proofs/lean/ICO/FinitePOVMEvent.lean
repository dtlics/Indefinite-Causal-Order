import QIT.HypothesisTesting.Basic

/-! Classical event postprocessing of an actual finite POVM. -/
namespace ICO.FinitePOVMEvent
open Matrix QIT
open scoped BigOperators ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {R O : Type*} [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O]

def probability (E : POVM R O) (ρ : State O) (S : Finset R) : ℝ :=
  ∑ r ∈ S, (E.prob ρ r : ℝ)

def test (E : POVM R O) (S : Finset R) : BinaryHypothesisTest O where
  effects b := if b then ∑ r ∈ S, E.effects r else ∑ r ∈ Sᶜ, E.effects r
  pos b := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact Matrix.posSemidef_sum _ (fun r _ => E.pos r)
    · exact Matrix.posSemidef_sum _ (fun r _ => E.pos r)
  sum_eq_one := by
    simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    rw [Finset.sum_add_sum_compl, E.sum_eq_one]

theorem test_accept (E : POVM R O) (ρ : State O) (S : Finset R) :
    ((test E S).acceptProb ρ : ℝ) = probability E ρ S := by
  rw [BinaryHypothesisTest.acceptProb_eq_trace_re]
  simp only [BinaryHypothesisTest.acceptRhoEffect, test, ↓reduceIte,
    Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, probability,
    POVM.prob_eq_trace_re]

theorem probability_mono (E : POVM R O) (ρ : State O) {S T : Finset R}
    (h : S ⊆ T) : probability E ρ S ≤ probability E ρ T := by
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun r _ _ => NNReal.coe_nonneg _)

theorem probability_compl (E : POVM R O) (ρ : State O) (S : Finset R) :
    probability E ρ S + probability E ρ Sᶜ = 1 := by
  unfold probability
  rw [Finset.sum_add_sum_compl]
  exact_mod_cast E.sum_prob ρ

theorem accuracy_implies_accept (E : POVM R O) (ρ : State O)
    (S G : Finset R) (hGS : G ⊆ S) (hG : (2/3:ℝ) ≤ probability E ρ G) :
    (2/3:ℝ) ≤ ((test E S).acceptProb ρ : ℝ) := by
  rw [test_accept]
  exact hG.trans (probability_mono E ρ hGS)

theorem accuracy_implies_reject (E : POVM R O) (ρ : State O)
    (S G : Finset R) (hGS : G ⊆ Sᶜ) (hG : (2/3:ℝ) ≤ probability E ρ G) :
    ((test E S).acceptProb ρ : ℝ) ≤ 1/3 := by
  rw [test_accept]
  have hm := probability_mono E ρ hGS
  have ht := probability_compl E ρ S
  linarith

#print axioms test_accept
#print axioms accuracy_implies_reject
end
end ICO.FinitePOVMEvent
