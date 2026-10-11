import ICO.BudgetTestingThreshold
import ICO.OrdinaryHaarIndistinguishability
import ICO.LudersLowWitness

/-! Unconditional ordinary-query lower bounds. The inputs, adaptive channels,
output measurement, and Haar comparison are actual quantum objects. -/
namespace ICO.C5Decision
open Matrix QIT MeasureTheory ICO.BudgetQueryTree ICO.BudgetContinuity ICO.BudgetTesting
  ICO.BudgetTestingThreshold ICO.TestingBounds
noncomputable section
set_option maxHeartbeats 2400000
variable {A M O B : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype O] [DecidableEq O] [Nonempty O]
  [Fintype B] [DecidableEq B]

theorem actual_singleHaarBound {q : ℕ} (ρ : State B) (r : ℝ)
    (hq : 1≤q) (hqr : (q:ℝ)≤r/100) (hd : (Fintype.card A:ℝ)=r^16) :
    SingleHaarBound (A:=A) (M:=M) (O:=O) q ρ
      (distanceBound q (Fintype.card A) r) := by
  have hqR : (1:ℝ)≤q := by exact_mod_cast hq
  have hr := radius_ge_hundred hqR hqr
  have hd2 : 2*r^2≤(Fintype.card A:ℝ) := by
    rw [hd]
    exact pow_sixteen_ge_two_sq (by linarith)
  have hden := threshold_denominators hqR hqr hd2
  have hqd : 2*q<Fintype.card A := by exact_mod_cast hden.2.2.1
  apply singleHaarBound_of_prepared
  intro tree
  cases q with
  | zero => omega
  | succ q =>
    exact ICO.OrdinaryHaarIndistinguishability.circuit_haar_bound
      (Classical.arbitrary A) (Classical.arbitrary M) (Classical.arbitrary O) tree
      (fun _ : PUnit => 1) ICO.BudgetPreparation.initial_norm ICO.BudgetPreparation.initial_mass
      hqd r (by linarith) hd

/-- Any adaptive ordinary algorithm deciding the same-hidden-basis versus
depolarizing witnesses needs more than `d^(1/16)/100` total oracle calls.
The arbitrary mixed input is prepared within the known part of the tree. -/
theorem main_lower_bound {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B)
    (hhigh : ∀U,(2/3:ℝ)≤acceptance T tree ρ (hidden U) (hidden U))
    (hlow : acceptance T tree ρ ICO.RecordingDepolarizing.withMemory
      ICO.RecordingDepolarizing.withMemory≤1/3) :
    (Fintype.card A:ℝ)^(1/16:ℝ)/100<(q:ℝ) := by
  by_contra hn
  have hqr := le_of_not_gt hn
  by_cases hq : q=0
  · subst q
    exact zero_query_main T tree ρ hhigh hlow
  · have hd := (ICO.QuantumDecision.radius_power_sixteen (Fintype.card A)
      (Nat.cast_nonneg _)).symm
    exact main_threshold T tree ρ _ (by omega) hqr hd
      (actual_singleHaarBound ρ _ (by omega) hqr hd) hhigh hlow

/-- The same lower bound holds when both boxes must be nonselective rank-one
measurements. A genuine opposing-promise pair handles the zero-query case. -/
theorem measurement_only_lower_bound {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B) (hdim : 4≤Fintype.card A)
    (hhigh : ∀U,(2/3:ℝ)≤acceptance T tree ρ (hidden U) (hidden U))
    (hlow : ∀U V : Matrix.unitaryGroup A ℂ, ICO.SwitchObservable.interference
      (ICO.SwitchObservable.basisProjection (U:CMatrix A))
      (ICO.SwitchObservable.basisProjection (V:CMatrix A))≤1/3 →
        acceptance T tree ρ (hidden U) (hidden V)≤1/3) :
    (Fintype.card A:ℝ)^(1/16:ℝ)/100<(q:ℝ) := by
  by_contra hn
  have hqr := le_of_not_gt hn
  by_cases hq : q=0
  · subst q
    exact zero_query_measurement_of_low_pair T tree ρ
      (ICO.LudersLowWitness.low_pair hdim) hhigh hlow
  · have hd := (ICO.QuantumDecision.radius_power_sixteen (Fintype.card A)
      (Nat.cast_nonneg _)).symm
    exact measurement_only_threshold T tree ρ _ (by omega) hqr hd
      (actual_singleHaarBound ρ _ (by omega) hqr hd) hhigh hlow

#print axioms main_lower_bound
#print axioms measurement_only_lower_bound
#print axioms actual_singleHaarBound
end
end ICO.C5Decision
