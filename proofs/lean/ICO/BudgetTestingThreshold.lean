import ICO.BudgetTesting

/-! The explicit sixteenth-root decision threshold, with the single-Haar
comparison exposed until the final physical theorem is substituted. -/
namespace ICO.BudgetTestingThreshold
open Matrix QIT MeasureTheory ICO.BudgetQueryTree ICO.BudgetContinuity ICO.BudgetTesting
noncomputable section
variable {A M O B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
  [Fintype B] [DecidableEq B]

theorem main_threshold {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B) (r : ℝ)
    (hq : 1≤q) (hqr : (q:ℝ)≤r/100) (hd : (Fintype.card A:ℝ)=r^16)
    (h : SingleHaarBound (A:=A) (M:=M) (O:=O) q ρ
      (ICO.TestingBounds.distanceBound q (Fintype.card A) r))
    (hhigh : ∀U,(2/3:ℝ)≤acceptance T tree ρ (hidden U) (hidden U))
    (hlow : acceptance T tree ρ ICO.RecordingDepolarizing.withMemory
      ICO.RecordingDepolarizing.withMemory≤1/3) : False := by
  apply main_testing_impossible T tree ρ _ h hhigh hlow
  rw [hd]
  exact ICO.TestingBounds.distanceBound_pow_sixteen_lt (by exact_mod_cast hq) hqr

theorem measurement_only_threshold [Nontrivial A] {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B) (r : ℝ)
    (hq : 1≤q) (hqr : (q:ℝ)≤r/100) (hd : (Fintype.card A:ℝ)=r^16)
    (h : SingleHaarBound (A:=A) (M:=M) (O:=O) q ρ
      (ICO.TestingBounds.distanceBound q (Fintype.card A) r))
    (hhigh : ∀U,(2/3:ℝ)≤acceptance T tree ρ (hidden U) (hidden U))
    (hlow : ∀U V : Matrix.unitaryGroup A ℂ, ICO.SwitchObservable.interference
      (ICO.SwitchObservable.basisProjection (U:CMatrix A))
      (ICO.SwitchObservable.basisProjection (V:CMatrix A))≤1/3 →
        acceptance T tree ρ (hidden U) (hidden V)≤1/3) : False := by
  apply measurement_only_testing_impossible T tree ρ _ h hhigh hlow
  change ICO.TestingBounds.hiddenOutcomeBound q (Fintype.card A) r<1/3
  rw [hd]
  exact ICO.TestingBounds.hiddenOutcomeBound_pow_sixteen_lt (by exact_mod_cast hq) hqr

theorem zero_query_main (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O 0 B) (ρ : State B)
    (hhigh : ∀U,(2/3:ℝ)≤acceptance T tree ρ (hidden U) (hidden U))
    (hlow : acceptance T tree ρ ICO.RecordingDepolarizing.withMemory
      ICO.RecordingDepolarizing.withMemory≤1/3) : False := by
  apply main_testing_impossible T tree ρ 0 ?_ hhigh hlow (by norm_num)
  intro S
  exact le_of_eq (ICO.BudgetHaarBound.zero_budget_distance S ρ.matrix)

theorem zero_query_measurement_of_low_pair (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O 0 B) (ρ : State B)
    (hpair : ∃U V : Matrix.unitaryGroup A ℂ, ICO.SwitchObservable.interference
      (ICO.SwitchObservable.basisProjection (U:CMatrix A))
      (ICO.SwitchObservable.basisProjection (V:CMatrix A))≤1/3)
    (hhigh : ∀U,(2/3:ℝ)≤acceptance T tree ρ (hidden U) (hidden U))
    (hlow : ∀U V : Matrix.unitaryGroup A ℂ, ICO.SwitchObservable.interference
      (ICO.SwitchObservable.basisProjection (U:CMatrix A))
      (ICO.SwitchObservable.basisProjection (V:CMatrix A))≤1/3 →
        acceptance T tree ρ (hidden U) (hidden V)≤1/3) : False := by
  obtain ⟨U,V,hUV⟩ := hpair
  have he := congrArg (fun f : MatrixMap B O => ICO.BornAverage.acceptCLM T (f ρ.matrix))
    (ICO.BudgetHaarBound.zero_budget_map tree rfl (hidden U) (hidden U) (hidden U) (hidden V))
  change acceptance T tree ρ (hidden U) (hidden U)=acceptance T tree ρ (hidden U) (hidden V) at he
  have hh := hhigh U
  have hl := hlow U V hUV
  linarith

#print axioms main_threshold
#print axioms measurement_only_threshold
end
end ICO.BudgetTestingThreshold
