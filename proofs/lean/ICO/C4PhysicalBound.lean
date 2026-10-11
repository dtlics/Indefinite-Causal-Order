import ICO.C4PhysicalEnsemble

/-! The averaged physical witness gives a worst-case adaptive simulation lower bound. -/

namespace ICO.C4PhysicalEnsemble
open Matrix QIT MeasureTheory ICO.HaarFamily ICO.CompositionGram ICO.ReverseCompositionGram
open ICO.CompositionGramAverage ICO.GramWitness ICO.CoupledChoi ICO.ChoiWitnessState
open ICO.AtMostFamilyCoherence ICO.TreeCoherence ICO.AverageCoherence
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1000000
variable {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Nonempty M]

def switchSampleColumns {r : ℕ} (UV : Sample A r) :=
  switchColumns (columns UV.1 UV.2) (reverseColumns UV.1 UV.2)

theorem switchSample_diagonal {r : ℕ} (UV : Sample A r) (ij : Fin (r+1) × Fin (r+1)) :
    gram (switchSampleColumns UV) ij ij = 1 :=
  switch_gram_diag_one _ _ (gram_diagonal UV.1 UV.2) (reverse_gram_diagonal UV.1 UV.2) ij

def ideal {r : ℕ} (UV : Sample A r) : State ((A × A) × Bool) :=
  idealState (switchSampleColumns UV) (switchSample_diagonal UV)

theorem switchSample_continuous {r : ℕ} : Continuous (switchSampleColumns (A := A) (r := r)) :=
  switchColumns_continuous _ _ columns_continuous reverseColumns_continuous

theorem gramX_integrable (r : ℕ) :
    Integrable (fun UV : Sample A r => ‖gram (columns UV.1 UV.2) - 1‖)
      (ensembleMeasure (A := A) r r) :=
  (gram_continuous.sub continuous_const).norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem gramY_integrable (r : ℕ) :
    Integrable (fun UV : Sample A r => ‖gram (reverseColumns UV.1 UV.2) - 1‖)
      (ensembleMeasure (A := A) r r) :=
  (reverse_gram_continuous.sub continuous_const).norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem gramZ_integrable (r : ℕ) :
    Integrable (fun UV : Sample A r => ‖gram (switchSampleColumns UV) - 1‖)
      (ensembleMeasure (A := A) r r) := by
  have hZ := switchSample_continuous (A := A) (r := r)
  have hG : Continuous (fun UV : Sample A r => gram (switchSampleColumns UV)) :=
    hZ.matrix_conjTranspose.matrix_mul hZ
  exact (hG.sub continuous_const).norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem gramZ_mean_bound (r : ℕ) :
    (∫ UV : Sample A r, ‖gram (switchSampleColumns UV) - 1‖ ∂ensembleMeasure (A := A) r r) ≤
      (((r+1)*(r+1) : ℕ) : ℝ) / Fintype.card A := by
  have hx := gramX_integrable (A := A) r
  have hy := gramY_integrable (A := A) r
  have hh := integral_mono (gramZ_integrable (A := A) r)
    ((hx.const_mul (1/2 : ℝ)).add (hy.const_mul (1/2 : ℝ)))
    (fun UV => switch_gram_defect_le (columns UV.1 UV.2) (reverseColumns UV.1 UV.2))
  simp only [Pi.add_apply] at hh
  rw [integral_add (hx.const_mul _) (hy.const_mul _), integral_const_mul, integral_const_mul] at hh
  have hX := defect_norm_average_le (A := A) r r
  have hY := reverse_defect_norm_average_le (A := A) r r
  linarith

theorem exists_distance_precise {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) (hq : q ≤ r+1) :
    ∃ UV : Sample A r,
      1/2 - 2 * ((((r+1)*(r+1) : ℕ) : ℝ) / Fintype.card A) -
        (((r+1)*(r+1) : ℕ) : ℝ) * reverseFactor (A := A) -
          (q : ℝ)*(q-1)/(2*(r+1)) ≤ (ideal UV).normalizedTraceDistance (ordinary tree UV) := by
  let X := fun UV : Sample A r => columns UV.1 UV.2
  let Y := fun UV : Sample A r => reverseColumns UV.1 UV.2
  have hZ : Continuous (fun UV : Sample A r => switchColumns (X UV) (Y UV)) := switchSample_continuous
  have hOrd := (witness_acceptance_continuous _ _ hZ (ordinary_matrix_continuous tree)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := ensembleMeasure (A := A) r r)
  have hFresh := (witness_acceptance_continuous _ _ hZ (fresh_matrix_continuous tree hq)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := ensembleMeasure (A := A) r r)
  have hIdeal := (witness_acceptance_continuous _ _ hZ
    (ideal_matrix_continuous _ hZ switchSample_diagonal)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ := ensembleMeasure (A := A) r r)
  obtain ⟨UV, hUV⟩ := exists_distance_from_gram_estimates X Y (ordinary tree) (fresh tree hq)
    switchSample_diagonal (gramX_integrable r) (gramY_integrable r) (gramZ_integrable r)
    (cross_integrable tree hq) hOrd hFresh hIdeal
    ((((r+1)*(r+1) : ℕ) : ℝ) / Fintype.card A)
    ((((r+1)*(r+1) : ℕ) : ℝ) / Fintype.card A)
    ((((r+1)*(r+1) : ℕ) : ℝ) / Fintype.card A)
    ((((r+1)*(r+1) : ℕ) : ℝ) * reverseFactor (A := A))
    ((q : ℝ)*(q-1)/(2*(r+1)))
    (defect_norm_average_le r r) (reverse_defect_norm_average_le r r) (gramZ_mean_bound r)
    (cross_mean_bound tree hq) (ordinary_fresh_coupling tree hq)
  refine ⟨UV, ?_⟩
  change _ ≤ (ideal UV).normalizedTraceDistance (ordinary tree UV) at hUV
  linarith

theorem reverseFactor_le : reverseFactor (A := A) ≤ 7 / (3 * Fintype.card A) := by
  have hd : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.one_lt_card (α := A)
  have hpos : (0 : ℝ) < Fintype.card A := by linarith
  have hden : (0 : ℝ) < (Fintype.card A : ℝ)^2-1 := by nlinarith
  have h : (Fintype.card A : ℝ) / ((Fintype.card A : ℝ)^2-1) ≤ 4/(3*Fintype.card A) := by
    apply (div_le_div_iff₀ hden (by positivity)).2
    nlinarith
  calc
    _ ≤ (Fintype.card A : ℝ)⁻¹ + 4/(3*Fintype.card A) := by
      simpa only [reverseFactor, add_comm] using add_le_add_left h ((Fintype.card A : ℝ)⁻¹)
    _ = _ := by field_simp; ring

theorem exists_distance_bound_of_budget {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) (hq : q ≤ r+1) :
    ∃ UV : Sample A r,
      1/2 - 13 * (((r+1)*(r+1) : ℕ) : ℝ) / (3*Fintype.card A) -
          (q : ℝ)*(q-1)/(2*(r+1)) ≤ (ideal UV).normalizedTraceDistance (ordinary tree UV) := by
  obtain ⟨UV, hUV⟩ := exists_distance_precise tree hq
  refine ⟨UV, le_trans ?_ hUV⟩
  have h := mul_le_mul_of_nonneg_left (reverseFactor_le (A := A))
    (show (0 : ℝ) ≤ (((r+1)*(r+1) : ℕ) : ℝ) by positivity)
  have hd : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (13 : ℝ)*(((r+1)*(r+1) : ℕ) : ℝ)/(3*Fintype.card A) =
      2*((((r+1)*(r+1) : ℕ) : ℝ)/Fintype.card A) +
        (((r+1)*(r+1) : ℕ) : ℝ)*(7/(3*Fintype.card A)) := by ring
  rw [he]
  linarith

theorem exists_distance_bound {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) :
    ∃ UV : Sample A r,
      1/2 - 13 * (((r+1)*(r+1) : ℕ) : ℝ) / (3*Fintype.card A) -
          (q : ℝ)*(q-1)/(2*(r+1)) ≤ (ideal UV).normalizedTraceDistance (ordinary tree UV) := by
  by_cases hq : q ≤ r+1
  · exact exists_distance_bound_of_budget tree hq
  · let UV : Sample A r := (fun _ => 1, fun _ => 1)
    refine ⟨UV, le_trans ?_ (State.normalizedTraceDistance_nonneg _ _)⟩
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
    have hqn : (r : ℝ)+1 ≤ (q : ℝ)-1 := by
      have hh : r+2 ≤ q := by omega
      have hh' : (r : ℝ)+2 ≤ q := by exact_mod_cast hh
      linarith
    have hpos : (0 : ℝ) < 2*((r : ℝ)+1) := by positivity
    have hη : (1 : ℝ) ≤ (q : ℝ)*(q-1)/(2*(r+1)) := by
      apply (le_div_iff₀ hpos).2
      nlinarith
    have hG : (0 : ℝ) ≤ 13 * (((r+1)*(r+1) : ℕ) : ℝ) / (3*Fintype.card A) := by positivity
    linarith

#print axioms exists_distance_bound_of_budget
#print axioms exists_distance_bound
end
end ICO.C4PhysicalEnsemble
