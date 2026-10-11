import ICO.C6SwitchTest
import ICO.C6Bounds
import ICO.BudgetTesting

/-! Actual adaptive decision reductions for the correlated SAME/MUB prior.
The physical correlated-prior comparison is explicitly a premise here, until
the independent cache and recording proof has been substituted. -/
namespace ICO.C6Decision
open Matrix QIT MeasureTheory ICO.BudgetQueryTree ICO.BudgetContinuity
open ICO.BudgetTesting ICO.BornAverage ICO.C6SwitchTest
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {A M O B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
  [Fintype B] [DecidableEq B]

def sameDensity {q : ℕ} (tree : Tree (A×M) O q B) (ρ : State B) : CMatrix O :=
  ∫ U, (tree.channel (hidden U) (hidden U)).map ρ.matrix ∂unitaryHaarMeasure (a:=A)

def mubDensity {q : ℕ} (tree : Tree (A×M) O q B) (ρ : State B)
    (H : Matrix.unitaryGroup A ℂ) : CMatrix O :=
  ∫ U, (tree.channel (hidden U) (hidden (U*H))).map ρ.matrix ∂unitaryHaarMeasure (a:=A)

theorem correlated_output_continuous {q : ℕ} (tree : Tree (A×M) O q B)
    (X : CMatrix B) (H : Matrix.unitaryGroup A ℂ) :
    Continuous (fun U => (tree.channel (hidden U) (hidden (U*H))).map X) := by
  have hg : Continuous (fun U : Matrix.unitaryGroup A ℂ => (U,U*H)) :=
    continuous_id.prodMk (continuous_id.mul continuous_const)
  have hc := (independent_output_continuous tree X).comp hg
  simpa only [Function.comp_def] using hc

theorem required_distance {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B) (H : Matrix.unitaryGroup A ℂ)
    (hH : ∀ i j, Complex.normSq ((H:CMatrix A) i j)=1/(Fintype.card A:ℝ))
    (hhigh : ∀ U, (2/3:ℝ)≤acceptance T tree ρ (hidden U) (hidden U))
    (hlow : ∀ U V, MutuallyUnbiased U V →
      acceptance T tree ρ (hidden U) (hidden V)≤1/3) :
    (1/3:ℝ)≤normalizedTraceDistance (sameDensity tree ρ) (mubDensity tree ρ H) := by
  let F := fun U : Matrix.unitaryGroup A ℂ =>
    (tree.channel (hidden U) (hidden U)).applyState ρ
  let G := fun U : Matrix.unitaryGroup A ℂ =>
    (tree.channel (hidden U) (hidden (U*H))).applyState ρ
  have hiF : Integrable (fun U => (F U).matrix) (unitaryHaarMeasure (a:=A)) :=
    (luders_output_continuous tree ρ.matrix).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiG : Integrable (fun U => (G U).matrix) (unitaryHaarMeasure (a:=A)) :=
    (correlated_output_continuous tree ρ.matrix H).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hF : ∀ U, (2/3:ℝ)≤(T.acceptProb (F U):ℝ) := by
    intro U
    simpa only [F, ←acceptance_eq] using hhigh U
  have hG : ∀ U, (T.acceptProb (G U):ℝ)≤1/3 := by
    intro U
    simpa only [G, ←acceptance_eq] using hlow U (U*H) (flat_translate U H hH)
  have hf := integral_mono (integrable_const (2/3:ℝ)) (accept_integrable T F hiF) hF
  have hg := integral_mono (accept_integrable T G hiG) (integrable_const (1/3:ℝ)) hG
  simp only [integral_const, probReal_univ, one_smul] at hf hg
  rw [←accept_average T F hiF] at hf
  rw [←accept_average T G hiG] at hg
  exact ICO.QuantumDecision.successful_decision_requires_distance T
    (averageState F hiF) (averageState G hiG) hf hg

theorem zero_query_impossible (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O 0 B) (ρ : State B) (H : Matrix.unitaryGroup A ℂ)
    (hH : ∀ i j, Complex.normSq ((H:CMatrix A) i j)=1/(Fintype.card A:ℝ))
    (hhigh : ∀ U, (2/3:ℝ)≤acceptance T tree ρ (hidden U) (hidden U))
    (hlow : ∀ U V, MutuallyUnbiased U V →
      acceptance T tree ρ (hidden U) (hidden V)≤1/3) : False := by
  let U : Matrix.unitaryGroup A ℂ := 1
  have he := congrArg (fun f : MatrixMap B O => acceptCLM T (f ρ.matrix))
    (ICO.BudgetHaarBound.zero_budget_map tree rfl
      (hidden U) (hidden U) (hidden U) (hidden (U*H)))
  change acceptance T tree ρ (hidden U) (hidden U)=
    acceptance T tree ρ (hidden U) (hidden (U*H)) at he
  have hh := hhigh U
  have hl := hlow U (U*H) (flat_translate U H hH)
  linarith

theorem lower_bound_of_comparison {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B) (n : ℕ)
    (hd : Fintype.card A=2^n)
    (hcomparison : ∀ H : Matrix.unitaryGroup A ℂ,
      (∀ i j, Complex.normSq ((H:CMatrix A) i j)=1/(Fintype.card A:ℝ)) →
      1≤q → 2*q<Fintype.card A → 4*q≤Fintype.card A →
      normalizedTraceDistance (sameDensity tree ρ) (mubDensity tree ρ H)≤
        ICO.C6Bounds.error q (Fintype.card A) ((Fintype.card A:ℝ)^(1/16:ℝ)))
    (hhigh : ∀ U, (2/3:ℝ)≤acceptance T tree ρ (hidden U) (hidden U))
    (hlow : ∀ U V, MutuallyUnbiased U V →
      acceptance T tree ρ (hidden U) (hidden V)≤1/3) :
    (Fintype.card A:ℝ)^(1/16:ℝ)/100 < q := by
  obtain ⟨H,hH⟩ := ICO.C6FlatUnitary.flat_unitary n hd
  by_cases hq : q=0
  · subst q
    exact False.elim (zero_query_impossible T tree ρ H hH hhigh hlow)
  have hq1 : 1≤q := by omega
  by_contra hn
  have hqr : (q:ℝ)≤(Fintype.card A:ℝ)^(1/16:ℝ)/100 := le_of_not_gt hn
  have hrpow := ICO.QuantumDecision.radius_power_sixteen (Fintype.card A) (by positivity)
  have hr := ICO.C6Bounds.radius_dimensions (by exact_mod_cast hq1) hqr
  have hsize : 2*q<Fintype.card A := by
    have hp : (0:ℝ)<((Fintype.card A:ℝ)^(1/16:ℝ))^4 := pow_pos hr.1 4
    rw [hrpow] at hr
    exact_mod_cast (show (2*(q:ℝ))<Fintype.card A by linarith [hr.2.2])
  have hfour : 4*q≤Fintype.card A := by
    have hqreal : (1:ℝ)≤q := by exact_mod_cast hq1
    have hr1 : 1≤(Fintype.card A:ℝ)^(1/16:ℝ) := by linarith
    have h14 : (Fintype.card A:ℝ)^(1/16:ℝ)≤((Fintype.card A:ℝ)^(1/16:ℝ))^4 := by
      simpa using pow_le_pow_right₀ hr1 (show (1:ℕ)≤4 by norm_num)
    rw [hrpow] at hr
    exact_mod_cast (show 4*(q:ℝ)≤Fintype.card A by linarith [hr.2.2])
  have hs := ICO.C6Bounds.error_lt_one_third hq1 hqr
  rw [hrpow] at hs
  have hb := hcomparison H hH hq1 hsize hfour
  have hl := required_distance T tree ρ H hH hhigh hlow
  linarith

#print axioms zero_query_impossible
#print axioms lower_bound_of_comparison
end
end ICO.C6Decision
