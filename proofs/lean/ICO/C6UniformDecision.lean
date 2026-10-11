import ICO.C6Decision
import ICO.C6UniformBounds

/-! Decision reduction with the checked uniform-sector cache error. The actual
correlated-prior comparison is explicitly a premise until the physical chain is
assembled. This is an adaptive channel-query statement, with arbitrary finite
private memory, a mixed input, and an arbitrary final binary POVM. -/
namespace ICO.C6UniformDecision
open Matrix QIT MeasureTheory ICO.BudgetQueryTree ICO.BudgetContinuity
open ICO.BudgetTesting ICO.BornAverage ICO.C6SwitchTest ICO.C6Decision
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {A M O B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
  [Fintype B] [DecidableEq B]

theorem lower_bound_of_comparison {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B) (n : ℕ)
    (hd : Fintype.card A=2^n)
    (hcomparison : ∀ H : Matrix.unitaryGroup A ℂ,
      (∀ i j, Complex.normSq ((H:CMatrix A) i j)=1/(Fintype.card A:ℝ)) →
      1≤q → 2*q<Fintype.card A → 4*q≤Fintype.card A →
      normalizedTraceDistance (sameDensity tree ρ) (mubDensity tree ρ H)≤
        ICO.C6UniformBounds.uniformError q (Fintype.card A) ((Fintype.card A:ℝ)^(1/16:ℝ)))
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
  have hs := ICO.C6UniformBounds.uniformError_lt_one_third hq1 hqr
  rw [hrpow] at hs
  have hb := hcomparison H hH hq1 hsize hfour
  have hl := required_distance T tree ρ H hH hhigh hlow
  linarith

#print axioms lower_bound_of_comparison
end
end ICO.C6UniformDecision
