import ICO.ProbabilityConstants
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

/-! Concentration for the independent bounded outcomes of repeated switch
experiments. Hoeffding's inequality is applied to actual random variables;
no concentration inequality is assumed. The quantum experiment's observable
identity and the construction of its independent product distribution are
separate from these measure-theoretic lemmas. -/

namespace ICO.SwitchStatistics

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem centered_subgaussian {X : Ω → ℝ} (hm : AEMeasurable X μ)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1) (p : ℝ)
    (hp : (∫ ω, X ω ∂μ) = p) :
    HasSubgaussianMGF (fun ω => X ω - p) (1 / 4 : NNReal) μ := by
  have h := hasSubgaussianMGF_of_mem_Icc hm hb
  rw [hp] at h
  norm_num at h
  exact h

theorem upper_tail {m : ℕ} (hm : 0 < m) (X : Fin m → Ω → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (p ε : ℝ) (hmean : ∀ i, (∫ ω, X i ω ∂μ) = p) (hε : 0 ≤ ε) :
    μ.real {ω | (m : ℝ) * (p + ε) ≤ ∑ i, X i ω} ≤
      Real.exp (-2 * (m : ℝ) * ε ^ 2) := by
  have hInd : iIndepFun (fun i ω => X i ω - p) μ :=
    hind.comp (fun _ z => z - p) (by intro i; fun_prop)
  have hSG : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      HasSubgaussianMGF (fun ω => X i ω - p) (1 / 4 : NNReal) μ := by
    intro i hi
    exact centered_subgaussian (hmeas i) (hbound i) p (hmean i)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hInd hSG
    (show 0 ≤ (m : ℝ) * ε by positivity)
  have hset : {ω | (m : ℝ) * ε ≤ ∑ i : Fin m, (X i ω - p)} =
      {ω | (m : ℝ) * (p + ε) ≤ ∑ i, X i ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    constructor <;> intro hh <;> linarith
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_div,
    NNReal.coe_ofNat, hset] at h
  norm_num at h
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  convert h using 1
  congr 1
  field_simp
  <;> ring

theorem lower_tail {m : ℕ} (hm : 0 < m) (X : Fin m → Ω → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (p ε : ℝ) (hmean : ∀ i, (∫ ω, X i ω ∂μ) = p) (hε : 0 ≤ ε) :
    μ.real {ω | (∑ i, X i ω) ≤ (m : ℝ) * (p - ε)} ≤
      Real.exp (-2 * (m : ℝ) * ε ^ 2) := by
  have hInd : iIndepFun (fun i ω => p - X i ω) μ :=
    hind.comp (fun _ z => p - z) (by intro i; fun_prop)
  have hSG : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      HasSubgaussianMGF (fun ω => p - X i ω) (1 / 4 : NNReal) μ := by
    intro i hi
    have h := (centered_subgaussian (hmeas i) (hbound i) p (hmean i)).neg
    have heq : (fun ω => p - X i ω) = -(fun ω => X i ω - p) := by
      funext ω
      change p - X i ω = -(X i ω - p)
      ring
    rw [heq]
    exact h
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hInd hSG
    (show 0 ≤ (m : ℝ) * ε by positivity)
  have hset : {ω | (m : ℝ) * ε ≤ ∑ i : Fin m, (p - X i ω)} =
      {ω | (∑ i, X i ω) ≤ (m : ℝ) * (p - ε)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    constructor <;> intro hh <;> linarith
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_div,
    NNReal.coe_ofNat, hset] at h
  norm_num at h
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  convert h using 1
  congr 1
  field_simp
  <;> ring

theorem eighty_high_error (X : Fin 80 → Ω → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (p : ℝ) (hmean : ∀ i, (∫ ω, X i ω ∂μ) = p) (hp : 5 / 6 ≤ p) :
    μ.real {ω | (∑ i, X i ω) < 60} < 1 / 3 := by
  have h := lower_tail (by norm_num : 0 < (80 : ℕ)) X hind hmeas hbound
    p (1 / 12) hmean (by norm_num)
  have hsub : {ω | (∑ i, X i ω) < 60} ⊆
      {ω | (∑ i, X i ω) ≤ (80 : ℝ) * (p - 1 / 12)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    linarith
  have ht := ICO.ProbabilityConstants.eighty_switch_repetitions (by norm_num : (80 : ℝ) ≤ 80)
  exact lt_of_le_of_lt ((measureReal_mono hsub).trans h) ht

theorem eighty_low_error (X : Fin 80 → Ω → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (p : ℝ) (hmean : ∀ i, (∫ ω, X i ω ∂μ) = p) (hp : p ≤ 2 / 3) :
    μ.real {ω | 60 ≤ ∑ i, X i ω} < 1 / 3 := by
  have h := upper_tail (by norm_num : 0 < (80 : ℕ)) X hind hmeas hbound
    p (1 / 12) hmean (by norm_num)
  have hsub : {ω | 60 ≤ ∑ i, X i ω} ⊆
      {ω | (80 : ℝ) * (p + 1 / 12) ≤ ∑ i, X i ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    linarith
  have ht := ICO.ProbabilityConstants.eighty_switch_repetitions (by norm_num : (80 : ℝ) ≤ 80)
  exact lt_of_le_of_lt ((measureReal_mono hsub).trans h) ht

#print axioms eighty_high_error
#print axioms eighty_low_error

end
end ICO.SwitchStatistics
