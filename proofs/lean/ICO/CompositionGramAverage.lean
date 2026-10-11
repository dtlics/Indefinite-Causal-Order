import ICO.CompositionGram

/-! # Expected Gram defect for the actual independent Haar composition ensemble -/

open scoped Matrix.Norms.L2Operator
open Matrix QIT MeasureTheory ICO.HaarFamily ICO.GramWitness ICO.CompositionGram

namespace ICO.CompositionGramAverage
set_option maxHeartbeats 600000
noncomputable section
universe u
variable {A : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]

def ensembleMeasure (r s : ℕ) :=
  (familyMeasure (A := A) (r + 1)).prod (familyMeasure (A := A) (s + 1))

instance ensembleMeasure_probability (r s : ℕ) : IsProbabilityMeasure
    (ensembleMeasure (A := A) r s) := inferInstanceAs (IsProbabilityMeasure
      ((familyMeasure (A := A) (r + 1)).prod (familyMeasure (A := A) (s + 1))))

theorem gram_continuous {r s : ℕ} :
    Continuous (fun UV : (Fin r → Unitary (A := A)) × (Fin s → Unitary (A := A)) =>
      gram (columns UV.1 UV.2)) :=
  columns_continuous.matrix_conjTranspose.matrix_mul columns_continuous

theorem hilbertSchmidtSq_sum {I : Type*} [Fintype I] [DecidableEq I] (G : CMatrix I) :
    hilbertSchmidtSq G = ∑ i, ∑ j, Complex.normSq (G i j) := by
  change (G.conjTranspose * G).trace.re = _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  exact Finset.sum_comm

theorem matrix_norm_average_of_entries
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I] [Nonempty I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : Ω → CMatrix I) (c : ℝ) (hc : 0 < c)
    (hnorm : Integrable (fun ω => ‖D ω‖) μ)
    (hentry : ∀ i j, Integrable (fun ω => Complex.normSq (D ω i j)) μ)
    (hmean : ∀ i j, (∫ ω, Complex.normSq (D ω i j) ∂μ) ≤ c ^ 2) :
    (∫ ω, ‖D ω‖ ∂μ) ≤ (Fintype.card I : ℝ) * c := by
  have hhs : Integrable (fun ω => hilbertSchmidtSq (D ω)) μ := by
    simp_rw [hilbertSchmidtSq_sum]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hentry i j
  have hm : (∫ ω, hilbertSchmidtSq (D ω) ∂μ) ≤ ((Fintype.card I : ℝ) * c) ^ 2 := by
    simp_rw [hilbertSchmidtSq_sum]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hentry i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hentry _ j)]
    calc
      _ ≤ ∑ _i : I, ∑ _j : I, c ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hmean i j
      _ = _ := by simp [pow_two]; ring
  have hd : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have h := ICO.AverageCoherence.integral_norm_of_square_bound μ hnorm hhs (p := 1)
    (by norm_num) (δ := (Fintype.card I : ℝ) * c) (by positivity)
    (fun ω => hilbertSchmidtSq_nonneg _) (fun ω => by
      simpa only [one_mul] using norm_sq_le_hilbertSchmidtSq (D ω))
    (by simpa only [one_mul] using hm)
  simpa only [one_mul] using h

theorem defect_entry_continuous {r s : ℕ} (ij kl : Fin r × Fin s) :
    Continuous (fun UV : (Fin r → Unitary (A := A)) × (Fin s → Unitary (A := A)) =>
      Complex.normSq ((gram (columns UV.1 UV.2) - 1) ij kl)) :=
  Complex.continuous_normSq.comp ((gram_continuous.sub continuous_const).matrix_elem ij kl)

theorem defect_entry_average_le {r s : ℕ} (ij kl : Fin (r + 1) × Fin (s + 1)) :
    (∫ UV, Complex.normSq ((gram (columns UV.1 UV.2) - 1) ij kl)
      ∂ensembleMeasure (A := A) r s) ≤ (Fintype.card A : ℝ)⁻¹ ^ 2 := by
  by_cases h : ij = kl
  · subst kl
    simp only [Matrix.sub_apply, gram_diagonal, Matrix.one_apply_eq, sub_self,
      Complex.normSq_zero, integral_zero]
    positivity
  · have hp (UV : (Fin (r + 1) → Unitary (A := A)) × (Fin (s + 1) → Unitary (A := A))) :
        Complex.normSq ((gram (columns UV.1 UV.2) - 1) ij kl) =
          (Fintype.card A : ℝ)⁻¹ ^ 2 *
            ICO.CompositionMoment.compositionOverlap UV.1 UV.2 ij.1 kl.1 ij.2 kl.2 := by
      simp only [Matrix.sub_apply, Matrix.one_apply, h, if_false, sub_zero,
        gram_entry_normSq]
    simp_rw [hp]
    rw [integral_const_mul]
    change _ * (∫ UV, ICO.CompositionMoment.compositionOverlap UV.1 UV.2 ij.1 kl.1 ij.2 kl.2
      ∂(familyMeasure (A := A) (r + 1)).prod (familyMeasure (A := A) (s + 1))) ≤ _
    rw [ICO.CompositionMoment.compositionOverlap_average ij.1 kl.1 ij.2 kl.2
      (by simpa using h), mul_one]

theorem defect_hilbertSchmidtSq_average_le (r s : ℕ) :
    (∫ UV, hilbertSchmidtSq (gram (columns UV.1 UV.2) - 1)
      ∂ensembleMeasure (A := A) r s) ≤
        (((r + 1) * (s + 1) : ℕ) / (Fintype.card A : ℝ)) ^ 2 := by
  have hint (ij kl : Fin (r + 1) × Fin (s + 1)) :
      Integrable (fun UV => Complex.normSq ((gram (columns UV.1 UV.2) - 1) ij kl))
        (ensembleMeasure (A := A) r s) :=
    (defect_entry_continuous ij kl).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [hilbertSchmidtSq_sum]
  rw [integral_finsetSum _ (fun ij _ => integrable_finsetSum _ (fun kl _ => hint ij kl))]
  simp_rw [integral_finsetSum _ (fun kl _ => hint _ kl)]
  calc
    _ ≤ ∑ _ij : Fin (r + 1) × Fin (s + 1),
        ∑ _kl : Fin (r + 1) × Fin (s + 1), (Fintype.card A : ℝ)⁻¹ ^ 2 :=
      Finset.sum_le_sum fun ij _ => Finset.sum_le_sum fun kl _ => defect_entry_average_le ij kl
    _ = _ := by simp [pow_two, div_eq_mul_inv]; ring

theorem defect_norm_average_le (r s : ℕ) :
    (∫ UV, ‖gram (columns UV.1 UV.2) - 1‖ ∂ensembleMeasure (A := A) r s) ≤
      ((r + 1) * (s + 1) : ℕ) / (Fintype.card A : ℝ) := by
  have hf : Integrable (fun UV => ‖gram (columns UV.1 UV.2) - 1‖)
      (ensembleMeasure (A := A) r s) :=
    (gram_continuous.sub continuous_const).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hc : Continuous (fun UV : (Fin (r + 1) → Unitary (A := A)) ×
      (Fin (s + 1) → Unitary (A := A)) =>
      hilbertSchmidtSq (gram (columns UV.1 UV.2) - 1)) := by
    simp_rw [hilbertSchmidtSq_sum]
    exact continuous_finsetSum _ fun ij _ => continuous_finsetSum _ fun kl _ =>
      defect_entry_continuous ij kl
  have hr := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := ensembleMeasure (A := A) r s)
  have hd : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have h := ICO.AverageCoherence.integral_norm_of_square_bound
    (ensembleMeasure (A := A) r s) hf hr (p := 1) (by norm_num)
    (δ := ((r + 1) * (s + 1) : ℕ) / (Fintype.card A : ℝ)) (by positivity)
    (fun UV => hilbertSchmidtSq_nonneg _) (fun UV => by
      simpa only [one_mul] using norm_sq_le_hilbertSchmidtSq
        (gram (columns UV.1 UV.2) - 1))
    (by simpa only [one_mul] using defect_hilbertSchmidtSq_average_le (A := A) r s)
  simpa only [one_mul] using h

end
end ICO.CompositionGramAverage

