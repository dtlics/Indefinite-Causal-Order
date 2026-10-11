import ICO.SwitchObservable
import ICO.HaarSecondMoment
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual interference of two nonselective rank-one measurements, and its
Haar fourth-moment average. The basis outcomes remain hidden. -/

namespace ICO.LudersPromise
open Matrix QIT MeasureTheory ICO.SwitchObservable ICO.HaarMoments ICO.HaarSecondMoment
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
set_option Elab.async false
variable {A : Type*} [Fintype A] [DecidableEq A]

theorem rankOne_four_trace (u v : A → ℂ) :
    (rankOneMatrix v * rankOneMatrix u * rankOneMatrix v * rankOneMatrix u).trace =
      (((Complex.normSq (star u ⬝ᵥ v)) ^ 2 : ℝ) : ℂ) := by
  have hs : star v ⬝ᵥ u = star (star u ⬝ᵥ v) := by
    simp [dotProduct, star_sum, star_mul, mul_comm]
  simp only [rankOneMatrix, Matrix.vecMulVec_mul_vecMulVec,
    smul_dotProduct, Matrix.trace_vecMulVec, dotProduct_smul, smul_eq_mul]
  change (((star v ⬝ᵥ u) * (star u ⬝ᵥ v)) * (star v ⬝ᵥ u)) *
    (v ⬝ᵥ star u) = _
  rw [dotProduct_comm v (star u), hs]
  simp only [Complex.ofReal_pow, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

theorem basisProjection_rankOne (U : CMatrix A) (i : A) :
    basisProjection U i = rankOneMatrix (fun a => U a i) := by
  ext a b
  simp [basisProjection, Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply,
    rankOneMatrix_apply, ite_and]

theorem basis_interference [Nonempty A] (U V : CMatrix A) :
    interference (basisProjection U) (basisProjection V) =
      (∑ i : A, ∑ j : A, Complex.normSq ((U.conjTranspose * V) i j) ^ 2) /
        (Fintype.card A : ℝ) := by
  unfold interference rawInterference
  simp only [basisProjection_hermitian]
  simp only [basisProjection_rankOne, rankOneMatrix_conjTranspose,
    rankOne_four_trace, Complex.re_sum, Complex.ofReal_re]
  rfl

theorem fourth_entry_average [Nontrivial A] (i j : A) :
    (∫ U : Matrix.unitaryGroup A ℂ, Complex.normSq ((U : CMatrix A) i j) ^ 2
      ∂unitaryHaarMeasure (a := A)) =
        2 / ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) + 1)) := by
  have hc : Continuous (fun U : Matrix.unitaryGroup A ℂ =>
      ((U : CMatrix A) i j * (U : CMatrix A) i j) *
        star ((U : CMatrix A) i j * (U : CMatrix A) i j)) :=
    ((entry_continuous i j).mul (entry_continuous i j)).mul
      ((entry_continuous i j).mul (entry_continuous i j)).star
  have hint := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := unitaryHaarMeasure (a := A))
  have hi := Complex.reCLM.integral_comp_comm hint
  have hp (z : ℂ) : ((z * z) * star (z * z)).re = Complex.normSq z ^ 2 := by
    rw [show ((z * z) * star (z * z)).re = Complex.normSq (z * z) by
      simp [Complex.normSq_apply, Complex.mul_re]
      ring]
    rw [Complex.normSq_mul]
    ring
  have hm := fourthMoment_delta i i j j i i j j
  simp [delta] at hm
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hminus : (Fintype.card A : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast ne_of_gt (Fintype.one_lt_card (α := A)))
  have hplus : (Fintype.card A : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (Fintype.card A)
  have hs : (Fintype.card A : ℂ) ^ 2 - 1 ≠ 0 := by
    rw [show (Fintype.card A : ℂ) ^ 2 - 1 =
      ((Fintype.card A : ℂ) - 1) * ((Fintype.card A : ℂ) + 1) by ring]
    exact mul_ne_zero hminus hplus
  have he : fourthMoment i i j j i i j j =
      2 / ((Fintype.card A : ℂ) * ((Fintype.card A : ℂ) + 1)) := by
    rw [hm]
    field_simp [hd, hminus, hplus, hs]
    ring
  simp only [Complex.reCLM_apply, hp] at hi
  change (∫ U : Matrix.unitaryGroup A ℂ, Complex.normSq ((U : CMatrix A) i j) ^ 2
    ∂unitaryHaarMeasure (a := A)) = (fourthMoment i i j j i i j j).re at hi
  simpa only [he, ← Complex.ofReal_natCast,
    ← Complex.ofReal_add, ← Complex.ofReal_one, ← Complex.ofReal_mul,
    ← Complex.ofReal_ofNat, ← Complex.ofReal_div, Complex.ofReal_re] using hi

#print axioms basis_interference
#print axioms fourth_entry_average

theorem relative_fourth_entry_average [Nontrivial A]
    (U : Matrix.unitaryGroup A ℂ) (i j : A) :
    (∫ V : Matrix.unitaryGroup A ℂ,
      Complex.normSq (((U : CMatrix A).conjTranspose * (V : CMatrix A)) i j) ^ 2
      ∂unitaryHaarMeasure (a := A)) =
        2 / ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) + 1)) := by
  have hh := integral_mul_left_eq_self
    (fun W : Matrix.unitaryGroup A ℂ => Complex.normSq ((W : CMatrix A) i j) ^ 2) U⁻¹
    (μ := unitaryHaarMeasure (a := A))
  rw [fourth_entry_average] at hh
  simpa only [Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.inv_val,
    Matrix.star_eq_conjTranspose] using hh

theorem relative_entry_continuous (i j : A) :
    Continuous (fun UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ =>
      Complex.normSq (((UV.1 : CMatrix A).conjTranspose * (UV.2 : CMatrix A)) i j) ^ 2) := by
  apply Continuous.pow
  apply Complex.continuous_normSq.comp
  apply (continuous_apply j).comp
  apply (continuous_apply i).comp
  exact (continuous_subtype_val.comp continuous_fst).matrix_conjTranspose.matrix_mul
    (continuous_subtype_val.comp continuous_snd)

theorem relative_entry_integrable [Nonempty A]
    (U : Matrix.unitaryGroup A ℂ) (i j : A) :
    Integrable (fun V : Matrix.unitaryGroup A ℂ =>
      Complex.normSq (((U : CMatrix A).conjTranspose * (V : CMatrix A)) i j) ^ 2)
      (unitaryHaarMeasure (a := A)) :=
  ((relative_entry_continuous i j).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem fixed_basis_interference_average [Nontrivial A] (U : Matrix.unitaryGroup A ℂ) :
    (∫ V : Matrix.unitaryGroup A ℂ,
      interference (basisProjection (U : CMatrix A)) (basisProjection (V : CMatrix A))
      ∂unitaryHaarMeasure (a := A)) = 2 / ((Fintype.card A : ℝ) + 1) := by
  simp_rw [basis_interference]
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const,
    integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => relative_entry_integrable U i j))]
  simp_rw [integral_finsetSum _ (fun j _ => relative_entry_integrable U _ j),
    relative_fourth_entry_average]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hd : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hp : (Fintype.card A : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hd, hp]

theorem basis_interference_continuous [Nonempty A] :
    Continuous (fun UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ =>
      interference (basisProjection (UV.1 : CMatrix A))
        (basisProjection (UV.2 : CMatrix A))) := by
  have he : (fun UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ =>
      interference (basisProjection (UV.1 : CMatrix A))
        (basisProjection (UV.2 : CMatrix A))) =
      (fun UV => (∑ i : A, ∑ j : A,
        Complex.normSq (((UV.1 : CMatrix A).conjTranspose * (UV.2 : CMatrix A)) i j) ^ 2) /
          (Fintype.card A : ℝ)) := by
    funext UV
    exact basis_interference _ _
  rw [he]
  exact (continuous_finsetSum _ (fun i _ =>
    continuous_finsetSum _ (fun j _ => relative_entry_continuous i j))).div_const _

theorem independent_basis_interference_average [Nontrivial A] :
    (∫ UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ,
      interference (basisProjection (UV.1 : CMatrix A))
        (basisProjection (UV.2 : CMatrix A))
      ∂(unitaryHaarMeasure (a := A)).prod (unitaryHaarMeasure (a := A))) =
        2 / ((Fintype.card A : ℝ) + 1) := by
  have hint := basis_interference_continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
    (μ := (unitaryHaarMeasure (a := A)).prod (unitaryHaarMeasure (a := A)))
  rw [integral_prod _ hint]
  simp_rw [fixed_basis_interference_average]
  simp

theorem basis_interference_nonneg [Nonempty A] (U V : CMatrix A) :
    0 ≤ interference (basisProjection U) (basisProjection V) := by
  rw [basis_interference]
  exact div_nonneg (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
    (fun j _ => sq_nonneg _))) (Nat.cast_nonneg _)

#print axioms independent_basis_interference_average

theorem low_promise_failure_probability [Nontrivial A] :
    ((unitaryHaarMeasure (a := A)).prod (unitaryHaarMeasure (a := A))).real
      {UV | (1 / 3 : ℝ) < interference (basisProjection (UV.1 : CMatrix A))
        (basisProjection (UV.2 : CMatrix A))} ≤
      6 / ((Fintype.card A : ℝ) + 1) := by
  let ν := (unitaryHaarMeasure (a := A)).prod (unitaryHaarMeasure (a := A))
  have hint := basis_interference_continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := ν)
  have hnon : ∀ᵐ UV ∂ν, 0 ≤ interference
      (basisProjection (UV.1 : CMatrix A)) (basisProjection (UV.2 : CMatrix A)) :=
    Filter.Eventually.of_forall (fun UV => basis_interference_nonneg
      (UV.1 : CMatrix A) (UV.2 : CMatrix A))
  have hh := mul_meas_ge_le_integral_of_nonneg hnon hint (1 / 3 : ℝ)
  rw [independent_basis_interference_average] at hh
  have hsub : {UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ |
      (1 / 3 : ℝ) < interference (basisProjection (UV.1 : CMatrix A))
        (basisProjection (UV.2 : CMatrix A))} ⊆
      {UV | (1 / 3 : ℝ) ≤ interference (basisProjection (UV.1 : CMatrix A))
        (basisProjection (UV.2 : CMatrix A))} := by
    intro UV h
    change (1 / 3 : ℝ) ≤ interference (basisProjection (UV.1 : CMatrix A))
      (basisProjection (UV.2 : CMatrix A))
    exact le_of_lt h
  have hm := measureReal_mono (μ := ν) hsub
  dsimp only [ν] at hm hh
  rw [show 6 / ((Fintype.card A : ℝ) + 1) =
    3 * (2 / ((Fintype.card A : ℝ) + 1)) by ring]
  linarith

#print axioms low_promise_failure_probability
end
end ICO.LudersPromise
