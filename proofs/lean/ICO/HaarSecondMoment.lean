import ICO.HaarMoments
import ICO.AverageCoherence

/-! # Entry orthogonality derived from the actual fourth Haar moment -/

open scoped Matrix.Norms.L2Operator
open Matrix QIT MeasureTheory ICO.HaarMoments

namespace ICO.HaarSecondMoment

set_option maxHeartbeats 350000
noncomputable section
universe u
variable {A : Type u} [Fintype A] [DecidableEq A]

def secondMoment [Nonempty A] (i k m p : A) : ℂ :=
  ∫ U : Matrix.unitaryGroup A ℂ, (U : CMatrix A) i k * star ((U : CMatrix A) m p)
    ∂unitaryHaarMeasure (a := A)

theorem entry_continuous (i j : A) :
    Continuous (fun U : Matrix.unitaryGroup A ℂ => (U : CMatrix A) i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

theorem column_norm (U : Matrix.unitaryGroup A ℂ) (l : A) :
    (∑ j, (U : CMatrix A) j l * star ((U : CMatrix A) j l)) = 1 := by
  have h := congrFun (congrFun (Matrix.UnitaryGroup.star_mul_self U) l) l
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm] using h

theorem secondMoment_sum_fourth [Nonempty A] (i k m p l : A) :
    secondMoment i k m p = ∑ j, fourthMoment i j k l m j p l := by
  unfold secondMoment fourthMoment
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [] with U
    calc
      _ = ((U : CMatrix A) i k * star ((U : CMatrix A) m p)) *
          (∑ j, (U : CMatrix A) j l * star ((U : CMatrix A) j l)) := by
        rw [column_norm, mul_one]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [star_mul]
        ring
  · intro j hj
    exact (((entry_continuous i k).mul (entry_continuous j l)).mul
      (((entry_continuous m p).mul (entry_continuous j l)).star)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

theorem delta_sum_mul (i m : A) : (∑ j, delta i j * delta j m) = delta i m := by
  simp [delta]

theorem secondMoment_delta [Nontrivial A] (i k m p : A) :
    secondMoment i k m p = delta i m * delta p k / (Fintype.card A : ℂ) := by
  let l : A := Classical.arbitrary A
  rw [secondMoment_sum_fourth i k m p l]
  simp_rw [fourthMoment_delta]
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hm : (Fintype.card A : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast ne_of_gt (Fintype.one_lt_card (α := A))
  have hp : (Fintype.card A : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (Fintype.card A)
  have hs : (Fintype.card A : ℂ) ^ 2 - 1 ≠ 0 := by
    rw [show (Fintype.card A : ℂ) ^ 2 - 1 =
      ((Fintype.card A : ℂ) - 1) * ((Fintype.card A : ℂ) + 1) by ring]
    exact mul_ne_zero hm hp
  by_cases him : i = m <;> by_cases hpk : p = k <;>
    by_cases hpl : p = l <;> by_cases hlk : l = k
  all_goals
    simp [delta, him, hpk, hpl, hlk, ← Finset.sum_div, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, eq_comm]
    <;> field_simp [hd, hs]
    <;> ring

theorem trace_normSq_continuous :
    Continuous (fun U : Matrix.unitaryGroup A ℂ => Complex.normSq (U : CMatrix A).trace) :=
  Complex.continuous_normSq.comp continuous_subtype_val.matrix_trace

theorem trace_product_average [Nontrivial A] :
    (∫ U : Matrix.unitaryGroup A ℂ,
      (U : CMatrix A).trace * star (U : CMatrix A).trace
      ∂unitaryHaarMeasure (a := A)) = 1 := by
  have hp (U : Matrix.unitaryGroup A ℂ) :
      (U : CMatrix A).trace * star (U : CMatrix A).trace =
        ∑ i : A, ∑ j : A, (U : CMatrix A) i i * star ((U : CMatrix A) j j) := by
    simp only [Matrix.trace, Matrix.diag_apply, star_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm
  simp_rw [hp]
  have hint (i j : A) : Integrable
      (fun U : Matrix.unitaryGroup A ℂ => (U : CMatrix A) i i * star ((U : CMatrix A) j j))
      (unitaryHaarMeasure (a := A)) :=
    ((entry_continuous i i).mul (entry_continuous j j).star).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hint _ j)]
  change (∑ i : A, ∑ j : A, secondMoment i i j j) = 1
  simp_rw [secondMoment_delta]
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [delta, eq_comm, ite_div, hd]

theorem trace_normSq_average [Nontrivial A] :
    (∫ U : Matrix.unitaryGroup A ℂ, Complex.normSq (U : CMatrix A).trace
      ∂unitaryHaarMeasure (a := A)) = 1 := by
  have hp (z : ℂ) : (z * star z).re = Complex.normSq z := by
    simp [Complex.normSq_apply, Complex.mul_re]
  have hint : Integrable (fun U : Matrix.unitaryGroup A ℂ =>
      (U : CMatrix A).trace * star (U : CMatrix A).trace) (unitaryHaarMeasure (a := A)) :=
    (continuous_subtype_val.matrix_trace.mul
      continuous_subtype_val.matrix_trace.star).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have h := Complex.reCLM.integral_comp_comm hint
  simpa only [Complex.reCLM_apply, hp, trace_product_average, Complex.one_re] using h

theorem translated_trace_normSq_average [Nontrivial A] (V : Matrix.unitaryGroup A ℂ) :
    (∫ U : Matrix.unitaryGroup A ℂ, Complex.normSq ((V * U : Matrix.unitaryGroup A ℂ) :
        CMatrix A).trace ∂unitaryHaarMeasure (a := A)) = 1 := by
  rw [integral_mul_left_eq_self (fun U : Matrix.unitaryGroup A ℂ =>
    Complex.normSq (U : CMatrix A).trace) V]
  exact trace_normSq_average

end
end ICO.HaarSecondMoment
