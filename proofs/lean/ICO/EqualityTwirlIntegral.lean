import ICO.EqualityTwirl

/-! Genuine local matrix Haar twirls for the equality projector. -/

open scoped Matrix.Norms.L2Operator
open Matrix QIT MeasureTheory ICO.HaarMoments ICO.HaarFrame ICO.CausalReverse ICO.EqualityTwirl

namespace ICO.EqualityTwirl
set_option maxHeartbeats 800000
noncomputable section
universe u
variable {A : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]

local instance twirlCMatrixContinuousENorm {ι : Type u} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) := SeminormedAddGroup.toContinuousENorm

theorem unitary_entry_continuous (a b : A) :
    Continuous (fun U : Matrix.unitaryGroup A ℂ => (U : CMatrix A) a b) :=
  continuous_subtype_val.matrix_elem a b

theorem sameTensor_continuous : Continuous (sameTensor (A := A)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (unitary_entry_continuous i.1 j.1).mul (unitary_entry_continuous i.2 j.2)

theorem conjugateTensor_continuous : Continuous (conjugateTensor (A := A)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (unitary_entry_continuous i.1 j.1).mul (unitary_entry_continuous i.2 j.2).star

theorem matrix_integral_entry (F : Matrix.unitaryGroup A ℂ → CMatrix (A × A))
    (hF : Continuous F) (i j : A × A) :
    (∫ U, F U ∂unitaryHaarMeasure (a := A)) i j =
      ∫ U, F U i j ∂unitaryHaarMeasure (a := A) := by
  have hint := hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := unitaryHaarMeasure (a := A))
  simpa [cMatrixEntryCLM] using ((cMatrixEntryCLM i j).integral_comp_comm hint).symm

def swapMatrix : CMatrix (A × A) := fun i j => delta i.1 j.2 * delta i.2 j.1

theorem same_equality_twirl :
    (∫ U : Matrix.unitaryGroup A ℂ,
      (sameTensor U).conjTranspose * equalityProjector (A := A) * sameTensor U
        ∂unitaryHaarMeasure (a := A)) =
      ((Fintype.card A : ℂ) + 1)⁻¹ • (1 + swapMatrix (A := A)) := by
  have hQ := sameTensor_continuous (A := A)
  ext i j
  rw [matrix_integral_entry _ ((hQ.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hQ)]
  simp_rw [same_integrand_entry]
  have hint (x : A) : Integrable (fun U : Matrix.unitaryGroup A ℂ =>
      star ((U : CMatrix A) x i.1 * (U : CMatrix A) x i.2) *
        ((U : CMatrix A) x j.1 * (U : CMatrix A) x j.2)) (unitaryHaarMeasure (a := A)) :=
    (((unitary_entry_continuous x i.1).mul (unitary_entry_continuous x i.2)).star.mul
      ((unitary_entry_continuous x j.1).mul (unitary_entry_continuous x j.2))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [integral_finset_sum _ (fun x _ => hint x)]
  have hm (x : A) : (∫ U : Matrix.unitaryGroup A ℂ,
      star ((U : CMatrix A) x i.1 * (U : CMatrix A) x i.2) *
        ((U : CMatrix A) x j.1 * (U : CMatrix A) x j.2) ∂unitaryHaarMeasure (a := A)) =
      fourthMoment x x j.1 j.2 x x i.1 i.2 := by
    unfold fourthMoment
    apply integral_congr_ae
    filter_upwards [] with U
    ring
  simp_rw [hm]
  rw [row_fourth_sum]
  simp only [Matrix.smul_apply, Matrix.add_apply, identity_pair_entry, swapMatrix, smul_eq_mul]
  ring

theorem conjugate_equality_twirl :
    (∫ U : Matrix.unitaryGroup A ℂ,
      (conjugateTensor U).conjTranspose * equalityProjector (A := A) * conjugateTensor U
        ∂unitaryHaarMeasure (a := A)) =
      ((Fintype.card A : ℂ) + 1)⁻¹ • (1 + (Fintype.card A : ℂ) • bellMatrix A) := by
  have hQ := conjugateTensor_continuous (A := A)
  ext i j
  rw [matrix_integral_entry _ ((hQ.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hQ)]
  simp_rw [conjugate_integrand_entry]
  have hint (x : A) : Integrable (fun U : Matrix.unitaryGroup A ℂ =>
      star ((U : CMatrix A) x i.1) * (U : CMatrix A) x i.2 *
        ((U : CMatrix A) x j.1 * star ((U : CMatrix A) x j.2))) (unitaryHaarMeasure (a := A)) :=
    (((unitary_entry_continuous x i.1).star.mul (unitary_entry_continuous x i.2)).mul
      ((unitary_entry_continuous x j.1).mul (unitary_entry_continuous x j.2).star)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [integral_finset_sum _ (fun x _ => hint x)]
  have hm (x : A) : (∫ U : Matrix.unitaryGroup A ℂ,
      star ((U : CMatrix A) x i.1) * (U : CMatrix A) x i.2 *
        ((U : CMatrix A) x j.1 * star ((U : CMatrix A) x j.2)) ∂unitaryHaarMeasure (a := A)) =
      fourthMoment x x i.2 j.1 x x i.1 j.2 := by
    unfold fourthMoment
    apply integral_congr_ae
    filter_upwards [] with U
    rw [star_mul]
    ring
  simp_rw [hm]
  rw [row_fourth_sum]
  simp only [Matrix.smul_apply, Matrix.add_apply, identity_pair_entry, bell_entry_delta, smul_eq_mul]
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [delta, eq_comm]
  field_simp [hd]
  ring

#print axioms same_equality_twirl
#print axioms conjugate_equality_twirl
end
end ICO.EqualityTwirl
