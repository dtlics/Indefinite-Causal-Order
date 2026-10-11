import ICO.EqualityTwirlIntegral

open scoped Matrix.Norms.L2Operator
open Matrix QIT MeasureTheory ICO.HaarMoments ICO.HaarFrame ICO.CausalReverse

namespace ICO.EqualityTwirl
set_option maxHeartbeats 800000
noncomputable section
universe u
variable {A : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem column_orthogonality (U : Matrix.unitaryGroup A ℂ) (a b : A) :
    (∑ x, star ((U : CMatrix A) x a) * (U : CMatrix A) x b) = delta a b := by
  have h := congrArg (fun M : CMatrix A => M a b) (Matrix.UnitaryGroup.star_mul_self U)
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, delta] using h

theorem conjugateTensor_bell_invariant (U : Matrix.unitaryGroup A ℂ) :
    (conjugateTensor U).conjTranspose * bellMatrix A * conjugateTensor U = bellMatrix A := by
  ext i j
  have he : ((conjugateTensor U).conjTranspose * bellMatrix A * conjugateTensor U) i j =
      (∑ x, star ((U : CMatrix A) x i.1) * (U : CMatrix A) x i.2) *
        (∑ y, star ((U : CMatrix A) y j.2) * (U : CMatrix A) y j.1) / Fintype.card A := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, conjugateTensor,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.map_apply, bell_entry_delta,
      delta, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum, div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring
  rw [he, column_orthogonality, column_orthogonality, bell_entry_delta, delta_comm j.2 j.1]

theorem conjugate_complement_equality_twirl :
    (∫ U : Matrix.unitaryGroup A ℂ,
      (conjugateTensor U).conjTranspose * (equalityProjector (A := A) - bellMatrix A) * conjugateTensor U
        ∂unitaryHaarMeasure (a := A)) =
      ((Fintype.card A : ℂ) + 1)⁻¹ • (1 - bellMatrix A) := by
  have hQ := conjugateTensor_continuous (A := A)
  have hcont := (hQ.matrix_conjTranspose.matrix_mul
    (continuous_const (y := equalityProjector (A := A)))).matrix_mul hQ
  have hint := hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := unitaryHaarMeasure (a := A))
  have he (U : Matrix.unitaryGroup A ℂ) :
      (conjugateTensor U).conjTranspose * (equalityProjector (A := A) - bellMatrix A) * conjugateTensor U =
      (conjugateTensor U).conjTranspose * equalityProjector (A := A) * conjugateTensor U - bellMatrix A := by
    rw [Matrix.mul_sub, Matrix.sub_mul, conjugateTensor_bell_invariant]
  simp_rw [he]
  rw [integral_sub hint (integrable_const _), conjugate_equality_twirl]
  simp only [integral_const, probReal_univ, one_smul]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  have hp : (Fintype.card A : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (Fintype.card A)
  field_simp [hp]
  ring

#print axioms conjugateTensor_bell_invariant
#print axioms conjugate_complement_equality_twirl
end
end ICO.EqualityTwirl
