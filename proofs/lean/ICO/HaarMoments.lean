import QIT.Symmetry.UnitaryTwirl
import QIT.Util.CMatrixCLM

/-!+# Matrix entries of the fourth Haar moment

The Haar measure and the two-copy twirl are QIT's genuine integrals over the
unitary group. This adapter turns their symmetric/antisymmetric decomposition
into identities for products of four unitary entries. No unitary-design
hypothesis or moment identity is postulated.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix QIT MeasureTheory

namespace ICO.HaarMoments

noncomputable section

universe u
variable {A : Type u} [Fintype A] [DecidableEq A]

/-- Two tensor copies in QIT have the expected matrix entries. -/
theorem unitary_two_entry (U : Matrix.unitaryGroup A ℂ) (i j k l : A) :
    (unitaryTensorPowerMatrix U 2 : CMatrix (TensorPower A 2))
      (twoCopyTensorWord i j) (twoCopyTensorWord k l) =
        (U : CMatrix A) i k * (U : CMatrix A) j l := by
  rw [unitaryTensorPowerMatrix_apply_eq_fin_prod]
  simp [Fin.prod_univ_two]

/-- Matrix entries commute with the finite-dimensional Haar integral. -/
theorem unitaryTwirl_entry [Nonempty A] (X : CMatrix (TensorPower A 2))
    (i j : TensorPower A 2) :
    unitaryTwirl 2 X i j =
      ∫ U : Matrix.unitaryGroup A ℂ, unitaryTwirlIntegrand 2 X U i j
        ∂unitaryHaarMeasure (a := A) := by
  simpa [unitaryTwirl, cMatrixEntryCLM] using
    ((cMatrixEntryCLM (ι := TensorPower A 2) i j).integral_comp_comm
      (unitaryTwirl_integrand_integrable 2 X)).symm

/-- Fourth entry moment, with two unconjugated and two conjugated factors. -/
def fourthMoment [Nonempty A] (i j k l m n p q : A) : ℂ :=
  ∫ U : Matrix.unitaryGroup A ℂ,
    ((U : CMatrix A) i k * (U : CMatrix A) j l) *
      star ((U : CMatrix A) m p * (U : CMatrix A) n q)
    ∂unitaryHaarMeasure (a := A)

/-- A fourth entry moment is an entry of the two-copy twirl of a matrix unit. -/
theorem fourthMoment_eq_twirl_single [Nonempty A] (i j k l m n p q : A) :
    fourthMoment i j k l m n p q =
      unitaryTwirl 2
        (Matrix.single (twoCopyTensorWord k l) (twoCopyTensorWord p q) (1 : ℂ))
        (twoCopyTensorWord i j) (twoCopyTensorWord m n) := by
  rw [unitaryTwirl_entry]
  apply integral_congr_ae
  filter_upwards [] with U
  simp [unitaryTwirlIntegrand, Matrix.mul_apply, Matrix.single,
    Matrix.conjTranspose_apply, unitary_two_entry, ite_and]

/-- Exact fourth moment in spectral-projector form. This is the direct
coordinate bridge from QIT's proved two-copy Haar theorem. -/
theorem fourthMoment_symmetric_antisymmetric [Nontrivial A]
    (i j k l m n p q : A) :
    fourthMoment i j k l m n p q =
      (symmetricProjectionMatrix (a := A) 2
          (twoCopyTensorWord p q) (twoCopyTensorWord k l) /
        (symmetricProjectionMatrix (a := A) 2).trace) *
          symmetricProjectionMatrix (a := A) 2
            (twoCopyTensorWord i j) (twoCopyTensorWord m n) +
      (antisymmetricProjectionMatrix_two (a := A)
          (twoCopyTensorWord p q) (twoCopyTensorWord k l) /
        (antisymmetricProjectionMatrix_two (a := A)).trace) *
          antisymmetricProjectionMatrix_two (a := A)
            (twoCopyTensorWord i j) (twoCopyTensorWord m n) := by
  rw [fourthMoment_eq_twirl_single,
    unitaryTwirl_two_eq_symmetric_antisymmetric_trace_decomposition]
  simp [Matrix.trace_mul_single, Matrix.smul_apply, smul_eq_mul]

/-- Complex Kronecker delta, used to state the entry formula without
tensor-coordinate implementation details. -/
def delta (i j : A) : ℂ := if i = j then 1 else 0

theorem delta_comm (i j : A) : delta i j = delta j i := by
  simp [delta, eq_comm]

theorem one_two_entry (i j k l : A) :
    (1 : CMatrix (TensorPower A 2))
      (twoCopyTensorWord i j) (twoCopyTensorWord k l) =
        delta i k * delta j l := by
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp [Matrix.one_apply, delta, hik, hjl]

theorem swap_two_entry (i j k l : A) :
    tensorPowerSwapMatrix_two (a := A)
      (twoCopyTensorWord i j) (twoCopyTensorWord k l) =
        delta i l * delta j k := by
  by_cases hil : i = l <;> by_cases hjk : j = k <;>
    simp [tensorPowerSwapMatrix_two, permutationMatrix,
      permEquiv_twoCopySwapPerm_twoCopyTensorWord, delta, hil, hjk]

theorem symmetric_two_entry (i j k l : A) :
    symmetricProjectionMatrix (a := A) 2
      (twoCopyTensorWord i j) (twoCopyTensorWord k l) =
        (delta i k * delta j l + delta i l * delta j k) / 2 := by
  rw [symmetricProjectionMatrix_two_eq_half_one_add_swap]
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    one_two_entry, swap_two_entry]
  ring

theorem antisymmetric_two_entry (i j k l : A) :
    antisymmetricProjectionMatrix_two (a := A)
      (twoCopyTensorWord i j) (twoCopyTensorWord k l) =
        (delta i k * delta j l - delta i l * delta j k) / 2 := by
  rw [antisymmetricProjectionMatrix_two_eq_half_one_sub_swap]
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
    one_two_entry, swap_two_entry]
  ring

/-- The explicit fourth Haar moment (the order-two Weingarten formula). -/
theorem fourthMoment_delta [Nontrivial A] (i j k l m n p q : A) :
    fourthMoment i j k l m n p q =
      ((delta p k * delta q l) * (delta i m * delta j n) +
        (delta p l * delta q k) * (delta i n * delta j m)) /
          ((Fintype.card A : ℂ) ^ 2 - 1) -
      ((delta p k * delta q l) * (delta i n * delta j m) +
        (delta p l * delta q k) * (delta i m * delta j n)) /
          ((Fintype.card A : ℂ) * ((Fintype.card A : ℂ) ^ 2 - 1)) := by
  rw [fourthMoment_symmetric_antisymmetric]
  simp only [symmetric_two_entry, antisymmetric_two_entry,
    symmetricProjectionMatrix_two_trace, antisymmetricProjectionMatrix_two_trace]
  have hd : (Fintype.card A : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hm : (Fintype.card A : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (ne_of_gt (Fintype.one_lt_card (α := A)))
  have hp : (Fintype.card A : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero (Fintype.card A))
  have hs : (Fintype.card A : ℂ) ^ 2 - 1 ≠ 0 := by
    rw [show (Fintype.card A : ℂ) ^ 2 - 1 =
      ((Fintype.card A : ℂ) - 1) * ((Fintype.card A : ℂ) + 1) by ring]
    exact mul_ne_zero hm hp
  field_simp [hd, hm, hp, hs]
  <;> ring

end

end ICO.HaarMoments
