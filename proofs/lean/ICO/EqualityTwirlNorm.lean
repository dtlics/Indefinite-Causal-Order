import ICO.EqualityTwirlBell
import ICO.GramWitness

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix QIT MeasureTheory ICO.HaarMoments ICO.HaarFrame ICO.CausalReverse

namespace ICO.EqualityTwirl
set_option maxHeartbeats 600000
noncomputable section
universe u
variable {A : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]

local instance localMatrixNonUnitalCStar (n : Type u) [Fintype n] [DecidableEq n] :
    NonUnitalCStarAlgebra (CMatrix n) := ⟨⟩
local instance localMatrixCStar (n : Type u) [Fintype n] [DecidableEq n] :
    CStarAlgebra (CMatrix n) := ⟨⟩

theorem swapMatrix_hermitian : (swapMatrix (A := A)).conjTranspose = swapMatrix := by
  ext i j
  by_cases h : i.1 = j.2 <;> by_cases k : i.2 = j.1 <;>
    simp [swapMatrix, Matrix.conjTranspose_apply, delta, eq_comm, mul_comm, h, k]

theorem swapMatrix_square : swapMatrix (A := A) * swapMatrix = 1 := by
  ext i j
  simp [swapMatrix, Matrix.mul_apply, Fintype.sum_prod_type, delta, Matrix.one_apply, Prod.ext_iff, eq_comm]
  by_cases h : i.1 = j.1 <;> by_cases k : i.2 = j.2 <;> simp [h, k]

theorem swapMatrix_norm : ‖swapMatrix (A := A)‖ = 1 := by
  apply CStarRing.norm_of_mem_unitary
  constructor <;> simpa only [Matrix.star_eq_conjTranspose, swapMatrix_hermitian] using (swapMatrix_square (A := A))

theorem bell_complement_norm_le_one : ‖1 - bellMatrix A‖ ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (Matrix.le_iff.mp (bellMatrix_le_one (A := A))).nonneg).2
  exact sub_le_self _ (bellMatrix_pos (A := A)).nonneg

theorem local_scalar_norm : ‖((Fintype.card A : ℂ) + 1)⁻¹‖ = 1 / ((Fintype.card A : ℝ)+1) := by
  have he : (Fintype.card A : ℂ)+1 = (((Fintype.card A : ℝ)+1 : ℝ) : ℂ) := by simp
  rw [he, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [one_div]

theorem same_equality_twirl_norm_le :
    ‖∫ U : Matrix.unitaryGroup A ℂ,
      (sameTensor U).conjTranspose * equalityProjector (A := A) * sameTensor U
        ∂unitaryHaarMeasure (a := A)‖ ≤ 2 / ((Fintype.card A : ℝ)+1) := by
  rw [same_equality_twirl, norm_smul, local_scalar_norm]
  have hs : ‖(1 : CMatrix (A × A)) + swapMatrix‖ ≤ 2 := by
    have h := norm_add_le (1 : CMatrix (A × A)) (swapMatrix (A := A))
    simpa only [norm_one, swapMatrix_norm, one_add_one_eq_two] using h
  calc
    _ ≤ (1 / ((Fintype.card A : ℝ)+1)) * 2 := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

theorem conjugate_complement_twirl_norm_le :
    ‖∫ U : Matrix.unitaryGroup A ℂ,
      (conjugateTensor U).conjTranspose * (equalityProjector (A := A) - bellMatrix A) * conjugateTensor U
        ∂unitaryHaarMeasure (a := A)‖ ≤ 1 / ((Fintype.card A : ℝ)+1) := by
  rw [conjugate_complement_equality_twirl, norm_smul, local_scalar_norm]
  exact mul_le_of_le_one_right (by positivity) bell_complement_norm_le_one

#print axioms same_equality_twirl_norm_le
#print axioms conjugate_complement_twirl_norm_le
end
end ICO.EqualityTwirl
