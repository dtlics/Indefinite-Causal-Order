import ICO.CausalReverse
import QIT.HypothesisTesting.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

namespace ICO.GramWitness
open Matrix QIT ICO.CausalReverse
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 0

local instance matrixNonUnitalCStar (n : Type*) [Fintype n] [DecidableEq n] :
    NonUnitalCStarAlgebra (CMatrix n) := ⟨⟩
local instance matrixCStar (n : Type*) [Fintype n] [DecidableEq n] :
    CStarAlgebra (CMatrix n) := ⟨⟩

variable {H I : Type*} [Fintype H] [DecidableEq H] [Nonempty H]
  [Fintype I] [DecidableEq I] [Nonempty I]

def gram (Z : Matrix H I ℂ) : CMatrix I := Zᴴ * Z
def frame (Z : Matrix H I ℂ) : CMatrix H := Z * Zᴴ
def scale (Z : Matrix H I ℂ) : ℝ := max 1 ‖frame Z‖
def effect (Z : Matrix H I ℂ) : CMatrix H := (((scale Z)⁻¹ : ℝ) : ℂ) • frame Z

theorem frame_pos (Z : Matrix H I ℂ) : (frame Z).PosSemidef := by
  simpa [frame] using Matrix.posSemidef_conjTranspose_mul_self Zᴴ

theorem gram_pos (Z : Matrix H I ℂ) : (gram Z).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self Z

theorem scale_pos (Z : Matrix H I ℂ) : 0 < scale Z :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem effect_pos (Z : Matrix H I ℂ) : (effect Z).PosSemidef := by
  apply (frame_pos Z).smul
  exact_mod_cast (inv_nonneg.mpr (scale_pos Z).le)

theorem effect_norm_le_one (Z : Matrix H I ℂ) : ‖effect Z‖ ≤ 1 := by
  have hs := scale_pos Z
  calc
    ‖effect Z‖ = ‖frame Z‖ / scale Z := by
      rw [effect, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr hs.le)]
      ring
    _ ≤ 1 := (div_le_one hs).2 (le_max_right _ _)

theorem effect_le_one (Z : Matrix H I ℂ) : effect Z ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg (effect Z) (effect_pos Z).nonneg).mp
    (effect_norm_le_one Z)

theorem frame_gram_norm (Z : Matrix H I ℂ) : ‖frame Z‖ = ‖gram Z‖ := by
  calc
    ‖frame Z‖ = ‖Zᴴ‖ * ‖Zᴴ‖ := by
      simpa [frame] using Matrix.l2_opNorm_conjTranspose_mul_self Zᴴ
    _ = ‖Z‖ * ‖Z‖ := by rw [Matrix.l2_opNorm_conjTranspose]
    _ = ‖gram Z‖ := (Matrix.l2_opNorm_conjTranspose_mul_self Z).symm

theorem scale_le_one_add_defect (Z : Matrix H I ℂ) : scale Z ≤ 1 + ‖gram Z - 1‖ := by
  apply max_le
  · exact le_add_of_nonneg_right (norm_nonneg _)
  · rw [frame_gram_norm]
    have hh := norm_add_le (gram Z - 1) (1 : CMatrix I)
    simpa [norm_one, add_comm] using hh

theorem hermitian_trace_square (G : CMatrix I) (hG : G.IsHermitian) :
    (G * G).trace.re = ∑ i, ∑ j, Complex.normSq (G i j) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hji : G j i = star (G i j) := (congrFun (congrFun hG j) i).symm
  rw [hji]
  simp [Complex.normSq_apply]

theorem trace_frame (Z : Matrix H I ℂ) (hdiag : ∀ i, gram Z i i = 1) :
    (frame Z).trace = Fintype.card I := by
  rw [frame, Matrix.trace_mul_comm]
  change (gram Z).trace = _
  simp [Matrix.trace, hdiag]

theorem trace_frame_square_ge_card (Z : Matrix H I ℂ) (hdiag : ∀ i, gram Z i i = 1) :
    (Fintype.card I : ℝ) ≤ (frame Z * frame Z).trace.re := by
  have heq : (frame Z * frame Z).trace = (gram Z * gram Z).trace := by
    unfold frame gram
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm Z, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc]
  rw [heq, hermitian_trace_square _ (gram_pos Z).isHermitian]
  calc
    (Fintype.card I : ℝ) = ∑ i : I, Complex.normSq (gram Z i i) := by simp [hdiag]
    _ ≤ ∑ i : I, ∑ j : I, Complex.normSq (gram Z i j) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.single_le_sum (fun j hj => Complex.normSq_nonneg _) (Finset.mem_univ i)

def idealState (Z : Matrix H I ℂ) (hdiag : ∀ i, gram Z i i = 1) : State H where
  matrix := (((Fintype.card I : ℝ)⁻¹ : ℝ) : ℂ) • frame Z
  pos := (frame_pos Z).smul (by
    exact_mod_cast (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card I)) :
      (0 : ℝ) ≤ (Fintype.card I : ℝ)⁻¹))
  trace_eq_one := by
    simp [Matrix.trace_smul, trace_frame Z hdiag, Complex.ofReal_inv,
      Fintype.card_ne_zero]

def witnessTest (Z : Matrix H I ℂ) : BinaryHypothesisTest H where
  effects b := cond b (effect Z) (1 - effect Z)
  pos b := by
    cases b
    · exact Matrix.le_iff.mp (effect_le_one Z)
    · exact effect_pos Z
  sum_eq_one := by simp

theorem ideal_acceptance_formula (Z : Matrix H I ℂ) (hdiag : ∀ i, gram Z i i = 1) :
    ((witnessTest Z).acceptProb (idealState Z hdiag) : ℝ) =
      (frame Z * frame Z).trace.re / ((Fintype.card I : ℝ) * scale Z) := by
  rw [BinaryHypothesisTest.acceptProb_eq_trace_re]
  change (((( ((Fintype.card I : ℝ)⁻¹ : ℝ) : ℂ) • frame Z) *
    ((((scale Z)⁻¹ : ℝ) : ℂ) • frame Z)).trace).re = _
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, zero_add, add_zero, sub_zero,
    div_eq_mul_inv, mul_inv]
  ring

/-- The adaptive simulator is tested by an actual valid effect. Its ideal
acceptance loss is at most the operator-norm defect of the column Gram matrix. -/
theorem ideal_acceptance_ge_one_sub_defect (Z : Matrix H I ℂ)
    (hdiag : ∀ i, gram Z i i = 1) :
    1 - ‖gram Z - 1‖ ≤ ((witnessTest Z).acceptProb (idealState Z hdiag) : ℝ) := by
  rw [ideal_acceptance_formula]
  have hs := scale_pos Z
  have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have ht := trace_frame_square_ge_card Z hdiag
  have hscale := scale_le_one_add_defect Z
  have he : 0 ≤ ‖gram Z - 1‖ := norm_nonneg _
  calc
    1 - ‖gram Z - 1‖ ≤ 1 / (1 + ‖gram Z - 1‖) := by
      apply (le_div_iff₀ (by positivity)).2
      nlinarith [sq_nonneg ‖gram Z - 1‖]
    _ ≤ 1 / scale Z := one_div_le_one_div_of_le hs hscale
    _ ≤ (frame Z * frame Z).trace.re / ((Fintype.card I : ℝ) * scale Z) := by
      apply (le_div_iff₀ (mul_pos hn hs)).2
      have hi : 1 / scale Z * ((Fintype.card I : ℝ) * scale Z) = Fintype.card I := by
        field_simp
      rwa [hi]

#print axioms effect_le_one
#print axioms ideal_acceptance_ge_one_sub_defect
end
end ICO.GramWitness
