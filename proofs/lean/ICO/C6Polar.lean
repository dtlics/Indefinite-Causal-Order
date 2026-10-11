import QIT.Util.Matrix.PosSqrt
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecificLimits.Normed

/-! Rectangular polar normalization by the actual positive square root. -/
namespace ICO.C6Polar
open Matrix QIT
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
set_option Elab.async false
variable {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [Fintype β] [DecidableEq β] [Nonempty β]
local instance normMatrixNonUnitalCStar (n : Type*) [Fintype n] [DecidableEq n] :
    NonUnitalCStarAlgebra (CMatrix n) := ⟨⟩
local instance normMatrixCStar (n : Type*) [Fintype n] [DecidableEq n] :
    CStarAlgebra (CMatrix n) := ⟨⟩

def gram (E : Matrix β α ℂ) : CMatrix α := Eᴴ*E
def root (E : Matrix β α ℂ) : CMatrix α := psdSqrt (gram E)
def polar (E : Matrix β α ℂ) : Matrix β α ℂ := E*(root E)⁻¹

theorem gram_pos (E : Matrix β α ℂ) : (gram E).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self E

theorem root_hermitian (E : Matrix β α ℂ) : (root E)ᴴ=root E :=
  (psdSqrt_isHermitian (gram E)).eq

theorem root_square (E : Matrix β α ℂ) : root E*root E=gram E :=
  psdSqrt_mul_self_of_posSemidef (gram_pos E)

theorem gram_isUnit (E : Matrix β α ℂ) (h : ‖gram E-1‖<1) : IsUnit (gram E) := by
  have hn : ‖1-gram E‖<1 := by rw [norm_sub_rev]; exact h
  have hh := isUnit_one_sub_of_norm_lt_one hn
  have he : (1 : CMatrix α)-(1-gram E)=gram E := by abel
  rwa [he] at hh

theorem root_isUnit (E : Matrix β α ℂ) (h : IsUnit (gram E)) : IsUnit (root E) := by
  exact (CFC.isUnit_sqrt_iff (gram E) (gram_pos E).nonneg).mpr h

theorem root_mul_inv (E : Matrix β α ℂ) (h : IsUnit (gram E)) : root E*(root E)⁻¹=1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (root_isUnit E h))

theorem inv_mul_root (E : Matrix β α ℂ) (h : IsUnit (gram E)) : (root E)⁻¹*root E=1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (root_isUnit E h))

theorem polar_isometry_of_isUnit (E : Matrix β α ℂ) (h : IsUnit (gram E)) :
    (polar E)ᴴ * polar E=1 := by
  simp only [polar, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
    root_hermitian]
  calc
    _ = (root E)⁻¹*(gram E)*(root E)⁻¹ := by simp only [gram, Matrix.mul_assoc]
    _ = ((root E)⁻¹*root E)*(root E*(root E)⁻¹) := by rw [← root_square]; noncomm_ring
    _ = 1 := by rw [inv_mul_root E h, root_mul_inv E h, Matrix.one_mul]

theorem polar_isometry (E : Matrix β α ℂ) (h : ‖gram E-1‖<1) :
    (polar E)ᴴ * polar E=1 := polar_isometry_of_isUnit E (gram_isUnit E h)

theorem polar_mul_root (E : Matrix β α ℂ) (h : IsUnit (gram E)) :
    polar E*root E=E := by
  simp only [polar, Matrix.mul_assoc, inv_mul_root E h, Matrix.mul_one]

theorem gram_commute (E : Matrix β α ℂ)
    (U : Matrix.unitaryGroup α ℂ) (V : Matrix.unitaryGroup β ℂ)
    (h : (V : CMatrix β)*E=E*(U : CMatrix α)) :
    Commute (gram E) (U : CMatrix α) := by
  have ha : Eᴴ*(V : CMatrix β) = (U : CMatrix α)*Eᴴ := by
    have hc := congrArg Matrix.conjTranspose h
    simp only [Matrix.conjTranspose_mul] at hc
    have hc' := congrArg (fun M => (U : CMatrix α)*M*(V : CMatrix β)) hc
    have hu : (U : CMatrix α)*(U : CMatrix α)ᴴ=1 := U.property.2
    have hv : (V : CMatrix β)ᴴ*(V : CMatrix β)=1 := V.property.1
    simpa only [Matrix.mul_assoc, hv, Matrix.mul_one,
      ← Matrix.mul_assoc (U : CMatrix α) (U : CMatrix α)ᴴ,
      hu, Matrix.one_mul] using hc'.symm
  change Eᴴ*E*(U : CMatrix α)=(U : CMatrix α)*(Eᴴ*E)
  calc
    _ = Eᴴ*(E*(U : CMatrix α)) := Matrix.mul_assoc _ _ _
    _ = Eᴴ*((V : CMatrix β)*E) := by rw [h]
    _ = (U : CMatrix α)*(Eᴴ*E) := by rw [← Matrix.mul_assoc, ha, Matrix.mul_assoc]

theorem root_commute (E : Matrix β α ℂ)
    (U : Matrix.unitaryGroup α ℂ) (V : Matrix.unitaryGroup β ℂ)
    (h : (V : CMatrix β)*E=E*(U : CMatrix α)) :
    Commute (root E) (U : CMatrix α) := by
  simpa only [root, psdSqrt, CFC.sqrt_eq_cfc] using
    (gram_commute E U V h).cfc_nnreal NNReal.sqrt

theorem polar_covariant (E : Matrix β α ℂ) (hg : IsUnit (gram E))
    (U : Matrix.unitaryGroup α ℂ) (V : Matrix.unitaryGroup β ℂ)
    (h : (V : CMatrix β)*E=E*(U : CMatrix α)) :
    (V : CMatrix β)*polar E=polar E*(U : CMatrix α) := by
  have hs := (root_commute E U V h).eq
  have hi := congrArg (fun M => (root E)⁻¹*M*(root E)⁻¹) hs
  have hi' : (U : CMatrix α)*(root E)⁻¹=(root E)⁻¹*(U : CMatrix α) := by
    calc
      _ = (root E)⁻¹*(root E*(U : CMatrix α))*(root E)⁻¹ := by rw [← Matrix.mul_assoc, inv_mul_root E hg, Matrix.one_mul]
      _ = (root E)⁻¹*((U : CMatrix α)*root E)*(root E)⁻¹ := by rw [hs]
      _ = _ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, root_mul_inv E hg, Matrix.mul_one]
  simp only [polar]
  rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, hi', ← Matrix.mul_assoc]

#print axioms polar_isometry
#print axioms polar_covariant
end
end ICO.C6Polar
