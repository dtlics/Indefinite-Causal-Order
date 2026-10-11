import ICO.C6Polar
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

namespace ICO.C6Polar
open Matrix QIT
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
set_option Elab.async false
variable {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [Fintype β] [DecidableEq β] [Nonempty β]
local instance normMatrixNonUnitalCStarForNorm (n : Type*) [Fintype n] [DecidableEq n] :
    NonUnitalCStarAlgebra (CMatrix n) := ⟨⟩
local instance normMatrixCStarForNorm (n : Type*) [Fintype n] [DecidableEq n] :
    CStarAlgebra (CMatrix n) := ⟨⟩

theorem abs_sqrt_sub_one_le (x : ℝ) (hx : 0≤x) :
    |Real.sqrt x-1|≤|x-1| := by
  have hs := Real.sq_sqrt hx
  have hn := Real.sqrt_nonneg x
  have hprod : (Real.sqrt x-1)*(Real.sqrt x+1)=x-1 := by nlinarith
  calc
    _ = |Real.sqrt x-1| * 1 := by ring
    _ ≤ |Real.sqrt x-1| * |Real.sqrt x+1| := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [abs_of_nonneg (by positivity)]
      linarith
    _ = |x-1| := by rw [← abs_mul, hprod]

theorem sqrt_defect_le (G : CMatrix α) (hG : G.PosSemidef) :
    ‖psdSqrt G-1‖≤‖G-1‖ := by
  have he : psdSqrt G-1=cfc (fun x : ℝ => Real.sqrt x-1) G := by
    rw [cfc_sub Real.sqrt (fun _ : ℝ=>1) G, cfc_const_one ℝ G]
    rw [psdSqrt, CFC.sqrt_eq_real_sqrt G hG.nonneg, cfcₙ_eq_cfc]
  rw [he]
  apply norm_cfc_le (norm_nonneg _)
  intro x hx
  have hxp : 0≤x := spectrum_nonneg_of_nonneg hG.nonneg hx
  have hn := norm_apply_le_norm_cfc (fun x : ℝ=>x-1) G hx
    (by fun_prop) hG.isHermitian
  have he' : cfc (fun x : ℝ=>x-1) G=G-1 := by
    rw [cfc_sub (fun x : ℝ=>x) (fun _ : ℝ=>1) G, cfc_id' ℝ G, cfc_const_one ℝ G]
  have hn' : ‖x-1‖≤‖G-1‖ := by
    convert hn using 1
    congr 1
    exact he'.symm
  exact (abs_sqrt_sub_one_le x hxp).trans hn'

theorem polar_norm_one (E : Matrix β α ℂ) (hg : IsUnit (gram E)) :
    ‖polar E‖=1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (polar E)
  rw [polar_isometry_of_isUnit E hg, norm_one] at h
  have hn := norm_nonneg (polar E)
  nlinarith

theorem polar_distance_le (E : Matrix β α ℂ) (hg : IsUnit (gram E)) :
    ‖E-polar E‖≤‖gram E-1‖ := by
  have he : E-polar E=polar E*(root E-1) := by
    rw [Matrix.mul_sub, Matrix.mul_one, polar_mul_root E hg]
  rw [he]
  calc
    _ ≤ ‖polar E‖*‖root E-1‖ := Matrix.l2_opNorm_mul _ _
    _ = ‖root E-1‖ := by rw [polar_norm_one E hg, one_mul]
    _ ≤ ‖gram E-1‖ := sqrt_defect_le (gram E) (gram_pos E)

theorem polar_distance_le_of_defect_lt_one (E : Matrix β α ℂ)
    (hg : ‖gram E-1‖<1) : ‖E-polar E‖≤‖gram E-1‖ :=
  polar_distance_le E (gram_isUnit E hg)

#print axioms sqrt_defect_le
#print axioms polar_distance_le_of_defect_lt_one
end
end ICO.C6Polar
