import ICO.C6BosonicRight

/-! Polar normalization commutes with an actual relabelling of basis indices. -/
namespace ICO.C6PolarReindex
open QIT Matrix ICO.C6Polar ICO.C6BosonicPolar ICO.C6BosonicRight
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
set_option Elab.async false
variable {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [Fintype β] [DecidableEq β] [Nonempty β]

theorem sqrt_submatrix (M:CMatrix α) (hM:M.PosSemidef) (e:α≃α) :
    psdSqrt (M.submatrix e e)=(psdSqrt M).submatrix e e := by
  have hsq : (psdSqrt M).submatrix e e * (psdSqrt M).submatrix e e=M.submatrix e e := by
    rw [Matrix.submatrix_mul_equiv,psdSqrt_mul_self_of_posSemidef hM]
  have hp := (psdSqrt_pos M).submatrix e
  exact CFC.sqrt_unique hsq hp.nonneg

theorem polar_submatrix (E:Matrix β α ℂ) (ei:α≃α) (eo:β≃β) :
    polar (E.submatrix eo ei)=(polar E).submatrix eo ei := by
  have hg : gram (E.submatrix eo ei)=(gram E).submatrix ei ei := by
    simp only [gram,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv]
  simp only [polar,root,hg,sqrt_submatrix _ (gram_pos E),Matrix.inv_submatrix_equiv,
    Matrix.submatrix_mul_equiv]

theorem rightPolar_transpose {A:Type*} [Fintype A] [DecidableEq A] [Nonempty A] (n:ℕ) :
    rightPolar (A:=A) n=(leftPolar (A:=A) n).submatrix (sectorTranspose (n+1)) (sectorTranspose n) := by
  rw [rightPolar,rightInsertion_transpose,polar_submatrix]
  rfl

#print axioms polar_submatrix
#print axioms rightPolar_transpose
end
end ICO.C6PolarReindex

