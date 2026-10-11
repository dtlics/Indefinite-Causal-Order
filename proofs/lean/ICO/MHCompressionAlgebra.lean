import ICO.MHWPartial

/-! The two fresh-oracle identities imply the complete W-domain identity. -/
namespace ICO.MHCompressionAlgebra
open Matrix QIT
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1000000
variable {H E : Type*} [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E]

theorem compressed_domain_intertwine (U : Matrix.unitaryGroup E ℂ)
    (D : Matrix E H ℂ) (L R PL PR : CMatrix H)
    (hPR : PR.conjTranspose=PR) (hR : R*PR=R)
    (hL : (U : CMatrix E)*D*PL=D*L)
    (hRi : (U : CMatrix E).conjTranspose*D*PR=D*R) :
    (U : CMatrix E)*D*(PL+R*R.conjTranspose)=D*(L+R.conjTranspose) := by
  have hU : (U : CMatrix E)*(U : CMatrix E).conjTranspose=1 := U.property.2
  have hret : (U : CMatrix E)*D*R=D*PR := by
    rw [Matrix.mul_assoc,← hRi]
    simp only [← Matrix.mul_assoc]
    rw [hU,Matrix.one_mul]
  have hRa : PR*R.conjTranspose=R.conjTranspose := by
    have he := congrArg Matrix.conjTranspose hR
    simpa only [Matrix.conjTranspose_mul,hPR] using he
  rw [Matrix.mul_add,Matrix.mul_add,hL]
  rw [← Matrix.mul_assoc,hret,Matrix.mul_assoc,hRa]

theorem compressed_inverse_domain_intertwine (U : Matrix.unitaryGroup E ℂ)
    (D : Matrix E H ℂ) (L R PL PR : CMatrix H)
    (hPL : PL.conjTranspose=PL) (hL : L*PL=L)
    (hLf : (U : CMatrix E)*D*PL=D*L)
    (hR : (U : CMatrix E).conjTranspose*D*PR=D*R) :
    (U : CMatrix E).conjTranspose*D*(PR+L*L.conjTranspose)=D*(R+L.conjTranspose) := by
  have hh := compressed_domain_intertwine U⁻¹ D R L PR PL hPL hL hR
    (by simpa only [Matrix.UnitaryGroup.inv_val,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using hLf)
  simpa only [Matrix.UnitaryGroup.inv_val,Matrix.star_eq_conjTranspose] using hh

#print axioms compressed_domain_intertwine
#print axioms compressed_inverse_domain_intertwine
end
end ICO.MHCompressionAlgebra
