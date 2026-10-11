import ICO.MHOracleCovariance

/-! Exact change of query and record coordinates for the full recording oracle. -/
namespace ICO.MHOracleTransform
open Matrix QIT ICO.MHOracleCovariance
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
variable {H : Type*} [Fintype H] [DecidableEq H]

theorem fullOracle_transform (A B : CMatrix H)
    (C D Q : Matrix.unitaryGroup H ℂ) :
    fullOracle
      ((Q : CMatrix H).conjTranspose*(D : CMatrix H)*A*(C : CMatrix H)*(Q : CMatrix H))
      ((Q : CMatrix H).conjTranspose*(C : CMatrix H).conjTranspose*B*
        (D : CMatrix H).conjTranspose*(Q : CMatrix H)) =
      (Q : CMatrix H).conjTranspose*(D : CMatrix H)*fullOracle A B*(C : CMatrix H)*(Q : CMatrix H) := by
  have hC : (C : CMatrix H)*(C : CMatrix H).conjTranspose=1 := C.property.2
  have hD : (D : CMatrix H).conjTranspose*(D : CMatrix H)=1 := D.property.1
  have hQ : (Q : CMatrix H)*(Q : CMatrix H).conjTranspose=1 := Q.property.2
  simp only [fullOracle, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc (Q : CMatrix H) (Q : CMatrix H).conjTranspose,
    hQ, Matrix.one_mul, ← Matrix.mul_assoc (C : CMatrix H) (C : CMatrix H).conjTranspose,
    hC, ← Matrix.mul_assoc (D : CMatrix H).conjTranspose (D : CMatrix H), hD]

#print axioms fullOracle_transform
end
end ICO.MHOracleTransform
