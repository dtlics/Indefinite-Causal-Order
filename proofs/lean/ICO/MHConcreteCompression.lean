import ICO.MHCompressionFresh
import ICO.MHCompressionFreshInverse
import ICO.MHCompressionAlgebra

namespace ICO.MHConcreteCompression
open Matrix QIT ICO.MHWPartial ICO.MHPurifiedOracle ICO.MHRecordDecompression
  ICO.MHCompressionFresh ICO.MHCompressionFreshInverse ICO.MHCompressionAlgebra
noncomputable section
variable {A : Type*} [Fintype A] [DecidableEq A]
set_option maxHeartbeats 800000

theorem forward_domain_intertwine :
    (queryMatrix (A:=A))*D*(oracleW.conjTranspose*oracleW)=D*oracleW := by
  rw [oracle_gram,oracleW]
  exact compressed_domain_intertwine queryUnitary D leftW rightW leftProjection rightProjection
    (predicate_projection rightPredicate).isSelfAdjoint.star_eq right_domain
    forward_fresh_intertwine inverse_fresh_intertwine

theorem final_gram : (oracleW (A:=A))*oracleW.conjTranspose=
    rightProjection+leftW*leftW.conjTranspose := by
  have hz := congrArg Matrix.conjTranspose (leftW_mul_rightW (A:=A))
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_zero] at hz
  simp only [oracleW,Matrix.conjTranspose_add,Matrix.conjTranspose_conjTranspose,
    Matrix.add_mul,Matrix.mul_add,right_gram,leftW_mul_rightW,hz,add_zero,zero_add]
  exact add_comm _ _

theorem inverse_domain_intertwine :
    (queryMatrix (A:=A)).conjTranspose*D*(oracleW*oracleW.conjTranspose)=D*oracleW.conjTranspose := by
  rw [final_gram]
  have hh := compressed_inverse_domain_intertwine (queryUnitary (A:=A)) D leftW rightW leftProjection rightProjection
    (predicate_projection leftPredicate).isSelfAdjoint.star_eq left_domain
    forward_fresh_intertwine inverse_fresh_intertwine
  have he : rightW+leftW.conjTranspose=(oracleW (A:=A)).conjTranspose := by
    simp only [oracleW,Matrix.conjTranspose_add,Matrix.conjTranspose_conjTranspose]
    exact add_comm _ _
  rw [he] at hh
  exact hh

#print axioms forward_domain_intertwine
#print axioms inverse_domain_intertwine
end
end ICO.MHConcreteCompression
