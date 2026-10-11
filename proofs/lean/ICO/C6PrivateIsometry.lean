import ICO.MHDecompressionErasure

/-! Private isometric encodings preserve the literal reduced matrix, including
arbitrary mixed inputs and arbitrary entanglement with visible memory. -/
namespace ICO.C6PrivateIsometry
open QIT
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {H K R E:Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Fintype E] [DecidableEq E]

def block (X:CMatrix (H×R)) (a b:H) : CMatrix R := fun i j=>X (a,i) (b,j)

theorem sandwich_block (J:Matrix E R ℂ) (X:CMatrix (H×R)) (a b:H) :
    block (Matrix.kronecker (1:CMatrix H) J*X*
      (Matrix.kronecker (1:CMatrix H) J).conjTranspose) a b =
      J*block X a b*J.conjTranspose := by
  ext e f
  simp [block,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply,Fintype.sum_prod_type,
    Finset.sum_mul,Finset.mul_sum,mul_assoc,apply_ite,Finset.sum_ite_irrel]

theorem private_erasure_matrix (J:Matrix E R ℂ) (hJ:J.conjTranspose*J=1)
    (X:CMatrix (H×R)) :
    partialTraceB (Matrix.kronecker (1:CMatrix H) J*X*
      (Matrix.kronecker (1:CMatrix H) J).conjTranspose)=partialTraceB X := by
  ext a b
  change (block (Matrix.kronecker (1:CMatrix H) J*X*
    (Matrix.kronecker (1:CMatrix H) J).conjTranspose) a b).trace=(block X a b).trace
  rw [sandwich_block,Matrix.trace_mul_cycle,hJ,Matrix.one_mul]

theorem known_intertwine (J:Matrix E R ℂ) (V:Matrix K H ℂ) :
    Matrix.kronecker V (1:CMatrix E)*Matrix.kronecker (1:CMatrix H) J=
      Matrix.kronecker (1:CMatrix K) J*Matrix.kronecker V (1:CMatrix R) := by
  simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.mul_one,Matrix.one_mul]

#print axioms private_erasure_matrix
end
end ICO.C6PrivateIsometry
