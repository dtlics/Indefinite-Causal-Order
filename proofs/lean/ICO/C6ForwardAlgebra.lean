import ICO.MHFockOracle
import ICO.MHFockKnownOperation

/-! The orthogonality estimate in the actual V-to-left-creation replacement.
The two error components lie in complementary left-image subspaces; their
combined factor has norm at most sqrt(2), rather than the triangle bound 2. -/
namespace ICO.C6ForwardAlgebra
open Matrix QIT ICO.MHFockOracle ICO.MHFockSpace ICO.MHFockSwap
open ICO.MHFockAlgebra ICO.MHBoundedRecording ICO.RecordingOracleAlgebra
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1600000
set_option Elab.async false
variable {I : Type*} [Fintype I] [DecidableEq I]

def errorFactor (A B : CMatrix I) : CMatrix I := (1-A*A.conjTranspose)-A*B

theorem factor_gram (A B : CMatrix I) (hA : A*A.conjTranspose*A=A)
    (hP : IsStarProjection (A*A.conjTranspose)) :
    (errorFactor A B).conjTranspose*errorFactor A B =
      (1-A*A.conjTranspose)+(A*B).conjTranspose*(A*B) := by
  let P := 1-A*A.conjTranspose
  have hPA : P*A=0 := by dsimp only [P]; noncomm_ring [hA]
  have hP' : P.conjTranspose=P := hP.one_sub.isSelfAdjoint.star_eq
  have hPP : P*P=P := hP.one_sub.isIdempotentElem.eq
  have hAP : A.conjTranspose*P=0 := by
    simpa only [Matrix.conjTranspose_mul, hP', Matrix.conjTranspose_zero] using
      congrArg Matrix.conjTranspose hPA
  change (P-A*B).conjTranspose*(P-A*B)=P+(A*B).conjTranspose*(A*B)
  calc
    _ = P*P-(P*A)*B-B.conjTranspose*(A.conjTranspose*P)+(A*B).conjTranspose*(A*B) := by
      rw [Matrix.conjTranspose_sub,hP',Matrix.conjTranspose_mul]
      noncomm_ring
    _ = _ := by rw [hPP,hPA,hAP]; simp

theorem factor_norm (A B : CMatrix I) (hA : A*A.conjTranspose*A=A)
    (hP : IsStarProjection (A*A.conjTranspose)) (hnA : ‖A‖≤1) (hnB : ‖B‖≤1) :
    ‖errorFactor A B‖≤Real.sqrt 2 := by
  have hPnorm := IsStarProjection.norm_le (1-A*A.conjTranspose) hP.one_sub
  have hAB : ‖A*B‖≤1 := by
    calc
      _ ≤ ‖A‖*‖B‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1*1 := mul_le_mul hnA hnB (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hg := norm_add_le (1-A*A.conjTranspose) ((A*B).conjTranspose*(A*B))
  rw [←factor_gram A B hA hP, Matrix.l2_opNorm_conjTranspose_mul_self,
    Matrix.l2_opNorm_conjTranspose_mul_self] at hg
  have hs : Real.sqrt 2 ^ 2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith [norm_nonneg (A*B),norm_nonneg (errorFactor A B),Real.sqrt_nonneg 2]

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem fullOracle_difference {t T : ℕ} (h : t+1≤T) :
    fullOracle (α:=α) h-leftOnFock h =
      errorFactor (leftOnFock h) (rightOnFock h)*(rightOnFock h).conjTranspose := by
  unfold fullOracle errorFactor
  noncomm_ring

theorem actual_factor_norm {t T : ℕ} (h : t+1≤T) (ht : t<Fintype.card α) :
    ‖errorFactor (leftOnFock (α:=α) h) (rightOnFock h)‖≤Real.sqrt 2 := by
  have hA : leftOnFock (α:=α) h*(leftOnFock h).conjTranspose*leftOnFock h=leftOnFock h := by
    rw [Matrix.mul_assoc,leftOnFock_gram h ht,leftOnFock_domain]
  have hP := image_projection (leftOnFock (α:=α) h)
    (sourceProjection (Nat.le_trans (Nat.le_succ t) h))
    (leftOnFock_gram h ht) (leftOnFock_domain h)
  have hBn : ‖rightOnFock (α:=α) h‖≤1 := by
    have hh := IsStarProjection.norm_le _
      (sourceProjection_projection (α:=α) (Nat.le_trans (Nat.le_succ t) h))
    rw [←rightOnFock_gram h ht,Matrix.l2_opNorm_conjTranspose_mul_self] at hh
    nlinarith [norm_nonneg (rightOnFock (α:=α) h)]
  exact factor_norm _ _ hA hP (leftOnFock_norm_le h ht) hBn

#print axioms actual_factor_norm
end
end ICO.C6ForwardAlgebra
