import ICO.C6BosonicLengthMasks
import ICO.C6BosonicHistorySupport

/-! Local inverse replacement: a suppressed retrieval and a projection onto
the old label span are the two explicit error terms. -/
namespace ICO.C6BosonicInverseError
open QIT ICO.C6BosonicFreshContraction
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
variable {H : Type*} [Fintype H] [DecidableEq H]

def inverseExpression (F G : CMatrix H) : CMatrix H :=
  (1-G*G.conjTranspose)*F.conjTranspose+G*(1-F*F.conjTranspose)

theorem mul_contraction (A B : CMatrix H) (hA : ‖A‖≤1) (hB : ‖B‖≤1) : ‖A*B‖≤1 :=
  (norm_mul_le _ _).trans ((mul_le_mul hA hB (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))

theorem norm_mul_right_contraction (A B : CMatrix H) (hB : ‖B‖≤1) : ‖A*B‖≤‖A‖ :=
  (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left hB (norm_nonneg _)).trans_eq (mul_one _))

theorem norm_mul_left_contraction (A B : CMatrix H) (hA : ‖A‖≤1) : ‖A*B‖≤‖B‖ :=
  (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right hA (norm_nonneg _)).trans_eq (one_mul _))

theorem adjoint_target_bound (G P R Rp : CMatrix H)
    (hP : P.conjTranspose=P) (hR : IsStarProjection R) (hRp : Rp.conjTranspose=Rp)
    (hPR : P*R=R*P) (hpred : G.conjTranspose*R=Rp*G.conjTranspose*R) :
    ‖G.conjTranspose*R*P‖≤‖P*G*Rp‖ := by
  have hs : R.conjTranspose=R := hR.isSelfAdjoint.star_eq
  have hh := congrArg Matrix.conjTranspose hpred
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hs,hRp] at hh
  have he : (G.conjTranspose*R*P).conjTranspose=R*(P*G*Rp) := by
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hP,hs]
    rw [hh]
    simp only [←Matrix.mul_assoc]
    rw [hPR]
  rw [←Matrix.l2_opNorm_conjTranspose (G.conjTranspose*R*P),he]
  exact norm_mul_left_contraction _ _ (IsStarProjection.norm_le _ hR)

theorem inverse_replacement_bound (F G P B R : CMatrix H) (α β : ℝ)
    (hF : ‖F‖≤1) (hG : ‖G‖≤1) (hImage : IsStarProjection (F*F.conjTranspose))
    (hB : IsStarProjection B) (hR : IsStarProjection R)
    (hRF : R*F=F*R) (hRFs : R*F.conjTranspose=F.conjTranspose*R)
    (hRB : R*B=B*R) (hret : (1-P)*F.conjTranspose*B=0)
    (hα : ‖G.conjTranspose*R*P‖≤α) (hβ : ‖P*G*R‖≤β) :
    ‖(inverseExpression F G-freshInverse F G (1-P))*B*R‖≤α+β := by
  let T := F.conjTranspose*B*R
  let Z := (1-F*F.conjTranspose)*B*R
  have hBn := IsStarProjection.norm_le _ hB
  have hRn := IsStarProjection.norm_le _ hR
  have hRR : R*R=R := hR.isIdempotentElem.eq
  have hFs : ‖F.conjTranspose‖≤1 := by rwa [Matrix.l2_opNorm_conjTranspose]
  have hTn : ‖T‖≤1 := mul_contraction _ _ (mul_contraction _ _ hFs hBn) hRn
  have hZn : ‖Z‖≤1 := mul_contraction _ _
    (mul_contraction _ _ (IsStarProjection.norm_le _ hImage.one_sub) hBn) hRn
  have hPT : P*T=T := by
    have hh : F.conjTranspose*B-P*F.conjTranspose*B=0 := by
      simpa only [Matrix.sub_mul,Matrix.one_mul] using hret
    have hp := (sub_eq_zero.mp hh).symm
    dsimp only [T]
    simp only [←Matrix.mul_assoc]
    rw [hp]
  have hRT : R*T=T := by
    dsimp only [T]
    rw [←Matrix.mul_assoc,←Matrix.mul_assoc,hRFs]
    simp only [Matrix.mul_assoc]
    rw [←Matrix.mul_assoc R B,hRB]
    simp only [Matrix.mul_assoc]
    rw [hRR]
  have hRC : R*(1-F*F.conjTranspose)=(1-F*F.conjTranspose)*R := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul]
    rw [←Matrix.mul_assoc R F,hRF,Matrix.mul_assoc,hRFs,←Matrix.mul_assoc]
  have hRZ : R*Z=Z := by
    dsimp only [Z]
    rw [←Matrix.mul_assoc,←Matrix.mul_assoc,hRC]
    simp only [Matrix.mul_assoc]
    rw [←Matrix.mul_assoc R B,hRB]
    simp only [Matrix.mul_assoc]
    rw [hRR]
  have h1 : ‖G*G.conjTranspose*T‖≤α := by
    have he : G.conjTranspose*T=(G.conjTranspose*R*P)*T := by
      simp only [Matrix.mul_assoc]
      rw [hPT,hRT]
    rw [Matrix.mul_assoc,he]
    exact (norm_mul_left_contraction _ _ hG).trans
      ((norm_mul_right_contraction _ _ hTn).trans hα)
  have h2 : ‖P*G*Z‖≤β := by
    have he : P*G*Z=(P*G*R)*Z := by simp only [Matrix.mul_assoc]; rw [hRZ]
    rw [he]
    exact (norm_mul_right_contraction _ _ hZn).trans hβ
  have he : (inverseExpression F G-freshInverse F G (1-P))*B*R=
      -(G*G.conjTranspose*T)+P*G*Z := by
    dsimp only [inverseExpression,freshInverse,T,Z]
    noncomm_ring
  rw [he]
  exact (norm_add_le _ _).trans (by rw [norm_neg]; exact add_le_add h1 h2)

#print axioms adjoint_target_bound
#print axioms inverse_replacement_bound
end
end ICO.C6BosonicInverseError
