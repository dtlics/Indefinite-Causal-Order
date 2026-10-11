import ICO.MHProjectedMeanLoss
import ICO.C6PolarFock

/-! Coherent contraction of retrieval plus a fresh birth.  The support
condition is isolated for subsequent substitution of the actual label rule. -/
namespace ICO.C6BosonicFreshContraction
open QIT ICO.MHProtocolOverlap ICO.MHProjectedMeanLoss
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
set_option maxHeartbeats 1800000
variable {H : Type*} [Fintype H] [DecidableEq H]

def freshInverse (F G Q : CMatrix H) : CMatrix H :=
  F.conjTranspose + Q*G*(1-F*F.conjTranspose)

theorem retrieval_complement_energy (F : CMatrix H)
    (hF : IsStarProjection (F*F.conjTranspose)) (x : EuclideanSpace ℂ H) :
    ‖act F.conjTranspose x‖^2 + ‖act (1-F*F.conjTranspose) x‖^2 = ‖x‖^2 := by
  have hr : ‖act F.conjTranspose x‖^2=(⟪x,act (F*F.conjTranspose) x⟫_ℂ).re := by
    have hh := act_adjoint_inner F.conjTranspose x (act F.conjTranspose x)
    rw [Matrix.conjTranspose_conjTranspose,←act_mul] at hh
    exact (inner_self_eq_norm_sq (𝕜:=ℂ) _).symm.trans (congrArg Complex.re hh)
  rw [hr,projection_norm_square _ hF.one_sub,act_sub]
  have hi : act (1 : CMatrix H) x=x := by simp [act]
  rw [hi,inner_sub_right,Complex.sub_re]
  have hx : (⟪x,x⟫_ℂ).re=‖x‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) x
  rw [hx]
  ring

theorem freshInverse_vector_contraction (F G Q : CMatrix H)
    (hF : IsStarProjection (F*F.conjTranspose)) (hG : ‖G‖≤1)
    (hQ : IsStarProjection Q) (x : EuclideanSpace ℂ H)
    (hret : act Q (act F.conjTranspose x)=0) :
    ‖act (freshInverse F G Q) x‖≤‖x‖ := by
  let r := act F.conjTranspose x
  let b := act G (act (1-F*F.conjTranspose) x)
  have horth : ⟪r,act Q b⟫_ℂ=0 := by
    have hh := act_adjoint_inner Q r b
    have hQs : Q.conjTranspose=Q := hQ.isSelfAdjoint.star_eq
    change act Q r=0 at hret
    rw [hQs,hret,inner_zero_left] at hh
    exact hh.symm
  have hb : ‖act Q b‖≤‖act (1-F*F.conjTranspose) x‖ := by
    have h1 := (act_norm_le Q b).trans
      (mul_le_mul_of_nonneg_right (IsStarProjection.norm_le Q hQ) (norm_nonneg b))
    have h2 := (act_norm_le G (act (1-F*F.conjTranspose) x)).trans
      (mul_le_mul_of_nonneg_right hG (norm_nonneg _))
    exact (h1.trans_eq (one_mul _)).trans (h2.trans_eq (one_mul _))
  have he : act (freshInverse F G Q) x=r+act Q b := by
    simp only [freshInverse,act,map_add,ContinuousLinearMap.add_apply,map_mul]
    rfl
  rw [he]
  have hs := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero r (act Q b) horth
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have henergy := retrieval_complement_energy F hF x
  change ‖r‖^2+‖act (1-F*F.conjTranspose) x‖^2=‖x‖^2 at henergy
  nlinarith [norm_nonneg (r+act Q b),norm_nonneg x]

theorem freshInverse_supported_norm (F G Q B : CMatrix H)
    (hF : IsStarProjection (F*F.conjTranspose)) (hG : ‖G‖≤1)
    (hQ : IsStarProjection Q) (hB : IsStarProjection B)
    (hret : Q*F.conjTranspose*B=0) : ‖freshInverse F G Q*B‖≤1 := by
  change ‖act (freshInverse F G Q*B)‖≤1
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [act_mul,one_mul]
  have hz : act Q (act F.conjTranspose (act B x))=0 := by
    rw [←act_mul,←act_mul,hret]
    simp [act]
  have h := freshInverse_vector_contraction F G Q hF hG hQ (act B x) hz
  exact h.trans ((act_norm_le B x).trans
    ((mul_le_mul_of_nonneg_right (IsStarProjection.norm_le B hB) (norm_nonneg _)).trans_eq
      (one_mul _)))

#print axioms freshInverse_vector_contraction
#print axioms freshInverse_supported_norm
end
end ICO.C6BosonicFreshContraction
