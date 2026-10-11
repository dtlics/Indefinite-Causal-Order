import ICO.MHProtocolOverlap
import ICO.MHFockFullCovariance

/-! One query's bilinear overlap loss, with the actual covariance defect
and projected recording-domain loss kept as separately proved quantities. -/
namespace ICO.MHOverlapStep
open Matrix QIT ICO.MHProtocolOverlap ICO.MHFockFullCovariance
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
variable {H : Type*} [Fintype H] [DecidableEq H]

theorem unitary_inner (U : Matrix.unitaryGroup H ℂ) (x y : EuclideanSpace ℂ H) :
    ⟪act (U : CMatrix H) x,act (U : CMatrix H) y⟫_ℂ=⟪x,y⟫_ℂ := by
  have hU : (U : CMatrix H).conjTranspose*(U : CMatrix H)=1 := U.property.1
  rw [act_adjoint_inner,← act_mul,hU]
  simp [act]

theorem unitary_act_norm (U : Matrix.unitaryGroup H ℂ) (x : EuclideanSpace ℂ H) :
    ‖act (U : CMatrix H) x‖=‖x‖ := ICO.PureHybrid.unitary_action_norm U x

theorem covariance_overlap_defect (W V P : CMatrix H)
    (C D Q : Matrix.unitaryGroup H ℂ) (ε : ℝ)
    (hW : ‖W‖≤1) (hWV : W.conjTranspose*V=P)
    (hcov : ‖(Q : CMatrix H)*V-(D : CMatrix H)*V*(C : CMatrix H)*(Q : CMatrix H)‖≤ε) :
    ‖((D : CMatrix H)*W*(C : CMatrix H)).conjTranspose*(Q : CMatrix H)*V-
      (C : CMatrix H).conjTranspose*P*(C : CMatrix H)*(Q : CMatrix H)‖≤ε := by
  have hD : (D : CMatrix H).conjTranspose*(D : CMatrix H)=1 := D.property.1
  have he : ((D : CMatrix H)*W*(C : CMatrix H)).conjTranspose*(Q : CMatrix H)*V-
      (C : CMatrix H).conjTranspose*P*(C : CMatrix H)*(Q : CMatrix H) =
      (C : CMatrix H).conjTranspose*W.conjTranspose*(D : CMatrix H).conjTranspose*
        ((Q : CMatrix H)*V-(D : CMatrix H)*V*(C : CMatrix H)*(Q : CMatrix H)) := by
    rw [Matrix.mul_sub]
    simp only [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc,← Matrix.mul_assoc (D : CMatrix H).conjTranspose
      (D : CMatrix H),hD,Matrix.one_mul]
    simp only [← Matrix.mul_assoc, hWV]
  rw [he]
  have hC := ICO.MHSectorCovariance.unitary_norm_le C
  have hDn := ICO.MHSectorCovariance.unitary_norm_le D
  have hprefix : ‖(C : CMatrix H).conjTranspose*W.conjTranspose*(D : CMatrix H).conjTranspose‖≤1 := by
    have hh := (norm_mul_le ((C : CMatrix H).conjTranspose*W.conjTranspose)
      (D : CMatrix H).conjTranspose).trans (mul_le_mul_of_nonneg_right
        (norm_mul_le _ _) (norm_nonneg _))
    simp only [Matrix.l2_opNorm_conjTranspose] at hh
    have hm := mul_le_mul (mul_le_mul hC hW (norm_nonneg W) (by norm_num))
      hDn (norm_nonneg (D : CMatrix H)) (by norm_num)
    exact hh.trans (by simpa using hm)
  exact (left_mul_contraction _ _ hprefix).trans hcov

theorem query_overlap_step (x y : EuclideanSpace ℂ H) (W V P B : CMatrix H)
    (C D Q : Matrix.unitaryGroup H ℂ) (ε : ℝ)
    (hx : ‖x‖≤1) (hy : ‖y‖≤1) (hW : ‖W‖≤1)
    (hWV : W.conjTranspose*V=P)
    (hB : B.conjTranspose=B) (hBx : act B (act (C : CMatrix H) x)=act (C : CMatrix H) x)
    (hcov : ‖(Q : CMatrix H)*V-(D : CMatrix H)*V*(C : CMatrix H)*(Q : CMatrix H)‖≤ε) :
    (⟪x,act (Q : CMatrix H) y⟫_ℂ).re-
        ‖act (B-P) (act (C : CMatrix H) (act (Q : CMatrix H) y))‖-ε ≤
      (⟪act ((D : CMatrix H)*W*(C : CMatrix H)) x,
        act (Q : CMatrix H) (act V y)⟫_ℂ).re := by
  have hl := projected_loss_overlap (act (C : CMatrix H) x)
    (act (C : CMatrix H) (act (Q : CMatrix H) y)) P B
    (by rwa [unitary_act_norm]) hB hBx
  rw [unitary_inner] at hl
  have hc := covariance_overlap_defect W V P C D Q ε hW hWV hcov
  have hm := matrix_inner_change_le x y
    ((C : CMatrix H).conjTranspose*P*(C : CMatrix H)*(Q : CMatrix H))
    (((D : CMatrix H)*W*(C : CMatrix H)).conjTranspose*(Q : CMatrix H)*V)
    ε hx hy (by rwa [norm_sub_rev])
  have he : ⟪x,act ((C : CMatrix H).conjTranspose*P*(C : CMatrix H)*(Q : CMatrix H)) y⟫_ℂ =
      ⟪act (C : CMatrix H) x,act P (act (C : CMatrix H) (act (Q : CMatrix H) y))⟫_ℂ := by
    simp only [act_mul]
    rw [← act_adjoint_inner]
  have he' : ⟪x,act (((D : CMatrix H)*W*(C : CMatrix H)).conjTranspose*(Q : CMatrix H)*V) y⟫_ℂ =
      ⟪act ((D : CMatrix H)*W*(C : CMatrix H)) x,act (Q : CMatrix H) (act V y)⟫_ℂ := by
    simp only [act_mul]
    rw [← act_adjoint_inner]
    simp only [act_mul]
  rw [he,he'] at hm
  linarith

#print axioms query_overlap_step
end
end ICO.MHOverlapStep
