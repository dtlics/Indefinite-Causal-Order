import ICO.MHAveragedHybrid
import ICO.MHOracleTransform

/-! Pointwise overlap estimates for actual query maps and projected losses. -/
namespace ICO.MHProtocolOverlap
open Matrix QIT
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
set_option maxHeartbeats 1200000
variable {H : Type*} [Fintype H] [DecidableEq H]

def act (M : CMatrix H) : EuclideanSpace ℂ H →L[ℂ] EuclideanSpace ℂ H :=
  (Matrix.toEuclideanCLM (n := H) (𝕜 := ℂ)) M

theorem act_mul (M N : CMatrix H) (x : EuclideanSpace ℂ H) :
    act (M*N) x=act M (act N x) := by
  simp only [act,map_mul]
  rfl

theorem act_sub (M N : CMatrix H) (x : EuclideanSpace ℂ H) :
    act (M-N) x=act M x-act N x := by
  simp only [act,map_sub,ContinuousLinearMap.sub_apply]

theorem act_norm_le (M : CMatrix H) (x : EuclideanSpace ℂ H) :
    ‖act M x‖≤‖M‖*‖x‖ :=
  ContinuousLinearMap.le_opNorm (act M) x

theorem act_adjoint_inner (M : CMatrix H) (x y : EuclideanSpace ℂ H) :
    ⟪act M x,y⟫_ℂ=⟪x,act M.conjTranspose y⟫_ℂ := by
  have hh := (ContinuousLinearMap.adjoint_inner_right (act M) x y).symm
  rw [← ContinuousLinearMap.star_eq_adjoint] at hh
  simpa only [act,← map_star,Matrix.star_eq_conjTranspose] using hh

theorem inner_change_le (x a b : EuclideanSpace ℂ H) (ε : ℝ)
    (hx : ‖x‖≤1) (hab : ‖a-b‖≤ε) :
    (⟪x,a⟫_ℂ).re-ε≤(⟪x,b⟫_ℂ).re := by
  have hh := (Complex.re_le_norm (⟪x,a-b⟫_ℂ)).trans (norm_inner_le_norm x (a-b))
  have hm := mul_le_mul_of_nonneg_right hx (norm_nonneg (a-b))
  rw [inner_sub_right,Complex.sub_re] at hh
  nlinarith

theorem matrix_inner_change_le (x y : EuclideanSpace ℂ H) (M N : CMatrix H) (ε : ℝ)
    (hx : ‖x‖≤1) (hy : ‖y‖≤1) (hMN : ‖M-N‖≤ε) :
    (⟪x,act M y⟫_ℂ).re-ε≤(⟪x,act N y⟫_ℂ).re := by
  apply inner_change_le x _ _ ε hx
  rw [← act_sub]
  have hh := act_norm_le (M-N) y
  have hm := mul_le_mul_of_nonneg_left hy (norm_nonneg (M-N))
  nlinarith

theorem projected_loss_overlap (x y : EuclideanSpace ℂ H) (P B : CMatrix H)
    (hx : ‖x‖≤1) (hB : B.conjTranspose=B) (hBx : act B x=x) :
    (⟪x,y⟫_ℂ).re-‖act (B-P) y‖≤(⟪x,act P y⟫_ℂ).re := by
  have he : ⟪x,act B y⟫_ℂ=⟪x,y⟫_ℂ := by
    have hh := act_adjoint_inner B x y
    rw [hBx,hB] at hh
    exact hh.symm
  have hh := inner_change_le x (act B y) (act P y) ‖act (B-P) y‖ hx (by rw [← act_sub])
  rwa [he] at hh

#print axioms matrix_inner_change_le
#print axioms projected_loss_overlap
end
end ICO.MHProtocolOverlap
