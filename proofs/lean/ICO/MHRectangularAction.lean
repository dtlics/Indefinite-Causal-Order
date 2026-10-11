import ICO.MHProjectedMeanLoss

/-! Literal rectangular matrix action and isometric public operations. -/
namespace ICO.MHRectangularAction
open Matrix QIT ICO.MHProtocolOverlap ICO.MHProjectedMeanLoss ICO.CausalReverse
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
set_option maxHeartbeats 1800000
variable {H K F : Type*} [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype F] [DecidableEq F]

def rectAct (M : Matrix K H ℂ) : EuclideanSpace ℂ H→ₗ[ℂ]EuclideanSpace ℂ K :=
  Matrix.toEuclideanLin M

theorem rectAct_square (M : CMatrix H) (x : EuclideanSpace ℂ H) :
    rectAct M x=act M x := rfl

theorem rectAct_mul (L : Matrix F K ℂ) (M : Matrix K H ℂ) (x : EuclideanSpace ℂ H) :
    rectAct (L*M) x=rectAct L (rectAct M x) := by
  change WithLp.toLp 2 ((L*M)*ᵥWithLp.ofLp x)=
    WithLp.toLp 2 (L*ᵥ(M*ᵥWithLp.ofLp x))
  rw [Matrix.mulVec_mulVec]

theorem rectAct_adjoint_inner (M : Matrix K H ℂ)
    (x : EuclideanSpace ℂ H) (y : EuclideanSpace ℂ K) :
    ⟪rectAct M x,y⟫_ℂ=⟪x,rectAct M.conjTranspose y⟫_ℂ := by
  have hh := (LinearMap.adjoint_inner_right (rectAct M) x y).symm
  simpa only [rectAct,Matrix.toEuclideanLin_conjTranspose_eq_adjoint] using hh

theorem rectAct_norm_le (M : Matrix K H ℂ) (x : EuclideanSpace ℂ H) :
    ‖rectAct M x‖≤‖M‖*‖x‖ := Matrix.l2_opNorm_mulVec M x

theorem rectAct_inner (M : Matrix K H ℂ) (hM : M.conjTranspose*M=1)
    (x y : EuclideanSpace ℂ H) : ⟪rectAct M x,rectAct M y⟫_ℂ=⟪x,y⟫_ℂ := by
  rw [rectAct_adjoint_inner,←rectAct_mul,hM]
  simp only [rectAct,Matrix.toEuclideanLin_apply,Matrix.one_mulVec,WithLp.toLp_ofLp]

theorem rectAct_norm (M : Matrix K H ℂ) (hM : M.conjTranspose*M=1)
    (x : EuclideanSpace ℂ H) : ‖rectAct M x‖=‖x‖ := by
  have hh := congrArg Complex.re (rectAct_inner M hM x x)
  have h1 : (⟪rectAct M x,rectAct M x⟫_ℂ).re=‖rectAct M x‖^2 :=
    inner_self_eq_norm_sq (𝕜:=ℂ) (rectAct M x)
  have h2 : (⟪x,x⟫_ℂ).re=‖x‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) x
  rw [h1,h2] at hh
  nlinarith [norm_nonneg x,norm_nonneg (rectAct M x)]

def matrixIsometry (M : Matrix K H ℂ) (hM : M.conjTranspose*M=1) :
    EuclideanSpace ℂ H→ₗᵢ[ℂ]EuclideanSpace ℂ K :=
  { toLinearMap := rectAct M
    norm_map' := rectAct_norm M hM }

theorem compressed_quadratic (J : Matrix K H ℂ) (M : CMatrix K) (z : EuclideanSpace ℂ H) :
    tracePair (ICO.PureHybrid.outer (rectAct J z) (rectAct J z)) M=
      tracePair (ICO.PureHybrid.outer z z) (J.conjTranspose*M*J) := by
  rw [quadratic_trace,quadratic_trace]
  change (⟪rectAct J z,rectAct M (rectAct J z)⟫_ℂ).re=
    (⟪z,rectAct (J.conjTranspose*M*J) z⟫_ℂ).re
  rw [rectAct_adjoint_inner,rectAct_mul,rectAct_mul]

#print axioms matrixIsometry
#print axioms compressed_quadratic
end
end ICO.MHRectangularAction
