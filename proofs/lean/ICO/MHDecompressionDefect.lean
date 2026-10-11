import ICO.MHRectangularAction

/-! Exact loss of a physical unitary query versus a decompressed partial
recording query. All dimensions may be finite and different. -/
namespace ICO.MHDecompressionDefect
open Matrix QIT ICO.MHRectangularAction ICO.MHProtocolOverlap
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
set_option maxHeartbeats 1600000
variable {H E : Type*} [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E]

theorem defect_gram (U : Matrix.unitaryGroup E ℂ) (D : Matrix E H ℂ)
    (W B : CMatrix H) (hD : D.conjTranspose*D=B)
    (hBW : B*W=W) (hBP : B*(W.conjTranspose*W)=W.conjTranspose*W)
    (hUW : (U : CMatrix E)*D*(W.conjTranspose*W)=D*W) :
    ((U : CMatrix E)*D-D*W).conjTranspose*((U : CMatrix E)*D-D*W)=B-W.conjTranspose*W := by
  have hU : (U : CMatrix E).conjTranspose*(U : CMatrix E)=1 := U.property.1
  have hfirst : ((U : CMatrix E)*D).conjTranspose*((U : CMatrix E)*D)=B := by
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : CMatrix E).conjTranspose (U : CMatrix E),hU,Matrix.one_mul,hD]
  have hcross : ((U : CMatrix E)*D).conjTranspose*(D*W)=W.conjTranspose*W := by
    rw [← hUW,← Matrix.mul_assoc,hfirst,hBP]
  have hcross' : (D*W).conjTranspose*((U : CMatrix E)*D)=W.conjTranspose*W := by
    have hh := congrArg Matrix.conjTranspose hcross
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose] using hh
  have hlast : (D*W).conjTranspose*(D*W)=W.conjTranspose*W := by
    simp only [Matrix.conjTranspose_mul,← Matrix.mul_assoc]
    rw [Matrix.mul_assoc W.conjTranspose D.conjTranspose D,hD,Matrix.mul_assoc,hBW]
  simp only [Matrix.conjTranspose_sub,Matrix.sub_mul,Matrix.mul_sub,hfirst,hcross,hcross',hlast]
  abel

theorem rectAct_norm_sq (M : Matrix E H ℂ) (x : EuclideanSpace ℂ H) :
    ‖rectAct M x‖^2=(⟪x,rectAct (M.conjTranspose*M) x⟫_ℂ).re := by
  rw [rectAct_mul,← rectAct_adjoint_inner]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (rectAct M x)).symm

theorem rectAct_matrix_sub (M N : Matrix E H ℂ) (x : EuclideanSpace ℂ H) :
    rectAct (M-N) x=rectAct M x-rectAct N x := by
  change WithLp.toLp 2 ((M-N)*ᵥWithLp.ofLp x)=WithLp.toLp 2 (M*ᵥWithLp.ofLp x)-WithLp.toLp 2 (N*ᵥWithLp.ofLp x)
  rw [Matrix.sub_mulVec]
  rfl

theorem defect_norm_sq (U : Matrix.unitaryGroup E ℂ) (D : Matrix E H ℂ)
    (W B : CMatrix H) (hD : D.conjTranspose*D=B)
    (hBW : B*W=W) (hBP : B*(W.conjTranspose*W)=W.conjTranspose*W)
    (hUW : (U : CMatrix E)*D*(W.conjTranspose*W)=D*W)
    (x : EuclideanSpace ℂ H) (hx : rectAct B x=x) :
    ‖rectAct (U : CMatrix E) (rectAct D x)-rectAct D (rectAct W x)‖^2=
      ‖x‖^2-‖rectAct W x‖^2 := by
  rw [← rectAct_mul,← rectAct_mul,← rectAct_matrix_sub,rectAct_norm_sq,
    defect_gram U D W B hD hBW hBP hUW,rectAct_matrix_sub,hx,inner_sub_right,Complex.sub_re]
  rw [show (⟪x,x⟫_ℂ).re=‖x‖^2 from inner_self_eq_norm_sq (𝕜 := ℂ) x,← rectAct_norm_sq W x]

theorem defect_norm_sq_le (U : Matrix.unitaryGroup E ℂ) (D : Matrix E H ℂ)
    (W B : CMatrix H) (hD : D.conjTranspose*D=B)
    (hBW : B*W=W) (hBP : B*(W.conjTranspose*W)=W.conjTranspose*W)
    (hUW : (U : CMatrix E)*D*(W.conjTranspose*W)=D*W)
    (x : EuclideanSpace ℂ H) (hx : rectAct B x=x) (hn : ‖x‖≤1) :
    ‖rectAct (U : CMatrix E) (rectAct D x)-rectAct D (rectAct W x)‖^2≤
      1-‖rectAct W x‖^2 := by
  rw [defect_norm_sq U D W B hD hBW hBP hUW x hx]
  nlinarith [norm_nonneg x]

#print axioms defect_norm_sq
end
end ICO.MHDecompressionDefect