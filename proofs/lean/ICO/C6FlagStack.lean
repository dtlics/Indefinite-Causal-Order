import ICO.C6BosonicFreshContraction
import ICO.C6PolarCompression
import ICO.MHRectangularAction
import ICO.MHFockKnownOperation

/-! Norms of literal orthogonally flagged matrices. -/
namespace ICO.C6FlagStack
open QIT ICO.MHRectangularAction ICO.MHUniqueNorm ICO.MHBlockNorm
  ICO.MHFockKnownOperation ICO.C6BosonicFreshContraction ICO.MHProtocolOverlap ICO.C6PolarCompression
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {X Y Z J:Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z] [Fintype J] [DecidableEq J]

def stack (F:J→Matrix Y X ℂ) : Matrix (J×Y) X ℂ := fun o i=>F o.1 o.2 i

theorem stack_norm_sq (F:J→Matrix Y X ℂ) (x:EuclideanSpace ℂ X) :
    ‖rectAct (stack F) x‖^2=∑j,‖rectAct (F j) x‖^2 := by
  simp only [rectAct,Matrix.toEuclideanLin_apply,PiLp.norm_sq_eq_of_L2,Fintype.sum_prod_type]
  rfl

theorem stack_norm_of_energy (F:J→Matrix Y X ℂ) (B:ℝ) (hB:0≤B)
    (h:∀x:EuclideanSpace ℂ X,∑j,‖rectAct (F j) x‖^2≤B*‖x‖^2) :
    ‖stack F‖≤Real.sqrt B := by
  apply matrix_norm_le_of_square_sum _ B hB
  intro v
  have hh:=h (WithLp.toLp 2 v)
  rw [←stack_norm_sq] at hh
  simpa only [rectAct,Matrix.toEuclideanLin_apply,WithLp.ofLp_toLp,PiLp.norm_sq_eq_of_L2] using hh

theorem stack_energy (F:J→Matrix Y X ℂ) (b:ℝ) (hb:0≤b) (hF:‖stack F‖≤b)
    (x:EuclideanSpace ℂ X) :
    ∑j,‖rectAct (F j) x‖^2≤b^2*‖x‖^2 := by
  rw [←stack_norm_sq]
  have hh:‖rectAct (stack F) x‖≤b*‖x‖:=
    (rectAct_norm_le _ _).trans (mul_le_mul_of_nonneg_right hF (norm_nonneg x))
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hh 2

theorem stack_common_norm (L:Matrix Z Y ℂ) (F:J→Matrix Y X ℂ)
    (hL:‖L‖≤1) (hF:‖stack F‖≤1) : ‖stack (fun j=>L*F j)‖≤1 := by
  rw [←Real.sqrt_one]
  apply stack_norm_of_energy _ _ (by norm_num)
  intro x
  calc
    _ ≤ ∑j,‖rectAct (F j) x‖^2 := by
      apply Finset.sum_le_sum
      intro j hj
      rw [rectAct_mul]
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (rectAct_norm_le _ _).trans
        ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))
    _ ≤ 1*‖x‖^2 := by simpa only [one_pow] using stack_energy F 1 (by norm_num) hF x

theorem stack_right (F:J→Matrix Y X ℂ) (B:Matrix X Z ℂ) :
    stack (fun j=>F j*B)=stack F*B := by ext o i; rfl

theorem split_stack_norm (F G:CMatrix X) (hF:IsStarProjection (F*F.conjTranspose))
    (hG:‖G‖≤1) :
    ‖stack (fun b:Bool=>if b then G*(1-F*F.conjTranspose) else F.conjTranspose)‖≤1 := by
  rw [←Real.sqrt_one]
  apply stack_norm_of_energy _ _ (by norm_num)
  intro x
  simp only [Fintype.sum_bool,Bool.false_eq_true,if_true,if_false,rectAct_mul,one_mul]
  have hb:‖rectAct G (rectAct (1-F*F.conjTranspose) x)‖≤‖rectAct (1-F*F.conjTranspose) x‖ :=
    (rectAct_norm_le _ _).trans
      ((mul_le_mul_of_nonneg_right hG (norm_nonneg _)).trans_eq (one_mul _))
  have he:=retrieval_complement_energy F hF x
  change ‖rectAct F.conjTranspose x‖^2+‖rectAct (1-F*F.conjTranspose) x‖^2=‖x‖^2 at he
  have hh:=pow_le_pow_left₀ (norm_nonneg _) hb 2
  linarith

theorem stack_tensor (F:J→Matrix Y X ℂ) (M:Type*) [Fintype M] [DecidableEq M] :
    stack (fun j=>Matrix.kronecker (F j) (1:CMatrix M))=
      (Matrix.kronecker (stack F) (1:CMatrix M)).submatrix
        (Equiv.prodAssoc J Y M).symm (Equiv.refl (X×M)) := by
  ext o i
  rfl

theorem stack_tensor_norm (F:J→Matrix Y X ℂ) (M:Type*) [Fintype M] [DecidableEq M] :
    ‖stack (fun j=>Matrix.kronecker (F j) (1:CMatrix M))‖≤‖stack F‖ := by
  rw [stack_tensor]
  exact (rectangular_reindex_norm_le _ _ _).trans (tensor_identity_norm_le _)

theorem split_compressed_norm (F E Q N B:CMatrix X)
    (hF:IsStarProjection (F*F.conjTranspose)) (hN:IsStarProjection N)
    (hc:N*(1-F*F.conjTranspose)=(1-F*F.conjTranspose)*N)
    (hE:‖Q*E*N‖≤1) (hB:‖B‖≤1) :
    ‖stack (fun b:Bool=>(if b then Q*E*(1-F*F.conjTranspose) else F.conjTranspose)*N*B)‖≤1 := by
  have he:(fun b:Bool=>(if b then Q*E*(1-F*F.conjTranspose) else F.conjTranspose)*N*B)=
      (fun b:Bool=>(if b then (Q*E*N)*(1-F*F.conjTranspose) else F.conjTranspose)*N*B) := by
    funext b
    cases b
    · rfl
    · change (Q*E*(1-F*F.conjTranspose))*N*B=(Q*E*N*(1-F*F.conjTranspose))*N*B
      rw [Matrix.mul_assoc (Q*E) N,hc]
      simp only [Matrix.mul_assoc]
      rw [←Matrix.mul_assoc N N,hN.isIdempotentElem.eq]
  rw [he,stack_right,stack_right]
  have hs:=split_stack_norm F (Q*E*N) hF hE
  have hn:‖N‖≤1:=IsStarProjection.norm_le _ hN
  have hsn:‖stack (fun b:Bool=>if b then (Q*E*N)*(1-F*F.conjTranspose) else F.conjTranspose)*N‖≤1:=
    (Matrix.l2_opNorm_mul _ _).trans (by
      simpa only [one_mul] using mul_le_mul hs hn (norm_nonneg N) (by norm_num : (0:ℝ)≤1))
  exact (Matrix.l2_opNorm_mul _ _).trans (by
    simpa only [one_mul] using mul_le_mul hsn hB (norm_nonneg B) (by norm_num : (0:ℝ)≤1))
#print axioms split_stack_norm
end
end ICO.C6FlagStack



