import ICO.C6FlagStack

namespace ICO.C6RawLocalAlgebra
open Matrix QIT ICO.C6FlagStack ICO.MHRectangularAction
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {X:Type*} [Fintype X] [DecidableEq X]

theorem compressed_difference (L L' B N R:CMatrix X)
    (hN:N*N=N) (hBN:B*N=N*B) :
    (L*B-L'*N*B)*N*R=(L-L')*B*N*R := by
  simp only [Matrix.sub_mul,Matrix.mul_assoc]
  rw [←Matrix.mul_assoc B N,hBN]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc N N,hN]

theorem masked_branch_difference (F G E Q N B R:CMatrix X)
    (hN:N*N=N) (hBN:B*N=N*B) (hNR:N*R=R*N) (hBR:B*R=R*B)
    (hCR:(1-F*Fᴴ)*R=R*(1-F*Fᴴ)) (b:Bool) :
    ((if b then Q*G*(1-F*Fᴴ) else Fᴴ)*B-
      (if b then Q*E*(1-F*Fᴴ) else Fᴴ)*N*B)*N*R=
      if b then Q*((G-E)*R)*(1-F*Fᴴ)*B*N else 0 := by
  rw [compressed_difference _ _ _ _ _ hN hBN]
  cases b
  · simp
  · simp only [if_true]
    rw [←Matrix.sub_mul,←Matrix.mul_sub]
    simp only [Matrix.mul_assoc]
    rw [hNR,←Matrix.mul_assoc B R,hBR]
    simp only [Matrix.mul_assoc]
    rw [←Matrix.mul_assoc (1-F*Fᴴ) R,hCR]
    simp only [Matrix.mul_assoc]

theorem one_birth_stack_bound (M:CMatrix X) (ε:ℝ) (hε:0≤ε) (hM:‖M‖≤ε) :
    ‖stack (fun b:Bool=>if b then M else 0)‖≤ε := by
  rw [←Real.sqrt_sq hε]
  apply stack_norm_of_energy _ _ (sq_nonneg _)
  intro x
  simp only [Fintype.sum_bool,Bool.false_eq_true,if_true,if_false]
  have hz:rectAct (0:CMatrix X) x=0:=by simp [ICO.MHRectangularAction.rectAct]
  rw [hz,norm_zero,zero_pow (by decide:2≠0),add_zero]
  have hh:‖rectAct M x‖≤ε*‖x‖:=(ICO.MHRectangularAction.rectAct_norm_le _ _).trans
    (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hh 2

theorem sandwich_bound (Q D C B N:CMatrix X) (ε:ℝ) (hε:0≤ε)
    (hQ:‖Q‖≤1) (hD:‖D‖≤ε) (hC:‖C‖≤1) (hB:‖B‖≤1) (hN:‖N‖≤1) :
    ‖Q*D*C*B*N‖≤ε := by
  have hQD:‖Q*D‖≤ε:=(Matrix.l2_opNorm_mul _ _).trans (by
    simpa only [one_mul] using mul_le_mul hQ hD (norm_nonneg _) (by norm_num:(0:ℝ)≤1))
  have hQDC:‖Q*D*C‖≤ε:=(Matrix.l2_opNorm_mul _ _).trans (by
    simpa only [mul_one] using mul_le_mul hQD hC (norm_nonneg _) hε)
  have hQDCB:‖Q*D*C*B‖≤ε:=(Matrix.l2_opNorm_mul _ _).trans (by
    simpa only [mul_one] using mul_le_mul hQDC hB (norm_nonneg _) hε)
  exact (Matrix.l2_opNorm_mul _ _).trans (by
    simpa only [mul_one] using mul_le_mul hQDCB hN (norm_nonneg _) hε)

#print axioms masked_branch_difference
end
end ICO.C6RawLocalAlgebra

