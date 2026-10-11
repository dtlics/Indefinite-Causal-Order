import ICO.C6PolarNorm

/-! Quantitative conditioning of the actual polar normalization. -/
namespace ICO.C6BosonicInverseRoot
open Matrix QIT ICO.C6Polar
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
variable {a b : Type*} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]

theorem inverse_root_square_bound (E : Matrix b a ℂ) (δ : ℝ)
    (hδ : δ < 1) (hE : ‖gram E - 1‖ ≤ δ) :
    ‖(root E)⁻¹‖^2 ≤ 1 / (1-δ) := by
  have hg := gram_isUnit E (hE.trans_lt hδ)
  let H : CMatrix a := (root E)⁻¹ * (root E)⁻¹
  have hGH : gram E * H = 1 := by
    rw [←root_square E]
    dsimp [H]
    calc
      _ = root E * (root E * (root E)⁻¹) * (root E)⁻¹ := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [root_mul_inv E hg,Matrix.mul_one,root_mul_inv E hg]
  have hrepr : H = 1 + (1-gram E)*H := by
    rw [Matrix.sub_mul,Matrix.one_mul,hGH]
    abel
  have hH : ‖H‖ ≤ 1 + δ*‖H‖ := by
    calc
      _ = ‖1+(1-gram E)*H‖ := congrArg norm hrepr
      _ ≤ ‖(1 : CMatrix a)‖ + ‖(1-gram E)*H‖ := norm_add_le _ _
      _ ≤ 1 + δ*‖H‖ := by
        rw [norm_one]
        apply add_le_add le_rfl
        apply (Matrix.l2_opNorm_mul _ _).trans
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rwa [norm_sub_rev]
  have hn : ‖(root E)⁻¹‖^2 = ‖H‖ := by
    have hi : ((root E)⁻¹).conjTranspose=(root E)⁻¹ := by
      rw [Matrix.conjTranspose_nonsing_inv,root_hermitian]
    rw [pow_two,←Matrix.l2_opNorm_conjTranspose_mul_self,hi]
  rw [hn]
  apply (le_div_iff₀ (by linarith : 0<1-δ)).2
  nlinarith

theorem compressed_polar_square_bound (E : Matrix b a ℂ) (P : CMatrix b)
    (δ β : ℝ) (hδ : δ < 1) (hE : ‖gram E-1‖ ≤ δ)
    (hP : ‖P*E‖^2 ≤ β) : ‖P*polar E‖^2 ≤ β/(1-δ) := by
  have hβ : 0 ≤ β := (sq_nonneg _).trans hP
  have hmul : ‖P*polar E‖ ≤ ‖P*E‖ * ‖(root E)⁻¹‖ := by
    rw [polar,←Matrix.mul_assoc]
    exact Matrix.l2_opNorm_mul _ _
  have hs : ‖P*polar E‖^2 ≤ (‖P*E‖ * ‖(root E)⁻¹‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hmul 2
  calc
    _ ≤ ‖P*E‖^2 * ‖(root E)⁻¹‖^2 := by simpa only [mul_pow] using hs
    _ ≤ β * (1/(1-δ)) := mul_le_mul hP (inverse_root_square_bound E δ hδ hE)
      (sq_nonneg _) hβ
    _ = β/(1-δ) := by ring

#print axioms compressed_polar_square_bound
end
end ICO.C6BosonicInverseRoot
