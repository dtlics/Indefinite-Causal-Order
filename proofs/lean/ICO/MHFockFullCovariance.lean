import ICO.MHFockBothCovariance
import ICO.MHOracleTransform

/-! The published full-oracle covariance estimate on the actual finite
multiset register. The proof obtains the slightly stronger constant 12. -/

namespace ICO.MHFockFullCovariance

open QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockAlgebra
  ICO.MHFockRotation ICO.MHFockSwap ICO.MHFockOracle ICO.MHFockBothCovariance
  ICO.MHSectorCovariance ICO.RecordingOracleAlgebra ICO.MHOracleTransform
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 3000000

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem left_mul_contraction (L X : CMatrix a) (hL : ‖L‖≤1) : ‖L*X‖≤‖X‖ :=
  (norm_mul_le _ _).trans (by nlinarith [norm_nonneg X])

theorem sandwich_contraction (L X R : CMatrix a) (hL : ‖L‖≤1) (hR : ‖R‖≤1) : ‖L*X*R‖≤‖X‖ := by
  have hh := norm_mul_le (L*X) R
  have hl := left_mul_contraction L X hL
  have hm := mul_le_mul_of_nonneg_left hR (norm_nonneg (L*X))
  nlinarith

theorem unitary_unrotate (Q : Matrix.unitaryGroup a ℂ) (M A : CMatrix a) :
    ‖(Q : CMatrix a).conjTranspose*M-A‖ ≤ ‖M-(Q : CMatrix a)*A‖ := by
  have hQ : (Q : CMatrix a).conjTranspose*(Q : CMatrix a)=1 := Q.property.1
  have he : (Q : CMatrix a).conjTranspose*M-A = (Q : CMatrix a).conjTranspose*(M-(Q : CMatrix a)*A) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hQ, Matrix.one_mul]
  rw [he]
  apply left_mul_contraction
  rw [Matrix.l2_opNorm_conjTranspose]
  exact unitary_norm_le Q

theorem unitary_rotate_defect (Q : Matrix.unitaryGroup a ℂ) (M A : CMatrix a) (r : ℝ)
    (hh : ‖A-(Q : CMatrix a).conjTranspose*M‖≤r) : ‖M-(Q : CMatrix a)*A‖≤r := by
  have hQ : (Q : CMatrix a)*(Q : CMatrix a).conjTranspose=1 := Q.property.2
  have he : M-(Q : CMatrix a)*A = (Q : CMatrix a)*((Q : CMatrix a).conjTranspose*M-A) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hQ, Matrix.one_mul]
  rw [he]
  refine (left_mul_contraction _ _ (unitary_norm_le Q)).trans ?_
  rwa [norm_sub_rev]

theorem transformed_norm_le (A : CMatrix a) (C D Q : Matrix.unitaryGroup a ℂ) (hA : ‖A‖≤1) :
    ‖(Q : CMatrix a).conjTranspose*(D : CMatrix a)*A*(C : CMatrix a)*(Q : CMatrix a)‖≤1 := by
  have hh := sandwich_contraction ((Q⁻¹*D : Matrix.unitaryGroup a ℂ) : CMatrix a) A
    ((C*Q : Matrix.unitaryGroup a ℂ) : CMatrix a) (unitary_norm_le _) (unitary_norm_le _)
  have hl : ‖(Q : CMatrix a).conjTranspose*(D : CMatrix a)*A*(C : CMatrix a)*(Q : CMatrix a)‖≤‖A‖ := by
    simpa only [Matrix.UnitaryGroup.mul_val,Matrix.UnitaryGroup.inv_val,Matrix.mul_assoc] using hh
  exact hl.trans hA

theorem full_covariance_from_insertions (A B : CMatrix a) (C D Q : Matrix.unitaryGroup a ℂ)
    (ε : ℝ) (hA : ‖A‖≤1) (hB : ‖B‖≤1)
    (hQA : IsStarProjection (A*A.conjTranspose)) (hQB : IsStarProjection (B*B.conjTranspose))
    (hL : ‖(D : CMatrix a)*A*((C : CMatrix a)*(Q : CMatrix a))-(Q : CMatrix a)*A‖≤2*ε)
    (hR : ‖(C : CMatrix a).conjTranspose*B*((D : CMatrix a).conjTranspose*(Q : CMatrix a))-(Q : CMatrix a)*B‖≤2*ε) :
    ‖(D : CMatrix a)*ICO.MHOracleCovariance.fullOracle A B*((C : CMatrix a)*(Q : CMatrix a))-
      (Q : CMatrix a)*ICO.MHOracleCovariance.fullOracle A B‖≤12*ε := by
  let A' : CMatrix a := (Q : CMatrix a).conjTranspose*(D : CMatrix a)*A*(C : CMatrix a)*(Q : CMatrix a)
  let B' : CMatrix a := (Q : CMatrix a).conjTranspose*(C : CMatrix a).conjTranspose*B*(D : CMatrix a).conjTranspose*(Q : CMatrix a)
  have hA' : ‖A'‖≤1 := transformed_norm_le A C D Q hA
  have hB' : ‖B'‖≤1 := transformed_norm_le B D⁻¹ C⁻¹ Q hB
  have hδA : ‖A-A'‖≤2*ε := by
    rw [norm_sub_rev]
    have hh := unitary_unrotate Q ((D : CMatrix a)*A*((C : CMatrix a)*(Q : CMatrix a))) A
    have hl : ‖A'-A‖≤‖(D : CMatrix a)*A*((C : CMatrix a)*(Q : CMatrix a))-(Q : CMatrix a)*A‖ := by
      simpa only [A',Matrix.mul_assoc] using hh
    exact hl.trans hL
  have hδB : ‖B-B'‖≤2*ε := by
    rw [norm_sub_rev]
    have hh := unitary_unrotate Q ((C : CMatrix a).conjTranspose*B*((D : CMatrix a).conjTranspose*(Q : CMatrix a))) B
    have hl : ‖B'-B‖≤‖(C : CMatrix a).conjTranspose*B*((D : CMatrix a).conjTranspose*(Q : CMatrix a))-(Q : CMatrix a)*B‖ := by
      simpa only [B',Matrix.mul_assoc] using hh
    exact hl.trans hR
  have hh := ICO.MHOracleCovariance.fullOracle_difference_norm_le A B A' B' (2*ε) hA hB hA' hB' hQA hQB hδA hδB
  change ‖ICO.MHOracleCovariance.fullOracle A B-
    ICO.MHOracleCovariance.fullOracle
      ((Q : CMatrix a).conjTranspose*(D : CMatrix a)*A*(C : CMatrix a)*(Q : CMatrix a))
      ((Q : CMatrix a).conjTranspose*(C : CMatrix a).conjTranspose*B*(D : CMatrix a).conjTranspose*(Q : CMatrix a))‖≤6*(2*ε) at hh
  rw [fullOracle_transform] at hh
  have hh' : ‖ICO.MHOracleCovariance.fullOracle A B-
      (Q : CMatrix a).conjTranspose*(D : CMatrix a)*ICO.MHOracleCovariance.fullOracle A B*(C : CMatrix a)*(Q : CMatrix a)‖≤12*ε := by
    calc
      _ ≤ 6*(2*ε) := hh
      _ = _ := by ring
  exact unitary_rotate_defect Q
    ((D : CMatrix a)*ICO.MHOracleCovariance.fullOracle A B*((C : CMatrix a)*(Q : CMatrix a)))
    (ICO.MHOracleCovariance.fullOracle A B) (12*ε) (by simpa only [Matrix.mul_assoc] using hh')

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem fullOracle_covariance_twelve (C D : Matrix.unitaryGroup α ℂ)
    {t T : ℕ} (h : t+1≤T) (ht : t<Fintype.card α) :
    ‖(fockQuery D T : CMatrix (InputCutoff (α := α) T)) * ICO.MHFockOracle.fullOracle h *
        ((fockQuery C T : CMatrix (InputCutoff (α := α) T)) * (fockQ C D T : CMatrix (InputCutoff (α := α) T))) -
      (fockQ C D T : CMatrix (InputCutoff (α := α) T)) * ICO.MHFockOracle.fullOracle h‖ ≤
      12 * Real.sqrt ((2*(t:ℝ)*(t+1))/Fintype.card α) := by
  apply full_covariance_from_insertions (leftOnFock (α := α) h) (rightOnFock (α := α) h)
    (fockQuery C T) (fockQuery D T) (fockQ C D T)
  · exact leftOnFock_norm_le h ht
  · change ‖swapMatrix T*leftOnFock h*(swapMatrix T).conjTranspose‖≤1
    rw [swapMatrix_selfAdjoint]
    exact (swap_norm_le T _).trans (leftOnFock_norm_le h ht)
  · exact image_projection _ _ (leftOnFock_gram h ht) (leftOnFock_domain h)
  · exact image_projection _ _ (rightOnFock_gram h ht) (rightOnFock_domain h)
  · exact left_covariance C D h ht
  · simpa only [fockQuery_inverse] using right_covariance C D h ht
theorem fullOracle_covariance (C D : Matrix.unitaryGroup α ℂ)
    {t T : ℕ} (h : t+1≤T) (ht : t<Fintype.card α) :
    ‖(fockQuery D T : CMatrix (InputCutoff (α := α) T)) * ICO.MHFockOracle.fullOracle h *
        ((fockQuery C T : CMatrix (InputCutoff (α := α) T)) * (fockQ C D T : CMatrix (InputCutoff (α := α) T))) -
      (fockQ C D T : CMatrix (InputCutoff (α := α) T)) * ICO.MHFockOracle.fullOracle h‖ ≤
      16 * Real.sqrt ((2*(t:ℝ)*(t+1))/Fintype.card α) :=
  (fullOracle_covariance_twelve C D h ht).trans (by nlinarith [Real.sqrt_nonneg ((2*(t:ℝ)*(t+1))/Fintype.card α)])

end
end ICO.MHFockFullCovariance

