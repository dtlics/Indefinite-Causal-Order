import ICO.MHWRestricted

/-! Passing the concrete recording covariance estimate to inverse queries. -/
namespace ICO.MHInverseCovariance
open Matrix QIT ICO.MHFockFullCovariance ICO.MHFockRotation ICO.MHFockBothCovariance
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHWRestricted ICO.MHCutoffOverlap
  ICO.MHFockProjection ICO.MHSectorCovariance ICO.MHFockAlgebra
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
variable {H : Type*} [Fintype H] [DecidableEq H]

theorem inverse_covariance (V : CMatrix H) (C D Q : Matrix.unitaryGroup H ℂ) (ε : ℝ)
    (hcov : ‖(Q : CMatrix H)*V-(D : CMatrix H)*V*(C : CMatrix H)*(Q : CMatrix H)‖≤ε) :
    ‖(Q : CMatrix H)*V.conjTranspose-
      (C : CMatrix H).conjTranspose*V.conjTranspose*(D : CMatrix H).conjTranspose*(Q : CMatrix H)‖≤ε := by
  have hQl : (Q : CMatrix H).conjTranspose*(Q : CMatrix H)=1 := Q.property.1
  have hQr : (Q : CMatrix H)*(Q : CMatrix H).conjTranspose=1 := Q.property.2
  have he : (Q : CMatrix H)*
      ((Q : CMatrix H)*V-(D : CMatrix H)*V*(C : CMatrix H)*(Q : CMatrix H)).conjTranspose*
        (Q : CMatrix H)=
      (Q : CMatrix H)*V.conjTranspose-
        (C : CMatrix H).conjTranspose*V.conjTranspose*(D : CMatrix H).conjTranspose*(Q : CMatrix H) := by
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.mul_assoc]
    rw [hQl,Matrix.mul_one]
    rw [←Matrix.mul_assoc (Q : CMatrix H) (Q : CMatrix H).conjTranspose,hQr,Matrix.one_mul]
  rw [←he]
  have hh := sandwich_contraction (Q : CMatrix H)
    ((Q : CMatrix H)*V-(D : CMatrix H)*V*(C : CMatrix H)*(Q : CMatrix H)).conjTranspose
    (Q : CMatrix H) (unitary_norm_le Q) (unitary_norm_le Q)
  rw [Matrix.l2_opNorm_conjTranspose] at hh
  exact hh.trans hcov

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem inverse_fullOracle_covariance (C D : Matrix.unitaryGroup A ℂ)
    {q T : ℕ} (hq : q+1≤T) (hqd : q<Fintype.card A) :
    ‖(fockQ C D T : CMatrix (InputCutoff (α:=A) T))*(ICO.MHFockOracle.fullOracle hq).conjTranspose-
      (fockQuery C⁻¹ T : CMatrix (InputCutoff (α:=A) T))*(ICO.MHFockOracle.fullOracle hq).conjTranspose*
      (fockQuery D⁻¹ T : CMatrix (InputCutoff (α:=A) T))*(fockQ C D T : CMatrix (InputCutoff (α:=A) T))‖≤
      16*Real.sqrt ((2*(q:ℝ)*(q+1))/Fintype.card A) := by
  have hh := fullOracle_covariance C D hq hqd
  rw [norm_sub_rev] at hh
  have hi := inverse_covariance (ICO.MHFockOracle.fullOracle hq) (fockQuery C T)
    (fockQuery D T) (fockQ C D T) _ (by simpa only [Matrix.mul_assoc] using hh)
  simpa only [fockQuery_inverse] using hi

theorem inverse_restricted_covariance (C D : Matrix.unitaryGroup A ℂ)
    {q T : ℕ} (hq : q+1≤T) (hqd : q<Fintype.card A) :
    ‖(fockQ C D T : CMatrix (InputCutoff (α:=A) T))*
        ((ICO.MHFockOracle.fullOracle hq).conjTranspose*ICO.MHFockAlgebra.sourceProjection (Nat.le_trans (Nat.le_succ q) hq))-
      (fockQuery C⁻¹ T : CMatrix (InputCutoff (α:=A) T))*
        ((ICO.MHFockOracle.fullOracle hq).conjTranspose*ICO.MHFockAlgebra.sourceProjection (Nat.le_trans (Nat.le_succ q) hq))*
      (fockQuery D⁻¹ T : CMatrix (InputCutoff (α:=A) T))*(fockQ C D T : CMatrix (InputCutoff (α:=A) T))‖≤
      16*Real.sqrt ((2*(q:ℝ)*(q+1))/Fintype.card A) :=
  cutoff_covariance _ _ (fockQuery D⁻¹ T) (fockQuery C⁻¹ T) (fockQ C D T)
    (sourceProjection_projection _) (source_commute_query D⁻¹ _) (source_commute_rotation C D _)
    _ (inverse_fullOracle_covariance C D hq hqd)

#print axioms inverse_restricted_covariance
end
end ICO.MHInverseCovariance
