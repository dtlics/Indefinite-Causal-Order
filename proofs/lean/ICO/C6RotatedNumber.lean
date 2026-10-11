import ICO.C6NumberRotationAlgebra

namespace ICO.C6RotatedNumber
open Matrix QIT ICO.C6NumberRotationAlgebra ICO.C6FockNumber ICO.C6FockNumberContinuation
  ICO.C6BosonicCacheSupport ICO.C6BosonicFockRotated ICO.C6BosonicFockSupport
  ICO.C6PolarFock ICO.C6PolarFockCovariance ICO.MHFockRotation ICO.MHFockBothCovariance
  ICO.MHBoundedRecording
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
set_option Elab.async false

section Algebra
variable {X:Type*} [Fintype X] [DecidableEq X]

theorem commuting_conjugate (C R:Matrix.unitaryGroup X ℂ) (N:CMatrix X)
    (hCR:(C:CMatrix X)*(R:CMatrix X)=(R:CMatrix X)*(C:CMatrix X))
    (hCN:(C:CMatrix X)*N=N*(C:CMatrix X)) :
    ((C*R:Matrix.unitaryGroup X ℂ):CMatrix X)*N*
      (((C*R:Matrix.unitaryGroup X ℂ):CMatrix X))ᴴ=(R:CMatrix X)*N*(R:CMatrix X)ᴴ := by
  change ((C:CMatrix X)*(R:CMatrix X))*N*((C:CMatrix X)*(R:CMatrix X))ᴴ=_
  rw [hCR,Matrix.conjTranspose_mul]
  have hc:(C:CMatrix X)*(C:CMatrix X)ᴴ=1:=C.property.2
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (C:CMatrix X) N,hCN]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (C:CMatrix X) (C:CMatrix X)ᴴ,hc,Matrix.one_mul]

end Algebra
variable {A:Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem left_preserves_rotated_number (U:Matrix.unitaryGroup A ℂ) (S:Finset A) (k:ℕ)
    {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A) :
    rotatedNumber U S k T*polarLeftOnFock h=polarLeftOnFock h*rotatedNumber U S k T := by
  let C:=fockQuery U T
  let R:=fockQ U 1 T
  have hC:polarLeftOnFock h*((C*R:Matrix.unitaryGroup (InputCutoff (α:=A) T) ℂ):CMatrix (InputCutoff (α:=A) T))=
      (R:CMatrix (InputCutoff (α:=A) T))*polarLeftOnFock h := by
    simpa only [query_one,Matrix.one_mul] using ICO.C6PolarFockCovariance.left_covariance U 1 h ht
  have hh:=transported_intertwining (polarLeftOnFock h) (polarLeftOnFock h)
    (rightNumber S k T) (rightNumber S k T) (C*R) R hC (left_preserves_number S k h)
  rw [commuting_conjugate C R (rightNumber S k T) (query_record_rotation U U T) (query_rightDiagonal U (fun _ p=>if ICO.C6BosonicSupport.labelNumber S p=k then 1 else 0) T)] at hh
  exact hh

theorem fresh_birth_covariance (U:Matrix.unitaryGroup A ℂ) (B:Finset A)
    {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A) :
    (rotatedFresh U B T*polarRightOnFock h)*(fockQ U 1 T:CMatrix (InputCutoff (α:=A) T))=
      (((fockQuery U T)*(fockQ U 1 T):Matrix.unitaryGroup (InputCutoff (α:=A) T) ℂ):CMatrix (InputCutoff (α:=A) T))*
        (queryFresh B T*polarRightOnFock h) := by
  let C:CMatrix (InputCutoff (α:=A) T):=fockQuery U T
  let R:CMatrix (InputCutoff (α:=A) T):=fockQ U 1 T
  have hc:C*Cᴴ=1:=(fockQuery U T).property.2
  have hg:=ICO.C6PolarFockCovariance.right_covariance U 1 h ht
  simp only [inv_one,query_one,Matrix.one_mul,fockQuery_inverse,
    Matrix.UnitaryGroup.inv_val,Matrix.star_eq_conjTranspose] at hg
  change Cᴴ*polarRightOnFock h*R=R*polarRightOnFock h at hg
  have hg':polarRightOnFock h*R=C*R*polarRightOnFock h := by
    have he:=congrArg (fun M=>C*M) hg
    simpa only [←Matrix.mul_assoc,hc,Matrix.one_mul] using he
  change (C*queryFresh B T*Cᴴ)*polarRightOnFock h*R=(C*R)*(queryFresh B T*polarRightOnFock h)
  calc
    _ = C*queryFresh B T*(Cᴴ*polarRightOnFock h*R) := by simp only [Matrix.mul_assoc]
    _ = C*queryFresh B T*(R*polarRightOnFock h) := by rw [hg]
    _ = _ := by
      simp only [Matrix.mul_assoc]
      rw [←Matrix.mul_assoc (queryFresh B T) R,queryFresh_commutes]
      simp only [Matrix.mul_assoc]
      rfl

theorem fresh_birth_preserves_rotated_number (U:Matrix.unitaryGroup A ℂ)
    (S B:Finset A) (hSB:S⊆B) (k:ℕ) {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A) :
    rotatedNumber U S k T*(rotatedFresh U B T*polarRightOnFock h)=
      (rotatedFresh U B T*polarRightOnFock h)*rotatedNumber U S k T := by
  let C:=fockQuery U T
  let R:=fockQ U 1 T
  have hh:=transported_intertwining (rotatedFresh U B T*polarRightOnFock h)
    (queryFresh B T*polarRightOnFock h) (rightNumber S k T) (rightNumber S k T)
    R (C*R) (fresh_birth_covariance U B h ht) (fresh_birth_preserves_old_number S B hSB k h ht)
  rw [commuting_conjugate C R (rightNumber S k T) (query_record_rotation U U T) (query_rightDiagonal U (fun _ p=>if ICO.C6BosonicSupport.labelNumber S p=k then 1 else 0) T)] at hh
  exact hh

#print axioms left_preserves_rotated_number
#print axioms fresh_birth_preserves_rotated_number
end
end ICO.C6RotatedNumber
