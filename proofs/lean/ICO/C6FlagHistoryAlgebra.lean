import ICO.C6FlagBirthAlgebra
import ICO.C6BosonicHistorySupport

namespace ICO.C6FlagHistoryAlgebra
open Matrix QIT ICO.C6FlagBirthAlgebra ICO.C6FlagQueryAlgebra ICO.C6NumberRotationAlgebra
  ICO.C6RotatedNumber ICO.C6RotatedNumberContinuation ICO.C6FockNumber
  ICO.C6BosonicCacheSupport ICO.C6BosonicFockSupport ICO.C6BosonicFockRotated
  ICO.C6BosonicHistorySupport ICO.C6CacheSpanProjection ICO.MHFockRotation
  ICO.C6PolarFock ICO.MHBoundedRecording
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 900000
set_option Elab.async false

section General
variable {X:Type*} [Fintype X] [DecidableEq X]

theorem sandwich_shift (N M A P G E:CMatrix X)
    (hA:N*A=A*N) (hP:A*P=A) (hE:E*M=M*E)
    (hG:N*(P*G)*M=(P*G)*M) : N*(A*G*E)*M=(A*G*E)*M := by
  calc
    _ = N*((A*P)*G*E)*M := congrArg (fun Z:CMatrix X=>N*(Z*G*E)*M) hP.symm
    _ = A*(N*(P*G)*M)*E := by
      simp only [Matrix.mul_assoc]
      rw [hE]
      rw [←Matrix.mul_assoc N A,hA]
      simp only [Matrix.mul_assoc]
    _ = A*((P*G)*M)*E := by rw [hG]
    _ = _ := by
      simp only [←Matrix.mul_assoc]
      rw [hP]
      simp only [Matrix.mul_assoc]
      rw [hE]

end General
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem record_number_commute (S B:Finset A) (k T:ℕ) :
    rightNumber S k T*fockRecord B T=fockRecord B T*rightNumber S k T := by
  unfold rightNumber rightDiagonal fockRecord
  rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun i=>mul_comm _ _)

theorem rotated_record_number (U:Matrix.unitaryGroup A ℂ) (S B:Finset A) (k T:ℕ) :
    rotatedNumber U S k T*rotatedRecord U B T=rotatedRecord U B T*rotatedNumber U S k T := by
  let R:CMatrix (InputCutoff (α:=A) T):=fockQ U 1 T
  have hr:Rᴴ*R=1:=(fockQ U 1 T).property.1
  change (R*rightNumber S k T*Rᴴ)*(R*fockRecord B T*Rᴴ)=
    (R*fockRecord B T*Rᴴ)*(R*rightNumber S k T*Rᴴ)
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc Rᴴ R,hr,Matrix.one_mul,
    ←Matrix.mul_assoc Rᴴ R,hr,Matrix.one_mul]
  rw [←Matrix.mul_assoc (rightNumber S k T) (fockRecord B T),record_number_commute]
  simp only [Matrix.mul_assoc]

theorem history_number_commute {s:ℕ} (v:Fin s→EuclideanSpace ℂ A)
    (U:Matrix.unitaryGroup A ℂ) (B S:Finset A) (hB:historyProjection v=spanProjection U B)
    (k T:ℕ) :
    rotatedNumber U S k T*historySupport v T=historySupport v T*rotatedNumber U S k T := by
  rw [historySupport,hB,fockSupport_rotated]
  exact rotated_record_number U S B k T

theorem inert_number_commute (U:Matrix.unitaryGroup A ℂ) (S:Finset A) (k:ℕ)
    {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A) :
    rotatedNumber U S k T*(1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)=
      (1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)*rotatedNumber U S k T := by
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul]
  rw [←Matrix.mul_assoc,left_preserves_rotated_number U S k h ht,
    Matrix.mul_assoc,retrieval_preserves_rotated_number U S k h ht]
  simp only [Matrix.mul_assoc]

#print axioms history_number_commute
#print axioms sandwich_shift
end
end ICO.C6FlagHistoryAlgebra
