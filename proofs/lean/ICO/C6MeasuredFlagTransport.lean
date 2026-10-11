import ICO.C6SelectedBirthFlag

namespace ICO.C6MeasuredFlagTransport
open Matrix QIT ICO.C6SelectedBirthFlag ICO.C6FlagHistoryAlgebra ICO.C6FlagQueryAlgebra
  ICO.C6FlagBirthAlgebra ICO.C6ResidualSelection ICO.C6ResidualModes
  ICO.C6CacheHistorySpan ICO.C6CacheSpanProjection ICO.C6BosonicHistorySupport
  ICO.C6BosonicReencoding ICO.C6BosonicQueryAlgebra ICO.C6FockQueryMatrix
  ICO.C6BosonicFockRotated ICO.C6RotatedNumber ICO.C6RotatedNumberContinuation
  ICO.C6NumberRotationAlgebra ICO.C6RotatedSelection ICO.C6PolarFock ICO.MHBoundedRecording
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem measured_retrieval_preserves {s t T:ℕ} (v:Fin s→EuclideanSpace ℂ A)
    (x:EuclideanSpace ℂ A) (U:Matrix.unitaryGroup A ℂ) (B S:Finset A)
    (hB:historyProjection v=spanProjection U B) (k:ℕ)
    (h:t+1≤T) (ht:t<Fintype.card A) :
    rotatedNumber U S k T*(polarLeftOnFock h*queryMatrix (rankOne x) T*
      (polarLeftOnFock h)ᴴ*historySupport v T)=
      (polarLeftOnFock h*queryMatrix (rankOne x) T*
      (polarLeftOnFock h)ᴴ*historySupport v T)*rotatedNumber U S k T := by
  let N:=rotatedNumber U S k T
  have hF:=left_preserves_rotated_number U S k h ht
  have hX:=query_preserves_rotated_number U S k T (rankOne x)
  have hR:=retrieval_preserves_rotated_number U S k h ht
  have hB':=history_number_commute v U B S hB k T
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (rotatedNumber U S k T) (polarLeftOnFock h),hF]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (rotatedNumber U S k T) (queryMatrix (rankOne x) T),hX]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (rotatedNumber U S k T) (polarLeftOnFock h)ᴴ,hR]
  simp only [Matrix.mul_assoc]
  rw [hB']

theorem measured_birth_preserves_other {q t T:ℕ} (v:Fin q→EuclideanSpace ℂ A) (i:Active v)
    (U:Matrix.unitaryGroup A ℂ) (a:A) (ha:column U a=mode v i) (B S:Finset A)
    (hB:historyProjection (prior v i)=spanProjection U B) (haS:a∉S) (k:ℕ)
    (h:t+1≤T) (ht:t<Fintype.card A) :
    rotatedNumber U S k T*
      (polarLeftOnFock h*queryMatrix (rankOne (v i)) T*rotatedFresh U B T*
        polarRightOnFock h*(1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)*historySupport (prior v i) T)=
      (polarLeftOnFock h*queryMatrix (rankOne (v i)) T*rotatedFresh U B T*
        polarRightOnFock h*(1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)*historySupport (prior v i) T)*
        rotatedNumber U S k T := by
  let N:=rotatedNumber U S k T
  let F:=polarLeftOnFock (α:=A) h
  let X:=queryMatrix (rankOne (v i)) T
  let Q:=rotatedFresh U B T
  let P:=rotatedSelected U {a} T
  let G:=polarRightOnFock (α:=A) h
  let E:=(1-F*Fᴴ)*historySupport (prior v i) T
  have hXQ:N*(X*Q)=(X*Q)*N := by
    have hX:=query_preserves_rotated_number U S k T (rankOne (v i))
    have hQ:N*Q=Q*N := by
      rw [show Q=1-queryMatrix (spanProjection U B) T from rotatedFresh_complement U B T]
      simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul]
      rw [query_preserves_rotated_number U S k T]
    rw [←Matrix.mul_assoc,hX,Matrix.mul_assoc,hQ,←Matrix.mul_assoc]
  have hP:(X*Q)*P=X*Q:=fresh_measurement_selection v i U a ha B hB T
  have hPG:N*(P*G)=(P*G)*N:=selected_preserves_other U a S haS k h ht
  have hE:N*E=E*N := by
    change N*((1-F*Fᴴ)*historySupport (prior v i) T)=_
    rw [←Matrix.mul_assoc,inert_number_commute U S k h ht,Matrix.mul_assoc,
      history_number_commute (prior v i) U B S hB k T,←Matrix.mul_assoc]
  have hmid:N*((X*Q)*G)=((X*Q)*G)*N := by
    calc
      _ = N*(((X*Q)*P)*G) := congrArg (fun Z:CMatrix (InputCutoff (α:=A) T)=>N*(Z*G)) hP.symm
      _ = (X*Q)*((P*G)*N) := by
        rw [Matrix.mul_assoc,←Matrix.mul_assoc N (X*Q),hXQ,Matrix.mul_assoc,hPG]
      _ = _ := by rw [←Matrix.mul_assoc,←Matrix.mul_assoc,hP]
  have hF:N*F=F*N:=left_preserves_rotated_number U S k h ht
  change N*((F*X*Q*G)*(1-F*Fᴴ)*historySupport (prior v i) T)=_
  calc
    _ = N*(F*((X*Q)*G)*E) := by simp only [E,Matrix.mul_assoc]
    _ = F*((X*Q)*G)*E*N := by
      calc
        _ = (N*F)*((X*Q)*G)*E := by simp only [Matrix.mul_assoc]
        _ = (F*N)*((X*Q)*G)*E := by rw [hF]
        _ = F*(N*((X*Q)*G))*E := by simp only [Matrix.mul_assoc]
        _ = F*(((X*Q)*G)*N)*E := by rw [hmid]
        _ = F*((X*Q)*G)*(N*E) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hE]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [E,Matrix.mul_assoc]; rfl

#print axioms measured_retrieval_preserves
#print axioms measured_birth_preserves_other
end
end ICO.C6MeasuredFlagTransport
