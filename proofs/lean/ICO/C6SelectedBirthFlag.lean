import ICO.C6FlagHistoryAlgebra

/-! The literal measured fresh birth has occupation one in its actual
nonzero residual mode. Its inert-image and history-support factors remain. -/
namespace ICO.C6SelectedBirthFlag
open Matrix QIT ICO.C6FlagHistoryAlgebra ICO.C6FlagQueryAlgebra ICO.C6FlagBirthAlgebra
  ICO.C6ResidualSelection ICO.C6ResidualModes ICO.C6CacheHistorySpan ICO.C6CacheSpanProjection
  ICO.C6BosonicReencoding ICO.C6BosonicQueryAlgebra ICO.C6FockQueryMatrix
  ICO.C6BosonicHistorySupport ICO.C6BosonicFockRotated ICO.C6RotatedNumber
  ICO.C6RotatedNumberContinuation ICO.C6RotatedSelection ICO.C6NumberRotationAlgebra
  ICO.C6PolarFock ICO.MHBoundedRecording
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem measured_birth_flag {q t T:ℕ} (v:Fin q→EuclideanSpace ℂ A) (i:Active v)
    (U:Matrix.unitaryGroup A ℂ) (a:A) (ha:column U a=mode v i) (B:Finset A)
    (hB:historyProjection (prior v i)=spanProjection U B)
    (h:t+1≤T) (ht:t<Fintype.card A) :
    rotatedNumber U {a} 1 T*
      (polarLeftOnFock h*queryMatrix (rankOne (v i)) T*rotatedFresh U B T*
        polarRightOnFock h*(1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)*historySupport (prior v i) T)*
        rotatedNumber U {a} 0 T=
      (polarLeftOnFock h*queryMatrix (rankOne (v i)) T*rotatedFresh U B T*
        polarRightOnFock h*(1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)*historySupport (prior v i) T)*
        rotatedNumber U {a} 0 T := by
  let F:=polarLeftOnFock (α:=A) h
  let G:=polarRightOnFock (α:=A) h
  let X:=queryMatrix (rankOne (v i)) T
  let Q:=rotatedFresh U B T
  let L:=F*X*Q
  let E:=(1-F*Fᴴ)*historySupport (prior v i) T
  let N:=rotatedNumber U {a} 1 T
  let M:=rotatedNumber U {a} 0 T
  have hNF:N*F=F*N:=left_preserves_rotated_number U {a} 1 h ht
  have hNX:N*X=X*N:=query_preserves_rotated_number U {a} 1 T _
  have hNQ:N*Q=Q*N := by
    rw [show Q=1-queryMatrix (spanProjection U B) T from rotatedFresh_complement U B T]
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul]
    rw [query_preserves_rotated_number U {a} 1 T]
  have hNL:N*L=L*N := by
    dsimp only [L]
    simp only [Matrix.mul_assoc]
    rw [←Matrix.mul_assoc N F,hNF]
    simp only [Matrix.mul_assoc]
    rw [←Matrix.mul_assoc N X,hNX]
    simp only [Matrix.mul_assoc]
    rw [hNQ]
  have hLP:L*rotatedSelected U {a} T=L := by
    change (F*X*Q)*rotatedSelected U {a} T=F*X*Q
    simpa only [F,X,Q,Matrix.mul_assoc] using
      congrArg (fun Z:CMatrix (InputCutoff (α:=A) T)=>F*Z)
        (fresh_measurement_selection v i U a ha B hB T)
  have hEM:E*M=M*E := by
    have h1:=inert_number_commute U {a} 0 h ht
    have h2:=history_number_commute (prior v i) U B {a} hB 0 T
    change ((1-F*Fᴴ)*historySupport (prior v i) T)*M=M*((1-F*Fᴴ)*historySupport (prior v i) T)
    rw [Matrix.mul_assoc,←h2,←Matrix.mul_assoc,←h1,Matrix.mul_assoc]
  have hh:=sandwich_shift N M L (rotatedSelected U {a} T) G E hNL hLP hEM
    (selected_shift U {a} 0 h ht)
  simpa only [N,M,L,E,F,G,X,Q,Matrix.mul_assoc] using hh

#print axioms measured_birth_flag
end
end ICO.C6SelectedBirthFlag
