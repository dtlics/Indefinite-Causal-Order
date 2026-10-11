import ICO.C6FockNumberContinuation
import ICO.C6BosonicKnownSupport
import ICO.MHFockRotationSwap

namespace ICO.C6NumberRotationAlgebra
open Matrix QIT ICO.C6FockNumber ICO.C6FockNumberContinuation ICO.C6BosonicCacheSupport
  ICO.C6BosonicKnownSupport ICO.C6BosonicFockRotated ICO.C6BosonicFockSupport
  ICO.C6PolarFock ICO.C6PolarFockCovariance ICO.MHFockRotation ICO.MHFockRotationSwap
  ICO.MHBoundedRecording ICO.MHSectorCovariance ICO.MHFockPublicRotation
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 1024
set_option Elab.async false

section General
variable {X:Type*} [Fintype X] [DecidableEq X]

theorem transported_intertwining (A B P Q:CMatrix X) (U V:Matrix.unitaryGroup X ℂ)
    (h:A*(U:CMatrix X)=(V:CMatrix X)*B) (hP:Q*B=B*P) :
    ((V:CMatrix X)*Q*(V:CMatrix X)ᴴ)*A=A*((U:CMatrix X)*P*(U:CMatrix X)ᴴ) := by
  have hu:(U:CMatrix X)*(U:CMatrix X)ᴴ=1:=U.property.2
  have hv:(V:CMatrix X)ᴴ*(V:CMatrix X)=1:=V.property.1
  have he:A=(V:CMatrix X)*B*(U:CMatrix X)ᴴ := by
    have hh:=congrArg (fun M=>M*(U:CMatrix X)ᴴ) h
    simpa only [Matrix.mul_assoc,hu,Matrix.mul_one] using hh
  calc
    _ = ((V:CMatrix X)*Q*(V:CMatrix X)ᴴ)*((V:CMatrix X)*B*(U:CMatrix X)ᴴ) := by rw [←he]
    _ = (V:CMatrix X)*(Q*B)*(U:CMatrix X)ᴴ := by
      simp only [Matrix.mul_assoc]
      rw [←Matrix.mul_assoc (V:CMatrix X)ᴴ (V:CMatrix X),hv,Matrix.one_mul]
    _ = (V:CMatrix X)*(B*P)*(U:CMatrix X)ᴴ := by rw [hP]
    _ = A*((U:CMatrix X)*P*(U:CMatrix X)ᴴ) := by
      calc
        _ = ((V:CMatrix X)*B)*P*(U:CMatrix X)ᴴ := by simp only [Matrix.mul_assoc]
        _ = (A*(U:CMatrix X))*P*(U:CMatrix X)ᴴ := by rw [h]
        _ = _ := by simp only [Matrix.mul_assoc]

end General
variable {A:Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem query_rightDiagonal (U:Matrix.unitaryGroup A ℂ)
    (f:∀n,TensorPowerProfile (A×A) n→ℂ) (T:ℕ) :
    (fockQuery U T:CMatrix (InputCutoff (α:=A) T))*rightDiagonal f T=
      rightDiagonal f T*(fockQuery U T:CMatrix (InputCutoff (α:=A) T)) := by
  ext ⟨⟨s,q⟩,x,p⟩ ⟨⟨s',q'⟩,y,p'⟩
  simp only [rightDiagonal,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases hs:s=s'
  · subst s'
    rw [fockQuery_entry_same]
    by_cases hq:q=q'
    · subst q'; exact mul_comm _ _
    · simp [hq]
  · rw [fockQuery_entry_other U T _ _ hs]
    simp

theorem query_record_rotation (U V:Matrix.unitaryGroup A ℂ) (T:ℕ) :
    (fockQuery U T:CMatrix (InputCutoff (α:=A) T))*(fockQ V 1 T:CMatrix (InputCutoff (α:=A) T))=
      (fockQ V 1 T:CMatrix (InputCutoff (α:=A) T))*(fockQuery U T:CMatrix (InputCutoff (α:=A) T)) := by
  have he:=rotation_known (μ:=Unit) (ν:=Unit) V 1 T
    (Matrix.kronecker (U:CMatrix A) (1:CMatrix Unit))
  rw [←query_tensor_known] at he
  simp only [Matrix.kronecker] at he
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,Matrix.one_mul] at he
  ext i j
  have hh:=congrFun (congrFun he (i,())) (j,())
  simpa only [Matrix.kroneckerMap_apply,Matrix.one_apply,ite_true,mul_one] using hh.symm

def rotatedNumber (U:Matrix.unitaryGroup A ℂ) (S:Finset A) (k T:ℕ) :
    CMatrix (InputCutoff (α:=A) T) :=
  (fockQ U 1 T:CMatrix (InputCutoff (α:=A) T))*rightNumber S k T*
    (fockQ U 1 T:CMatrix (InputCutoff (α:=A) T))ᴴ

#print axioms transported_intertwining
#print axioms query_record_rotation
end
end ICO.C6NumberRotationAlgebra
