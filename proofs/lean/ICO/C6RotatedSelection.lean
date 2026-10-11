import ICO.C6RotatedNumber
import ICO.C6NumberSelection

namespace ICO.C6RotatedSelection
open Matrix QIT ICO.C6RotatedNumber ICO.C6NumberRotationAlgebra ICO.C6NumberSelection
  ICO.C6FockNumber ICO.C6BosonicCacheSupport ICO.C6BosonicFockSupport
  ICO.C6BosonicFockRotated ICO.C6PolarFock ICO.MHFockRotation ICO.MHBoundedRecording
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def rotatedSelected (U:Matrix.unitaryGroup A ℂ) (S:Finset A) (T:ℕ) :
    CMatrix (InputCutoff (α:=A) T) :=
  (fockQuery U T:CMatrix (InputCutoff (α:=A) T))*querySelected S T*
    (fockQuery U T:CMatrix (InputCutoff (α:=A) T))ᴴ

theorem querySelected_compl (S:Finset A) (T:ℕ) : querySelected S T=queryFresh Sᶜ T := by
  unfold querySelected queryFresh
  congr 1
  ext i
  simp

theorem selected_covariance (U:Matrix.unitaryGroup A ℂ) (S:Finset A)
    {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A) :
    (rotatedSelected U S T*polarRightOnFock h)*(fockQ U 1 T:CMatrix (InputCutoff (α:=A) T))=
      (((fockQuery U T)*(fockQ U 1 T):Matrix.unitaryGroup (InputCutoff (α:=A) T) ℂ):
        CMatrix (InputCutoff (α:=A) T))*(querySelected S T*polarRightOnFock h) := by
  simpa only [rotatedSelected,querySelected_compl,rotatedFresh] using
    fresh_birth_covariance U Sᶜ h ht

theorem selected_shift (U:Matrix.unitaryGroup A ℂ) (S:Finset A) (k:ℕ)
    {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A) :
    rotatedNumber U S (k+1) T*(rotatedSelected U S T*polarRightOnFock h)*rotatedNumber U S k T=
      (rotatedSelected U S T*polarRightOnFock h)*rotatedNumber U S k T := by
  let C:=fockQuery U T
  let R:=fockQ U 1 T
  let L:=rotatedSelected U S T*polarRightOnFock h
  let B:=querySelected S T*polarRightOnFock h
  have hr:(R:CMatrix (InputCutoff (α:=A) T))ᴴ*(R:CMatrix (InputCutoff (α:=A) T))=1:=R.property.1
  have hv:((C*R:Matrix.unitaryGroup (InputCutoff (α:=A) T) ℂ):CMatrix (InputCutoff (α:=A) T))ᴴ*
      ((C*R:Matrix.unitaryGroup (InputCutoff (α:=A) T) ℂ):CMatrix (InputCutoff (α:=A) T))=1 :=
    (C*R).property.1
  have he:L*(R:CMatrix (InputCutoff (α:=A) T))=
      ((C*R:Matrix.unitaryGroup (InputCutoff (α:=A) T) ℂ):CMatrix (InputCutoff (α:=A) T))*B :=
    selected_covariance U S h ht
  have hc:rotatedNumber U S (k+1) T=
      ((C*R:Matrix.unitaryGroup (InputCutoff (α:=A) T) ℂ):CMatrix (InputCutoff (α:=A) T))*
        rightNumber S (k+1) T*
        ((C*R:Matrix.unitaryGroup (InputCutoff (α:=A) T) ℂ):CMatrix (InputCutoff (α:=A) T))ᴴ := by
    exact (commuting_conjugate C R (rightNumber S (k+1) T)
      (query_record_rotation U U T)
      (query_rightDiagonal U (fun _ p=>if ICO.C6BosonicSupport.labelNumber S p=k+1 then 1 else 0) T)).symm
  change rotatedNumber U S (k+1) T*L*rotatedNumber U S k T=L*rotatedNumber U S k T
  rw [hc,rotatedNumber]
  change _=L*((R:CMatrix (InputCutoff (α:=A) T))*rightNumber S k T*(R:CMatrix (InputCutoff (α:=A) T))ᴴ)
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc L (R:CMatrix (InputCutoff (α:=A) T)),he]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc
    (((C*R:Matrix.unitaryGroup (InputCutoff (α:=A) T) ℂ):CMatrix (InputCutoff (α:=A) T))ᴴ)
    ((C*R:Matrix.unitaryGroup (InputCutoff (α:=A) T) ℂ):CMatrix (InputCutoff (α:=A) T)),
    hv,Matrix.one_mul]
  have hb:rightNumber S (k+1) T*B*rightNumber S k T=B*rightNumber S k T:=
    selected_birth_shift S k h ht
  calc
    _ = ((C*R:Matrix.unitaryGroup (InputCutoff (α:=A) T) ℂ):CMatrix (InputCutoff (α:=A) T))*
        (rightNumber S (k+1) T*B*rightNumber S k T)*(R:CMatrix (InputCutoff (α:=A) T))ᴴ := by
          simp only [Matrix.mul_assoc]; rfl
    _ = _ := by rw [hb]; simp only [Matrix.mul_assoc]; rfl

#print axioms selected_shift
end
end ICO.C6RotatedSelection
