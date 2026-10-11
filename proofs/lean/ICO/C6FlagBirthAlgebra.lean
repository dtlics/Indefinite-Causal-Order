import ICO.C6FlagQueryAlgebra
import ICO.C6ResidualSelection

namespace ICO.C6FlagBirthAlgebra
open Matrix QIT ICO.C6FlagQueryAlgebra ICO.C6ResidualSelection ICO.C6RotatedSelection
  ICO.C6RotatedNumber ICO.C6RotatedNumberContinuation ICO.C6NumberRotationAlgebra
  ICO.C6NumberSelection ICO.C6FockNumber ICO.C6BosonicFockSupport
  ICO.C6BosonicFockRotated ICO.C6PolarFock ICO.MHFockRotation ICO.MHBoundedRecording
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem selected_fresh (U:Matrix.unitaryGroup A ℂ) (a:A) (S:Finset A)
    (ha:a∉S) (T:ℕ) :
    rotatedSelected U {a} T*rotatedFresh U S T=rotatedSelected U {a} T := by
  have hd:querySelected {a} T*queryFresh S T=querySelected {a} T := by
    unfold querySelected queryFresh
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    by_cases hi:i.2.1=a
    · simp [hi,ha]
    · simp [hi]
  let C:CMatrix (InputCutoff (α:=A) T):=fockQuery U T
  have hc:Cᴴ*C=1:=(fockQuery U T).property.1
  change (C*querySelected {a} T*Cᴴ)*(C*queryFresh S T*Cᴴ)=C*querySelected {a} T*Cᴴ
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc Cᴴ C,hc,Matrix.one_mul,
    ←Matrix.mul_assoc (querySelected {a} T) (queryFresh S T),hd]

theorem selected_preserves_other (U:Matrix.unitaryGroup A ℂ) (a:A) (S:Finset A)
    (ha:a∉S) (k:ℕ) {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A) :
    rotatedNumber U S k T*(rotatedSelected U {a} T*polarRightOnFock h)=
      (rotatedSelected U {a} T*polarRightOnFock h)*rotatedNumber U S k T := by
  have hN:rotatedNumber U S k T*rotatedSelected U {a} T=
      rotatedSelected U {a} T*rotatedNumber U S k T := by
    rw [rotatedSelected_query]
    exact query_preserves_rotated_number U S k T _
  calc
    _ = rotatedNumber U S k T*(rotatedSelected U {a} T*(rotatedFresh U S T*polarRightOnFock h)) := by
      rw [←Matrix.mul_assoc (rotatedSelected U {a} T),selected_fresh U a S ha T]
    _ = rotatedSelected U {a} T*((rotatedFresh U S T*polarRightOnFock h)*rotatedNumber U S k T) := by
      rw [←Matrix.mul_assoc,hN,Matrix.mul_assoc,
        fresh_birth_preserves_rotated_number U S S (fun _ h=>h) k h ht]
    _ = _ := by
      rw [←Matrix.mul_assoc,←Matrix.mul_assoc,selected_fresh U a S ha T]

#print axioms selected_preserves_other
end
end ICO.C6FlagBirthAlgebra
