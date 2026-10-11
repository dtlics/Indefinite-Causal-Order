import ICO.C6RotatedNumber

namespace ICO.C6RotatedNumberContinuation
open Matrix QIT ICO.C6RotatedNumber ICO.C6NumberRotationAlgebra ICO.C6FockNumber
  ICO.C6FockNumberContinuation ICO.C6BosonicFreshContraction ICO.C6BosonicKnownSupport
  ICO.C6BosonicFockRotated ICO.C6PolarFock ICO.MHFockPublicRotation ICO.MHFockRotation
  ICO.MHBoundedRecording ICO.MHFockKnownOperation
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 350000
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem rotatedNumber_adjoint (U:Matrix.unitaryGroup A ℂ) (S:Finset A) (k T:ℕ) :
    (rotatedNumber U S k T)ᴴ=rotatedNumber U S k T := by
  let R:CMatrix (InputCutoff (α:=A) T):=fockQ U 1 T
  change (R*rightNumber S k T*Rᴴ)ᴴ=R*rightNumber S k T*Rᴴ
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,rightNumber_adjoint,Matrix.mul_assoc]

#check rotatedNumber_adjoint
theorem retrieval_preserves_rotated_number (U:Matrix.unitaryGroup A ℂ) (S:Finset A) (k:ℕ)
    {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A) :
    rotatedNumber U S k T*(polarLeftOnFock h)ᴴ=(polarLeftOnFock h)ᴴ*rotatedNumber U S k T := by
  have he:=congrArg Matrix.conjTranspose (left_preserves_rotated_number U S k h ht)
  simpa only [Matrix.conjTranspose_mul,rotatedNumber_adjoint] using he.symm

#check retrieval_preserves_rotated_number
theorem freshInverse_preserves_rotated_number (U:Matrix.unitaryGroup A ℂ)
    (S B:Finset A) (hSB:S⊆B) (k:ℕ) {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A) :
    rotatedNumber U S k T*freshInverse (polarLeftOnFock h) (polarRightOnFock h) (rotatedFresh U B T)=
      freshInverse (polarLeftOnFock h) (polarRightOnFock h) (rotatedFresh U B T)*rotatedNumber U S k T := by
  have hc:rotatedNumber U S k T*(1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)=
      (1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)*rotatedNumber U S k T := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul]
    rw [←Matrix.mul_assoc,left_preserves_rotated_number U S k h ht,
      Matrix.mul_assoc,retrieval_preserves_rotated_number U S k h ht]
    simp only [Matrix.mul_assoc]
  unfold freshInverse
  rw [Matrix.mul_add,Matrix.add_mul,retrieval_preserves_rotated_number U S k h ht]
  apply congrArg (fun X:CMatrix (InputCutoff (α:=A) T)=>
    (polarLeftOnFock h)ᴴ*rotatedNumber U S k T+X)
  rw [←Matrix.mul_assoc,fresh_birth_preserves_rotated_number U S B hSB k h ht,
    Matrix.mul_assoc,hc]
  simp only [Matrix.mul_assoc]

#check freshInverse_preserves_rotated_number
theorem rotated_number_tensor {M:Type*} [Fintype M] [DecidableEq M]
    (U:Matrix.unitaryGroup A ℂ) (S:Finset A) (k T:ℕ) :
    Matrix.kronecker (rotatedNumber U S k T) (1:CMatrix M)=
      Matrix.kronecker (fockQ U 1 T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix M)*
        Matrix.kronecker (rightNumber S k T) (1:CMatrix M)*
          (Matrix.kronecker (fockQ U 1 T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix M))ᴴ := by
  simp only [rotatedNumber,Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,Matrix.mul_one,Matrix.mul_one]

#check rotated_number_tensor
theorem known_preserves_rotated_number {M N:Type*} [Fintype M] [DecidableEq M]
    [Fintype N] [DecidableEq N] (U:Matrix.unitaryGroup A ℂ) (S:Finset A) (k T:ℕ)
    (K:Matrix (A×N) (A×M) ℂ) :
    Matrix.kronecker (rotatedNumber U S k T) (1:CMatrix N)*known T K=
      known T K*Matrix.kronecker (rotatedNumber U S k T) (1:CMatrix M) := by
  rw [rotated_number_tensor,rotated_number_tensor]
  simp only [Matrix.mul_assoc]
  rw [rotation_adjoint_known]
  rw [←Matrix.mul_assoc (Matrix.kronecker (rightNumber S k T) (1:CMatrix N)) (known T K),
    known_preserves_number]
  simp only [←Matrix.mul_assoc]
  rw [rotation_known]

#print axioms freshInverse_preserves_rotated_number
#print axioms known_preserves_rotated_number
end
end ICO.C6RotatedNumberContinuation
