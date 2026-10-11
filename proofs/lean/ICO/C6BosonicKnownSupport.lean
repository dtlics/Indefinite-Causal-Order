import ICO.C6BosonicCacheSupport

/-! Arbitrary accessible rectangular operations preserve private left-label
support, in every rotated basis and with arbitrary changing memory. -/
namespace ICO.C6BosonicKnownSupport
open QIT ICO.C6BosonicFockSupport ICO.C6BosonicFockRotated
  ICO.C6BosonicLabelSupport ICO.MHFockKnownOperation ICO.MHFockPublicRotation
  ICO.MHFockRotation ICO.MHBoundedRecording
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
variable {A M N : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

theorem record_tensor_diagonal (S : Finset A) (T : ℕ) :
    Matrix.kronecker (fockRecord S T) (1:CMatrix M)=
      Matrix.diagonal (fun i : InputCutoff (α:=A) T×M => if LabelsIn S i.1.2.2 then 1 else 0) := by
  ext i j
  simp only [fockRecord,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.diagonal_apply,
    Matrix.one_apply,Prod.mk.injEq]
  by_cases h1 : i.1=j.1 <;> by_cases h2 : i.2=j.2 <;> simp [Prod.ext_iff,h1,h2]

theorem known_record_support (S : Finset A) (T : ℕ) (K : Matrix (A×N) (A×M) ℂ) :
    Matrix.kronecker (fockRecord S T) (1:CMatrix N)*known T K=
      known T K*Matrix.kronecker (fockRecord S T) (1:CMatrix M) := by
  rw [record_tensor_diagonal,record_tensor_diagonal]
  ext o i
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,known_coefficient]
  by_cases hr : records o.1=records i.1
  · have hh := congrArg (fun R : Records (α:=A) T => LabelsIn S R.2.1) hr
    change LabelsIn S o.1.2.2=LabelsIn S i.1.2.2 at hh
    simp only [hh,mul_comm]
  · simp [hr]

theorem rotation_adjoint_known (U : Matrix.unitaryGroup A ℂ) (T : ℕ)
    (K : Matrix (A×N) (A×M) ℂ) :
    (Matrix.kronecker (fockQ U 1 T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix N)).conjTranspose*
      known T K=known T K*
        (Matrix.kronecker (fockQ U 1 T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix M)).conjTranspose := by
  let RN := Matrix.kronecker (fockQ U 1 T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix N)
  let RM := Matrix.kronecker (fockQ U 1 T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix M)
  have hn : RN.conjTranspose*RN=1 := (ICO.MHSectorCovariance.tensorUnitary (fockQ U 1 T) 1).property.1
  have hm : RM*RM.conjTranspose=1 := (ICO.MHSectorCovariance.tensorUnitary (fockQ U 1 T) 1).property.2
  have he := congrArg (fun X => RN.conjTranspose*X*RM.conjTranspose) (rotation_known U 1 T K)
  change RN.conjTranspose*(RN*known T K)*RM.conjTranspose=
    RN.conjTranspose*(known T K*RM)*RM.conjTranspose at he
  simp only [Matrix.mul_assoc] at he
  rw [←Matrix.mul_assoc RN.conjTranspose RN,hn,Matrix.one_mul,hm,Matrix.mul_one] at he
  exact he.symm

theorem rotated_record_tensor (U : Matrix.unitaryGroup A ℂ) (S : Finset A) (T : ℕ) :
    Matrix.kronecker (rotatedRecord U S T) (1:CMatrix M)=
      Matrix.kronecker (fockQ U 1 T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix M)*
        Matrix.kronecker (fockRecord S T) (1:CMatrix M)*
          (Matrix.kronecker (fockQ U 1 T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix M)).conjTranspose := by
  simp only [rotatedRecord,Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,Matrix.mul_one,Matrix.mul_one]

theorem known_rotated_record_support (U : Matrix.unitaryGroup A ℂ) (S : Finset A) (T : ℕ)
    (K : Matrix (A×N) (A×M) ℂ) :
    Matrix.kronecker (rotatedRecord U S T) (1:CMatrix N)*known T K=
      known T K*Matrix.kronecker (rotatedRecord U S T) (1:CMatrix M) := by
  rw [rotated_record_tensor,rotated_record_tensor]
  simp only [Matrix.mul_assoc]
  rw [rotation_adjoint_known]
  rw [←Matrix.mul_assoc (Matrix.kronecker (fockRecord S T) (1:CMatrix N)) (known T K),
    known_record_support]
  simp only [←Matrix.mul_assoc]
  rw [rotation_known]

#print axioms known_record_support
#print axioms known_rotated_record_support
end
end ICO.C6BosonicKnownSupport
