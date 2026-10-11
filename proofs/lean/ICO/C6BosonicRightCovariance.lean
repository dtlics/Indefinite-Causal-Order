import ICO.C6BosonicRight

/-! Exact covariance of the polar inverse-oracle creator. -/
namespace ICO.C6BosonicRightCovariance
open QIT ICO.C6Polar ICO.C6BosonicPolar ICO.C6BosonicRight
  ICO.MHSectorCovariance ICO.MHSymmetric ICO.MHRightCovariance
  ICO.MHOccupationCovariance
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def rightInputRotation (C D : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    Matrix.unitaryGroup (Sector (A:=A) n) ℂ :=
  tensorUnitary C (symmetricRotation (rightEdgeUnitary C D) n)

def rightOutputRotation (C D : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    Matrix.unitaryGroup (Sector (A:=A) n) ℂ :=
  tensorUnitary D⁻¹ (symmetricRotation (rightEdgeUnitary C D) n)

theorem normalized_right_covariance (C D : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    Matrix.kronecker (D : CMatrix A) (1 : CMatrix (TensorPowerProfile (A×A) (n+1))) *
        rightInsertion (A:=A) n * Matrix.kronecker (C : CMatrix A)
          (occupationRotation (rightEdgeUnitary C D) n) =
      Matrix.kronecker (1 : CMatrix A) (occupationRotation (rightEdgeUnitary C D) (n+1)) *
        rightInsertion (A:=A) n := by
  rw [rightInsertion]
  simp only [Matrix.mul_smul,Matrix.smul_mul]
  exact congrArg (fun M => (Real.sqrt (Fintype.card A) : ℂ)⁻¹ • M)
    (occupationRightCreator_covariance C D n)

theorem rightInsertion_covariance (C D : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    (rightOutputRotation C D (n+1) : CMatrix (Sector (A:=A) (n+1))) *
        rightInsertion (A:=A) n =
      rightInsertion (A:=A) n *
        (rightInputRotation C D n : CMatrix (Sector (A:=A) n)) := by
  have h := normalized_right_covariance C D n
  have h' := congrArg (fun M =>
    Matrix.kronecker ((D⁻¹ : Matrix.unitaryGroup A ℂ) : CMatrix A)
      (1 : CMatrix (TensorPowerProfile (A×A) (n+1))) * M) h
  have hD : ((D⁻¹ : Matrix.unitaryGroup A ℂ) : CMatrix A)*(D : CMatrix A)=1 := D.property.1
  have hleft : Matrix.kronecker ((D⁻¹ : Matrix.unitaryGroup A ℂ) : CMatrix A)
      (1 : CMatrix (TensorPowerProfile (A×A) (n+1))) *
      Matrix.kronecker (D : CMatrix A)
      (1 : CMatrix (TensorPowerProfile (A×A) (n+1))) = 1 := by
    simp only [Matrix.kronecker]
    rw [←Matrix.mul_kronecker_mul,hD,Matrix.one_mul,Matrix.one_kronecker_one]
  have hright : Matrix.kronecker ((D⁻¹ : Matrix.unitaryGroup A ℂ) : CMatrix A)
      (1 : CMatrix (TensorPowerProfile (A×A) (n+1))) *
      Matrix.kronecker (1 : CMatrix A) (occupationRotation (rightEdgeUnitary C D) (n+1)) =
      (rightOutputRotation C D (n+1) : CMatrix (Sector (A:=A) (n+1))) := by
    simp only [Matrix.kronecker]
    rw [←Matrix.mul_kronecker_mul,Matrix.mul_one,Matrix.one_mul]
    rfl
  simpa only [←Matrix.mul_assoc,hleft,Matrix.one_mul,hright,
    rightInputRotation,tensorUnitary,symmetricRotation] using h'.symm

theorem rightPolar_covariance (C D : Matrix.unitaryGroup A ℂ) {n : ℕ}
    (hn : n<Fintype.card A) :
    (rightOutputRotation C D (n+1) : CMatrix (Sector (A:=A) (n+1))) * rightPolar n =
      rightPolar n * (rightInputRotation C D n : CMatrix (Sector (A:=A) n)) := by
  exact polar_covariant _ (gram_isUnit _ (rightInsertion_defect_lt_one hn))
    (rightInputRotation C D n) (rightOutputRotation C D (n+1))
    (rightInsertion_covariance C D n)

#print axioms rightPolar_covariance
end
end ICO.C6BosonicRightCovariance
