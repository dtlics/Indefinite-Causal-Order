import ICO.C6BosonicBounds
import ICO.C6Polar
import ICO.C6PolarNorm
import ICO.MHSectorCovariance

/-! The actual polar-normalized left creator and its exact rotation covariance.
The construction is made on every fixed particle sector. Its isometry assertion
uses the physically relevant condition that the sector size is below d. -/
namespace ICO.C6BosonicPolar
open QIT ICO.C6BosonicBounds ICO.C6Polar ICO.MHERecordingApprox
  ICO.MHSectorCovariance ICO.MHSymmetric ICO.MHCreationCovariance
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

instance profileNonempty (n : ℕ) : Nonempty (TensorPowerProfile (A×A) n) := by
  let a : A := Classical.choice ‹Nonempty A›
  let w : TensorPower (A×A) n := (tensorPowerEquiv n).symm (fun _ => (a,a))
  exact ⟨⟨tensorPowerTypeProfile n w, tensorPowerTypeProfile_mem_profiles n w⟩⟩

abbrev Sector (n : ℕ) := A × TensorPowerProfile (A×A) n

def leftPolar (n : ℕ) : Matrix (Sector (A:=A) (n+1)) (Sector (A:=A) n) ℂ :=
  polar (symmetricInsertion (α:=A) n)

theorem gram_defect_lt_one {n : ℕ} (hn : n < Fintype.card A) :
    ‖gram (symmetricInsertion (α:=A) n)-1‖ < 1 := by
  apply (symmetricInsertion_gram_defect (A:=A) n).trans_lt
  apply (div_lt_one (by exact_mod_cast Fintype.card_pos (α:=A))).2
  exact_mod_cast hn

theorem leftPolar_isometry {n : ℕ} (hn : n < Fintype.card A) :
    (leftPolar (A:=A) n).conjTranspose * leftPolar (A:=A) n = 1 :=
  polar_isometry _ (gram_defect_lt_one hn)

theorem leftPolar_distance {n : ℕ} (hn : n < Fintype.card A) :
    ‖symmetricInsertion (α:=A) n - leftPolar (A:=A) n‖ ≤
      (n : ℝ) / Fintype.card A :=
  (polar_distance_le_of_defect_lt_one _ (gram_defect_lt_one hn)).trans
    (symmetricInsertion_gram_defect n)

def inputRotation (C D : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    Matrix.unitaryGroup (Sector (A:=A) n) ℂ :=
  tensorUnitary C (symmetricRotation (leftEdgeUnitary C D) n)

def outputRotation (C D : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    Matrix.unitaryGroup (Sector (A:=A) n) ℂ :=
  tensorUnitary D⁻¹ (symmetricRotation (leftEdgeUnitary C D) n)

theorem symmetricInsertion_covariance (C D : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    (outputRotation C D (n+1) : CMatrix (Sector (A:=A) (n+1))) *
        symmetricInsertion (α:=A) n =
      symmetricInsertion (α:=A) n *
        (inputRotation C D n : CMatrix (Sector (A:=A) n)) := by
  have h := normalized_left_covariance C D n
  have h' := congrArg (fun M =>
    Matrix.kronecker ((D⁻¹ : Matrix.unitaryGroup A ℂ) : CMatrix A)
      (1 : CMatrix (TensorPowerProfile (A×A) (n+1))) * M) h
  have hD : ((D⁻¹ : Matrix.unitaryGroup A ℂ) : CMatrix A)*(D : CMatrix A)=1 := by
    exact D.property.1
  have hleft : Matrix.kronecker ((D⁻¹ : Matrix.unitaryGroup A ℂ) : CMatrix A)
      (1 : CMatrix (TensorPowerProfile (A×A) (n+1))) *
      Matrix.kronecker (D : CMatrix A)
      (1 : CMatrix (TensorPowerProfile (A×A) (n+1))) = 1 := by
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul, hD, Matrix.one_mul, Matrix.one_kronecker_one]
  have hright : Matrix.kronecker ((D⁻¹ : Matrix.unitaryGroup A ℂ) : CMatrix A)
      (1 : CMatrix (TensorPowerProfile (A×A) (n+1))) *
      Matrix.kronecker (1 : CMatrix A) (occupationRotation (leftEdgeUnitary C D) (n+1)) =
      (outputRotation C D (n+1) : CMatrix (Sector (A:=A) (n+1))) := by
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
    rfl
  simpa only [← Matrix.mul_assoc, hleft, Matrix.one_mul, hright,
    inputRotation, tensorUnitary, symmetricRotation] using h'.symm

theorem leftPolar_covariance (C D : Matrix.unitaryGroup A ℂ) {n : ℕ}
    (hn : n < Fintype.card A) :
    (outputRotation C D (n+1) : CMatrix (Sector (A:=A) (n+1))) * leftPolar n =
      leftPolar n * (inputRotation C D n : CMatrix (Sector (A:=A) n)) := by
  exact polar_covariant _ (gram_isUnit _ (gram_defect_lt_one hn))
    (inputRotation C D n) (outputRotation C D (n+1))
    (symmetricInsertion_covariance C D n)

theorem leftPolar_image_covariance (C D : Matrix.unitaryGroup A ℂ) {n : ℕ}
    (hn : n < Fintype.card A) :
    (outputRotation C D (n+1) : CMatrix (Sector (A:=A) (n+1))) *
        (leftPolar n * (leftPolar n).conjTranspose) =
      (leftPolar n * (leftPolar n).conjTranspose) *
        (outputRotation C D (n+1) : CMatrix (Sector (A:=A) (n+1))) := by
  have h := leftPolar_covariance C D hn
  have ha := congrArg Matrix.conjTranspose h
  have hu : (inputRotation C D n : CMatrix (Sector (A:=A) n)) *
      (inputRotation C D n : CMatrix (Sector (A:=A) n)).conjTranspose=1 :=
    (inputRotation C D n).property.2
  have hv : (outputRotation C D (n+1) : CMatrix (Sector (A:=A) (n+1))).conjTranspose *
      (outputRotation C D (n+1) : CMatrix (Sector (A:=A) (n+1)))=1 :=
    (outputRotation C D (n+1)).property.1
  simp only [Matrix.conjTranspose_mul] at ha
  have hh := congrArg (fun M =>
    (inputRotation C D n : CMatrix (Sector (A:=A) n))*M*
      (outputRotation C D (n+1) : CMatrix (Sector (A:=A) (n+1)))) ha
  have ht : (inputRotation C D n : CMatrix (Sector (A:=A) n)) *
      (leftPolar n).conjTranspose = (leftPolar n).conjTranspose *
      (outputRotation C D (n+1) : CMatrix (Sector (A:=A) (n+1))) := by
    simpa only [Matrix.mul_assoc, hv, Matrix.mul_one,
      ← Matrix.mul_assoc (inputRotation C D n : CMatrix (Sector (A:=A) n))
        (inputRotation C D n : CMatrix (Sector (A:=A) n)).conjTranspose,
      hu, Matrix.one_mul] using hh
  calc
    _ = ((outputRotation C D (n+1) : CMatrix (Sector (A:=A) (n+1))) *
        leftPolar n) * (leftPolar n).conjTranspose := (Matrix.mul_assoc _ _ _).symm
    _ = _ := by rw [h, Matrix.mul_assoc, ht, ← Matrix.mul_assoc]

#print axioms leftPolar_isometry
#print axioms leftPolar_covariance
#print axioms leftPolar_image_covariance
end
end ICO.C6BosonicPolar
