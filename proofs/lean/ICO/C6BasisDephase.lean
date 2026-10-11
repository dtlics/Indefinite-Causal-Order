import ICO.C6DephaseChannel
import ICO.C6MatrixCovariance

/-! Literal known-basis dephasing with arbitrary quantum memory. -/
namespace ICO.C6BasisDephase
open QIT Matrix ICO.C6DephaseChannel ICO.C6MatrixCovariance ICO.SwitchObservable ICO.MHWordRotation
open scoped BigOperators ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1200000
universe u
variable {A M : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

def headRotation (U : Matrix.unitaryGroup A ℂ) : Matrix.unitaryGroup (A × M) ℂ :=
  tensorUnitary U 1

def sideRotation (V : Matrix.unitaryGroup M ℂ) : Matrix.unitaryGroup (A × M) ℂ :=
  tensorUnitary 1 V

def basisMap (U : Matrix.unitaryGroup A ℂ) : MatrixMap (A × M) (A × M) :=
  ICO.AllChannelDilation.oracleMap (basisProjection (U : CMatrix A))

theorem basis_kraus (U : Matrix.unitaryGroup A ℂ) (j : A) :
    Matrix.kronecker (basisProjection (U : CMatrix A) j) (1 : CMatrix M) =
    (headRotation (M := M) U : CMatrix (A × M)) * pinchingKraus j *
      (headRotation (M := M) U : CMatrix (A × M)).conjTranspose := by
  simp only [headRotation, tensorUnitary, pinchingKraus, Matrix.kronecker,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp [basisProjection]

theorem basis_apply (U : Matrix.unitaryGroup A ℂ) (X : CMatrix (A × M)) :
    basisMap U X =
      (headRotation (M := M) U : CMatrix (A × M)) *
        pinchingMap ((headRotation (M := M) U : CMatrix (A × M)).conjTranspose * X *
          (headRotation (M := M) U : CMatrix (A × M))) *
        (headRotation (M := M) U : CMatrix (A × M)).conjTranspose := by
  change (∑ j : A, _ * X * _) = _ * (∑ j : A, _ * _ * _) * _
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [basis_kraus U j]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

theorem pinching_side_commute (V : Matrix.unitaryGroup M ℂ) (j : A) :
    pinchingKraus j * (sideRotation (A := A) V : CMatrix (A × M)) =
      (sideRotation (A := A) V : CMatrix (A × M)) * pinchingKraus j := by
  simp only [pinchingKraus, sideRotation, tensorUnitary, Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

theorem pinching_side_conjugate (V : Matrix.unitaryGroup M ℂ) (X : CMatrix (A × M)) :
    pinchingMap ((sideRotation (A := A) V : CMatrix (A × M)) * X *
        (sideRotation (A := A) V : CMatrix (A × M)).conjTranspose) =
      (sideRotation (A := A) V : CMatrix (A × M)) * pinchingMap X *
        (sideRotation (A := A) V : CMatrix (A × M)).conjTranspose := by
  change (∑ j : A, _ * _ * _) = _ * (∑ j : A, _ * X * _) * _
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have h := pinching_side_commute (A := A) V j
  have ha := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_mul] at ha
  calc
    _ = (pinchingKraus j * (sideRotation (A := A) V : CMatrix (A × M))) * X *
      ((sideRotation (A := A) V : CMatrix (A × M)).conjTranspose * (pinchingKraus j).conjTranspose) := by
        simp only [Matrix.mul_assoc]
    _ = ((sideRotation (A := A) V : CMatrix (A × M)) * pinchingKraus j) * X *
      ((pinchingKraus j).conjTranspose * (sideRotation (A := A) V : CMatrix (A × M)).conjTranspose) := by rw [h, ha]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem head_side_factor (U : Matrix.unitaryGroup A ℂ) (V : Matrix.unitaryGroup M ℂ) :
    (headRotation (M := M) U : CMatrix (A × M)) * (sideRotation (A := A) V : CMatrix (A × M)) =
      Matrix.kronecker (U : CMatrix A) (V : CMatrix M) := by
  simp only [headRotation, sideRotation, tensorUnitary, Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul]
  simp

theorem invariant_basis_apply (U : Matrix.unitaryGroup A ℂ) (V : Matrix.unitaryGroup M ℂ)
    (X : CMatrix (A × M))
    (hX : Matrix.kronecker (U : CMatrix A) (V : CMatrix M) * X =
      X * Matrix.kronecker (U : CMatrix A) (V : CMatrix M)) :
    basisMap U X = Matrix.kronecker (U : CMatrix A) (V : CMatrix M) *
      pinchingMap X * (Matrix.kronecker (U : CMatrix A) (V : CMatrix M)).conjTranspose := by
  let R := headRotation (M := M) U
  let S := sideRotation (A := A) V
  have hs : (S : CMatrix (A × M)) * (S : CMatrix (A × M)).conjTranspose = 1 := S.property.2
  have hr : (R : CMatrix (A × M)).conjTranspose * (R : CMatrix (A × M)) = 1 := R.property.1
  have hx : (R : CMatrix (A × M)) * (S : CMatrix (A × M)) * X =
    X * ((R : CMatrix (A × M)) * (S : CMatrix (A × M))) := by
    simpa only [R, S, head_side_factor] using hX
  have hh := congrArg (fun B => (R : CMatrix (A × M)).conjTranspose * B *
    (S : CMatrix (A × M)).conjTranspose) hx
  have he : (R : CMatrix (A × M)).conjTranspose * X * (R : CMatrix (A × M)) =
    (S : CMatrix (A × M)) * X * (S : CMatrix (A × M)).conjTranspose := by
    simpa only [Matrix.mul_assoc,
      ← Matrix.mul_assoc (R : CMatrix (A × M)).conjTranspose (R : CMatrix (A × M)),
      hr, Matrix.one_mul, hs, Matrix.mul_one] using hh.symm
  rw [basis_apply]
  change (R : CMatrix (A × M)) * pinchingMap ((R : CMatrix (A × M)).conjTranspose * X *
    (R : CMatrix (A × M))) * (R : CMatrix (A × M)).conjTranspose = _
  rw [he, pinching_side_conjugate]
  rw [← head_side_factor U V]
  simp only [R, S, Matrix.conjTranspose_mul, Matrix.mul_assoc]

#print axioms basis_apply
#print axioms invariant_basis_apply
end
end ICO.C6BasisDephase
