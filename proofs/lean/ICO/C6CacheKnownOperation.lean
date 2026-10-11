import ICO.C6CacheReference

/-! Arbitrary known operations on query and memory commute with the
private cache rotation. No restriction on entanglement is imposed. -/
namespace ICO.C6CacheKnownOperation
open QIT Matrix ICO.C6CacheReference ICO.C6CacheQueryBound ICO.C6CacheDecode
  ICO.C6MatrixCovariance ICO.C6BosonicPolar ICO.MHSectorCovariance
  ICO.MHSymmetric ICO.MHCreationCovariance
open scoped Matrix
noncomputable section
set_option maxHeartbeats 1700000
universe u
variable {A M N : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

def externalEquiv (n : ℕ) (M : Type u) :
    Cache (A := A) (M := M) n ≃ TensorPowerProfile (A×A) n × (A×M) where
  toFun x := (x.1.2,(x.1.1,x.2))
  invFun x := ((x.2.1,x.1),x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def externalLift (n : ℕ) (K : Matrix (A×N) (A×M) ℂ) :
    Matrix (Cache (A := A) (M := N) n) (Cache (A := A) (M := M) n) ℂ :=
  (Matrix.kronecker (1 : CMatrix (TensorPowerProfile (A×A) n)) K).submatrix
    (externalEquiv n N) (externalEquiv n M)

theorem stored_external_factor (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    (storedRotation (M := M) U n : CMatrix (Cache (A := A) (M := M) n)) =
      (Matrix.kronecker (occupationRotation (leftEdgeUnitary U 1) n)
        (1 : CMatrix (A×M))).submatrix (externalEquiv n M) (externalEquiv n M) := by
  ext ⟨⟨a,p⟩,m⟩ ⟨⟨b,q⟩,l⟩
  simp [storedRotation, outputRotation, tensorUnitary, symmetricRotation,
    externalEquiv, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    mul_assoc, mul_left_comm, mul_comm, ite_and]

theorem externalLift_covariance (U : Matrix.unitaryGroup A ℂ) (n : ℕ)
    (K : Matrix (A×N) (A×M) ℂ) :
    (storedRotation (M := N) U n : CMatrix (Cache (A := A) (M := N) n))*externalLift n K =
      externalLift n K*(storedRotation (M := M) U n : CMatrix (Cache (A := A) (M := M) n)) := by
  let R := occupationRotation (leftEdgeUnitary U 1) n
  have h : Matrix.kronecker R (1 : CMatrix (A×N))*Matrix.kronecker 1 K =
      Matrix.kronecker 1 K*Matrix.kronecker R (1 : CMatrix (A×M)) := by
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.mul_one, Matrix.one_mul]
  have hh := congrArg (fun B => B.submatrix (externalEquiv (A := A) n N)
    (externalEquiv (A := A) n M)) h
  dsimp only at hh
  rw [← Matrix.submatrix_mul_equiv _ _ _ (externalEquiv n N),
    ← Matrix.submatrix_mul_equiv _ _ _ (externalEquiv n M)] at hh
  simpa only [R, externalLift, ← stored_external_factor] using hh

theorem externalLift_gram (n : ℕ) (K : Matrix (A×N) (A×M) ℂ)
    (hK : K.conjTranspose*K=1) :
    (externalLift n K).conjTranspose*externalLift n K=1 := by
  rw [externalLift, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ (externalEquiv n N)]
  have h : (Matrix.kronecker (1 : CMatrix (TensorPowerProfile (A×A) n)) K).conjTranspose*
      Matrix.kronecker (1 : CMatrix (TensorPowerProfile (A×A) n)) K=
        (1 : CMatrix (TensorPowerProfile (A×A) n × (A×M))) := by
    simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
    rw [← Matrix.mul_kronecker_mul, hK, Matrix.mul_one, Matrix.one_kronecker_one]
  rw [h, Matrix.submatrix_one_equiv]

theorem known_preserves_stored (n : ℕ) (K : Matrix (A×N) (A×M) ℂ)
    (X : CMatrix (Cache (A := A) (M := M) n)) (hi : StoredInvariant n X) :
    StoredInvariant n (externalLift n K*X*(externalLift n K).conjTranspose) := by
  intro U
  exact encode_invariant (externalLift n K) (storedRotation U n) (storedRotation U n)
    (externalLift_covariance U n K) X (hi U)

#print axioms externalLift_gram
#print axioms known_preserves_stored
end
end ICO.C6CacheKnownOperation
