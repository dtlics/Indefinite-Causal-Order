import ICO.C6WordSplit
import ICO.C6MatrixCovariance
import ICO.C6DephaseChannel

/-! The literal first-quantized decoding of all cache particles, including
their image coordinates and unrestricted quantum side memory. -/
namespace ICO.C6CacheDecode
open QIT Matrix ICO.MHSymmetric ICO.MHCreationCovariance ICO.C6BosonicPolar
  ICO.C6LabelSymmetry ICO.C6WordSplit ICO.C6MatrixCovariance ICO.MHSectorCovariance
open scoped BigOperators ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1400000
universe u
variable {A M : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

abbrev Cache (n : ℕ) := Sector (A := A) n × M
abbrev WordCache (n : ℕ) := (A × TensorPower (A × A) n) × M
abbrev Decoded (n : ℕ) := TensorPower A (n + 1) × (TensorPower A n × M)

def wordEquiv (n : ℕ) : WordCache (A := A) (M := M) n ≃ Decoded (A := A) (M := M) n where
  toFun x := ((x.1.1, (labelImageEquiv n x.1.2).1), ((labelImageEquiv n x.1.2).2, x.2))
  invFun y := ((y.1.1, (labelImageEquiv n).symm (y.1.2, y.2.1)), y.2.2)
  left_inv x := by rcases x with ⟨⟨a, w⟩, m⟩; simp
  right_inv y := by rcases y with ⟨⟨a, w⟩, v, m⟩; simp

def rawDecode (n : ℕ) : Matrix (WordCache (A := A) (M := M) n) (Cache (A := A) (M := M) n) ℂ :=
  Matrix.kronecker (Matrix.kronecker (1 : CMatrix A)
    (occupationEmbedding (a := A × A) n)) (1 : CMatrix M)

def decode (n : ℕ) : Matrix (Decoded (A := A) (M := M) n) (Cache (A := A) (M := M) n) ℂ :=
  (rawDecode n).submatrix (wordEquiv n).symm id

theorem rawDecode_gram (n : ℕ) :
    (rawDecode (A := A) (M := M) n).conjTranspose * rawDecode (A := A) (M := M) n = 1 := by
  simp only [rawDecode, Matrix.kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    occupationEmbedding_gram]
  simp only [Matrix.one_mul, Matrix.one_kronecker_one]

theorem decode_gram (n : ℕ) :
    (decode (A := A) (M := M) n).conjTranspose * decode (A := A) (M := M) n = 1 := by
  rw [decode, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ id (wordEquiv n).symm id, rawDecode_gram,
    Matrix.submatrix_id_id]

def cacheRotation (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    Matrix.unitaryGroup (Cache (A := A) (M := M) n) ℂ :=
  tensorUnitary (inputRotation U 1 n) 1

def rawRotation (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    CMatrix (WordCache (A := A) (M := M) n) :=
  Matrix.kronecker (Matrix.kronecker (U : CMatrix A)
    (unitaryTensorPowerMatrix (leftEdgeUnitary U 1) n :
      CMatrix (TensorPower (A × A) n))) 1

theorem raw_intertwine (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    rawRotation (M := M) U n * rawDecode n =
      rawDecode n * (cacheRotation (M := M) U n : CMatrix (Cache (A := A) (M := M) n)) := by
  simp only [rawRotation, rawDecode, cacheRotation, inputRotation,
    tensorUnitary, symmetricRotation, Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul, occupationRotation_intertwine]
  simp

theorem raw_rotation_split (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    (rawRotation (M := M) U n).submatrix (wordEquiv n).symm (wordEquiv n).symm =
      commonRotation (Z := TensorPower A n × M) U (n + 1) := by
  ext x y
  rcases x with ⟨⟨a, w⟩, v, m⟩
  rcases y with ⟨⟨b, w'⟩, v', m'⟩
  change ((U : CMatrix A) a b *
    (unitaryTensorPowerMatrix (leftEdgeUnitary U 1) n :
      CMatrix (TensorPower (A × A) n))
      ((labelImageEquiv n).symm (w, v)) ((labelImageEquiv n).symm (w', v'))) *
        (1 : CMatrix M) m m' = _
  rw [edge_rotation_split]
  simp only [labelImageEquiv, Equiv.apply_symm_apply]
  change ((U : CMatrix A) a b *
      ((unitaryTensorPowerMatrix U n : CMatrix (TensorPower A n)) w w' *
        (if v = v' then 1 else 0))) * (1 : CMatrix M) m m' =
    ((U : CMatrix A) a b *
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower A n)) w w') *
      (1 : CMatrix (TensorPower A n × M)) (v, m) (v', m')
  by_cases hv : v = v' <;> by_cases hm : m = m' <;>
    simp [Matrix.one_apply, hv, hm, Prod.mk.injEq]

theorem decode_intertwine (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    commonRotation (Z := TensorPower A n × M) U (n + 1) * decode n =
      decode n * (cacheRotation (M := M) U n : CMatrix (Cache (A := A) (M := M) n)) := by
  have h := congrArg (fun B => B.submatrix (wordEquiv n).symm id)
    (raw_intertwine (M := M) U n)
  dsimp only at h
  rw [← Matrix.submatrix_mul_equiv _ _ (wordEquiv n).symm (wordEquiv n).symm id,
    raw_rotation_split] at h
  rw [← Matrix.submatrix_mul_equiv (rawDecode n) _ (wordEquiv n).symm
    (Equiv.refl _) id] at h
  exact h

def CacheInvariant (n : ℕ) (X : CMatrix (Cache (A := A) (M := M) n)) : Prop :=
  ∀ U : Matrix.unitaryGroup A ℂ,
    (cacheRotation (M := M) U n : CMatrix (Cache (A := A) (M := M) n)) * X =
      X * (cacheRotation (M := M) U n : CMatrix (Cache (A := A) (M := M) n))

theorem decoded_invariant (n : ℕ) (X : CMatrix (Cache (A := A) (M := M) n))
    (hX : CacheInvariant n X) : CommonInvariant (n + 1) (decode n * X * (decode n).conjTranspose) := by
  intro U
  let V := tensorUnitary (unitaryTensorPowerMatrix U (n + 1))
    (1 : Matrix.unitaryGroup (TensorPower A n × M) ℂ)
  exact encode_invariant (decode n) (cacheRotation U n) V (decode_intertwine U n) X (hX U)

#print axioms decode_gram
#print axioms decoded_invariant
end
end ICO.C6CacheDecode
