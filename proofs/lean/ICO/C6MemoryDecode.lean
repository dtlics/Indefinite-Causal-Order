import ICO.C6CacheDecode
import ICO.C6MemoryNatural

/-! The cache decoder factors as identity on the retrieved query and an
isometry on its side memory, which includes all cache image registers. -/
namespace ICO.C6MemoryDecode
open QIT Matrix ICO.C6CacheDecode ICO.C6WordSplit ICO.C6MemoryNatural ICO.MHSymmetric
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
universe u
variable {A M : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

def profileDecode (n : ℕ) : Matrix (TensorPower A n × TensorPower A n)
    (TensorPowerProfile (A × A) n) ℂ :=
  (occupationEmbedding n).submatrix (labelImageEquiv n).symm id

theorem profileDecode_gram (n : ℕ) :
    (profileDecode (A := A) n).conjTranspose * profileDecode (A := A) n = 1 := by
  rw [profileDecode, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ id (labelImageEquiv n).symm id,
    occupationEmbedding_gram, Matrix.submatrix_id_id]

def rawMemoryDecode (n : ℕ) :
    Matrix ((TensorPower A n × TensorPower A n) × M)
      (TensorPowerProfile (A × A) n × M) ℂ :=
  Matrix.kronecker (profileDecode n) (1 : CMatrix M)

theorem rawMemoryDecode_gram (n : ℕ) :
    (rawMemoryDecode (A := A) (M := M) n).conjTranspose *
      rawMemoryDecode (A := A) (M := M) n = 1 := by
  simp only [rawMemoryDecode, Matrix.kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul, profileDecode_gram]
  simp only [Matrix.one_mul, Matrix.one_kronecker_one]

def memoryDecode (n : ℕ) : Matrix (TensorPower A n × (TensorPower A n × M))
    (TensorPowerProfile (A × A) n × M) ℂ :=
  (rawMemoryDecode n).submatrix
    (Equiv.prodAssoc (TensorPower A n) (TensorPower A n) M).symm id

theorem memoryDecode_gram (n : ℕ) :
    (memoryDecode (A := A) (M := M) n).conjTranspose *
      memoryDecode (A := A) (M := M) n = 1 := by
  rw [memoryDecode, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ id
      (Equiv.prodAssoc (TensorPower A n) (TensorPower A n) M).symm id,
    rawMemoryDecode_gram, Matrix.submatrix_id_id]

def cacheHead (n : ℕ) (X : CMatrix (Cache (A := A) (M := M) n)) :
    CMatrix (A × (TensorPowerProfile (A × A) n × M)) :=
  X.submatrix (Equiv.prodAssoc A (TensorPowerProfile (A × A) n) M).symm
    (Equiv.prodAssoc A (TensorPowerProfile (A × A) n) M).symm

theorem decode_head_factor (n : ℕ) :
    (decode (A := A) (M := M) n).submatrix
      (Equiv.prodAssoc A (TensorPower A n) (TensorPower A n × M)).symm
      (Equiv.prodAssoc A (TensorPowerProfile (A × A) n) M).symm =
      queryEmbedding (A := A) (memoryDecode (M := M) n) := by
  ext x y
  change ((1 : CMatrix A) x.1 y.1 *
    occupationEmbedding n ((labelImageEquiv n).symm (x.2.1, x.2.2.1)) y.2.1) *
      (1 : CMatrix M) x.2.2.2 y.2.2 =
    (1 : CMatrix A) x.1 y.1 *
      (occupationEmbedding n ((labelImageEquiv n).symm (x.2.1, x.2.2.1)) y.2.1 *
        (1 : CMatrix M) x.2.2.2 y.2.2)
  ring

theorem decoded_head (n : ℕ) (X : CMatrix (Cache (A := A) (M := M) n)) :
    ICO.C6DephaseChannel.headMatrix n (decode n * X * (decode n).conjTranspose) =
      queryEmbedding (A := A) (memoryDecode (M := M) n) * cacheHead n X *
        (queryEmbedding (A := A) (memoryDecode (M := M) n)).conjTranspose := by
  let eo := (Equiv.prodAssoc A (TensorPower A n) (TensorPower A n × M)).symm
  let ei := (Equiv.prodAssoc A (TensorPowerProfile (A × A) n) M).symm
  change (decode n * X * (decode n).conjTranspose).submatrix eo eo = _
  have houter := Matrix.submatrix_mul_equiv (decode (A := A) (M := M) n * X)
    (decode (A := A) (M := M) n).conjTranspose eo ei eo
  have hinner := Matrix.submatrix_mul_equiv (decode (A := A) (M := M) n) X eo ei ei
  rw [← houter, ← hinner,
    ← Matrix.conjTranspose_submatrix (decode (A := A) (M := M) n) eo ei]
  rw [decode_head_factor]
  rfl

#print axioms memoryDecode_gram
#print axioms decoded_head
end
end ICO.C6MemoryDecode
