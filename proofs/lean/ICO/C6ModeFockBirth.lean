import ICO.C6ModeFockCore
import ICO.C6RawSelectedMemory
import ICO.C6PrivateAppendAlgebra
import ICO.C6RawSupportedStage

namespace ICO.C6ModeFockBirth
open Matrix QIT ICO.C6ModeFockCore ICO.C6ModeFockEncoding ICO.C6DecodedHistory
  ICO.C6RawSelectedMemory ICO.C6PrivateAppendAlgebra ICO.C6PrivateImageAppend
  ICO.C6SelectedImageFactor ICO.C6AcceptedBirthFactor ICO.C6AcceptedModes
  ICO.C6ActualAcceptedModes ICO.C6ActualResidualWeight ICO.C6FlagCount
  ICO.C6TwoFockVisible ICO.C6CacheDecode ICO.C6CacheQueryBound
  ICO.C6RetainedSectorOperations ICO.C6PolarFock ICO.C6RetainedHistory
  ICO.C6BosonicFockRotated ICO.C6CacheSpanProjection ICO.C6BosonicReencoding
  ICO.C6FockQueryMatrix ICO.C6ChoiceMeasurement ICO.C6RightImageErasure
  ICO.C6RawSupportedStage ICO.MHFockSwap ICO.MHBoundedRecording
  ICO.RecordingPurifiedProtocol
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1900000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A M:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

def measured {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ) (n:ℕ)
    (η:History (A×Bool) n) (b:Bool) (j:A) : CMatrix (InputCutoff (α:=A) T×M) :=
  Matrix.kronecker (queryMatrix (rankOne (WithLp.toLp 2 (queryVector H (b,j)))) T*
    rotatedFresh (historyUnitary (vectors H n η)) (historyIndices (vectors H n η)) T*
      symmetricRightOnFock h) (1:CMatrix M)

def nextModes (H:Matrix.unitaryGroup A ℂ) (n:ℕ) (η:History (A×Bool) n)
    (κ:History Bool n) (b:Bool) (j:A) : Fin (flagCount n κ+1)→EuclideanSpace ℂ A :=
  fun k=>modes (rightVectors H (n+1) ((j,b),η)) (n:=n+1) (true,κ)
    (Fin.cast (flagCount_true n κ).symm k)

theorem measured_encoding {t T l n:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (η:History (A×Bool) n) (κ:History Bool n) (hs:l+flagCount n κ≤t) (b:Bool) (j:A) :
    measured (M:=M) h H n η b j*
      encoding T l (flagCount n κ) (by omega) (modes (rightVectors H n η) κ)=
      birthAmplitude H n η b j •
        (encoding T l (flagCount n κ+1) (by omega) (nextModes H n η κ b j)*
          appendPrivate (flagCount n κ) (imagePreparation (M:=M) (outcomeBasis H b) l j)) := by
  rw [encoding,←Matrix.mul_assoc]
  change (measured (M:=M) h H n η b j*memoryJ T l (flagCount n κ) (by omega))*_= _
  rw [show measured (M:=M) h H n η b j*memoryJ T l (flagCount n κ) (by omega)=_
    from actual_measured_raw_memory h hs H n η b j]
  rw [Matrix.mul_assoc,actual_factorization_memory,Matrix.mul_smul]
  simp only [encoding,nextModes,Matrix.mul_assoc]
  rfl

theorem birth_tensor {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (n:ℕ) (η:History (A×Bool) n) (b:Bool) (j:A) :
    Matrix.kronecker (bareCore h H n η j b true) (1:CMatrix M)=
      Matrix.kronecker (polarLeftOnFock (α:=A) h) (1:CMatrix M)*
        measured (M:=M) h H n η b j*
        (1-Matrix.kronecker (polarLeftOnFock h) (1:CMatrix M)*
          (Matrix.kronecker (polarLeftOnFock h) (1:CMatrix M))ᴴ) := by
  have hc:(1-Matrix.kronecker (polarLeftOnFock (α:=A) h) (1:CMatrix M)*
      (Matrix.kronecker (polarLeftOnFock h) (1:CMatrix M))ᴴ)=
      Matrix.kronecker (1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ) (1:CMatrix M) := by
    rw [ICO.C6TwoFockMemory.kronecker_sub_left]
    simp only [Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
      ←Matrix.mul_kronecker_mul,Matrix.one_mul,
      Matrix.one_kronecker_one]
  rw [hc]
  simp only [bareCore,bareInverse,↓reduceIte,measured,Matrix.kronecker,
    ←Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_assoc]

theorem birth_encoding {t T l n:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (η:History (A×Bool) n) (κ:History Bool n) (hs:l+flagCount n κ+1≤t) (b:Bool) (j:A) :
    Matrix.kronecker (bareCore h H n η j b true) (1:CMatrix M)*
      encoding T l (flagCount n κ) (by omega) (modes (rightVectors H n η) κ)=
      encoding T (l+1) (flagCount n κ+1) (by omega) (nextModes H n η κ b j)*
        (birthAmplitude H n η b j •
          appendPrivate (flagCount n κ) (birthMatrix (M:=M) (outcomeBasis H b) l j)) := by
  rw [birth_tensor,Matrix.mul_assoc,Matrix.mul_assoc,missing_encoding h (by omega),
    ←Matrix.mul_assoc (measured (M:=M) h H n η b j),measured_encoding h H η κ (by omega) b j]
  simp only [Matrix.smul_mul,Matrix.mul_smul]
  apply congrArg (fun D=>birthAmplitude H n η b j • D)
  rw [←Matrix.mul_assoc,←Matrix.mul_assoc,left_encoding (l:=l) (r:=flagCount n κ+1) h (by omega)]
  simp only [Matrix.mul_assoc]
  apply congrArg (fun D=>encoding (M:=M) T (l+1) (flagCount n κ+1) (by omega)
    (nextModes H n η κ b j)*D)
  rw [←Matrix.mul_assoc,←append_post,←append_pre]
  rfl

#print axioms birth_encoding
end
end ICO.C6ModeFockBirth
