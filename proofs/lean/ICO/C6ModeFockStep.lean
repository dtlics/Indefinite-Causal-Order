import ICO.C6ModeFockBirth
import ICO.C6KnownTensor
import ICO.LudersPromise

namespace ICO.C6ModeFockStep
open Matrix QIT ICO.C6ModeFockBirth ICO.C6ModeFockCore ICO.C6ModeFockEncoding
  ICO.C6ModeFockRetrieval ICO.C6DecodedHistory ICO.C6KnownTensor
  ICO.C6RawSupportedStage ICO.C6RawFlagSlices ICO.C6AcceptedBirthFactor
  ICO.C6AcceptedModes ICO.C6ActualAcceptedModes ICO.C6ActualResidualWeight
  ICO.C6FlagCount ICO.C6CacheDecode ICO.C6CacheQueryBound ICO.C6PolarFock
  ICO.C6BosonicReencoding ICO.C6FockQueryMatrix ICO.C6ChoiceMeasurement
  ICO.MHBoundedRecording ICO.MHFockKnownOperation ICO.RecordingPurifiedProtocol
open scoped Matrix BigOperators
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A M:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

theorem query_rankOne (H:Matrix.unitaryGroup A ℂ) (b:Bool) (j:A) :
    rankOne (WithLp.toLp 2 (queryVector H (b,j)))=
      ICO.SwitchObservable.basisProjection (outcomeBasis H b:CMatrix A) j := by
  rw [actual_column,ICO.LudersPromise.basisProjection_rankOne]
  ext x y
  rfl

theorem retrieval_tensor {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (n:ℕ) (η:History (A×Bool) n) (b:Bool) (j:A) :
    Matrix.kronecker (bareCore h H n η j b false) (1:CMatrix M)=
      retrieval (M:=M) h (outcomeBasis H b) j := by
  unfold retrieval
  rw [known_tensor]
  simp only [bareCore,bareInverse,Bool.false_eq_true,if_false,query_rankOne,
    Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ←Matrix.mul_kronecker_mul,Matrix.one_mul]

def historyCore (H:Matrix.unitaryGroup A ℂ) (n:ℕ) (η:History (A×Bool) n)
    (κ:History Bool n) (b f:Bool) (j:A) :
    Matrix (ImageCache (A:=A) (flagCount (n+1) (f,κ)) M)
      (ImageCache (A:=A) (flagCount n κ) M) ℂ := by
  change Matrix (ImageCache (A:=A) (flagCount n κ+if f then 1 else 0) M)
    (ImageCache (A:=A) (flagCount n κ) M) ℂ
  exact core (M:=M) (outcomeBasis H b) j (birthAmplitude H n η b j) (flagCount n κ) f

theorem core_encoding {t T n:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (η:History (A×Bool) n) (κ:History Bool n) (hs:2*flagCount n κ+1≤t)
    (b f:Bool) (j:A) :
    Matrix.kronecker (bareCore h H n η j b f) (1:CMatrix M)*
      encoding T (flagCount n κ) (flagCount n κ) (by omega)
        (modes (rightVectors H n η) κ)=
      encoding (M:=M) T (flagCount (n+1) (f,κ)) (flagCount (n+1) (f,κ))
        (by cases f <;> simp only [flagCount, Bool.false_eq_true,reduceIte] <;> omega)
        (modes (rightVectors H (n+1) ((j,b),η)) (f,κ))*
      historyCore (M:=M) H n η κ b f j := by
  cases f with
  | false=>
    dsimp only [historyCore,core,flagCount]
    have he:=rightModes_false H n η κ b j
    change modes (rightVectors H (n+1) ((j,b),η)) (false,κ)=_ at he
    rw [he,retrieval_tensor]
    exact retrieval_encoding_any h (by omega) _ _ _
  | true=>
    simpa only [historyCore,core_true,flagCount,if_true,nextModes,Fin.cast_refl] using
      birth_encoding (l:=flagCount n κ) h H η κ (by omega) b j

theorem choice_encoding (T l:ℕ) (h:l+l≤T) (v:Fin l→EuclideanSpace ℂ A)
    (b:Bool) :
    Matrix.kronecker (1:CMatrix (InputCutoff (α:=A) T)) (choiceProject b M)*
      encoding T l l h v=
      encoding T l l h v*choiceImages (A:=A) (M:=M) l b := by
  rw [←known_memory,encoding_known]
  rfl

variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem step_encoding {t T n:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (η:History (A×Bool) n) (κ:History Bool n) (hs:2*flagCount n κ+1≤t)
    (b f:Bool) (j:A) :
    known T (smallKnown (K n))*Matrix.kronecker (bareCore h H n η j b f)
      (choiceProject b (μ n))*
      encoding T (flagCount n κ) (flagCount n κ) (by omega)
        (modes (rightVectors H n η) κ)=
      encoding (M:=Bool×μ (n+1)) T (flagCount (n+1) (f,κ)) (flagCount (n+1) (f,κ))
        (by cases f <;> simp only [flagCount, Bool.false_eq_true,reduceIte] <;> omega)
        (modes (rightVectors H (n+1) ((j,b),η)) (f,κ))*
      C6DecodedHistory.stage H K n η κ j b f := by
  have ht:Matrix.kronecker (bareCore h H n η j b f) (choiceProject b (μ n))=
      Matrix.kronecker (bareCore h H n η j b f) (1:CMatrix (Bool×μ n))*
      Matrix.kronecker (1:CMatrix (InputCutoff (α:=A) T)) (choiceProject b (μ n)) := by
    simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.mul_one,Matrix.one_mul]
  rw [ht,Matrix.mul_assoc,Matrix.mul_assoc,choice_encoding,
    ←Matrix.mul_assoc (Matrix.kronecker (bareCore h H n η j b f) (1:CMatrix (Bool×μ n))),
    core_encoding h H η κ hs b f j]
  rw [←Matrix.mul_assoc,←Matrix.mul_assoc,encoding_known]
  simp only [Matrix.mul_assoc,id_eq]
  dsimp only [C6DecodedHistory.stage,knownImages,historyCore,flagCount]
  simp only [Matrix.mul_assoc,id_eq]
  rfl

#print axioms step_encoding
end
end ICO.C6ModeFockStep
