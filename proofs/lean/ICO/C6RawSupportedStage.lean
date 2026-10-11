import ICO.C6RawFlagSlices

namespace ICO.C6RawSupportedStage
open Matrix QIT ICO.C6RawFlagSlices ICO.C6RawFlags ICO.C6PolarFock
  ICO.C6RetainedHistory ICO.C6BosonicHistorySupport ICO.C6CacheSpanProjection
  ICO.C6BosonicFockRotated ICO.C6BosonicReencoding ICO.C6FockQueryMatrix
  ICO.C6ChoiceMeasurement ICO.MHFockKnownOperation ICO.MHBoundedRecording
  ICO.MHFockSwap ICO.RecordingPurifiedProtocol
open scoped Matrix
noncomputable section
set_option maxHeartbeats 1300000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def bareInverse {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ) (i:ℕ)
    (η:History (A×Bool) i) (f:Bool) : CMatrix (InputCutoff (α:=A) T) :=
  if f then rotatedFresh (historyUnitary (vectors H i η)) (historyIndices (vectors H i η)) T*
    symmetricRightOnFock h*(1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)
  else (polarLeftOnFock h)ᴴ

def bareCore {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ) (i:ℕ)
    (η:History (A×Bool) i) (j:A) (b f:Bool) : CMatrix (InputCutoff (α:=A) T) :=
  polarLeftOnFock h*queryMatrix (rankOne (WithLp.toLp 2 (queryVector H (b,j)))) T*
    bareInverse h H i η f

theorem branchStage_factor {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ)
    (η:History (A×Bool) i) (j:A) (b f:Bool) :
    branchStage h H K i η j b f=
      known T (smallKnown (K i))*
        Matrix.kronecker (bareCore h H i η j b f) (choiceProject b (μ i))*
        Matrix.kronecker (historyZero H i T η) (1:CMatrix (Bool×μ i))*
        Matrix.kronecker (historySupport (vectors H i η) T) (1:CMatrix (Bool×μ i)) := by
  have he :
      Matrix.kronecker (bareCore h H i η j b f) (choiceProject b (μ i))*
        Matrix.kronecker (historyZero H i T η) (1:CMatrix (Bool×μ i))*
        Matrix.kronecker (historySupport (vectors H i η) T) (1:CMatrix (Bool×μ i))=
      Matrix.kronecker (polarLeftOnFock h*
        queryMatrix (rankOne (WithLp.toLp 2 (queryVector H (b,j)))) T*
        rawFlagInverse h H i η f) (choiceProject b (μ i)) := by
    simp only [Matrix.kronecker]
    rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,Matrix.mul_one,Matrix.mul_one]
    simp only [bareCore,bareInverse,rawFlagInverse,Matrix.mul_assoc]
  rw [branchStage,branchMiddle_tensor,←he]
  simp only [Matrix.mul_assoc]

theorem branchStage_on_supported {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ)
    (η:History (A×Bool) i) (j:A) (b f:Bool)
    (v:InputCutoff (α:=A) T×(Bool×μ i)→ℂ)
    (hS:Matrix.kronecker (historySupport (vectors H i η) T) (1:CMatrix (Bool×μ i))*ᵥv=v)
    (hZ:Matrix.kronecker (historyZero H i T η) (1:CMatrix (Bool×μ i))*ᵥv=v) :
    branchStage h H K i η j b f*ᵥv=
      known T (smallKnown (K i))*ᵥ
        (Matrix.kronecker (bareCore h H i η j b f) (choiceProject b (μ i))*ᵥv) := by
  rw [branchStage_factor]
  simp only [←Matrix.mulVec_mulVec,hS,hZ]

#print axioms branchStage_on_supported
end
end ICO.C6RawSupportedStage
