import ICO.C6BirthFlags
import ICO.C6RightHistorySupport

/-! A causal raw-birth trajectory. The added right-vacuum projector is the
literal zero-occupation projector outside the retained history span. -/
namespace ICO.C6RawFlags
open Matrix QIT ICO.C6BirthFlags ICO.C6RetainedHistory ICO.C6HistoryControlled
  ICO.C6PairedTrajectory ICO.C6PolarFock ICO.C6BosonicFockRotated
  ICO.C6BosonicHistorySupport ICO.C6CacheSpanProjection ICO.C6NumberRotationAlgebra
  ICO.MHFockSwap ICO.RecordingPurifiedProtocol ICO.MHBoundedRecording ICO.MHRectangularAction
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

def historyZero (H:Matrix.unitaryGroup A ℂ) (i T:ℕ) (η:History (A×Bool) i) :
    CMatrix (InputCutoff (α:=A) T) :=
  rotatedNumber (historyUnitary (vectors H i η)) (historyIndices (vectors H i η))ᶜ 0 T

def rawFlagInverse {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ) (i:ℕ)
    (η:History (A×Bool) i) (birth:Bool) : CMatrix (InputCutoff (α:=A) T) :=
  (if birth then rotatedFresh (historyUnitary (vectors H i η)) (historyIndices (vectors H i η)) T*
      symmetricRightOnFock h*(1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)
    else (polarLeftOnFock h)ᴴ)*historyZero H i T η*historySupport (vectors H i η) T

variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def rawFlagStage {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ) (birth:Bool) :
    Matrix (InputCutoff (α:=A) T×Public (A:=A) μ (i+1))
      (InputCutoff (α:=A) T×Public (A:=A) μ i) ℂ :=
  publicStage T K i*Matrix.kronecker (polarLeftOnFock h) (1:CMatrix (Middle (A:=A) μ i))*
    middleStage T H i*controlled (M:=μ i) (fun η=>rawFlagInverse h H i η birth)

def rawFlagRun {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0)) :
    (i:ℕ)→History Bool i→EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ i)
  | 0,_=>z
  | i+1,κ=>rectAct (rawFlagStage h H K i κ.1) (rawFlagRun h H K z i κ.2)

end
end ICO.C6RawFlags

