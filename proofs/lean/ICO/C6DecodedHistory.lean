import ICO.C6SelectedImageFactor
import ICO.C6ModeFockRetrieval
import ICO.C6RawFlagSlices

/-! A literal cache-and-private-images realization of every retained branch.
All matrices are explicit; the fresh coefficient is the actual residual norm. -/
namespace ICO.C6DecodedHistory
open Matrix QIT ICO.C6SelectedImageFactor ICO.C6PrivateImageAppend
  ICO.C6RetainedSectorOperations ICO.C6CacheDecode ICO.C6CacheQueryBound
  ICO.C6CacheKnownOperation ICO.C6ModeFockRetrieval ICO.C6RawFlagSlices
  ICO.C6AcceptedBirthFactor ICO.C6ActualAcceptedModes ICO.C6FlagCount
  ICO.C6ActualResidualWeight ICO.RecordingPurifiedProtocol
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A M N:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

abbrev ImageCache (r:ℕ) (M:Type) := Cache (A:=A) (M:=M) r×(Fin r→A)

def missing : (r:ℕ)→CMatrix (Cache (A:=A) (M:=M) r)
  | 0=>1
  | r+1=>1-memoryPolar r*(memoryPolar r)ᴴ

def retrieved (U:Matrix.unitaryGroup A ℂ) (j:A) :
    (r:ℕ)→CMatrix (Cache (A:=A) (M:=M) r)
  | 0=>0
  | r+1=>cacheRetrieval U r j

def birthMatrix (U:Matrix.unitaryGroup A ℂ) (r:ℕ) (j:A) :
    Matrix (Cache (A:=A) (M:=M) (r+1)×A) (Cache (A:=A) (M:=M) r) ℂ :=
  Matrix.kronecker (memoryPolar r) (1:CMatrix A)*
    imagePreparation U r j*missing r

def knownImages (r:ℕ) (K:Matrix (A×N) (A×M) ℂ) :
    Matrix (ImageCache (A:=A) r N) (ImageCache (A:=A) r M) ℂ :=
  Matrix.kronecker (externalLift r K) (1:CMatrix (Fin r→A))

def choiceImages (r:ℕ) (b:Bool) : CMatrix (ImageCache (A:=A) r (Bool×M)) :=
  knownImages r (Matrix.kronecker (1:CMatrix A) (choiceProject b M))

def core (U:Matrix.unitaryGroup A ℂ) (j:A) (c:ℂ) (r:ℕ) (f:Bool) :
    Matrix (ImageCache (A:=A) (r+if f then 1 else 0) M) (ImageCache (A:=A) r M) ℂ := by
  cases f
  · exact Matrix.kronecker (retrieved (M:=M) U j r) (1:CMatrix (Fin r→A))
  · exact c • appendPrivate r (birthMatrix (M:=M) U r j)

@[simp] theorem core_false (U:Matrix.unitaryGroup A ℂ) (j:A) (c:ℂ) (r:ℕ) :
    core (M:=M) U j c r false=
      Matrix.kronecker (retrieved (M:=M) U j r) (1:CMatrix (Fin r→A)) := rfl

@[simp] theorem core_true (U:Matrix.unitaryGroup A ℂ) (j:A) (c:ℂ) (r:ℕ) :
    core (M:=M) U j c r true=c • appendPrivate r (birthMatrix (M:=M) U r j) := rfl

variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def stage (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ)
    (η:History (A×Bool) i) (κ:History Bool i) (j:A) (b f:Bool) :
    Matrix (ImageCache (A:=A) (flagCount (i+1) (f,κ)) (Bool×μ (i+1)))
      (ImageCache (A:=A) (flagCount i κ) (Bool×μ i)) ℂ := by
  change Matrix (ImageCache (A:=A) (flagCount i κ+if f then 1 else 0) (Bool×μ (i+1)))
    (ImageCache (A:=A) (flagCount i κ) (Bool×μ i)) ℂ
  exact knownImages (flagCount i κ+if f then 1 else 0) (smallKnown (K i))*
    core (M:=Bool×μ i) (outcomeBasis H b) j (birthAmplitude H i η b j) (flagCount i κ) f*
      choiceImages (flagCount i κ) b

def run (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:ImageCache (A:=A) 0 (Bool×μ 0)→ℂ) :
    (i:ℕ)→History (A×Bool) i→(κ:History Bool i)→
      ImageCache (A:=A) (flagCount i κ) (Bool×μ i)→ℂ
  | 0,_,_=>z
  | i+1,η,κ=>stage H K i η.2 κ.2 η.1.1 η.1.2 κ.1*ᵥrun H K z i η.2 κ.2

@[simp] theorem run_succ (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:ImageCache (A:=A) 0 (Bool×μ 0)→ℂ) (i:ℕ)
    (η:History (A×Bool) i) (κ:History Bool i) (j:A) (b f:Bool) :
    run H K z (i+1) ((j,b),η) (f,κ)=stage H K i η κ j b f*ᵥrun H K z i η κ := rfl

end
end ICO.C6DecodedHistory
