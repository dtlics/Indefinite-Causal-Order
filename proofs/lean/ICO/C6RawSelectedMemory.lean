import ICO.C6RawSelectedSector
import ICO.C6SelectedImageFactor

namespace ICO.C6RawSelectedMemory
open Matrix QIT ICO.C6RawSelectedSector ICO.C6SelectedImageFactor
  ICO.C6TwoFockMemory ICO.C6TwoFockVisible ICO.C6TwoFockSector
  ICO.C6FockQueryMatrix ICO.C6BosonicReencoding ICO.C6BosonicFockRotated
  ICO.C6CacheSpanProjection ICO.C6OrthogonalModeBirth ICO.MHBoundedRecording
  ICO.MHFockSwap ICO.C6AcceptedBirthFactor ICO.C6ActualAcceptedModes
  ICO.C6ActualResidualWeight ICO.C6ResidualModes ICO.C6HistoryConjugation
  ICO.C6RetainedHistory ICO.C6ChoiceMeasurement ICO.RecordingPurifiedProtocol
open scoped Matrix
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A M:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

theorem selectedMemory_factor (l r:ℕ) (ψ β:A→ℂ) :
    selectedMemory (M:=M) l ψ (selectedRaw r β)=
      (Matrix.kronecker (selectedSector l r ψ β) (1:CMatrix M)).submatrix
        (sectorMemoryFirst (M:=M) l (r+1)) (sectorMemoryFirst (M:=M) l r) := by
  ext o i
  rfl

theorem measured_raw_memory {t T l r:ℕ} (h:t+1≤T) (hs:l+r≤t)
    (ψ:EuclideanSpace ℂ A) (U:Matrix.unitaryGroup A ℂ) (S:Finset A) :
    Matrix.kronecker (queryMatrix (rankOne ψ) T*rotatedFresh U S T*
      symmetricRightOnFock (α:=A) h) (1:CMatrix M)*memoryJ T l r (by omega)=
    memoryJ T l (r+1) (by omega)*selectedMemory (M:=M) l (WithLp.ofLp ψ)
      (selectedRaw r (fun a=>star ((1-spanProjection U S)*ᵥWithLp.ofLp ψ) a)) := by
  rw [memoryJ_factor,memoryJ_factor,selectedMemory_factor,mul_submatrix_id,
    Matrix.submatrix_mul_equiv _ _ _ (sectorMemoryFirst (A:=A) (M:=M) l (r+1))]
  simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.mul_one]
  rw [measured_raw_sector h hs]

theorem nextResidual_entry (H:Matrix.unitaryGroup A ℂ) (n:ℕ)
    (η:History (A×Bool) n) (b:Bool) (j a:A) :
    nextResidual H n η b j a=
      star ((1-historyProjection (vectors H n η))*ᵥqueryVector H (b,j)) a := by
  unfold nextResidual rightVectors
  rw [residual_bar,vectors_snoc,residual_eq_projection,prior_snoc,Fin.snoc_last]
  rfl

theorem actual_measured_raw_memory {t T l r:ℕ} (h:t+1≤T) (hs:l+r≤t)
    (H:Matrix.unitaryGroup A ℂ) (n:ℕ) (η:History (A×Bool) n) (b:Bool) (j:A) :
    Matrix.kronecker (queryMatrix (rankOne (WithLp.toLp 2 (queryVector H (b,j)))) T*
      rotatedFresh (historyUnitary (vectors H n η)) (historyIndices (vectors H n η)) T*
      symmetricRightOnFock (α:=A) h) (1:CMatrix M)*memoryJ T l r (by omega)=
    memoryJ T l (r+1) (by omega)*selectedMemory (M:=M) l
      (fun a=>(outcomeBasis H b:CMatrix A) a j)
      (selectedRaw r (fun a=>nextResidual H n η b j a)) := by
  rw [measured_raw_memory h hs]
  have hv:WithLp.ofLp (WithLp.toLp 2 (queryVector H (b,j)))=
      (fun a=>(outcomeBasis H b:CMatrix A) a j) := by
    exact congrArg WithLp.ofLp (actual_column H b j)
  rw [hv]
  congr 2
  apply congrArg (selectedRaw r)
  funext a
  change star ((1-historyProjection (vectors H n η))*ᵥ
    (fun a=>(outcomeBasis H b:CMatrix A) a j)) a=_
  rw [←hv]
  exact (nextResidual_entry H n η b j a).symm

#print axioms actual_measured_raw_memory
end
end ICO.C6RawSelectedMemory
