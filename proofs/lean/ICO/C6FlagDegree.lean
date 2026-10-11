import ICO.C6FockLengthShift
import ICO.C6RawFlags
import ICO.C6FlagCount

namespace ICO.C6FlagDegree
open Matrix QIT ICO.C6FockLengthShift ICO.C6BirthFlags ICO.C6RawFlags
  ICO.C6RetainedHistory ICO.C6PolarFock ICO.C6PolarLengths ICO.C6PairedTrajectory
  ICO.C6BosonicHistorySupport ICO.C6BosonicFockRotated ICO.C6BosonicFockSupport
  ICO.C6NumberRotationAlgebra ICO.C6FockNumber ICO.C6BosonicCacheSupport
  ICO.MHBoundedRecording ICO.MHFockKnownOperation ICO.MHFockRotation
  ICO.MHFockTransport ICO.MHSectorCovariance ICO.MHRectangularAction ICO.MHFockProjection
  ICO.RecordingPurifiedProtocol ICO.MHFockOracle ICO.C6FlagCount
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem shift_fresh (U:Matrix.unitaryGroup A ℂ) (S:Finset A) (T:ℕ) :
    Shift (rotatedFresh U S T) 0 0 := by
  have hU:Shift (fockQuery U T:CMatrix (InputCutoff (α:=A) T)) 0 0:=
    shift_family (fun n r=>(queryTurn U n r:CMatrix (Sector (α:=A) n r))) T
  exact shift_mul _ _ (shift_mul _ _ hU (shift_diagonal _)) (shift_adjoint _ hU)

theorem shift_number (U:Matrix.unitaryGroup A ℂ) (S:Finset A) (k T:ℕ) :
    Shift (rotatedNumber U S k T) 0 0 := by
  have hU:Shift (fockQ U 1 T:CMatrix (InputCutoff (α:=A) T)) 0 0:=
    shift_family (fun n r=>(outputTurn U 1 n r:CMatrix (Sector (α:=A) n r))) T
  exact shift_mul _ _ (shift_mul _ _ hU (shift_diagonal _)) (shift_adjoint _ hU)

theorem shift_right {t T:ℕ} (h:t+1≤T) : Shift (polarRightOnFock (α:=A) h) 0 1 := by
  intro o i ho
  obtain ⟨hl,hr⟩:=right_lengths h o i ho
  constructor
  · simpa only [leftDegree,add_zero] using congrArg (fun n:ℕ=>(n:ℤ)) hl
  · dsimp [rightDegree]
    exact_mod_cast hr

theorem flagInverse_degree {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (i:ℕ) (η:History (A×Bool) i) (f:Bool) :
    Shift (flagInverse h H i η f) (if f then 0 else -1) (if f then 1 else 0) := by
  have hB:Shift (historySupport (vectors H i η) T) 0 0:=shift_family _ _
  have hC:=shift_sub _ _ (shift_one (A:=A) T) (shift_left_image (A:=A) h)
  cases f
  · simpa only [flagInverse,Bool.false_eq_true,↓reduceIte,neg_zero,add_zero] using
      shift_mul _ _ (shift_adjoint _ (shift_left (A:=A) h)) hB
  · simpa only [flagInverse,↓reduceIte,zero_add,add_zero] using
      shift_mul _ _ (shift_mul _ _ (shift_mul _ _ (shift_fresh _ _ T) (shift_right (A:=A) h)) hC) hB

theorem rawFlagInverse_degree {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (i:ℕ) (η:History (A×Bool) i) (f:Bool) :
    Shift (rawFlagInverse h H i η f) (if f then 0 else -1) (if f then 1 else 0) := by
  have hB:Shift (historySupport (vectors H i η) T) 0 0:=shift_family _ _
  have hZ:Shift (historyZero H i T η) 0 0:=shift_number _ _ _ _
  have hC:=shift_sub _ _ (shift_one (A:=A) T) (shift_left_image (A:=A) h)
  cases f
  · simpa only [rawFlagInverse,Bool.false_eq_true,↓reduceIte,neg_zero,add_zero] using
      shift_mul _ _ (shift_mul _ _ (shift_adjoint _ (shift_left (A:=A) h)) hZ) hB
  · simpa only [rawFlagInverse,↓reduceIte,zero_add,add_zero] using
      shift_mul _ _ (shift_mul _ _ (shift_mul _ _
        (shift_mul _ _ (shift_fresh _ _ T) (shift_raw_right (A:=A) h)) hC) hZ) hB

variable {M N O:Type} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
  [Fintype O] [DecidableEq O]

def MemShift {T:ℕ} (F:Matrix (InputCutoff (α:=A) T×N) (InputCutoff (α:=A) T×M) ℂ)
    (l r:ℤ) : Prop :=
  ∀o i,F o i≠0→leftDegree o.1=leftDegree i.1+l ∧ rightDegree o.1=rightDegree i.1+r

theorem mem_mul {T:ℕ} (F:Matrix (InputCutoff (α:=A) T×O) (InputCutoff (α:=A) T×N) ℂ)
    (G:Matrix (InputCutoff (α:=A) T×N) (InputCutoff (α:=A) T×M) ℂ) {l r l' r':ℤ}
    (hF:MemShift F l r) (hG:MemShift G l' r') : MemShift (F*G) (l+l') (r+r') := by
  intro o i h
  obtain ⟨j,hf,hg⟩:=mul_entry_nonzero F G o i h
  obtain ⟨hl,hr⟩:=hF o j hf
  obtain ⟨hl',hr'⟩:=hG j i hg
  constructor <;> linarith

theorem mem_tensor {T:ℕ} (F:CMatrix (InputCutoff (α:=A) T)) (D:Matrix N M ℂ)
    {l r:ℤ} (hF:Shift F l r) : MemShift (Matrix.kronecker F D) l r := by
  intro o i h
  exact hF o.1 i.1 (by intro hz;exact h (by simp [Matrix.kronecker,Matrix.kroneckerMap_apply,hz]))

theorem mem_known (T:ℕ) (K:Matrix (A×N) (A×M) ℂ) : MemShift (known T K) 0 0 := by
  intro o i h
  have he:=congrArg (fun z:Records (α:=A) T=>z.1) (known_records T K o i h)
  constructor
  · simpa only [leftDegree,add_zero] using congrArg (fun s:Lengths T=>(s.val.1.val:ℤ)) he
  · simpa only [rightDegree,add_zero] using congrArg (fun s:Lengths T=>(s.val.2.val:ℤ)) he

theorem mem_controlled {T i:ℕ} (F:History (A×Bool) i→CMatrix (InputCutoff (α:=A) T))
    {l r:ℤ} (hF:∀η,Shift (F η) l r) : MemShift (controlled (M:=M) F) l r := by
  intro o x h
  rw [controlled_entry] at h
  split_ifs at h with he
  · exact hF _ _ _ h
  · exact (h rfl).elim

variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem flagStage_degree {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ) (f:Bool) :
    MemShift (flagStage h H K i f) (if f then 1 else 0) (if f then 1 else 0) := by
  have hp:=mem_known T (ICO.C6FockPairs.publicQuery (E:=History (A×Bool) i) (K i))
  have hm:=mem_known T (ICO.C6FockChoiceMeasurement.middleQuery (M:=History (A×Bool) i×μ i) H)
  have hc:=mem_controlled (M:=μ i) (fun η=>flagInverse h H i η f) (fun η=>flagInverse_degree h H i η f)
  have hs:=mem_mul _ _ (mem_mul _ _ (mem_mul _ _ hp
    (mem_tensor _ (1:CMatrix (Middle (A:=A) μ i)) (shift_left (A:=A) h))) hm) hc
  cases f <;> simpa only [flagStage,Bool.false_eq_true,↓reduceIte] using hs

theorem rawFlagStage_degree {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ) (f:Bool) :
    MemShift (rawFlagStage h H K i f) (if f then 1 else 0) (if f then 1 else 0) := by
  have hp:=mem_known T (ICO.C6FockPairs.publicQuery (E:=History (A×Bool) i) (K i))
  have hm:=mem_known T (ICO.C6FockChoiceMeasurement.middleQuery (M:=History (A×Bool) i×μ i) H)
  have hc:=mem_controlled (M:=μ i) (fun η=>rawFlagInverse h H i η f) (fun η=>rawFlagInverse_degree h H i η f)
  have hs:=mem_mul _ _ (mem_mul _ _ (mem_mul _ _ hp
    (mem_tensor _ (1:CMatrix (Middle (A:=A) μ i)) (shift_left (A:=A) h))) hm) hc
  cases f <;> simpa only [rawFlagStage,Bool.false_eq_true,↓reduceIte] using hs

#print axioms rawFlagStage_degree
end
end ICO.C6FlagDegree
