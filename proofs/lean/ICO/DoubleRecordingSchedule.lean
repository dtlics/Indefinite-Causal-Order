import ICO.DoubleQuerySchedule
import ICO.ProtocolRecordingTrajectory

namespace ICO.DoubleRecordingSchedule
open Matrix QIT ICO.SequentialIsometry ICO.RecordingPurifiedProtocol
  ICO.RecordingPublicStep ICO.DoubleQuerySchedule ICO.RecordingOperatorSupport
  ICO.PathRecordingSupport ICO.RecordingProcess ICO.RecordingOracleAlgebra
open scoped BigOperators
noncomputable section
universe u
set_option maxHeartbeats 2400000
variable {A : Type u} [Fintype A] [DecidableEq A]
variable {μ : ℕ → Type u} [∀ t,Fintype (μ t)] [∀ t,DecidableEq (μ t)]

theorem copy_lift {M : Type u} [Fintype M] [DecidableEq M] :
    knownOperation (ICO.LudersUnitaryStages.copyQuery (A:=A) (M:=M))=
      ICO.RecordingOperatorSupport.copyQuery := by
  ext o i
  simp only [knownOperation,ICO.LudersUnitaryStages.copyQuery,
    ICO.RecordingOperatorSupport.copyQuery,Prod.mk.injEq]
  split_ifs <;> simp_all <;> aesop

def oracle (n : ℕ) : CMatrix (Basis A) :=
  if direction n then inverseRecording else forwardRecording

def runFrom (K : (t : ℕ) → Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (k : ℕ) (v : Basis A×Memory (A:=A) μ k 0 → ℂ) :
    (n : ℕ) → Basis A×Memory (A:=A) μ k n → ℂ
  | 0 => v
  | n+1 => knownOperation (known K k n) *ᵥ
      (Matrix.kronecker (oracle (A:=A) n) (1 : CMatrix (Memory (A:=A) μ k n)) *ᵥ
        runFrom K k v n)

theorem runFrom_two (K : (t : ℕ) → Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (k : ℕ) (v : Basis A×Memory (A:=A) μ k 0 → ℂ) :
    runFrom K k v 2=stepMatrix forwardRecording
      (publicStep (h:=History A k) (K k)) *ᵥ v := by
  change knownOperation (publicStep (h:=History A k) (K k)) *ᵥ
    (Matrix.kronecker forwardRecording (1 : CMatrix (A×(History A k×μ k))) *ᵥ
      (knownOperation (ICO.LudersUnitaryStages.copyQuery) *ᵥ
        (Matrix.kronecker inverseRecording (1 : CMatrix (History A k×μ k)) *ᵥ v))) = _
  rw [copy_lift]
  simp only [stepMatrix,wrapperMatrix,Matrix.mulVec_mulVec,Matrix.mul_assoc]

theorem runFrom_shift (K : (t : ℕ) → Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (k : ℕ) (v : Basis A×Memory (A:=A) μ k 0 → ℂ) (n : ℕ) :
    runFrom K k v (n+2)=runFrom K (k+1)
      (stepMatrix forwardRecording (publicStep (h:=History A k) (K k)) *ᵥ v) n := by
  induction n with
  | zero => exact runFrom_two K k v
  | succ n ih =>
    change knownOperation (known K (k+1) n) *ᵥ
      (Matrix.kronecker (oracle (A:=A) n)
        (1 : CMatrix (Memory (A:=A) μ (k+1) n)) *ᵥ runFrom K k v (n+2)) = _
    rw [ih]
    rfl

theorem runFrom_even_heq (K : (t : ℕ) → Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (x : (t : ℕ) → Basis A×(History A t×μ t) → ℂ)
    (hx : ∀t,x (t+1)=stepMatrix forwardRecording
      (publicStep (h:=History A t) (K t)) *ᵥ x t) (k n : ℕ) :
    HEq (runFrom K k (x k) (2*n)) (x (k+n)) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have hn : 2*(n+1)=2*n+2 := by omega
    rw [hn,runFrom_shift]
    have hh := congrArg (fun z => runFrom K (k+1) z (2*n)) (hx k).symm
    apply HEq.trans (heq_of_eq hh)
    exact (ih (k+1)).trans (dependent_heq x (by omega))

theorem recording_even {M O : Type u} [Fintype M] [DecidableEq M]
    [Fintype O] [DecidableEq O] {q : ℕ} (tail : Protocol A (A×M) O q)
    (v : A×M → ℂ) (n : ℕ) :
    runFrom tail.tailKnown 0 (ICO.ProtocolRecordingTrajectory.run tail forwardRecording v 0) (2*n)=
      ICO.ProtocolRecordingTrajectory.run tail forwardRecording v n ∘
        zeroEquiv (A:=A) (μ:=tail.tailMemory) (Basis A) n := by
  have h := runFrom_even_heq tail.tailKnown (ICO.ProtocolRecordingTrajectory.run tail forwardRecording v)
    (fun t => rfl) 0 n
  apply heq_cast_fun
  exact h.trans (dependent_heq (ICO.ProtocolRecordingTrajectory.run tail forwardRecording v) (Nat.zero_add n))

theorem oracle_adjoint_choice (n : ℕ) : oracle (A:=A) n=
    if direction n then (forwardRecording (α:=A)).conjTranspose else forwardRecording := by
  simp only [oracle,inverseRecording_eq_adjoint]

#print axioms recording_even
#print axioms runFrom_shift
end
end ICO.DoubleRecordingSchedule
