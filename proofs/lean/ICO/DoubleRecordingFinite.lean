import ICO.DoubleRecordingSchedule
import ICO.MHFiniteSignedTrajectory

namespace ICO.DoubleRecordingFinite
open Matrix QIT ICO.SequentialIsometry ICO.RecordingPurifiedProtocol
  ICO.DoubleQuerySchedule ICO.RecordingOperatorSupport ICO.PathRecordingSupport
  ICO.RecordingOracleAlgebra ICO.MHFiniteSignedTrajectory ICO.RecordingCopyIdentity
open scoped BigOperators
noncomputable section
universe u
set_option maxHeartbeats 2400000
variable {A : Type u} [Fintype A] [DecidableEq A]
variable {μ : ℕ → Type u} [∀t,Fintype (μ t)] [∀t,DecidableEq (μ t)]

theorem finiteInitial_entry {M : Type u} [Fintype M] [DecidableEq M]
    (z : A×M→ℂ) (o : Basis A×M) :
    finiteInitial z o=if o.1.2.1=∅ ∧ o.1.2.2=∅ then z (o.1.1,o.2) else 0 := by
  rcases o with ⟨⟨a,l,r⟩,m⟩
  simp [finiteInitial,basisEmbedding,finiteEmpty,Matrix.mulVec,dotProduct,
    Matrix.submatrix_apply,Matrix.one_apply,Fintype.sum_prod_type,Prod.mk.injEq,
    ite_and,ite_mul]

theorem run_eq (K : (t : ℕ) → Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (z : A×Memory (A:=A) μ 0 0→ℂ) (t : ℕ) :
    MHFiniteSignedTrajectory.run (known K 0) direction z t=
      ICO.DoubleRecordingSchedule.runFrom K 0 (finiteInitial z) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MHFiniteSignedTrajectory.run,ICO.DoubleRecordingSchedule.runFrom,ih]
    simp only [oldChoice,ICO.DoubleRecordingSchedule.oracle_adjoint_choice]

variable {M O : Type u} [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

theorem initial_eq {q : ℕ} (tail : Protocol A (A×M) O q) (v : A×M→ℂ) :
    finiteInitial (ICO.ProtocolLudersTrajectory.run tail (1:CMatrix A) v 0)=
      ICO.ProtocolRecordingTrajectory.initial v := by
  funext o
  rw [finiteInitial_entry]
  rfl

theorem finite_even {q : ℕ} (tail : Protocol A (A×M) O q) (v : A×M→ℂ) (n : ℕ) :
    MHFiniteSignedTrajectory.run (known tail.tailKnown 0) direction
      (ICO.ProtocolLudersTrajectory.run tail (1:CMatrix A) v 0) (2*n)=
      ICO.ProtocolRecordingTrajectory.run tail forwardRecording v n ∘
        zeroEquiv (A:=A) (μ:=tail.tailMemory) (Basis A) n := by
  rw [run_eq]
  exact (congrArg (fun z => ICO.DoubleRecordingSchedule.runFrom tail.tailKnown 0 z (2*n))
    (initial_eq tail v)).trans (ICO.DoubleRecordingSchedule.recording_even tail v n)

#print axioms finite_even
end
end ICO.DoubleRecordingFinite
