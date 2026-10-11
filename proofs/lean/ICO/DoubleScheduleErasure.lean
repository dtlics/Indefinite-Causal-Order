import ICO.DoubleRecordingFinite
import ICO.MHFockFiniteErasure
import ICO.ProtocolResponseNorm

namespace ICO.DoubleScheduleErasure
open Matrix QIT ICO.SequentialIsometry ICO.RecordingPurifiedProtocol
  ICO.DoubleQuerySchedule ICO.RecordingOperatorSupport ICO.PathRecordingSupport
  ICO.RecordingOracleAlgebra ICO.RecordingRetainedProcess ICO.RecordingHistory
  ICO.MHFockFiniteTrajectory ICO.MHFockFiniteErasure ICO.MHDecompressionErasure
  ICO.MHFockTrajectory ICO.DoubleRecordingFinite ICO.ClassicalDilation
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 300000
universe u
variable {A M O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

def stageErasure {q : ℕ} (tail : Protocol A (A×M) O q) (n : ℕ) :
    Channel (A×Memory (A:=A) tail.tailMemory 0 (2*n)) (A×tail.tailMemory n) :=
  eraseHistory.comp (isometryChannel
    (permutation (zeroEquiv (A:=A) (μ:=tail.tailMemory) A n))
    (permutation_isometry _))

theorem stageErasure_apply {q : ℕ} (tail : Protocol A (A×M) O q) (n : ℕ)
    (X : CMatrix (A×Memory (A:=A) tail.tailMemory 0 (2*n))) :
    (stageErasure tail n).map X=eraseHistory.map
      (X.submatrix (zeroEquiv (A:=A) (μ:=tail.tailMemory) A n).symm
        (zeroEquiv (A:=A) (μ:=tail.tailMemory) A n).symm) := by
  change eraseHistory.map ((isometryChannel _ _).map X)=_
  rw [isometryChannel_apply,permutation_sandwich]

theorem visible_cast {I J : Type u} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (h : I=J) (v : Basis A×J→ℂ) :
    (visibleMap (rankOneMatrix (v ∘ Equiv.cast (congrArg (fun X => Basis A×X) h)))).submatrix
      (Equiv.cast (congrArg (fun X => A×X) h)).symm
      (Equiv.cast (congrArg (fun X => A×X) h)).symm =
      visibleMap (rankOneMatrix v) := by
  cases h
  ext i j
  rcases i with ⟨a,m⟩
  rcases j with ⟨b,n⟩
  simp only [Matrix.submatrix_apply,Equiv.cast_refl,Equiv.refl_symm,Equiv.refl_apply,
    Function.comp_apply,visibleMap_apply,rankOneMatrix_apply]

theorem erase_visible {H : Type u} [Fintype H] [DecidableEq H]
    (v : Basis A×(H×M)→ℂ) :
    eraseHistory.map (visibleMap (rankOneMatrix v))=
      visibleMap (eraseHistory.map (rankOneMatrix v)) := by
  ext i j
  rcases i with ⟨a,m⟩
  rcases j with ⟨b,n⟩
  simp only [eraseHistory_apply,visibleMap_apply]
  exact Finset.sum_comm

theorem finite_visible_endpoint {q : ℕ} (tail : Protocol A (A×M) O q)
    (v : A×M→ℂ) (n : ℕ) :
    (stageErasure tail n).map (visibleMap (rankOneMatrix
      (ICO.MHFiniteSignedTrajectory.run (known tail.tailKnown 0) direction
        (ICO.ProtocolLudersTrajectory.run tail (1:CMatrix A) v 0) (2*n))))=
      visible n (ICO.ProtocolRecordingTrajectory.run tail forwardRecording v n) := by
  rw [stageErasure_apply,finite_even]
  have hm : Memory (A:=A) tail.tailMemory 0 (2*n)=(History A n×tail.tailMemory n) := by
    simpa only [Nat.zero_add] using memory_even_eq (A:=A) (μ:=tail.tailMemory) 0 n
  have he := visible_cast hm (ICO.ProtocolRecordingTrajectory.run tail forwardRecording v n)
  exact (congrArg eraseHistory.map he).trans (erase_visible _)

theorem fock_visible_endpoint {q T : ℕ} (tail : Protocol A (A×M) O q)
    (v : A×M→ℂ) (n : ℕ) (hq : 2*n+1≤T)
    (hT : 2*Fintype.card (A×A)≤T) (hnd : 2*n<Fintype.card A) :
    (stageErasure tail n).map (fockVisible T
      (ICO.MHFockTrajectory.run T (known tail.tailKnown 0)
        (fun t => Vchoice hq (direction t))
        (ICO.ProtocolLudersTrajectory.run tail (1:CMatrix A) v 0) (2*n)))=
      visible n (ICO.ProtocolRecordingTrajectory.run tail forwardRecording v n) := by
  rw [run_intertwining hq hT hnd _ _ _ (2*n) le_rfl,setMemory_visible]
  exact finite_visible_endpoint tail v n

theorem physical_initial_norm {q : ℕ} (tail : Protocol A (A×M) O q) (v : A×M→ℂ) :
    ‖WithLp.toLp 2 (ICO.ProtocolLudersTrajectory.run tail (1:CMatrix A) v 0)‖=
      ‖WithLp.toLp 2 v‖ := by
  have h := ICO.ProtocolHaarOutput.response_norm_sq tail v 0 (1 : Matrix.unitaryGroup A ℂ)
  rw [ICO.ProtocolHaarOutput.rankOne_trace_re_norm_sq] at h
  change ‖WithLp.toLp 2 (ICO.ProtocolLudersTrajectory.run tail (1:CMatrix A) v 0)‖^2=
    ‖WithLp.toLp 2 v‖^2 at h
  nlinarith [norm_nonneg (WithLp.toLp 2 (ICO.ProtocolLudersTrajectory.run tail (1:CMatrix A) v 0)),
    norm_nonneg (WithLp.toLp 2 v)]

#print axioms fock_visible_endpoint
#print axioms physical_initial_norm
end
end ICO.DoubleScheduleErasure
