import ICO.ProtocolRecordingTrajectory
import ICO.ProtocolChannel

namespace ICO.ProtocolRecordingBound
open Matrix QIT ICO.SequentialIsometry ICO.ProtocolRecordingTrajectory
  ICO.RecordingPurifiedProtocol ICO.RecordingPublicStep ICO.RecordingProcess
  ICO.RecordingOracleAlgebra ICO.RecordingOperatorSupport ICO.RecordingDistance
  ICO.RecordingVaryingPurification
open scoped BigOperators ComplexOrder MatrixOrder
noncomputable section
universe u
set_option maxHeartbeats 2400000
variable {A M O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

def depolarized {q : ℕ} (tail : Protocol A (A×M) O q) (v : A×M → ℂ) (t : ℕ) :=
  tail.tailEvolution (depolarizingKraus (A:=A)) (rankOneMatrix v) t

theorem depolarized_recurrence {q : ℕ} (tail : Protocol A (A×M) O q)
    (v : A×M → ℂ) (t : ℕ) :
    depolarized tail v (t+1) =
      (ICO.RecordingVaryingDistance.followedBy
        (rectPublicChannel (tail.tailKnown t) (tail.tailKnown_isometry t))).map
          (depolarized tail v t) := by
  rw [ICO.RecordingVaryingDistance.followedBy_apply]
  change tail.tailKnown t * ICO.AllChannelDilation.oracleMap depolarizingKraus
    (depolarized tail v t) * (tail.tailKnown t).conjTranspose = _
  rw [depolarizingKraus_memory,ICO.RecordingDepolarizing.withMemory_apply]
  simp only [rectPublicChannel,Channel.ofReferenceIsometry_map,MatrixMap.ofReferenceIsometry_apply]

theorem depolarized_pos {q : ℕ} (tail : Protocol A (A×M) O q)
    (v : A×M → ℂ) (t : ℕ) : (depolarized tail v t).PosSemidef := by
  induction t with
  | zero => exact rankOneMatrix_pos v
  | succ t ih =>
    rw [depolarized_recurrence]
    exact (ICO.RecordingVaryingDistance.followedBy
      (rectPublicChannel (tail.tailKnown t) (tail.tailKnown_isometry t))).mapsPositive _ ih

/-- The concrete ordinary protocol and its actual recording paths satisfy the
complete recording-to-depolarizing bound. Only the Haar-to-recording comparison
remains a premise at this endpoint. -/
theorem before_output_bound {q : ℕ} (tail : Protocol A (A×M) O q)
    (v : A×M → ℂ) (hv : ‖WithLp.toLp 2 v‖≤1) (hmass : (rankOneMatrix v).trace.re=1)
    (hqd : 2*(q+1)<Fintype.card A)
    (H : CMatrix (A×tail.tailMemory (q+1))) (hH : H.trace.re=1) (ε : ℝ)
    (hHaar : normalizedTraceDistance H
      (visible (q+1) (run tail forwardRecording v (q+1))) ≤ ε) :
    normalizedTraceDistance H (depolarized tail v (q+1)) ≤
      2*ε + 4*(q+1 : ℕ)*Real.sqrt (1/((Fintype.card A : ℝ)-(2*(q+1) : ℕ))) +
        (q+1 : ℕ)^2/(Fintype.card A : ℝ) := by
  apply ICO.RecordingVaryingTranscript.transcript_bound_from_haar_comparison
    (run tail leftInsertion v) (run tail forwardRecording v)
    tail.tailKnown tail.tailKnown_isometry rfl
    ((initial_norm_le v).trans hv) (initial_support v)
    ((congrArg Complex.re (initial_trace v)).trans hmass)
    (fun t => rfl) (fun t => rfl)
    (depolarized tail v) (initial_visible v) (depolarized_recurrence tail v)
    (q+1) hqd H hH ε hHaar

theorem output_bound {q : ℕ} (tail : Protocol A (A×M) O q)
    (v : A×M → ℂ) (hv : ‖WithLp.toLp 2 v‖≤1) (hmass : (rankOneMatrix v).trace.re=1)
    (hqd : 2*(q+1)<Fintype.card A)
    (H : CMatrix (A×tail.tailMemory (q+1))) (hH : H.trace.re=1) (hHpos : H.PosSemidef) (ε : ℝ)
    (hHaar : normalizedTraceDistance H
      (visible (q+1) (run tail forwardRecording v (q+1))) ≤ ε) :
    normalizedTraceDistance (tail.terminalChannel.map H)
      (tail.map depolarizingKraus (ICO.AllChannelDilation.oracleMap depolarizingKraus (rankOneMatrix v))) ≤
      2*ε + 4*(q+1 : ℕ)*Real.sqrt (1/((Fintype.card A : ℝ)-(2*(q+1) : ℕ))) +
        (q+1 : ℕ)^2/(Fintype.card A : ℝ) := by
  have hc := distance_contract tail.terminalChannel.map
    (erasureChannel_TNI tail.tailFinal tail.tailFinal_isometry)
    H (depolarized tail v (q+1)) hHpos (depolarized_pos tail v (q+1))
  have ho : tail.terminalChannel.map (depolarized tail v (q+1)) =
      tail.map depolarizingKraus (ICO.AllChannelDilation.oracleMap depolarizingKraus (rankOneMatrix v)) :=
    tail.tailEvolution_output _ _
  rw [ho] at hc
  exact hc.trans (before_output_bound tail v hv hmass hqd H hH ε hHaar)

#print axioms before_output_bound
#print axioms output_bound
end
end ICO.ProtocolRecordingBound
