import ICO.ProtocolResponseNorm

/-! The large-query part of the Haar recording estimate uses only the
physical subnormalized output bound. This preserves the stated full range. -/
namespace ICO.MHHaarRecordingTrivial
open Matrix QIT ICO.SequentialIsometry ICO.ProtocolHaarOutput
  ICO.RecordingPurifiedProtocol ICO.ProtocolRecordingTrajectory ICO.RecordingHistory
  ICO.RecordingRetainedProcess ICO.RecordingOracleAlgebra
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1800000
variable {H : Type*} [Fintype H] [DecidableEq H]

theorem positive_distance_le_one (ρ σ : CMatrix H) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (htρ : ρ.trace.re≤1) (htσ : σ.trace.re≤1) : normalizedTraceDistance ρ σ≤1 := by
  have hh : traceNorm (ρ-σ)≤ρ.trace.re+σ.trace.re := by
    calc
      _ = traceNorm (ρ+ -σ) := by rw [sub_eq_add_neg]
      _ ≤ traceNorm ρ+traceNorm (-σ) := traceNorm_add_le _ _
      _ = _ := by rw [traceNorm_neg,traceNorm_posSemidef_eq_trace_re ρ hρ,
        traceNorm_posSemidef_eq_trace_re σ hσ]
  unfold normalizedTraceDistance traceNormDistance
  linarith

variable {A M O : Type} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

theorem haar_recording_distance_le_one {q : ℕ} (tail : Protocol A (A×M) O q)
    (v : A×M→ℂ) (hv : ‖WithLp.toLp 2 v‖≤1) (hmass : (rankOneMatrix v).trace.re=1)
    (n : ℕ) :
    normalizedTraceDistance (haarDensity tail v n)
      (visible n (run tail forwardRecording v n))≤1 := by
  apply positive_distance_le_one
  · exact haarDensity_pos tail v n
  · change (visibleMap (eraseHistory.map (rankOneMatrix (run tail forwardRecording v n)))).PosSemidef
    exact visibleMap_TNI.mapsPositive _ (eraseHistory.mapsPositive _
      (rankOneMatrix_pos (run tail forwardRecording v n)))
  · rw [haarDensity_trace,hmass]
  · have hh := run_norm_le tail forwardRecording forward_initial_projection v hv n
    change (visibleMap (eraseHistory.map (rankOneMatrix (run tail forwardRecording v n)))).trace.re≤1
    rw [visibleMap_trace,eraseHistory.tracePreserving,rankOne_trace_re_norm_sq]
    nlinarith [norm_nonneg (WithLp.toLp 2 (run tail forwardRecording v n))]

theorem error_ge_one_of_large (t d : ℕ) (R : ℝ) (hR : 1≤R)
    (hd : (d:ℝ)=R^8) (ht : d<2*t) (hpos : 1≤t) :
    1≤9*(t:ℝ)*(t+1)/R := by
  have hr : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hpow : R≤R^8 := by
    simpa only [pow_one] using pow_le_pow_right₀ hR (show 1≤8 by norm_num)
  have htt : (d:ℝ)<2*(t:ℝ) := by exact_mod_cast ht
  have htn : (1:ℝ)≤t := by exact_mod_cast hpos
  apply (le_div_iff₀ hr).2
  rw [←hd] at hpow
  nlinarith

#print axioms haar_recording_distance_le_one
#print axioms error_ge_one_of_large
end
end ICO.MHHaarRecordingTrivial
