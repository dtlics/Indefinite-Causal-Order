import ICO.RecordingPurifiedProtocol
import ICO.PureHybrid

namespace ICO.RecordingTranscript
open QIT ICO.PathRecordingSupport ICO.RecordingProcess ICO.RecordingPurifiedProtocol
  ICO.RecordingPublicStep ICO.RecordingHistory ICO.RecordingRetainedProcess
  ICO.RecordingOracleAlgebra ICO.RecordingPartialIsometry ICO.RecordingCombination
  ICO.RecordingDistance ICO.RecordingDepolarizing ICO.RecordingOperatorSupport
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 0
universe u
variable {α : Type u} {μ : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [Fintype μ] [DecidableEq μ]

theorem visible_pure_distance_le (t : ℕ)
    (v w : Basis α × (History α t × μ) → ℂ)
    (hv : ‖WithLp.toLp 2 v‖ ≤ 1) (hw : ‖WithLp.toLp 2 w‖ ≤ 1) :
    normalizedTraceDistance (visible t v) (visible t w) ≤
      ‖WithLp.toLp 2 v - WithLp.toLp 2 w‖ := by
  have hp := ICO.PureHybrid.subnormalized_pure_distance_le
    (WithLp.toLp 2 v) (WithLp.toLp 2 w) hv hw
  have hout (z : Basis α × (History α t × μ) → ℂ) :
      ICO.PureHybrid.outer (WithLp.toLp 2 z) (WithLp.toLp 2 z) = rankOneMatrix z := by
    ext i j
    rfl
  rw [hout, hout] at hp
  have hp' : normalizedTraceDistance (rankOneMatrix v) (rankOneMatrix w) ≤
      ‖WithLp.toLp 2 v - WithLp.toLp 2 w‖ := by
    simpa only [normalizedTraceDistance, traceNormDistance, div_eq_mul_inv, mul_comm] using hp
  have he := distance_contract eraseHistory.map
    (MatrixMap.traceNonincreasingCP_of_tracePreserving
      eraseHistory.completelyPositive eraseHistory.tracePreserving)
    (rankOneMatrix v) (rankOneMatrix w) (rankOneMatrix_pos _) (rankOneMatrix_pos _)
  have hvv := distance_contract visibleMap visibleMap_TNI
    (reduced t v) (reduced t w)
    (eraseHistory.mapsPositive _ (rankOneMatrix_pos _))
    (eraseHistory.mapsPositive _ (rankOneMatrix_pos _))
  exact hvv.trans (he.trans hp')

theorem modified_recording_visible_distance
    (ψ χ : (t : ℕ) → Basis α × (History α t × μ) → ℂ)
    (K : ℕ → CMatrix (α × μ)) (hK : ∀ t, (K t).conjTranspose * K t = 1)
    (hinit : ψ 0 = χ 0) (hnorm : ‖WithLp.toLp 2 (ψ 0)‖ ≤ 1)
    (hempty : ∀ i, ψ 0 i ≠ 0 → i.1.2.1 = ∅ ∧ i.1.2.2 = ∅)
    (hmod : ∀ t, ψ (t + 1) =
      stepMatrix leftInsertion (publicStep (h := History α t) (K t)) *ᵥ ψ t)
    (hrec : ∀ t, χ (t + 1) =
      stepMatrix forwardRecording (publicStep (h := History α t) (K t)) *ᵥ χ t)
    (q : ℕ) (hqd : 2 * q < Fintype.card α) :
    normalizedTraceDistance (visible q (χ q)) (visible q (ψ q)) ≤
      (q : ℝ) * (2 * Real.sqrt (1 / ((Fintype.card α : ℝ) - (2 * q : ℕ)))) := by
  let M := fun t => History α t × μ
  let P := fun t => publicStep (h := History α t) (K t)
  have hP (t : ℕ) : (P t).conjTranspose * P t = 1 := publicStep_isometry _ (hK t)
  have hA : IsStarProjection (leftInsertion.conjTranspose * leftInsertion : CMatrix (Basis α)) := by
    rw [left_gram_eq_projection]
    exact domainProjection_isStarProjection
  have hψ := process_norm_le M ψ leftInsertion hA P hP hnorm hmod q
  have hχ0 : ‖WithLp.toLp 2 (χ 0)‖ ≤ 1 := by rw [← hinit]; exact hnorm
  have hχ := process_norm_le M χ forwardRecording forward_initial_projection P hP hχ0 hrec q
  have hh := recording_hybrid_norm_le M ψ χ P hP hinit hnorm hempty hmod hrec q hqd
  have hp := visible_pure_distance_le q (χ q) (ψ q) hχ hψ
  rw [norm_sub_rev] at hp
  exact hp.trans hh

/-- Complete recording-to-depolarizing assembly for actual public-isometry
protocols. The external Haar comparison is the sole analytic distance premise;
the modified-process error and lost mass are proved from the recurrences. -/
theorem transcript_bound_from_haar_comparison
    (ψ χ : (t : ℕ) → Basis α × (History α t × μ) → ℂ)
    (K : ℕ → CMatrix (α × μ)) (hK : ∀ t, (K t).conjTranspose * K t = 1)
    (hinit : ψ 0 = χ 0) (hnorm : ‖WithLp.toLp 2 (ψ 0)‖ ≤ 1)
    (hempty : ∀ i, ψ 0 i ≠ 0 → i.1.2.1 = ∅ ∧ i.1.2.2 = ∅)
    (hmass : (rankOneMatrix (ψ 0)).trace.re = 1)
    (hmod : ∀ t, ψ (t + 1) =
      stepMatrix leftInsertion (publicStep (h := History α t) (K t)) *ᵥ ψ t)
    (hrec : ∀ t, χ (t + 1) =
      stepMatrix forwardRecording (publicStep (h := History α t) (K t)) *ᵥ χ t)
    (σ : ℕ → CMatrix (α × μ)) (hσ0 : visible 0 (ψ 0) = σ 0)
    (hideal : ∀ t, σ (t + 1) = (followedBy (publicChannel (K t) (hK t))).map (σ t))
    (q : ℕ) (hqd : 2 * q < Fintype.card α)
    (H : CMatrix (α × μ)) (hH : H.trace.re = 1) (ε : ℝ)
    (hHaar : normalizedTraceDistance H (visible q (χ q)) ≤ ε) :
    normalizedTraceDistance H (σ q) ≤ 2 * ε +
      4 * (q : ℝ) * Real.sqrt (1 / ((Fintype.card α : ℝ) - (2 * q : ℕ))) +
        (q : ℝ) ^ 2 / (Fintype.card α : ℝ) := by
  have hrecmod := modified_recording_visible_distance ψ χ K hK hinit hnorm hempty hmod hrec q hqd
  have hmoddep := purified_modified_depolarizing_distance ψ K hK hempty hmass hmod
    σ hσ0 hideal q hqd
  have hh := haar_recording_modified_comparison H (visible q (χ q)) (visible q (ψ q)) (σ q)
    hH ε ((q : ℝ) * (2 * Real.sqrt (1 / ((Fintype.card α : ℝ) - (2 * q : ℕ)))))
    q (Fintype.card α) hHaar hrecmod hmoddep
  nlinarith

#print axioms visible_pure_distance_le
#print axioms modified_recording_visible_distance
#print axioms transcript_bound_from_haar_comparison
end
end ICO.RecordingTranscript
