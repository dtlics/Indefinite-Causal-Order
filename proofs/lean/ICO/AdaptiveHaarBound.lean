import ICO.ProtocolHaarOutput

namespace ICO.AdaptiveHaarBound
open Matrix QIT MeasureTheory ICO.SequentialIsometry ICO.RecordingHistory
  ICO.RecordingPurifiedProtocol ICO.ProtocolHaarOutput ICO.RecordingProcess
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
universe u
set_option maxHeartbeats 2400000
variable {A B O I : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
  [Fintype I] [DecidableEq I]

theorem prepared_output {q : ℕ} (p : Protocol A B O (q+1))
    (U : I → CMatrix A) (v : B → ℂ) :
    p.heading.tail.map U (ICO.AllChannelDilation.oracleMap U (rankOneMatrix (p.heading.pre*ᵥv))) =
      p.map U (rankOneMatrix v) := by
  rw [Protocol.heading_map]
  simp only [LinearMap.comp_apply,singleMap_apply,
    rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]

theorem prepared_norm_le {q : ℕ} (p : Protocol A B O (q+1)) (v : B → ℂ)
    (hv : ‖WithLp.toLp 2 v‖≤1) : ‖WithLp.toLp 2 (p.heading.pre*ᵥv)‖≤1 := by
  have hm := isometry_matrix_norm_le p.heading.pre p.heading.isometry
  have hvv := Matrix.l2_opNorm_mulVec p.heading.pre (WithLp.toLp 2 v)
  exact hvv.trans (by nlinarith [norm_nonneg p.heading.pre,norm_nonneg (WithLp.toLp 2 v)])

theorem prepared_trace {q : ℕ} (p : Protocol A B O (q+1)) (v : B → ℂ) :
    (rankOneMatrix (p.heading.pre*ᵥv)).trace=(rankOneMatrix v).trace := by
  rw [rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
  simpa only [ICO.ClassicalDilation.isometryChannel_apply] using
    (ICO.ClassicalDilation.isometryChannel p.heading.pre p.heading.isometry).tracePreserving (rankOneMatrix v)

/-- Oracle-independent preprocessing, terminal erasure and all classical
adaptivity have been compiled away constructively. Only the quantitative Haar
recording comparison is exposed as a premise. -/
theorem protocol_haar_bound {q : ℕ} (p : Protocol A B O (q+1))
    (v : B → ℂ) (hv : ‖WithLp.toLp 2 v‖≤1) (hmass : (rankOneMatrix v).trace.re=1)
    (hqd : 2*(q+1)<Fintype.card A) (ε : ℝ)
    (hHaar : normalizedTraceDistance (haarDensity p.heading.tail (p.heading.pre*ᵥv) (q+1))
      (visible (q+1) (ICO.ProtocolRecordingTrajectory.run p.heading.tail
        ICO.RecordingOracleAlgebra.forwardRecording (p.heading.pre*ᵥv) (q+1))) ≤ ε) :
    normalizedTraceDistance
      (∫ U, p.map (ICO.SwitchObservable.basisProjection (U:CMatrix A)) (rankOneMatrix v)
        ∂unitaryHaarMeasure (a:=A))
      (p.map depolarizingKraus (rankOneMatrix v)) ≤
      2*ε + 4*(q+1 : ℕ)*Real.sqrt (1/((Fintype.card A : ℝ)-(2*(q+1) : ℕ))) +
        (q+1 : ℕ)^2/(Fintype.card A : ℝ) := by
  have h := haar_output_bound p.heading.tail (p.heading.pre*ᵥv) (prepared_norm_le p v hv)
    ((congrArg Complex.re (prepared_trace p v)).trans hmass) hqd ε hHaar
  simp_rw [prepared_output p] at h
  exact h

#print axioms protocol_haar_bound
end
end ICO.AdaptiveHaarBound
