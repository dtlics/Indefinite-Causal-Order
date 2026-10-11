import ICO.MHDecompressionHybridMean
import ICO.ProtocolChannel
import ICO.ProtocolControl

/-! The physical frequency output and actual W-recording marginal differ
by the decompression hybrid, after erasing the inaccessible environment. -/
namespace ICO.MHDecompressionOutput
open Matrix QIT MeasureTheory ICO.MHDecompressionHybrid ICO.MHDecompressionHybridMean
  ICO.MHDecompressionKnown ICO.MHDecompressionStep ICO.MHDecompressionErasure
  ICO.MHRectangularAction ICO.MHFockSpace ICO.MHBoundedRecording
  ICO.MHDomainMeanProduct ICO.MHTernaryCompression ICO.RecordingCopyIdentity
  ICO.SequentialIsometry ICO.MHOutputMixture ICO.PureHybrid
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 512
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  {μ : ℕ→Type} [∀t,Fintype (μ t)] [∀t,DecidableEq (μ t)]

def physicalErasure (M : Type) [Fintype M] [DecidableEq M] : Channel ((A×Environment A)×M) (A×M) :=
  erasureChannel (basisEmbedding (environmentFirst M))
    (basisEmbedding_gram _ (environmentFirst M).injective)

theorem physicalErasure_apply (M : Type) [Fintype M] [DecidableEq M]
    (v : EuclideanSpace ℂ ((A×Environment A)×M)) :
    (physicalErasure (A:=A) M).map (outer v v)=physicalVisible (fun i => v i) := by
  change MatrixMap.ofKraus (ICO.SequentialIsometry.erasedKraus (basisEmbedding (environmentFirst M))) (rankOneMatrix (fun i => v i)) = _
  rw [erasedKraus_apply,← rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
  congr 1
  have hv : basisEmbedding (environmentFirst M)*ᵥ(fun i => v i)=(fun i => v i)∘(environmentFirst M).symm := by
    rw [basisEmbedding,Matrix.submatrix_mulVec_equiv]
    simp
  rw [hv]

theorem decompressed_visible {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (dir : ℕ→Bool)
    (z : A×μ 0→ℂ) (t:ℕ) (p : Rotation A) :
    physicalVisible (fun i => decompressedVector hT K dir z t p i)=
      fockVisible T (fun i => recordingVector hT K dir z t p i) := by
  apply decompression_visible hT
  exact congrArg (fun v : EuclideanSpace ℂ (InputCutoff (α:=A) T×μ t) => (fun i => v i))
    (recordingVector_bij hT K dir z t p)

theorem mean_output_bound {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (hK : ∀t,(K t).conjTranspose*K t=1)
    (dir : ℕ→Bool) (z : A×μ 0→ℂ) (hz : ‖WithLp.toLp 2 z‖≤1) (q:ℕ) (R:ℝ) (hR:0<R)
    (Y : (s:ℕ)→Rotation A→EuclideanSpace ℂ (InputCutoff (α:=A) T×μ s))
    (hY : ∀s,Continuous (Y s)) (hnY : ∀s p,‖Y s p‖≤1)
    (hoverlap : ∀s≤q,1-35*(q:ℝ)^2/R^2≤∫ p,
      (⟪recordingVector hT K dir z s p,Y s p⟫_ℂ).re ∂rotationMeasure A) :
    normalizedTraceDistance
      (∫ p, physicalVisible (frequencyRun K p.1 p.2 dir z q) ∂rotationMeasure A)
      (∫ p, fockVisible T (fun i => recordingVector hT K dir z q p i) ∂rotationMeasure A)≤9*(q:ℝ)^2/R := by
  have hh := output_distance_of_mean_error (physicalErasure (A:=A) (μ q)).map
    (erasureChannel_TNI _ (basisEmbedding_gram _ (environmentFirst (μ q)).injective))
    (frequencyVector K dir z q) (decompressedVector hT K dir z q)
    (frequencyVector_continuous K dir z q) (decompressedVector_continuous hT K dir z q)
    (fun p => by rw [frequencyVector_norm K hK]; exact hz)
    (decompressedVector_norm hT K hK dir z hz q) (9*(q:ℝ)^2/R)
    (mean_error_bound hT K hK dir z hz q R hR Y hY hnY hoverlap)
  simp only [physicalErasure_apply,decompressed_visible] at hh
  exact hh

#print axioms mean_output_bound
end
end ICO.MHDecompressionOutput