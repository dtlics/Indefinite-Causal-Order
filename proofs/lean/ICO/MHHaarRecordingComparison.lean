import ICO.MHDecompressionOutput
import ICO.MHActualRecordingOverlap
import ICO.MHFockVisibleDistance

/-! The actual Haar-frequency oracle and the explicit recording oracle are
close for every finite signed isometric protocol.  No overlap, domain, or
regularity hypotheses remain in this theorem. -/
namespace ICO.MHHaarRecordingComparison
open Matrix QIT MeasureTheory ICO.MHDecompressionHybrid ICO.MHDecompressionHybridMean
  ICO.MHDecompressionOutput ICO.MHDecompressionErasure ICO.MHActualRecordingOverlap
  ICO.MHFockVisibleDistance ICO.MHFockRunContinuity ICO.MHFockRotation ICO.MHSectorCovariance
  ICO.MHActualQueryLoss ICO.MHDomainMeanProduct ICO.MHBoundedRecording ICO.MHProtocolOverlap ICO.MHOverlapStep
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 512
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  {μ : ℕ→Type} [∀t,Fintype (μ t)] [∀t,DecidableEq (μ t)]

def referenceVector {q T : ℕ} (hq : q+1≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (dir : ℕ→Bool)
    (z : A×μ 0→ℂ) (s : ℕ) (p : Rotation A) : EuclideanSpace ℂ (InputCutoff (α:=A) T×μ s) :=
  act (Matrix.kronecker (fockQ p.1 p.2 T:CMatrix (InputCutoff (α:=A) T))
    (1:CMatrix (μ s))) (vVector hq K dir z s)

theorem referenceVector_continuous {q T : ℕ} (hq : q+1≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (dir : ℕ→Bool)
    (z : A×μ 0→ℂ) (s : ℕ) : Continuous (referenceVector hq K dir z s) :=
  (recordAction_continuous T (μ s)).clm_apply continuous_const

theorem referenceVector_norm {q T : ℕ} (hq : q+1≤T) (hsize : q<Fintype.card A)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (hK : ∀t,(K t).conjTranspose*K t=1) (dir : ℕ→Bool) (z : A×μ 0→ℂ)
    (hz : ‖WithLp.toLp 2 z‖≤1) (s : ℕ) (p : Rotation A) : ‖referenceVector hq K dir z s p‖≤1 := by
  change ‖act (memoryUnitary (M:=μ s) (fockQ p.1 p.2 T):CMatrix (InputCutoff (α:=A) T×μ s))
      (vVector hq K dir z s)‖≤1
  rw [unitary_act_norm]
  exact vVector_norm hq hsize K hK dir z hz s

theorem frequency_recording_distance {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (hq : q+1≤T) (hsize : q<Fintype.card A) (hsmall : 2*q≤Fintype.card A)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (hK : ∀t,(K t).conjTranspose*K t=1) (dir : ℕ→Bool) (z : A×μ 0→ℂ)
    (hz : ‖WithLp.toLp 2 z‖=1) (R : ℝ) (hR : 1≤R) (hd : (Fintype.card A:ℝ)=R^8) :
    normalizedTraceDistance
      (∫ p, physicalVisible (frequencyRun K p.1 p.2 dir z q) ∂rotationMeasure A)
      (∫ p, fockVisible T (WithLp.ofLp (wVector hT K dir z q p)) ∂rotationMeasure A)≤9*(q:ℝ)^2/R :=
  mean_output_bound hT K hK dir z hz.le q R (lt_of_lt_of_le zero_lt_one hR)
    (referenceVector hq K dir z) (referenceVector_continuous hq K dir z)
    (referenceVector_norm hq hsize K hK dir z hz.le)
    (actual_prefix_overlap hT hq hsize hsmall K hK dir z hz R hR hd)

/-- Actual signed oracle queries, arbitrary rectangular known isometries and
private memory, with the published 9q(q+1)/d^(1/8) bound. -/
theorem frequency_visible_distance {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (hq : q+1≤T) (hsize : q<Fintype.card A) (hsmall : 2*q≤Fintype.card A)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (hK : ∀t,(K t).conjTranspose*K t=1) (dir : ℕ→Bool) (z : A×μ 0→ℂ)
    (hz : ‖WithLp.toLp 2 z‖=1) (R : ℝ) (hR : 1≤R) (hd : (Fintype.card A:ℝ)=R^8) :
    normalizedTraceDistance
      (∫ p, physicalVisible (frequencyRun K p.1 p.2 dir z q) ∂rotationMeasure A)
      (fockVisible T (WithLp.ofLp (vVector hq K dir z q)))≤9*(q:ℝ)*((q:ℝ)+1)/R := by
  have h1 := frequency_recording_distance hT hq hsize hsmall K hK dir z hz R hR hd
  have h2 := (mean_visible_rotation_distance T (wVector hT K dir z q) (vVector hq K dir z q)
    (wVector_continuous hT K hK dir z q) (wVector_norm hT K hK dir z hz.le q)
    (vVector_norm hq hsize K hK dir z hz.le q)).trans
      (actual_mean_distance hT hq hsize hsmall K hK dir z hz R hR hd (s:=q) le_rfl)
  have ht := normalizedTraceDistance_triangle
    (∫ p, physicalVisible (frequencyRun K p.1 p.2 dir z q) ∂rotationMeasure A)
    (∫ p, fockVisible T (WithLp.ofLp (wVector hT K dir z q p)) ∂rotationMeasure A)
    (fockVisible T (WithLp.ofLp (vVector hq K dir z q)))
  calc
    _ ≤ 9*(q:ℝ)^2/R+9*(q:ℝ)/R := ht.trans (add_le_add h1 h2)
    _ = _ := by ring

#print axioms frequency_visible_distance
end
end ICO.MHHaarRecordingComparison