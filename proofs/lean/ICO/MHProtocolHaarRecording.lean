import ICO.MHFrequencyTrajectory
import ICO.DoubleScheduleErasure
import ICO.MHHaarRecordingComparison

namespace ICO.MHProtocolHaarRecording
open Matrix QIT MeasureTheory ICO.SequentialIsometry ICO.RecordingPurifiedProtocol
  ICO.DoubleQuerySchedule ICO.DoubleScheduleErasure ICO.MHFrequencyTrajectory
  ICO.MHDecompressionHybrid ICO.MHDecompressionOutput ICO.MHDecompressionErasure
  ICO.MHDomainMeanProduct ICO.MHHaarRecordingComparison ICO.MHActualRecordingOverlap
  ICO.MHOutputMixture ICO.RecordingDistance ICO.PureHybrid ICO.ProtocolHaarOutput
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockTrajectory ICO.RecordingOracleAlgebra
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 512
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ : ℕ→Type} [∀t,Fintype (μ t)] [∀t,DecidableEq (μ t)]

local instance matrixNonUnitalCStar {I : Type} [Fintype I] [DecidableEq I] :
    NonUnitalCStarAlgebra (CMatrix I) := ⟨⟩
local instance cmContinuousENorm {I : Type} [Fintype I] [DecidableEq I] :
    ContinuousENorm (CMatrix I) := SeminormedAddGroup.toContinuousENorm

theorem physical_visible_continuous (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (dir : ℕ→Bool) (z : A×μ 0→ℂ) (t : ℕ) :
    Continuous (fun p : Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ =>
      physicalVisible (frequencyRun K p.1 p.2 dir z t)) := by
  have h := (physicalErasure (A:=A) (μ t)).map.continuous_of_finiteDimensional.comp
    (outer_continuous _ (frequencyVector_continuous K dir z t))
  simpa only [Function.comp_def,physicalErasure_apply] using h

theorem physical_mean_pos (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (dir : ℕ→Bool) (z : A×μ 0→ℂ) (t : ℕ) :
    (∫ p,physicalVisible (frequencyRun K p.1 p.2 dir z t) ∂rotationMeasure A).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply integral_nonneg
  intro p
  exact (partialTraceB_posSemidef (Matrix.posSemidef_vecMulVec_self_star _)).nonneg

theorem channel_frequency_distance {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (hq : q+1≤T) (hsize : q<Fintype.card A) (hsmall : 2*q≤Fintype.card A)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (hK : ∀t,(K t).conjTranspose*K t=1) (dir : ℕ→Bool) (z : A×μ 0→ℂ)
    (hz : ‖WithLp.toLp 2 z‖=1) (R : ℝ) (hR : 1≤R) (hd : (Fintype.card A:ℝ)=R^8)
    {O : Type} [Fintype O] [DecidableEq O] (Φ : Channel (A×μ q) O) :
    normalizedTraceDistance
      (Φ.map (∫ p, physicalVisible (frequencyRun K p.1 p.2 dir z q) ∂rotationMeasure A))
      (Φ.map (fockVisible T (WithLp.ofLp (vVector hq K dir z q))))≤9*(q:ℝ)*((q:ℝ)+1)/R := by
  have hp : (fockVisible T (WithLp.ofLp (vVector hq K dir z q))).PosSemidef :=
    partialTraceB_posSemidef (Matrix.posSemidef_vecMulVec_self_star _)
  exact (distance_contract Φ.map Φ.traceNonincreasingCP_map _ _
    (physical_mean_pos K dir z q) hp).trans
    (frequency_visible_distance hT hq hsize hsmall K hK dir z hz R hR hd)

variable {M O : Type} [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

theorem physical_mean_endpoint {q : ℕ} (tail : Protocol A (A×M) O q)
    (v : A×M→ℂ) (n : ℕ) :
    (stageErasure tail n).map
      (∫ p,physicalVisible (physicalFrequency tail p.1 p.2 v (2*n)) ∂rotationMeasure A)=
      haarDensity tail v n := by
  have hc := physical_visible_continuous (known tail.tailKnown 0) direction
    (ICO.ProtocolLudersTrajectory.run tail (1:CMatrix A) v 0) (2*n)
  change Continuous (fun p : Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ =>
    physicalVisible (physicalFrequency tail p.1 p.2 v (2*n))) at hc
  have hi := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ:=rotationMeasure A)
  have hm := (stageErasure tail n).map.toContinuousLinearMap.integral_comp_comm hi
  change (∫ p,(stageErasure tail n).map
    (physicalVisible (physicalFrequency tail p.1 p.2 v (2*n))) ∂rotationMeasure A)=
    (stageErasure tail n).map (∫ p,physicalVisible (physicalFrequency tail p.1 p.2 v (2*n))
      ∂rotationMeasure A) at hm
  rw [← hm]
  have hfi := ((stageErasure tail n).map.continuous_of_finiteDimensional.comp hc).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ:=rotationMeasure A)
  dsimp only [Function.comp_def] at hfi
  rw [rotationMeasure,integral_prod_symm _ hfi]
  simp_rw [stageErasure_apply]
  exact physical_frequency_haar tail v n

/-- Complete actual Haar-to-recording comparison for n physical Lüders calls.
All adaptive-circuit, copied-history, signed-query, Haar and recording bridges
are included. The small-budget range is explicit. -/
theorem protocol_haar_recording {q : ℕ} (tail : Protocol A (A×M) O q)
    (v : A×M→ℂ) (hv : ‖WithLp.toLp 2 v‖=1) (n : ℕ)
    (hsmall : 4*n≤Fintype.card A) (R : ℝ) (hR : 1≤R) (hd : (Fintype.card A:ℝ)=R^8) :
    normalizedTraceDistance (haarDensity tail v n)
      (visible n (ICO.ProtocolRecordingTrajectory.run tail forwardRecording v n))≤
        9*(2*(n:ℝ))*(2*(n:ℝ)+1)/R := by
  let T := 2*Fintype.card (A×A)+2*n+1
  have hT : 2*Fintype.card (A×A)≤T := by dsimp [T]; omega
  have hq : 2*n+1≤T := by dsimp [T]; omega
  have hn : 2*n<Fintype.card A := by have hpos := Fintype.card_pos (α:=A); omega
  have hs : 2*(2*n)≤Fintype.card A := by omega
  have hz : ‖WithLp.toLp 2 (ICO.ProtocolLudersTrajectory.run tail (1:CMatrix A) v 0)‖=1 :=
    (physical_initial_norm tail v).trans hv
  have hh := channel_frequency_distance hT hq hn hs (known tail.tailKnown 0)
    (fun t => known_isometry tail.tailKnown tail.tailKnown_isometry 0 t) direction
    (ICO.ProtocolLudersTrajectory.run tail (1:CMatrix A) v 0) hz R hR hd (stageErasure tail n)
  change normalizedTraceDistance
    ((stageErasure tail n).map (∫ p,physicalVisible (physicalFrequency tail p.1 p.2 v (2*n)) ∂rotationMeasure A))
    ((stageErasure tail n).map (fockVisible T (ICO.MHFockTrajectory.run T (known tail.tailKnown 0)
      (fun t => Vchoice hq (direction t)) (ICO.ProtocolLudersTrajectory.run tail (1:CMatrix A) v 0) (2*n))))≤_ at hh
  rw [physical_mean_endpoint,fock_visible_endpoint tail v n hq hT hn] at hh
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh

#print axioms protocol_haar_recording
end
end ICO.MHProtocolHaarRecording
