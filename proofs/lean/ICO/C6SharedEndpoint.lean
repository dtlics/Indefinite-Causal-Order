import ICO.C6SharedFrequency
import ICO.C6ChoiceOutput
import ICO.DoubleScheduleErasure
import ICO.MHProtocolHaarRecording

namespace ICO.C6SharedEndpoint
open Matrix QIT MeasureTheory ICO.SequentialIsometry ICO.ClassicalDilation
  ICO.RecordingHistory ICO.RecordingPurifiedProtocol ICO.C6SharedBasis ICO.C6SharedStages
  ICO.C6SharedSchedule ICO.C6SharedQuerySchedule ICO.MHDecompressionErasure
  ICO.MHDomainMeanProduct ICO.MHProtocolHaarRecording ICO.MHActualRecordingOverlap
  ICO.MHFockFiniteErasure ICO.PureHybrid
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {A M O : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

local instance cmContinuousENorm {I : Type} [Fintype I] [DecidableEq I] :
    ContinuousENorm (CMatrix I) := SeminormedAddGroup.toContinuousENorm

def initial {q:ℕ} (tail : Protocol (A×Bool) ((A×Bool)×M) O q) (v:(A×Bool)×M→ℂ) :
    (A×Bool)×Memory (A:=A) tail.tailMemory 0 0→ℂ :=
  ICO.ProtocolLudersTrajectory.run tail (1:CMatrix (A×Bool)) v 0

def endpointEquiv {q:ℕ} (tail : Protocol (A×Bool) ((A×Bool)×M) O q) (n:ℕ) :
    (A×QueryMemory (A:=A) tail.tailMemory 0 (2*n)) ≃
      ((A×Bool)×(History (A×Bool) n×tail.tailMemory n)) :=
  (regroup (Memory (A:=A) tail.tailMemory 0 (2*n))).symm.trans
    (ICO.DoubleQuerySchedule.zeroEquiv (A:=A×Bool) (μ:=tail.tailMemory) (A×Bool) n)

def stageErasure {q:ℕ} (tail : Protocol (A×Bool) ((A×Bool)×M) O q) (n:ℕ) :
    Channel (A×QueryMemory (A:=A) tail.tailMemory 0 (2*n)) ((A×Bool)×tail.tailMemory n) :=
  eraseHistory.comp (isometryChannel (permutation (endpointEquiv tail n)) (permutation_isometry _))

theorem stageErasure_apply {q:ℕ} (tail : Protocol (A×Bool) ((A×Bool)×M) O q) (n:ℕ)
    (X:CMatrix (A×QueryMemory (A:=A) tail.tailMemory 0 (2*n))) :
    (stageErasure tail n).map X=eraseHistory.map
      (X.submatrix (endpointEquiv tail n).symm (endpointEquiv tail n).symm) := by
  change eraseHistory.map ((isometryChannel _ _).map X)=_
  rw [isometryChannel_apply,permutation_sandwich]

theorem run_physical {q:ℕ} (tail : Protocol (A×Bool) ((A×Bool)×M) O q)
    (U H : Matrix.unitaryGroup A ℂ) (v:(A×Bool)×M→ℂ) (n:ℕ) :
    ICO.C6SharedQuerySchedule.run H tail.tailKnown U 0 (initial tail v) (2*n)=
      ICO.ProtocolLudersTrajectory.run tail (basis U H:CMatrix (A×Bool)) v n ∘ endpointEquiv tail n := by
  have hi : initial tail v=ICO.ProtocolLudersTrajectory.run tail
      (basis U H:CMatrix (A×Bool)) v 0 := rfl
  rw [ICO.C6SharedQuerySchedule.run,hi,tagged_physical_even]
  rfl

theorem stageErasure_run {q:ℕ} (tail : Protocol (A×Bool) ((A×Bool)×M) O q)
    (U H : Matrix.unitaryGroup A ℂ) (v:(A×Bool)×M→ℂ) (n:ℕ) :
    (stageErasure tail n).map (rankOneMatrix
      (ICO.C6SharedQuerySchedule.run H tail.tailKnown U 0 (initial tail v) (2*n)))=
      eraseHistory.map (rankOneMatrix
        (ICO.ProtocolLudersTrajectory.run tail (basis U H:CMatrix (A×Bool)) v n)) := by
  rw [stageErasure_apply,run_physical]
  congr 1
  ext i j
  simp [Matrix.submatrix_apply,rankOneMatrix_apply]

def haarDensity {q:ℕ} (tail : Protocol (A×Bool) ((A×Bool)×M) O q)
    (H : Matrix.unitaryGroup A ℂ) (v:(A×Bool)×M→ℂ) (n:ℕ) :
    CMatrix ((A×Bool)×tail.tailMemory n) :=
  ∫U,eraseHistory.map (rankOneMatrix
    (ICO.ProtocolLudersTrajectory.run tail (basis U H:CMatrix (A×Bool)) v n))
    ∂unitaryHaarMeasure (a:=A)

theorem physical_mean_endpoint {q:ℕ} (tail : Protocol (A×Bool) ((A×Bool)×M) O q)
    (H : Matrix.unitaryGroup A ℂ) (v:(A×Bool)×M→ℂ) (n:ℕ) :
    (stageErasure tail n).map (∫p,physicalVisible
      (ICO.C6SharedFrequency.frequency H tail.tailKnown p.1 p.2 0 (initial tail v) (2*n))
      ∂rotationMeasure A)=haarDensity tail H v n := by
  have hc := physical_visible_continuous (known H tail.tailKnown 0)
    ICO.DoubleQuerySchedule.direction
    (initial tail v ∘ (regroup (Memory (A:=A) tail.tailMemory 0 0)).symm) (2*n)
  change Continuous (fun p:Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ =>
    physicalVisible (ICO.C6SharedFrequency.frequency H tail.tailKnown p.1 p.2 0
      (initial tail v) (2*n))) at hc
  have hi := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ:=rotationMeasure A)
  have hm := (stageErasure tail n).map.toContinuousLinearMap.integral_comp_comm hi
  change (∫p,(stageErasure tail n).map (physicalVisible
    (ICO.C6SharedFrequency.frequency H tail.tailKnown p.1 p.2 0 (initial tail v) (2*n)))
    ∂rotationMeasure A)=(stageErasure tail n).map _ at hm
  rw [←hm]
  have hfi := ((stageErasure tail n).map.continuous_of_finiteDimensional.comp hc).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ:=rotationMeasure A)
  dsimp only [Function.comp_def] at hfi
  rw [rotationMeasure,integral_prod_symm _ hfi]
  rw [ICO.C6SharedFrequency.frequency_haar]
  simp only [stageErasure_run,haarDensity]

theorem initial_norm {q:ℕ} (tail : Protocol (A×Bool) ((A×Bool)×M) O q)
    (v:(A×Bool)×M→ℂ) :
    ‖WithLp.toLp 2 (initial tail v ∘ (regroup (Memory (A:=A) tail.tailMemory 0 0)).symm)‖=
      ‖WithLp.toLp 2 v‖ := by
  have he := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (regroup (Memory (A:=A) tail.tailMemory 0 0))).norm_map (WithLp.toLp 2 (initial tail v))
  change ‖WithLp.toLp 2 (initial tail v ∘ (regroup (Memory (A:=A) tail.tailMemory 0 0)).symm)‖=
    ‖WithLp.toLp 2 (initial tail v)‖ at he
  exact he.trans (ICO.DoubleScheduleErasure.physical_initial_norm tail v)

#print axioms physical_mean_endpoint
#print axioms initial_norm
end
end ICO.C6SharedEndpoint
