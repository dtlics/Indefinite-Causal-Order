import ICO.MHFrequencyFourier
import ICO.MHDecompressionHybrid
import ICO.DoubleQuerySchedule
import ICO.ProtocolHaarOutput

namespace ICO.MHFrequencyTrajectory
open Matrix QIT MeasureTheory ICO.MHTernaryCompression ICO.MHFrequencyFourier
  ICO.MHControlledMixture ICO.MHDecompressionHybrid ICO.MHDecompressionInitial
  ICO.MHDecompressionErasure ICO.MHPhasePermutation ICO.DoubleQuerySchedule
  ICO.SequentialIsometry ICO.RecordingPurifiedProtocol ICO.PureHybrid
  ICO.MHHaarPurifiedMixture ICO.ProtocolHaarOutput
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ : ℕ → Type} [∀t,Fintype (μ t)] [∀t,DecidableEq (μ t)]

def fiberStep (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (C D : Matrix.unitaryGroup A ℂ) (dir : ℕ→Bool) (t : ℕ) (e : Environment A) :
    Matrix (A×μ (t+1)) (A×μ t) ℂ :=
  K t*Matrix.kronecker (hiddenChoice C D (dir t) e) (1 : CMatrix (μ t))

theorem frequency_transform (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (C D : Matrix.unitaryGroup A ℂ) (dir : ℕ→Bool) (z : A×μ 0→ℂ) (t : ℕ) :
    transform (frequencyRun K C D dir z t)=
      controlledTrajectory (H:=fun t => A×μ t) (fiberStep K C D dir) (fun _ => z) (uniformAmplitude (A:=A)) t := by
  induction t with
  | zero => exact transform_initial z
  | succ t ih =>
    rw [frequencyRun,transform_step,ih]
    rfl

theorem frequency_fibers (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (C D : Matrix.unitaryGroup A ℂ) (dir : ℕ→Bool) (z : A×μ 0→ℂ)
    (t : ℕ) (o : A×μ t) (e : Environment A) :
    transform (frequencyRun K C D dir z t) (o,e)=
      uniformAmplitude (A:=A)*fiberTrajectory (H:=fun t => A×μ t) (fiberStep K C D dir) (fun _ => z) t e o := by
  rw [frequency_transform]
  exact trajectory_fibers _ _ _ _ _ _

theorem doubled_fiber (K : (t : ℕ) → Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (C D : Matrix.unitaryGroup A ℂ) (z : A×Memory (A:=A) μ 0 0→ℂ)
    (t : ℕ) (e : Environment A) :
    fiberTrajectory (H:=fun t => A×Memory (A:=A) μ 0 t)
      (fiberStep (μ:=fun t => Memory (A:=A) μ 0 t) (known K 0) C D direction) (fun _ => z) t e=
      runFrom K (hiddenUnitary C D e : CMatrix A) 0 z t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [fiberTrajectory,fiberStep,runFrom,hiddenChoice,oracle,
      Matrix.mulVec_mulVec,ih]

variable {M O : Type} [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

def physicalFrequency {q : ℕ} (tail : Protocol A (A×M) O q)
    (C D : Matrix.unitaryGroup A ℂ) (v : A×M→ℂ) (t : ℕ) :=
  frequencyRun (known tail.tailKnown 0) C D direction
    (ICO.ProtocolLudersTrajectory.run tail (1:CMatrix A) v 0) t

theorem physical_frequency_fibers {q : ℕ} (tail : Protocol A (A×M) O q)
    (C D : Matrix.unitaryGroup A ℂ) (v : A×M→ℂ) (n : ℕ)
    (o : A×Memory (A:=A) tail.tailMemory 0 (2*n)) (e : Environment A) :
    transform (physicalFrequency tail C D v (2*n)) (o,e)=
      uniformAmplitude (A:=A)*
        ICO.ProtocolLudersTrajectory.run tail (hiddenUnitary C D e : CMatrix A) v n
          (zeroEquiv (A:=A) (μ:=tail.tailMemory) A n o) := by
  rw [physicalFrequency,frequency_fibers,doubled_fiber]
  have hi : ICO.ProtocolLudersTrajectory.run tail (1:CMatrix A) v 0=
      ICO.ProtocolLudersTrajectory.run tail (hiddenUnitary C D e : CMatrix A) v 0 := rfl
  rw [hi,physical_even]
  rfl

theorem physical_frequency_visible {q : ℕ} (tail : Protocol A (A×M) O q)
    (C D : Matrix.unitaryGroup A ℂ) (v : A×M→ℂ) (n : ℕ) :
    (physicalVisible (physicalFrequency tail C D v (2*n))).submatrix
      (zeroEquiv (A:=A) (μ:=tail.tailMemory) A n).symm
      (zeroEquiv (A:=A) (μ:=tail.tailMemory) A n).symm =
      partialTraceB (outer (purifiedResponse (response tail v n) C D)
        (purifiedResponse (response tail v n) C D)) := by
  rw [← transform_visible]
  ext i j
  simp only [partialTraceB,Matrix.submatrix_apply,rankOneMatrix_apply,outer,
    Matrix.vecMulVec_apply,PiLp.toLp_apply]
  apply Finset.sum_congr rfl
  intro e _
  rw [physical_frequency_fibers,physical_frequency_fibers]
  simp only [Equiv.apply_symm_apply,purifiedResponse,response,PiLp.toLp_apply,hiddenUnitary]

theorem physical_frequency_haar {q : ℕ} (tail : Protocol A (A×M) O q)
    (v : A×M→ℂ) (n : ℕ) :
    (∫ D, ∫ C, ICO.RecordingHistory.eraseHistory.map
      ((physicalVisible (physicalFrequency tail C D v (2*n))).submatrix
        (zeroEquiv (A:=A) (μ:=tail.tailMemory) A n).symm
        (zeroEquiv (A:=A) (μ:=tail.tailMemory) A n).symm)
      ∂unitaryHaarMeasure (a:=A) ∂unitaryHaarMeasure (a:=A)) = haarDensity tail v n := by
  simp_rw [physical_frequency_visible]
  exact purified_haar_visible tail v n

#print axioms physical_frequency_visible
#print axioms physical_frequency_haar
#print axioms frequency_transform
#print axioms physical_frequency_fibers
end
end ICO.MHFrequencyTrajectory
