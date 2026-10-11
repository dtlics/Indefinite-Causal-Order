import ICO.MHDecompressionStep
import ICO.MHDecompressionNorm
import ICO.MHFockRunContinuity
import ICO.MHProjectedProtocol
import ICO.MHOutputMixture
import ICO.MHDomainMeanProduct

/-! Canonical physical frequency-oracle trajectories and their actual
rotated-W decompressions, with changing public memory and signed queries. -/
namespace ICO.MHDecompressionHybrid
open Matrix QIT MeasureTheory ICO.MHDecompressionKnown ICO.MHDecompressionInitial
  ICO.MHDecompressionStep ICO.MHDecompressionNorm ICO.MHDecompressionErasure
  ICO.MHRotatedDecompressionDefect ICO.MHRotatedTrajectory ICO.MHRectangularAction
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockTrajectory ICO.MHFockKnownOperation
  ICO.MHFockRunIsometry ICO.MHFockRunContinuity ICO.MHWDomainProjection ICO.MHTernaryCompression
  ICO.MHFockSupportProjection ICO.MHFockDecompressionDefect ICO.MHDecompressionDefect
  ICO.MHDomainMeanProduct ICO.MHProjectedProtocol
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 512
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  {μ : ℕ→Type} [∀t,Fintype (μ t)] [∀t,DecidableEq (μ t)]

def frequencyRun (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (C D : Matrix.unitaryGroup A ℂ) (dir : ℕ→Bool) (z : A×μ 0→ℂ) :
    (t:ℕ)→(A×Environment A)×μ t→ℂ
  | 0 => frequencyInitial z
  | t+1 => physicalStep (K t) C D (dir t)*ᵥfrequencyRun K C D dir z t

def frequencyVector (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (dir : ℕ→Bool) (z : A×μ 0→ℂ) (t:ℕ)
    (p : Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ) : EuclideanSpace ℂ ((A×Environment A)×μ t) :=
  WithLp.toLp 2 (frequencyRun K p.1 p.2 dir z t)

def recordingVector {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (dir : ℕ→Bool) (z : A×μ 0→ℂ) (t:ℕ)
    (p : Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ) : EuclideanSpace ℂ (InputCutoff (α := A) T×μ t) :=
  WithLp.toLp 2 (MHFockTrajectory.run T K (fun s => rotatedW hT p.1 p.2 (dir s)) z t)

theorem physicalStep_isometry {M N : Type} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
    (K : Matrix (A×N) (A×M) ℂ) (hK : K.conjTranspose*K=1)
    (C D : Matrix.unitaryGroup A ℂ) (dir : Bool) :
    (physicalStep K C D dir).conjTranspose*physicalStep K C D dir=1 := by
  rw [physicalStep,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (physicalKnown K).conjTranspose (physicalKnown K),physicalKnown_isometry K hK,Matrix.one_mul]
  exact (spectatorUnitary (physicalRotated C D dir) M).property.1

theorem frequencyVector_next (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (dir : ℕ→Bool) (z : A×μ 0→ℂ) (t:ℕ) (p : Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ) :
    frequencyVector K dir z (t+1) p=rectAct (physicalStep (K t) p.1 p.2 (dir t)) (frequencyVector K dir z t p) := rfl

theorem recordingVector_next {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (dir : ℕ→Bool) (z : A×μ 0→ℂ) (t:ℕ)
    (p : Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ) :
    recordingVector hT K dir z (t+1) p=rectAct (recordingStep hT (K t) p.1 p.2 (dir t)) (recordingVector hT K dir z t p) := by
  unfold recordingVector at *
  change WithLp.toLp 2 (known T (K t)*ᵥ(_*ᵥ_))=WithLp.toLp 2 ((known T (K t)*_)*ᵥ_)
  rw [Matrix.mulVec_mulVec]
  rfl

theorem recordingVector_bij {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (dir : ℕ→Bool) (z : A×μ 0→ℂ) (t:ℕ)
    (p : Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ) :
    rectAct (Matrix.kronecker (bijProjection T) (1 : CMatrix (μ t))) (recordingVector hT K dir z t p)=
      recordingVector hT K dir z t p :=
  congrArg (WithLp.toLp 2) (rotatedRun_bij_fixed hT p.1 p.2 K dir z t)

theorem recordingVector_norm {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (hK : ∀t,(K t).conjTranspose*K t=1)
    (dir : ℕ→Bool) (z : A×μ 0→ℂ) (hz : ‖WithLp.toLp 2 z‖≤1) (t:ℕ)
    (p : Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ) : ‖recordingVector hT K dir z t p‖≤1 :=
  MHFockRunIsometry.run_norm_le T K hK _ (fun s => rotatedW_norm_le hT p.1 p.2 (dir s))
    (WithLp.toLp 2 z) hz t

theorem frequencyInitial_norm (z : A×μ 0→ℂ) : ‖WithLp.toLp 2 (frequencyInitial z)‖=‖WithLp.toLp 2 z‖ := by
  let T := 2*Fintype.card (A×A)
  have hT : 2*Fintype.card (A×A)≤T := le_rfl
  rw [← decompression_initial hT]
  change ‖rectAct (memoryD hT (μ 0)) (WithLp.toLp 2 (initial T z))‖=_
  have hx : rectAct (Matrix.kronecker (bijProjection T) (1 : CMatrix (μ 0))) (WithLp.toLp 2 (initial T z)) = WithLp.toLp 2 (initial T z) := congrArg (WithLp.toLp 2) (bij_fixed _ (initial_bij T z))
  rw [decompression_norm hT _ hx]
  exact initial_norm T (WithLp.toLp 2 z)

theorem frequencyVector_norm (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (hK : ∀t,(K t).conjTranspose*K t=1) (dir : ℕ→Bool) (z : A×μ 0→ℂ) (t:ℕ)
    (p : Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ) :
    ‖frequencyVector K dir z t p‖=‖WithLp.toLp 2 z‖ := by
  induction t with
  | zero => exact frequencyInitial_norm z
  | succ t ih => rw [frequencyVector_next,rectAct_norm _ (physicalStep_isometry _ (hK t) _ _ _),ih]

theorem physicalRotated_continuous (dir : Bool) :
    Continuous (fun p : Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ =>
      (physicalRotated p.1 p.2 dir : CMatrix (A×Environment A))) := by
  have hpre := tensor_identity_continuous (μ := Environment A) _ (continuous_subtype_val.comp (before_continuous (α := A) dir))
  have hpost := tensor_identity_continuous (μ := Environment A) _ (continuous_subtype_val.comp (after_continuous (α := A) dir))
  exact (hpost.matrix_mul continuous_const).matrix_mul hpre

theorem physicalStep_continuous {M N : Type} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
    (K : Matrix (A×N) (A×M) ℂ) (dir : Bool) :
    Continuous (fun p : Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ => physicalStep K p.1 p.2 dir) :=
  continuous_const.matrix_mul (tensor_identity_continuous _ (physicalRotated_continuous dir))

theorem frequencyVector_continuous (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (dir : ℕ→Bool) (z : A×μ 0→ℂ) (t:ℕ) : Continuous (frequencyVector K dir z t) := by
  have hh : ∀ t, Continuous (fun p : Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ => frequencyRun K p.1 p.2 dir z t) := by
    intro t
    induction t with
    | zero => exact continuous_const
    | succ t ih => exact (physicalStep_continuous (K t) (dir t)).matrix_mulVec ih
  exact (PiLp.continuous_toLp 2 _).comp (hh t)

theorem recordingVector_continuous {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (dir : ℕ→Bool) (z : A×μ 0→ℂ) (t:ℕ) :
    Continuous (recordingVector hT K dir z t) := by
  have hh : ∀ t, Continuous (fun p : Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ =>
      MHFockTrajectory.run T K (fun s => rotatedW hT p.1 p.2 (dir s)) z t) := by
    intro t
    induction t with
    | zero => exact continuous_const
    | succ t ih =>
      exact (continuous_const (y := known T (K t))).matrix_mulVec
        ((tensor_identity_continuous (μ := μ t) _ (rotatedW_continuous hT (dir t))).matrix_mulVec ih)
  exact (PiLp.continuous_toLp 2 _).comp (hh t)

#print axioms frequencyVector_norm
#print axioms recordingVector_continuous
end
end ICO.MHDecompressionHybrid