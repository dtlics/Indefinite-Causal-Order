import ICO.C6SharedQuerySchedule
import ICO.MHFrequencyTrajectory

/-! The physical shared-unitary response of the adaptive tagged circuit is
exactly the Haar average obtained by erasing the phase-permutation oracle. -/
namespace ICO.C6SharedFrequency
open Matrix QIT MeasureTheory ICO.MHTernaryCompression ICO.MHFrequencyFourier
  ICO.MHControlledMixture ICO.MHDecompressionHybrid ICO.MHDecompressionInitial
  ICO.MHDecompressionErasure ICO.MHPhasePermutation ICO.MHFrequencyTrajectory
  ICO.MHHaarPurifiedMixture ICO.C6SharedBasis ICO.C6SharedStages ICO.C6SharedSchedule
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ : ℕ→Type} [∀t,Fintype (μ t)] [∀t,DecidableEq (μ t)]

theorem run_continuous (H : Matrix.unitaryGroup A ℂ)
    (K : (t:ℕ)→Matrix ((A×Bool)×μ (t+1)) ((A×Bool)×μ t) ℂ)
    (k:ℕ) (v:(A×Bool)×Memory (A:=A) μ k 0→ℂ) (n:ℕ) :
    Continuous (fun U : Matrix.unitaryGroup A ℂ => ICO.C6SharedQuerySchedule.run H K U k v n) := by
  induction n with
  | zero =>
    change Continuous (fun _ : Matrix.unitaryGroup A ℂ => v ∘
      (regroup (Memory (A:=A) μ k 0)).symm)
    exact continuous_const
  | succ n ih =>
    simp only [ICO.C6SharedQuerySchedule.run_succ]
    apply (continuous_const : Continuous (fun _ : Matrix.unitaryGroup A ℂ =>
      ICO.C6SharedQuerySchedule.known H K k n)).matrix_mulVec
    apply Continuous.matrix_mulVec _ ih
    apply continuous_matrix
    intro i j
    simp only [ICO.DoubleQuerySchedule.oracle]
    split_ifs <;> simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.conjTranspose_apply]
    · exact (continuous_subtype_val.matrix_elem j.1 i.1).star.mul continuous_const
    · exact (continuous_subtype_val.matrix_elem i.1 j.1).mul continuous_const

def response (H : Matrix.unitaryGroup A ℂ)
    (K : (t:ℕ)→Matrix ((A×Bool)×μ (t+1)) ((A×Bool)×μ t) ℂ)
    (k:ℕ) (v:(A×Bool)×Memory (A:=A) μ k 0→ℂ) (n:ℕ) (U : Matrix.unitaryGroup A ℂ) :
    EuclideanSpace ℂ (A×ICO.C6SharedQuerySchedule.QueryMemory (A:=A) μ k n) :=
  WithLp.toLp 2 (ICO.C6SharedQuerySchedule.run H K U k v n)

theorem response_continuous (H : Matrix.unitaryGroup A ℂ)
    (K : (t:ℕ)→Matrix ((A×Bool)×μ (t+1)) ((A×Bool)×μ t) ℂ)
    (k:ℕ) (v:(A×Bool)×Memory (A:=A) μ k 0→ℂ) (n:ℕ) : Continuous (response H K k v n) :=
  (PiLp.continuous_toLp 2 _).comp (run_continuous H K k v n)

def frequency (H : Matrix.unitaryGroup A ℂ)
    (K : (t:ℕ)→Matrix ((A×Bool)×μ (t+1)) ((A×Bool)×μ t) ℂ)
    (C D : Matrix.unitaryGroup A ℂ) (k:ℕ) (v:(A×Bool)×Memory (A:=A) μ k 0→ℂ) (n:ℕ) :=
  frequencyRun (ICO.C6SharedQuerySchedule.known H K k) C D ICO.DoubleQuerySchedule.direction
    (v ∘ (regroup (Memory (A:=A) μ k 0)).symm) n

theorem fiber_eq_run (H : Matrix.unitaryGroup A ℂ)
    (K : (t:ℕ)→Matrix ((A×Bool)×μ (t+1)) ((A×Bool)×μ t) ℂ)
    (C D : Matrix.unitaryGroup A ℂ) (k:ℕ) (v:(A×Bool)×Memory (A:=A) μ k 0→ℂ)
    (n:ℕ) (e:Environment A) :
    fiberTrajectory (H:=fun t=>A×ICO.C6SharedQuerySchedule.QueryMemory (A:=A) μ k t)
      (fiberStep (ICO.C6SharedQuerySchedule.known H K k) C D
      ICO.DoubleQuerySchedule.direction) (fun _=>v ∘ (regroup (Memory (A:=A) μ k 0)).symm) n e=
      ICO.C6SharedQuerySchedule.run H K (hiddenUnitary C D e) k v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ICO.C6SharedQuerySchedule.run_succ]
    simp only [fiberTrajectory,fiberStep,hiddenChoice,ICO.DoubleQuerySchedule.oracle,
      Matrix.mulVec_mulVec,ih]

theorem frequency_visible (H : Matrix.unitaryGroup A ℂ)
    (K : (t:ℕ)→Matrix ((A×Bool)×μ (t+1)) ((A×Bool)×μ t) ℂ)
    (C D : Matrix.unitaryGroup A ℂ) (k:ℕ) (v:(A×Bool)×Memory (A:=A) μ k 0→ℂ) (n:ℕ) :
    physicalVisible (frequency H K C D k v n)=
      partialTraceB (ICO.PureHybrid.outer (purifiedResponse (response H K k v n) C D)
        (purifiedResponse (response H K k v n) C D)) := by
  rw [←transform_visible]
  ext i j
  simp only [partialTraceB,rankOneMatrix_apply,ICO.PureHybrid.outer,Matrix.vecMulVec_apply,
    PiLp.toLp_apply]
  apply Finset.sum_congr rfl
  intro e he
  simp only [frequency,frequency_fibers,fiber_eq_run,purifiedResponse,response,
    PiLp.toLp_apply,hiddenUnitary]

theorem frequency_haar {O : Type} [Fintype O] [DecidableEq O]
    (Φ:MatrixMap (A×ICO.C6SharedQuerySchedule.QueryMemory (A:=A) μ k n) O)
    (H : Matrix.unitaryGroup A ℂ)
    (K : (t:ℕ)→Matrix ((A×Bool)×μ (t+1)) ((A×Bool)×μ t) ℂ)
    (v:(A×Bool)×Memory (A:=A) μ k 0→ℂ) :
    (∫D,∫C,Φ (physicalVisible (frequency H K C D k v n))
      ∂unitaryHaarMeasure (a:=A) ∂unitaryHaarMeasure (a:=A)) =
    ∫U,Φ (rankOneMatrix (ICO.C6SharedQuerySchedule.run H K U k v n))
      ∂unitaryHaarMeasure (a:=A) := by
  simp_rw [frequency_visible]
  exact erased_haar_two Φ (response H K k v n) (response_continuous H K k v n)

#print axioms frequency_haar
end
end ICO.C6SharedFrequency
